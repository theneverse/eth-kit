// Copyright 2014 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

// Package state provides a caching layer atop the Ethereum state trie.
package ledger

import (
	"fmt"
	"math/big"
	"sort"
	"sync"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/log"
	"github.com/sirupsen/logrus"
	types2 "github.com/theneverse/neverse-kit/types"
	"github.com/theneverse/neverse-model/pb"
)

type revision struct {
	id           int
	journalIndex int
}

var (
	// emptyRoot is the known root hash of an empty trie.
	emptyRoot = common.HexToHash("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
)

type proofList [][]byte

func (n *proofList) Put(key []byte, value []byte) error {
	*n = append(*n, value)
	return nil
}

func (n *proofList) Delete(key []byte) error {
	panic("not supported")
}

var _ StateLedger = (*ComplexStateLedger)(nil)

// ComplexStateLedger structs within the ethereum protocol are used to store anything
// within the merkle trie. StateDBs take care of caching and storing
// nested states. It's the general query interface to retrieve:
// * Contracts
// * Accounts
type ComplexStateLedger struct {
	db           state.Database
	originalRoot *types2.Hash // The pre-state root, before any changes were made
	trie         state.Trie
	hasher       crypto.KeccakState

	// This map holds 'live' objects, which will get modified while processing a state transition.
	stateObjects        map[string]*StateObject
	stateObjectsPending map[string]struct{} // State objects finalized but not yet written to the trie
	stateObjectsDirty   map[string]struct{} // State objects modified in the current execution

	// DB error.
	// State objects are used by the consensus core and VM which are
	// unable to deal with database-level errors. Any error that occurs
	// during a database read is memoized here and will eventually be returned
	// by ComplexStateLedger.Commit.
	dbErr error

	// The refund counter, also used by state transitioning.
	refund uint64

	thash, bhash *types2.Hash
	height       uint64
	txIndex      int
	logs         map[string][]*pb.EvmLog
	logSize      uint
	events       sync.Map

	preimages map[string][]byte

	// Per-transaction access list
	accessList *AccessList

	// Journal of state modifications. This is the backbone of
	// Snapshot and RevertToSnapshot.
	journal        *journal
	validRevisions []revision
	nextRevisionId int
	logger         logrus.FieldLogger
}

func (l *ComplexStateLedger) GetMaxHeight() uint64 {
	panic("implement me")
}

func (l *ComplexStateLedger) RollbackState(height uint64) error {
	return nil
}

func (s *ComplexStateLedger) GetOrCreateAccount(address *types2.Address) IAccount {
	stateObject := s.getStateObject(address)
	if stateObject == nil {
		stateObject, _ = s.createObject(address)
	}
	return stateObject
}

func (s *ComplexStateLedger) GetAccount(address *types2.Address) IAccount {
	return s.getStateObject(address)
}

func (s *ComplexStateLedger) GetBalance(address *types2.Address) *big.Int {
	stateObject := s.getStateObject(address)
	if stateObject != nil {
		return stateObject.GetBalance()
	}
	return common.Big0
}

func (s *ComplexStateLedger) SetBalance(address *types2.Address, b *big.Int) {
	stateObject := s.GetOrCreateAccount(address)
	if stateObject != nil {
		stateObject.SetBalance(b)
	}
}

func (s *ComplexStateLedger) GetState(address *types2.Address, key []byte) (bool, []byte) {
	stateObject := s.getStateObject(address)
	if stateObject != nil {
		return stateObject.GetState(key)
	}
	return false, nil
}

func (s *ComplexStateLedger) SetState(address *types2.Address, key []byte, value []byte) {
	stateObject := s.GetOrCreateAccount(address)
	if stateObject != nil {
		stateObject.SetState(key, value)
	}
}

func (s *ComplexStateLedger) AddState(address *types2.Address, key []byte, value []byte) {
	stateObject := s.GetOrCreateAccount(address)
	if stateObject != nil {
		stateObject.AddState(key, value)
	}
}

func (s *ComplexStateLedger) SetCode(address *types2.Address, code []byte) {
	stateObject := s.GetOrCreateAccount(address)
	if stateObject != nil {
		stateObject.SetCodeAndHash(code)
	}
}

func (s *ComplexStateLedger) GetCode(address *types2.Address) []byte {
	stateObject := s.getStateObject(address)
	if stateObject != nil {
		return stateObject.Code()
	}
	return nil
}

func (s *ComplexStateLedger) SetNonce(address *types2.Address, nonce uint64) {
	stateObject := s.GetOrCreateAccount(address)
	if stateObject != nil {
		stateObject.SetNonce(nonce)
	}
}

func (s *ComplexStateLedger) GetNonce(address *types2.Address) uint64 {
	stateObject := s.getStateObject(address)
	if stateObject != nil {
		return stateObject.GetNonce()
	}

	return 0
}

func (s *ComplexStateLedger) QueryByPrefix(address *types2.Address, prefix string) (bool, [][]byte) {
	stateObject := s.getStateObject(address)
	if stateObject != nil {
		return stateObject.Query(prefix)
	}
	return false, nil
}

func (s *ComplexStateLedger) FlushDirtyData() (map[string]IAccount, *types2.Hash) {
	accounts := make(map[string]IAccount)

	if s.dbErr != nil {
		return nil, nil
	}
	// Finalize any pending changes and merge everything into the tries
	s.IntermediateRoot(true)

	// Commit objects to the trie, measuring the elapsed time
	codeWriter := s.db.TrieDB().DiskDB().NewBatch()
	for addr := range s.stateObjectsDirty {
		if obj := s.stateObjects[addr]; !obj.deleted {
			// Write any contract code associated with the state object
			if obj.code != nil && obj.dirtyCode {
				rawdb.WriteCode(codeWriter, common.BytesToHash(obj.CodeHash()), obj.code)
				obj.dirtyCode = false
			}
			// Write any storage changes in the state object to its storage trie
			if err := obj.CommitTrie(s.db); err != nil {
				return nil, nil
			}
		}
		accounts[addr] = s.stateObjects[addr]
	}
	if len(s.stateObjectsDirty) > 0 {
		s.stateObjectsDirty = make(map[string]struct{})
	}
	if codeWriter.ValueSize() > 0 {
		if err := codeWriter.Write(); err != nil {
			log.Crit("Failed to commit dirty codes", "error", err)
		}
	}
	// The onleaf func is called _serially_, so we can reuse the same account
	// for unmarshalling every time.
	account := &Account{}
	root, err := s.trie.Commit(func(_ [][]byte, _ []byte, leaf []byte, parent common.Hash) error {
		if err := account.Unmarshal(leaf); err != nil {
			return nil
		}
		if account.Root != emptyRoot {
			s.db.TrieDB().Reference(account.Root, parent)
		}
		return nil
	})
	if err != nil {
		return nil, nil
	}

	return accounts, types2.NewHash(root.Bytes())
}

func (s *ComplexStateLedger) Version() uint64 {
	panic("implement me")
}

func (s *ComplexStateLedger) Clear() {
	s.events = sync.Map{}
	s.stateObjects = make(map[string]*StateObject)
	s.stateObjectsPending = make(map[string]struct{})
	s.stateObjectsDirty = make(map[string]struct{})
}

func (s *ComplexStateLedger) AddEvent(event *pb.Event) {
	var events []*pb.Event
	hash := s.thash.String()
	value, ok := s.events.Load(hash)
	if ok {
		events = value.([]*pb.Event)
	}
	events = append(events, event)
	s.events.Store(hash, events)
}

func (s *ComplexStateLedger) Events(txHash string) []*pb.Event {
	events, ok := s.events.Load(txHash)
	if !ok {
		return nil
	}
	return events.([]*pb.Event)
}

func (s *ComplexStateLedger) Rollback(height uint64) error {
	return nil
}

func (s *ComplexStateLedger) PrepareBlock(hash *types2.Hash, height uint64) {
	s.logs = make(map[string][]*pb.EvmLog)
	s.bhash = hash
	s.height = height
}

func (s *ComplexStateLedger) ClearChangerAndRefund() {
	if len(s.journal.entries) > 0 {
		s.journal = newJournal()
		s.refund = 0
	}
	s.validRevisions = s.validRevisions[:0]
	s.nextRevisionId = 0
}

func (s *ComplexStateLedger) Close() {
	s.db.TrieDB().DiskDB().Close()
}

// New creates a new state from a given trie.
func New(root *types2.Hash, db state.Database, logger logrus.FieldLogger) (*ComplexStateLedger, error) {
	//logger.Warnf("OpenTrie root: %s", root.String())
	tr, err := db.OpenTrie(common.BytesToHash(root.RawHash[:]))
	if err != nil {
		return nil, fmt.Errorf("OpenTrie: %v", err)
	}
	sdb := &ComplexStateLedger{
		db:                  db,
		trie:                tr,
		originalRoot:        root,
		stateObjects:        make(map[string]*StateObject),
		stateObjectsPending: make(map[string]struct{}),
		stateObjectsDirty:   make(map[string]struct{}),
		logs:                make(map[string][]*pb.EvmLog),
		preimages:           make(map[string][]byte),
		journal:             newJournal(),
		accessList:          NewAccessList(),
		hasher:              crypto.NewKeccakState(),
		logger:              logger,
	}
	return sdb, nil
}

// setError remembers the first non-nil error it is called with.
func (s *ComplexStateLedger) setError(err error) {
	if s.dbErr == nil {
		s.dbErr = err
	}
}

func (s *ComplexStateLedger) Error() error {
	return s.dbErr
}

func (s *ComplexStateLedger) AddLog(log *pb.EvmLog) {
	s.journal.append(addLogChange{txhash: s.thash})

	log.TransactionHash = s.thash
	log.BlockHash = s.bhash
	log.TransactionIndex = uint64(s.txIndex)
	log.LogIndex = uint64(s.logSize)
	log.BlockNumber = s.height
	s.logs[s.thash.String()] = append(s.logs[s.thash.String()], log)
	s.logSize++
}

func (s *ComplexStateLedger) GetLogs(hash types2.Hash) []*pb.EvmLog {
	return s.logs[hash.String()]
}

// AddPreimage records a SHA3 preimage seen by the VM.
func (s *ComplexStateLedger) AddPreimage(hash types2.Hash, preimage []byte) {
	if _, ok := s.preimages[hash.String()]; !ok {
		s.journal.append(addPreimageChange{hash: &hash})
		pi := make([]byte, len(preimage))
		copy(pi, preimage)
		s.preimages[hash.String()] = pi
	}
}

// AddRefund adds gas to the refund counter
func (s *ComplexStateLedger) AddRefund(gas uint64) {
	s.journal.append(refundChange{prev: s.refund})
	s.refund += gas
}

// SubRefund removes gas from the refund counter.
// This method will panic if the refund counter goes below zero
func (s *ComplexStateLedger) SubRefund(gas uint64) {
	s.journal.append(refundChange{prev: s.refund})
	if gas > s.refund {
		panic(fmt.Sprintf("Refund counter below zero (gas: %d > refund: %d)", gas, s.refund))
	}
	s.refund -= gas
}

// Exist reports whether the given account address exists in the state.
// Notably this also returns true for suicided accounts.
func (s *ComplexStateLedger) Exist(addr *types2.Address) bool {
	return s.getStateObject(addr) != nil
}

// Empty returns whether the state object is either non-existent
// or empty according to the EIP161 specification (balance = nonce = code = 0)
func (s *ComplexStateLedger) Empty(addr *types2.Address) bool {
	so := s.getStateObject(addr)
	return so == nil || so.IsEmpty()
}

func (s *ComplexStateLedger) GetCodeSize(addr *types2.Address) int {
	stateObject := s.getStateObject(addr)
	if stateObject != nil {
		return stateObject.CodeSize(s.db)
	}
	return 0
}

func (s *ComplexStateLedger) GetCodeHash(addr *types2.Address) common.Hash {
	stateObject := s.getStateObject(addr)
	if stateObject == nil {
		return common.Hash{}
	}
	return common.BytesToHash(stateObject.CodeHash())
}

// GetCommittedState retrieves a value from the given account's committed storage trie.
func (s *ComplexStateLedger) GetCommittedState(addr *types2.Address, key []byte) []byte {
	stateObject := s.getStateObject(addr)
	if stateObject != nil {
		return stateObject.GetCommittedState(key)
	}
	return nil
}

// Database retrieves the low level database supporting the lower level trie ops.
func (s *ComplexStateLedger) Database() state.Database {
	return s.db
}

// StorageTrie returns the storage trie of an account.
// The return value is a copy and is nil for non-existent accounts.
func (s *ComplexStateLedger) StorageTrie(addr *types2.Address) state.Trie {
	stateObject := s.getStateObject(addr)
	if stateObject == nil {
		return nil
	}
	cpy := stateObject.deepCopy(s)
	cpy.updateTrie(s.db)
	return cpy.getTrie(s.db)
}

func (s *ComplexStateLedger) HasSuicided(addr *types2.Address) bool {
	stateObject := s.getStateObject(addr)
	if stateObject != nil {
		return stateObject.suicided
	}
	return false
}

/*
 * SETTERS
 */

// AddBalance adds amount to the account associated with addr.
func (s *ComplexStateLedger) AddBalance(addr *types2.Address, amount *big.Int) {
	stateObject := s.GetOrCreateAccount(addr)
	if stateObject != nil {
		stateObject.AddBalance(amount)
	}
}

// SubBalance subtracts amount from the account associated with addr.
func (s *ComplexStateLedger) SubBalance(addr *types2.Address, amount *big.Int) {
	stateObject := s.GetOrCreateAccount(addr)
	if stateObject != nil {
		stateObject.SubBalance(amount)
	}
}

// Suicide marks the given account as suicided.
// This clears the account balance.
//
// The account's state object is still available until the state is committed,
// getStateObject will return a non-nil account after Suicide.
func (s *ComplexStateLedger) Suicide(addr *types2.Address) bool {
	stateObject := s.getStateObject(addr)
	if stateObject == nil {
		return false
	}
	s.journal.append(suicideChange{
		account:     addr,
		prev:        stateObject.suicided,
		prevbalance: new(big.Int).Set(stateObject.GetBalance()),
	})
	stateObject.SetSuicided(true)
	stateObject.data.Balance = new(big.Int)

	return true
}

//
// Setting, updating & deleting state object methods.
//

// updateStateObject writes the given object to the trie.
func (s *ComplexStateLedger) updateStateObject(obj *StateObject) {
	// Encode the account and update the account trie
	addr := obj.GetAddress()

	data, err := obj.data.Marshal()
	if err != nil {
		panic(fmt.Errorf("can't encode object at %s: %v", addr.String(), err))
	}
	if err = s.trie.TryUpdate(addr.RawAddress[:], data); err != nil {
		s.setError(fmt.Errorf("updateStateObject (%s) error: %v", addr.String(), err))
	}
}

// deleteStateObject removes the given object from the state trie.
func (s *ComplexStateLedger) deleteStateObject(obj *StateObject) {
	// Delete the account from the trie
	addr := obj.GetAddress()
	if err := s.trie.TryDelete(addr.RawAddress[:]); err != nil {
		s.setError(fmt.Errorf("deleteStateObject (%s) error: %v", addr.String(), err))
	}
}

// getStateObject retrieves a state object given by the address, returning nil if
// the object is not found or was deleted in this execution context. If you need
// to differentiate between non-existent/just-deleted, use getDeletedStateObject.
func (s *ComplexStateLedger) getStateObject(addr *types2.Address) *StateObject {
	if obj := s.getDeletedStateObject(addr); obj != nil && !obj.deleted {
		return obj
	}
	return nil
}

// getDeletedStateObject is similar to getStateObject, but instead of returning
// nil for a deleted state object, it returns the actual object with the deleted
// flag set. This is needed by the state journal to revert to the correct s-
// destructed object instead of wiping all knowledge about the state object.
func (s *ComplexStateLedger) getDeletedStateObject(addr *types2.Address) *StateObject {
	// Prefer live objects if any is available
	if obj := s.stateObjects[addr.String()]; obj != nil {
		return obj
	}
	// If no live objects are available, attempt to use snapshots
	var (
		data *Account
		err  error
	)
	// Load from the database
	enc, err := s.trie.TryGet(addr.Bytes())
	if err != nil {
		s.setError(fmt.Errorf("getDeleteStateObject (%x) error: %v", addr.Bytes(), err))
		return nil
	}
	if len(enc) == 0 {
		return nil
	}
	data = new(Account)
	if err := data.Unmarshal(enc); err != nil {
		log.Error("Failed to decode state object", "addr", addr, "err", err)
		return nil
	}

	// Insert into the live set
	obj := newObject(s, addr, *data)
	s.setStateObject(obj)
	return obj
}

func (s *ComplexStateLedger) setStateObject(object *StateObject) {
	s.stateObjects[object.GetAddress().String()] = object
}

// createObject creates a new state object. If there is an existing account with
// the given address, it is overwritten and returned as the second return value.
func (s *ComplexStateLedger) createObject(addr *types2.Address) (newobj, prev *StateObject) {
	prev = s.getDeletedStateObject(addr) // Note, prev might have been deleted, we need that!

	newobj = newObject(s, addr, Account{})
	newobj.setNonce(0) // sets the object to dirty
	if prev == nil {
		s.journal.append(createObjectChange{account: addr})
	} else {
		s.journal.append(resetObjectChange{prev: prev, prevdestruct: false})
	}
	s.setStateObject(newobj)
	if prev != nil && !prev.deleted {
		return newobj, prev
	}
	return newobj, nil
}

// Snapshot returns an identifier for the current revision of the state.
func (s *ComplexStateLedger) Snapshot() int {
	id := s.nextRevisionId
	s.nextRevisionId++
	s.validRevisions = append(s.validRevisions, revision{id, s.journal.length()})
	return id
}

// RevertToSnapshot reverts all state changes made since the given revision.
func (s *ComplexStateLedger) RevertToSnapshot(revid int) {
	// Find the snapshot in the stack of valid snapshots.
	idx := sort.Search(len(s.validRevisions), func(i int) bool {
		return s.validRevisions[i].id >= revid
	})
	if idx == len(s.validRevisions) || s.validRevisions[idx].id != revid {
		panic(fmt.Errorf("revision id %v cannot be reverted", revid))
	}
	snapshot := s.validRevisions[idx].journalIndex

	// Replay the journal to undo changes and remove invalidated snapshots
	s.journal.revert(s, snapshot)
	s.validRevisions = s.validRevisions[:idx]
}

// GetRefund returns the current value of the refund counter.
func (s *ComplexStateLedger) GetRefund() uint64 {
	return s.refund
}

// Finalise finalises the state by removing the s destructed objects and clears
// the journal as well as the refunds. Finalise, however, will not push any updates
// into the tries just yet. Only IntermediateRoot or Commit will do that.
func (s *ComplexStateLedger) Finalise(deleteEmptyObjects bool) {
	addressesToPrefetch := make([][]byte, 0, len(s.journal.dirties))
	for addr := range s.journal.dirties {
		obj, exist := s.stateObjects[addr.String()]
		if !exist {
			// ripeMD is 'touched' at block 1714175, in tx 0x1237f737031e40bcde4a8b7e717b2d15e3ecadfe49bb1bbc71ee9deb09c6fcf2
			// That tx goes out of gas, and although the notion of 'touched' does not exist there, the
			// touch-event will still be recorded in the journal. Since ripeMD is a special snowflake,
			// it will persist in the journal even though the journal is reverted. In this special circumstance,
			// it may exist in `s.journal.dirties` but not in `s.stateObjects`.
			// Thus, we can safely ignore it here
			continue
		}
		if obj.suicided || (deleteEmptyObjects && obj.IsEmpty()) {
			obj.deleted = true
		} else {
			obj.finalise(true) // Prefetch slots in the background
		}
		s.stateObjectsPending[addr.String()] = struct{}{}
		s.stateObjectsDirty[addr.String()] = struct{}{}

		// At this point, also ship the address off to the precacher. The precacher
		// will start loading tries, and when the change is eventually committed,
		// the commit-phase will be a lot faster
		addressesToPrefetch = append(addressesToPrefetch, common.CopyBytes(addr.RawAddress[:])) // Copy needed for closure
	}
	// Invalidate journal because reverting across transactions is not allowed.
	s.clearJournalAndRefund()
}

// IntermediateRoot computes the current root hash of the state trie.
// It is called in between transactions to get the root hash that
// goes into transaction receipts.
func (s *ComplexStateLedger) IntermediateRoot(deleteEmptyObjects bool) common.Hash {
	// Finalise all the dirty storage states and write them into the tries
	s.Finalise(deleteEmptyObjects)

	// Although naively it makes sense to retrieve the account trie and then do
	// the contract storage and account updates sequentially, that short circuits
	// the account prefetcher. Instead, let's process all the storage updates
	// first, giving the account prefeches just a few more milliseconds of time
	// to pull useful data from disk.
	for addr := range s.stateObjectsPending {
		if obj := s.stateObjects[addr]; !obj.deleted {
			obj.updateRoot(s.db)
		}
	}
	usedAddrs := make([][]byte, 0, len(s.stateObjectsPending))
	for addr := range s.stateObjectsPending {
		if obj := s.stateObjects[addr]; obj.deleted {
			s.deleteStateObject(obj)
		} else {
			s.updateStateObject(obj)
		}
		usedAddrs = append(usedAddrs, types2.NewAddressByStr(addr).Bytes()) // Copy needed for closure
	}
	if len(s.stateObjectsPending) > 0 {
		s.stateObjectsPending = make(map[string]struct{})
	}
	return s.trie.Hash()
}

func (s *ComplexStateLedger) clearJournalAndRefund() {
	if len(s.journal.entries) > 0 {
		s.journal = newJournal()
		s.refund = 0
	}
	s.validRevisions = s.validRevisions[:0] // Snapshots can be created without journal entires
}

// Commit writes the state to the underlying in-memory trie database.
func (s *ComplexStateLedger) Commit(height uint64, accounts map[string]IAccount, stateRoot *types2.Hash) error {
	return s.db.TrieDB().Commit(common.BytesToHash(stateRoot.Bytes()), false, nil)
}

// PrepareAccessList handles the preparatory steps for executing a state transition with
// regards to both EIP-2929 and EIP-2930:
//
// - Add sender to access list (2929)
// - Add destination to access list (2929)
// - Add precompiles to access list (2929)
// - Add the contents of the optional tx access list (2930)
//
// This method should only be called if Yolov3/Berlin/2929+2930 is applicable at the current number.
func (s *ComplexStateLedger) PrepareAccessList(sender types2.Address, dst *types2.Address, precompiles []types2.Address, list AccessTupleList) {
	s.AddAddressToAccessList(sender)
	if dst != nil {
		s.AddAddressToAccessList(*dst)
		// If it's a create-tx, the destination will be added inside evm.create
	}
	for _, addr := range precompiles {
		s.AddAddressToAccessList(addr)
	}
	for _, el := range list {
		s.AddAddressToAccessList(el.Address)
		for _, key := range el.StorageKeys {
			s.AddSlotToAccessList(el.Address, key)
		}
	}
}

// AddAddressToAccessList adds the given address to the access list
func (s *ComplexStateLedger) AddAddressToAccessList(addr types2.Address) {
	if s.accessList.AddAddress(addr) {
		s.journal.append(accessListAddAccountChange{&addr})
	}
}

// AddSlotToAccessList adds the given (address, slot)-tuple to the access list
func (s *ComplexStateLedger) AddSlotToAccessList(addr types2.Address, slot types2.Hash) {
	addrMod, slotMod := s.accessList.AddSlot(addr, slot)
	if addrMod {
		// In practice, this should not happen, since there is no way to enter the
		// scope of 'address' without having the 'address' become already added
		// to the access list (via call-variant, create, etc).
		// Better safe than sorry, though
		s.journal.append(accessListAddAccountChange{&addr})
	}
	if slotMod {
		s.journal.append(accessListAddSlotChange{
			address: &addr,
			slot:    &slot,
		})
	}
}

// AddressInAccessList returns true if the given address is in the access list.
func (s *ComplexStateLedger) AddressInAccessList(addr types2.Address) bool {
	return s.accessList.ContainsAddress(addr)
}

// SlotInAccessList returns true if the given (address, slot)-tuple is in the access list.
func (s *ComplexStateLedger) SlotInAccessList(addr types2.Address, slot types2.Hash) (addressPresent bool, slotPresent bool) {
	return s.accessList.Contains(addr, slot)
}

func (s *ComplexStateLedger) StateAt(root *types2.Hash) (*ComplexStateLedger, error) {
	return New(root, s.db, s.logger)
}

func (s *ComplexStateLedger) Copy() StateLedger {
	return &ComplexStateLedger{
		db:                  s.db,
		trie:                s.db.CopyTrie(s.trie),
		stateObjects:        make(map[string]*StateObject),
		stateObjectsPending: make(map[string]struct{}),
		stateObjectsDirty:   make(map[string]struct{}),
		logs:                make(map[string][]*pb.EvmLog),
		preimages:           make(map[string][]byte),
		refund:              s.refund,
		logSize:             s.logSize,
		journal:             newJournal(),
		hasher:              crypto.NewKeccakState(),
		accessList:          NewAccessList(),
		logger:              s.logger,
	}
}
