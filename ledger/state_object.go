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

package ledger

import (
	"bytes"
	"encoding/json"
	"fmt"
	"math/big"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/trie"
	types2 "github.com/theneverse/neverse-kit/types"
)

var emptyCodeHash = crypto.Keccak256(nil)

type Code []byte

func (c Code) String() string {
	return string(c) //strings.Join(Disassemble(c), " ")
}

type Storage map[string][]byte

func (s Storage) String() (str string) {
	for key, value := range s {
		str += fmt.Sprintf("%X : %X\n", key, value)
	}

	return
}

func (s Storage) Copy() Storage {
	cpy := make(Storage)
	for key, value := range s {
		cpy[key] = value
	}

	return cpy
}

var _ IAccount = (*StateObject)(nil)

// StateObject represents an Ethereum account which is being modified.
//
// The usage pattern is as follows:
// First you need to obtain a state object.
// Account values can be accessed and modified through the object.
// Finally, call CommitTrie to write the modified storage trie into a database.
type StateObject struct {
	address  *types2.Address
	addrHash *types2.Hash // hash of ethereum address of the account
	data     Account
	db       *ComplexStateLedger

	// DB error.
	// State objects are used by the consensus core and VM which are
	// unable to deal with database-level errors. Any error that occurs
	// during a database read is memoized here and will eventually be returned
	// by StateDBImpl.Commit.
	dbErr error

	// Write caches.
	trie state.Trie // storage trie, which becomes non-nil on first access
	code Code       // contract bytecode, which gets set when code is loaded

	originStorage  Storage // Storage cache of original entries to dedup rewrites, reset for every transaction
	pendingStorage Storage // Storage entries that need to be flushed to disk, at the end of an entire block
	dirtyStorage   Storage // Storage entries that have been modified in the current transaction execution

	// Cache flags.
	// When an object is marked suicided it will be delete from the trie
	// during the "update" phase of the state transition.
	dirtyCode bool // true if the code was updated
	suicided  bool
	deleted   bool
}

func (s *StateObject) GetAddress() *types2.Address {
	return s.address
}

func (s *StateObject) GetDirtyStates() Storage {
	return s.dirtyStorage
}

func (s *StateObject) GetState(key []byte) (bool, []byte) {
	// If we have a dirty value for this state entry, return it
	value, dirty := s.dirtyStorage[string(key)]
	if dirty {
		return value != nil, value
	}
	// Otherwise return the entry's original value
	value = s.GetCommittedState(key)

	return value != nil, value
}

func (s *StateObject) GetCommittedState(key []byte) []byte {
	// If we have a pending write or clean cached, return that
	if value, pending := s.pendingStorage[string(key)]; pending {
		return value
	}
	if value, cached := s.originStorage[string(key)]; cached {
		return value
	}
	// If no live objects are available, attempt to use snapshots
	var (
		value []byte
		err   error
	)

	if value, err = s.getTrie(s.db.db).TryGet(key); err != nil {
		s.setError(err)
		return nil
	}

	s.originStorage[string(key)] = value
	return value
}

func (s *StateObject) SetState(key []byte, value []byte) {
	// If the new value is the same as old, don't set
	ok, prev := s.GetState(key)
	if ok && bytes.Equal(prev, value) {
		return
	}
	// New value is different, update and journal the change
	s.db.journal.append(storageChange{
		account:  s.address,
		key:      key,
		prevalue: prev,
	})
	s.setState(key, value)
}

func (s *StateObject) setState(key, value []byte) {
	s.dirtyStorage[string(key)] = value
}

func (s *StateObject) AddState(key []byte, value []byte) {
	s.db.journal.append(storageChange{
		account:  s.address,
		key:      key,
		prevalue: nil,
	})
	s.setState(key, value)
}

func (s *StateObject) SetCodeAndHash(code []byte) {
	prevcode := s.Code()
	s.db.journal.append(codeChange{
		account:  s.address,
		prevhash: s.CodeHash(),
		prevcode: prevcode,
	})
	codeHash := crypto.Keccak256Hash(code)
	s.setCode(types2.NewHash(codeHash.Bytes()), code)
}

func (s *StateObject) setCode(codeHash *types2.Hash, code []byte) {
	s.code = code
	s.data.CodeHash = codeHash.RawHash[:]
	s.dirtyCode = true
}

func (s *StateObject) Code() []byte {
	if s.code != nil {
		return s.code
	}
	if bytes.Equal(s.CodeHash(), emptyCodeHash) {
		return nil
	}
	code, err := s.db.db.ContractCode(common.BytesToHash(s.addrHash.RawHash[:]), common.BytesToHash(s.CodeHash()))
	if err != nil {
		s.setError(fmt.Errorf("can't load code hash %x: %v", s.CodeHash(), err))
	}
	s.code = code
	return code
}

func (s *StateObject) CodeHash() []byte {
	return s.data.CodeHash
}

func (s *StateObject) SetNonce(nonce uint64) {
	s.db.journal.append(nonceChange{
		account: s.address,
		prev:    s.data.Nonce,
	})
	s.setNonce(nonce)
}

func (s *StateObject) setNonce(nonce uint64) {
	s.data.Nonce = nonce
}

func (s *StateObject) GetNonce() uint64 {
	return s.data.Nonce
}

func (s *StateObject) GetBalance() *big.Int {
	return s.data.Balance
}

func (s *StateObject) SetBalance(amount *big.Int) {
	s.db.journal.append(balanceChange{
		account: s.address,
		prev:    new(big.Int).Set(s.data.Balance),
	})
	s.setBalance(amount)
}

func (s *StateObject) setBalance(amount *big.Int) {
	s.data.Balance = amount
}

// AddBalance adds amount to s's balance.
// It is used to add funds to the destination account of a transfer.
func (s *StateObject) AddBalance(amount *big.Int) {
	// EIP161: We must check emptiness for the objects such that the account
	// clearing (0,0,0 objects) can take effect.
	if amount.Sign() == 0 {
		if s.IsEmpty() {
			s.touch()
		}
		return
	}
	s.SetBalance(new(big.Int).Add(s.GetBalance(), amount))
}

// SubBalance removes amount from s's balance.
// It is used to remove funds from the origin account of a transfer.
func (s *StateObject) SubBalance(amount *big.Int) {
	if amount.Sign() == 0 {
		return
	}
	s.SetBalance(new(big.Int).Sub(s.GetBalance(), amount))
}

func (s *StateObject) Query(prefix string) (bool, [][]byte) {
	var (
		result [][]byte
		keys   = make(map[string]struct{})
	)

	for k, v := range s.dirtyStorage {
		if bytes.HasPrefix([]byte(k), []byte(prefix)) {
			if _, ok := keys[k]; !ok {
				keys[k] = struct{}{}
				result = append(result, v)
			}
		}
	}

	for k, v := range s.pendingStorage {
		if bytes.HasPrefix([]byte(k), []byte(prefix)) {
			if _, ok := keys[k]; !ok {
				keys[k] = struct{}{}
				result = append(result, v)
			}
		}
	}

	iterator := s.getTrie(s.db.db).NodeIterator(nil)
	it := trie.NewIterator(iterator)

	for it.Next() {
		key := s.trie.GetKey(it.Key)
		if bytes.HasPrefix(key, []byte(prefix)) {
			if _, ok := keys[string(key)]; !ok {
				keys[string(key)] = struct{}{}
				result = append(result, it.Value)
			}
		}
	}
	return len(result) != 0, result
}

func (s *StateObject) IsEmpty() bool {
	return s.data.Nonce == 0 && s.data.Balance.Sign() == 0 && bytes.Equal(s.data.CodeHash, emptyCodeHash)
}

func (s *StateObject) Suicided() bool {
	return s.suicided
}

func (s *StateObject) SetSuicided(b bool) {
	s.suicided = b
}

// Account is the Ethereum consensus representation of accounts.
// These objects are stored in the main account trie.
type Account struct {
	Nonce    uint64
	Balance  *big.Int
	Root     common.Hash // merkle root of the storage trie
	CodeHash []byte
}

// newObject creates a state object.
func newObject(db *ComplexStateLedger, address *types2.Address, data Account) *StateObject {
	if data.Balance == nil {
		data.Balance = new(big.Int)
	}
	if data.CodeHash == nil {
		data.CodeHash = emptyCodeHash
	}
	if data.Root == (common.Hash{}) {
		data.Root = emptyRoot
	}
	return &StateObject{
		db:             db,
		address:        address,
		addrHash:       types2.NewHash(crypto.Keccak256Hash(address.RawAddress[:]).Bytes()),
		data:           data,
		originStorage:  make(Storage),
		pendingStorage: make(Storage),
		dirtyStorage:   make(Storage),
	}
}

// setError remembers the first non-nil error it is called with.
func (s *StateObject) setError(err error) {
	if s.dbErr == nil {
		s.dbErr = err
	}
}

func (s *StateObject) touch() {
	s.db.journal.append(touchChange{
		account: s.address,
	})
	if s.address.String() == ripemd.String() {
		// Explicitly put it in the dirty-cache, which is otherwise generated from
		// flattened journals.
		s.db.journal.dirty(s.address)
	}
}

func (s *StateObject) getTrie(db state.Database) state.Trie {
	if s.trie == nil {
		var err error
		s.trie, err = db.OpenStorageTrie(common.BytesToHash(s.addrHash.RawHash[:]), s.data.Root)
		if err != nil {
			s.trie, _ = db.OpenStorageTrie(common.BytesToHash(s.addrHash.RawHash[:]), common.Hash{})
			s.setError(fmt.Errorf("can't create storage trie: %v", err))
		}
	}
	return s.trie
}

// finalise moves all dirty storage slots into the pending area to be hashed or
// committed later. It is invoked at the end of every transaction.
func (s *StateObject) finalise(prefetch bool) {
	slotsToPrefetch := make([][]byte, 0, len(s.dirtyStorage))
	for key, value := range s.dirtyStorage {
		s.pendingStorage[key] = value
		if !bytes.Equal(value, s.originStorage[key]) {
			slotsToPrefetch = append(slotsToPrefetch, common.CopyBytes([]byte(key))) // Copy needed for closure
		}
	}
	if len(s.dirtyStorage) > 0 {
		s.dirtyStorage = make(Storage)
	}
}

// updateTrie writes cached storage modifications into the object's storage trie.
// It will return nil if the trie has not been loaded and no changes have been made
func (s *StateObject) updateTrie(db state.Database) state.Trie {
	// Make sure all dirty slots are finalized into the pending storage area
	s.finalise(false) // Don't prefetch any more, pull directly if need be
	if len(s.pendingStorage) == 0 {
		return s.trie
	}

	// Insert all the pending updates into the trie
	tr := s.getTrie(db)

	usedStorage := make([][]byte, 0, len(s.pendingStorage))
	for key, value := range s.pendingStorage {
		// Skip noop changes, persist actual changes
		if bytes.Equal(value, s.originStorage[key]) {
			continue
		}
		s.originStorage[key] = value

		if value == nil {
			s.setError(tr.TryDelete([]byte(key)))
		} else {
			// Encoding []byte cannot fail, ok to ignore the error.
			s.setError(tr.TryUpdate([]byte(key), value))
		}
		usedStorage = append(usedStorage, common.CopyBytes([]byte(key))) // Copy needed for closure
	}
	if len(s.pendingStorage) > 0 {
		s.pendingStorage = make(Storage)
	}
	return tr
}

// UpdateRoot sets the trie root to the current root hash of
func (s *StateObject) updateRoot(db state.Database) {
	// If nothing changed, don't bother with hashing anything
	if s.updateTrie(db) == nil {
		return
	}
	s.data.Root = s.trie.Hash()
}

// CommitTrie the storage trie of the object to db.
// This updates the trie root.
func (s *StateObject) CommitTrie(db state.Database) error {
	// If nothing changed, don't bother with hashing anything
	if s.updateTrie(db) == nil {
		return nil
	}
	if s.dbErr != nil {
		return s.dbErr
	}
	root, err := s.trie.Commit(nil)
	if err == nil {
		s.data.Root = root
	}
	return err
}

func (s *StateObject) deepCopy(db *ComplexStateLedger) *StateObject {
	stateObject := newObject(db, s.address, s.data)
	if s.trie != nil {
		stateObject.trie = db.db.CopyTrie(s.trie)
	}
	stateObject.code = s.code
	stateObject.dirtyStorage = s.dirtyStorage.Copy()
	stateObject.originStorage = s.originStorage.Copy()
	stateObject.pendingStorage = s.pendingStorage.Copy()
	stateObject.suicided = s.suicided
	stateObject.dirtyCode = s.dirtyCode
	stateObject.deleted = s.deleted
	return stateObject
}

//
// Attribute accessors
//

// CodeSize returns the size of the contract code associated with this object,
// or zero if none. This method is an almost mirror of Code, but uses a cache
// inside the database to avoid loading codes seen recently.
func (s *StateObject) CodeSize(db state.Database) int {
	if s.code != nil {
		return len(s.code)
	}
	if bytes.Equal(s.CodeHash(), emptyCodeHash) {
		return 0
	}
	size, err := db.ContractCodeSize(common.BytesToHash(s.addrHash.RawHash[:]), common.BytesToHash(s.CodeHash()))
	if err != nil {
		s.setError(fmt.Errorf("can't load code size %x: %v", s.CodeHash(), err))
	}
	return size
}

func (account *Account) Marshal() ([]byte, error) {
	return json.Marshal(account)
}

func (account *Account) Unmarshal(data []byte) error {
	return json.Unmarshal(data, account)
}
