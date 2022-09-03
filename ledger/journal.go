// Copyright 2016 The go-ethereum Authors
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
	"math/big"

	types2 "github.com/theneverse/neverse-kit/types"
)

// journalEntry is a modification entry in the state change journal that can be
// reverted on demand.
type journalEntry interface {
	// revert undoes the changes introduced by this journal entry.
	revert(*ComplexStateLedger)

	// dirtied returns the Ethereum address modified by this journal entry.
	dirtied() *types2.Address
}

// journal contains the list of state modifications applied since the last state
// commit. These are tracked to be able to be reverted in case of an execution
// exception or revertal request.
type journal struct {
	entries []journalEntry          // Current changes tracked by the journal
	dirties map[*types2.Address]int // Dirty accounts and the number of changes
}

// newJournal create a new initialized journal.
func newJournal() *journal {
	return &journal{
		dirties: make(map[*types2.Address]int),
	}
}

// append inserts a new modification entry to the end of the change journal.
func (j *journal) append(entry journalEntry) {
	j.entries = append(j.entries, entry)
	if addr := entry.dirtied(); addr != nil {
		j.dirties[addr]++
	}
}

// revert undoes a batch of journalled modifications along with any reverted
// dirty handling too.
func (j *journal) revert(statedb *ComplexStateLedger, snapshot int) {
	for i := len(j.entries) - 1; i >= snapshot; i-- {
		// Undo the changes made by the operation
		j.entries[i].revert(statedb)

		// Drop any dirty tracking induced by the change
		if addr := j.entries[i].dirtied(); addr != nil {
			if j.dirties[addr]--; j.dirties[addr] == 0 {
				delete(j.dirties, addr)
			}
		}
	}
	j.entries = j.entries[:snapshot]
}

// dirty explicitly sets an address to dirty, even if the change entries would
// otherwise suggest it as clean. This method is an ugly hack to handle the RIPEMD
// precompile consensus exception.
func (j *journal) dirty(addr *types2.Address) {
	j.dirties[addr]++
}

// length returns the current number of entries in the journal.
func (j *journal) length() int {
	return len(j.entries)
}

type (
	// Changes to the account trie.
	createObjectChange struct {
		account *types2.Address
	}
	resetObjectChange struct {
		prev         *StateObject
		prevdestruct bool
	}
	suicideChange struct {
		account     *types2.Address
		prev        bool // whether account had already suicided
		prevbalance *big.Int
	}

	// Changes to individual accounts.
	balanceChange struct {
		account *types2.Address
		prev    *big.Int
	}
	nonceChange struct {
		account *types2.Address
		prev    uint64
	}
	storageChange struct {
		account       *types2.Address
		key, prevalue []byte
	}
	codeChange struct {
		account            *types2.Address
		prevcode, prevhash []byte
	}

	// Changes to other state values.
	refundChange struct {
		prev uint64
	}
	addLogChange struct {
		txhash *types2.Hash
	}
	addPreimageChange struct {
		hash *types2.Hash
	}
	touchChange struct {
		account *types2.Address
	}
	// Changes to the access list
	accessListAddAccountChange struct {
		address *types2.Address
	}
	accessListAddSlotChange struct {
		address *types2.Address
		slot    *types2.Hash
	}
)

func (ch createObjectChange) revert(s *ComplexStateLedger) {
	delete(s.stateObjects, ch.account.String())
	delete(s.stateObjectsDirty, ch.account.String())
}

func (ch createObjectChange) dirtied() *types2.Address {
	return ch.account
}

func (ch resetObjectChange) revert(s *ComplexStateLedger) {
	s.setStateObject(ch.prev)
}

func (ch resetObjectChange) dirtied() *types2.Address {
	return nil
}

func (ch suicideChange) revert(s *ComplexStateLedger) {
	obj := s.getStateObject(ch.account)
	if obj != nil {
		obj.suicided = ch.prev
		obj.setBalance(ch.prevbalance)
	}
}

func (ch suicideChange) dirtied() *types2.Address {
	return ch.account
}

var ripemd = types2.NewAddressByStr("0000000000000000000000000000000000000003")

func (ch touchChange) revert(s *ComplexStateLedger) {
}

func (ch touchChange) dirtied() *types2.Address {
	return ch.account
}

func (ch balanceChange) revert(s *ComplexStateLedger) {
	s.getStateObject(ch.account).setBalance(ch.prev)
}

func (ch balanceChange) dirtied() *types2.Address {
	return ch.account
}

func (ch nonceChange) revert(s *ComplexStateLedger) {
	s.getStateObject(ch.account).setNonce(ch.prev)
}

func (ch nonceChange) dirtied() *types2.Address {
	return ch.account
}

func (ch codeChange) revert(s *ComplexStateLedger) {
	s.getStateObject(ch.account).setCode(types2.NewHash(ch.prevhash), ch.prevcode)
}

func (ch codeChange) dirtied() *types2.Address {
	return ch.account
}

func (ch storageChange) revert(s *ComplexStateLedger) {
	s.getStateObject(ch.account).setState(ch.key, ch.prevalue)
}

func (ch storageChange) dirtied() *types2.Address {
	return ch.account
}

func (ch refundChange) revert(s *ComplexStateLedger) {
	s.refund = ch.prev
}

func (ch refundChange) dirtied() *types2.Address {
	return nil
}

func (ch addLogChange) revert(s *ComplexStateLedger) {
	logs := s.logs[ch.txhash.String()]
	if len(logs) == 1 {
		delete(s.logs, ch.txhash.String())
	} else {
		s.logs[ch.txhash.String()] = logs[:len(logs)-1]
	}
	s.logSize--
}

func (ch addLogChange) dirtied() *types2.Address {
	return nil
}

func (ch addPreimageChange) revert(s *ComplexStateLedger) {
	delete(s.preimages, ch.hash.String())
}

func (ch addPreimageChange) dirtied() *types2.Address {
	return nil
}

func (ch accessListAddAccountChange) revert(s *ComplexStateLedger) {
	/*
		One important invariant here, is that whenever a (addr, slot) is added, if the
		addr is not already present, the add causes two journal entries:
		- one for the address,
		- one for the (address,slot)
		Therefore, when unrolling the change, we can always blindly delete the
		(addr) at this point, since no storage adds can remain when come upon
		a single (addr) change.
	*/
	s.accessList.DeleteAddress(*ch.address)
}

func (ch accessListAddAccountChange) dirtied() *types2.Address {
	return nil
}

func (ch accessListAddSlotChange) revert(s *ComplexStateLedger) {
	s.accessList.DeleteSlot(*ch.address, *ch.slot)
}

func (ch accessListAddSlotChange) dirtied() *types2.Address {
	return nil
}
