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
	"bytes"
	"fmt"
	"io/ioutil"
	"math/big"
	"path/filepath"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/trie"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	types2 "github.com/theneverse/neverse-kit/types"
)

// Tests that updating a state trie does not leak any database writes prior to
// actually committing the state.
func TestUpdateLeaks(t *testing.T) {
	// Create an empty state database
	db := rawdb.NewMemoryDatabase()
	state, _ := New(&types2.Hash{}, state.NewDatabase(db), nil)

	// Update it with some accounts
	for i := byte(0); i < 255; i++ {
		addr := types2.NewAddress([]byte{i})
		state.AddBalance(addr, big.NewInt(int64(11*i)))
		state.SetNonce(addr, uint64(42*i))
		if i%2 == 0 {
			state.SetState(addr, []byte{i, i, i}, []byte{i, i, i, i})
		}
		if i%3 == 0 {
			state.SetCode(addr, []byte{i, i, i, i, i})
		}
	}

	root := state.IntermediateRoot(false)
	if err := state.Database().TrieDB().Commit(root, false, nil); err != nil {
		t.Errorf("can not commit trie %v to persistent database", root.Hex())
	}

	// Ensure that no data was leaked into the database
	it := db.NewIterator(nil, nil)
	for it.Next() {
		t.Errorf("State leaked into database: %x -> %x", it.Key(), it.Value())
	}
	it.Release()
}

// Tests that no intermediate state of an object is stored into the database,
// only the one right before the commit.
func TestIntermediateLeaks(t *testing.T) {
	// Create two state databases, one transitioning to the final state, the other final from the beginning
	transDb := rawdb.NewMemoryDatabase()
	finalDb := rawdb.NewMemoryDatabase()
	transState, _ := New(&types2.Hash{}, state.NewDatabase(transDb), nil)
	finalState, _ := New(&types2.Hash{}, state.NewDatabase(finalDb), nil)

	modify := func(state *ComplexStateLedger, addr *types2.Address, i, tweak byte) {
		state.SetBalance(addr, big.NewInt(int64(11*i)+int64(tweak)))
		state.SetNonce(addr, uint64(42*i+tweak))
		if i%2 == 0 {
			state.SetState(addr, []byte{i, i, i, 0}, common.Hash{}.Bytes())
			state.SetState(addr, []byte{i, i, i, tweak}, common.Hash{i, i, i, i, tweak}.Bytes())
		}
		if i%3 == 0 {
			state.SetCode(addr, []byte{i, i, i, i, i, tweak})
		}
	}

	// Modify the transient state.
	for i := byte(0); i < 10; i++ {
		modify(transState, types2.NewAddress([]byte{i}), i, 0)
	}
	// Write modifications to trie.
	transState.IntermediateRoot(false)

	// Overwrite all the data with new values in the transient database.
	for i := byte(0); i < 10; i++ {
		modify(transState, types2.NewAddress([]byte{i}), i, 99)
		modify(finalState, types2.NewAddress([]byte{i}), i, 99)
	}

	_, stateRoot := transState.FlushDirtyData()
	// Commit and cross check the databases.
	err := transState.Commit(0, nil, stateRoot)
	if err != nil {
		t.Fatalf("failed to commit transition state: %v", err)
	}
	if err = transState.Database().TrieDB().Commit(common.BytesToHash(stateRoot.Bytes()), false, nil); err != nil {
		t.Errorf("can not commit trie %v to persistent database", stateRoot.String())
	}

	_, finalRoot := finalState.FlushDirtyData()
	err = finalState.Commit(0, nil, finalRoot)
	if err != nil {
		t.Fatalf("failed to commit final state: %v", err)
	}
	if err = finalState.Database().TrieDB().Commit(common.BytesToHash(finalRoot.Bytes()), false, nil); err != nil {
		t.Errorf("can not commit trie %v to persistent database", finalRoot.String())
	}

	finalState.Clear()
	transState.Clear()
	it := finalDb.NewIterator(nil, nil)
	for it.Next() {
		key, fvalue := it.Key(), it.Value()
		tvalue, err := transDb.Get(key)
		if err != nil {
			t.Errorf("entry missing from the transition database: %x -> %x", key, fvalue)
		}
		if !bytes.Equal(fvalue, tvalue) {
			t.Errorf("the value associate key %x is mismatch,: %x in transition database ,%x in final database", key, tvalue, fvalue)
		}
	}
	it.Release()

	it = transDb.NewIterator(nil, nil)
	for it.Next() {
		key, tvalue := it.Key(), it.Value()
		fvalue, err := finalDb.Get(key)
		if err != nil {
			t.Errorf("extra entry in the transition database: %x -> %x", key, it.Value())
		}
		if !bytes.Equal(fvalue, tvalue) {
			t.Errorf("the value associate key %x is mismatch,: %x in transition database ,%x in final database", key, tvalue, fvalue)
		}
	}
}

func TestNew(t *testing.T) {
	transDb := rawdb.NewMemoryDatabase()
	transState, _ := New(&types2.Hash{}, state.NewDatabase(transDb), nil)

	addr := types2.NewAddress([]byte{1})
	balance := big.NewInt(10)

	transState.SetBalance(addr, balance)

	code := []byte{1, 2, 3}
	transState.SetCode(addr, code)

	transState.SetState(addr, []byte("key"), []byte("value"))

	_, transRoot := transState.FlushDirtyData()
	err := transState.Commit(0, nil, transRoot)
	assert.Nil(t, err)
	err = transState.Database().TrieDB().Commit(common.BytesToHash(transRoot.Bytes()), false, nil)
	assert.Nil(t, err)

	transState.Clear()

	transState, err = New(transRoot, state.NewDatabase(transDb), nil)
	assert.Nil(t, err)

	ok, val := transState.GetState(addr, []byte("key"))
	assert.True(t, ok)
	assert.Equal(t, "value", string(val))
	assert.Equal(t, code, transState.GetAccount(addr).Code())
}

func TestNew2(t *testing.T) {
	transDb := rawdb.NewMemoryDatabase()
	db := state.NewDatabase(transDb)
	transState, _ := New(&types2.Hash{}, db, nil)
	transState1, _ := New(&types2.Hash{}, db, nil)

	addr := types2.NewAddress([]byte{1})
	transState.SetState(addr, []byte("key"), []byte("value"))
	_, transRoot := transState.FlushDirtyData()
	_ = transState.Commit(0, nil, transRoot)

	transState.SetState(addr, []byte("key1"), []byte("value2"))
	_, transRoot2 := transState.FlushDirtyData()
	_ = transState.Commit(0, nil, transRoot2)
	//err := transState.Database().TrieDB().Commit(common.BytesToHash(root2.Bytes()), false, nil)
	//assert.Nil(t, err)

	transState1, err := transState1.StateAt(transRoot2)
	assert.Nil(t, err)
	acc := transState1.GetAccount(addr).(*StateObject)
	ok, val := acc.GetState([]byte("key"))
	fmt.Println(string(val))
	fmt.Println(ok)
}

func TestComplexStateLedger_QueryByPrefix(t *testing.T) {
	root, err := ioutil.TempDir("", "TestChainLedger")
	require.Nil(t, err)
	storage, err := rawdb.NewLevelDBDatabase(filepath.Join(root, "ledger"), 0, 0, "", false)
	assert.Nil(t, err)
	db := state.NewDatabaseWithConfig(storage.(ethdb.Database), &trie.Config{
		Cache:     256,
		Journal:   "",
		Preimages: true,
	})

	transState, err := New(&types2.Hash{}, db, nil)
	assert.Nil(t, err)

	addr := types2.NewAddress([]byte{1})
	ok, result := transState.QueryByPrefix(addr, "k")
	assert.False(t, ok)
	assert.Equal(t, 0, len(result))

	fmt.Println(result)

	transState.SetState(addr, []byte("key"), []byte("value"))
	transState.SetState(addr, []byte("key1"), []byte("value2"))
	transState.SetState(addr, []byte("abc"), []byte("value2"))
	transState.SetNonce(addr, 1)

	ok, result := transState.QueryByPrefix(addr, "k")
	assert.True(t, ok)
	assert.Equal(t, 2, len(result))

	fmt.Println(result)

	_, stateRoot := transState.FlushDirtyData()
	_ = transState.Commit(0, nil, stateRoot)

	err = transState.Database().TrieDB().Commit(common.BytesToHash(stateRoot.Bytes()), false, nil)
	assert.Nil(t, err)

	acc := transState.getStateObject(addr)
	ok, val := acc.GetState([]byte("key"))
	assert.True(t, ok)
	assert.Equal(t, "value", string(val))

	ok, result = transState.QueryByPrefix(addr, "k")
	assert.True(t, ok)
	assert.Equal(t, 2, len(result))

	fmt.Println(result)
}
