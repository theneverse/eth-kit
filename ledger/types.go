package ledger

import (
	"math/big"

	"github.com/ethereum/go-ethereum/common"
	types2 "github.com/ethereum/go-ethereum/core/types"
	"github.com/theneverse/neverse-kit/types"
	"github.com/theneverse/neverse-model/pb"
)

//go:generate mockgen -destination mock_ledger/mock_state_ledger.go -package mock_ledger -source types.go
type StateLedger interface {
	StateAccessor

	StateDB

	// AddEvent
	AddEvent(*pb.Event)

	// Events
	Events(txHash string) []*pb.Event

	AddLog(log *pb.EvmLog)

	GetLogs(types.Hash) []*pb.EvmLog

	// Rollback
	RollbackState(height uint64) error

	PrepareBlock(*types.Hash, uint64)

	ClearChangerAndRefund()

	// Close release resource
	Close()

	Copy() StateLedger

	Finalise(bool)

	// Version
	Version() uint64
}

// StateAccessor manipulates the state data
type StateAccessor interface {
	// GetOrCreateAccount
	GetOrCreateAccount(*types.Address) IAccount

	// GetAccount
	GetAccount(*types.Address) IAccount

	// GetBalance
	GetBalance(*types.Address) *big.Int

	// SetBalance
	SetBalance(*types.Address, *big.Int)

	// GetState
	GetState(*types.Address, []byte) (bool, []byte)

	// SetState
	SetState(*types.Address, []byte, []byte)

	// AddState
	AddState(*types.Address, []byte, []byte)

	// SetCode
	SetCode(*types.Address, []byte)

	// GetCode
	GetCode(*types.Address) []byte

	// SetNonce
	SetNonce(*types.Address, uint64)

	// GetNonce
	GetNonce(*types.Address) uint64

	// QueryByPrefix
	QueryByPrefix(address *types.Address, prefix string) (bool, [][]byte)

	// Commit commits the state data
	Commit(height uint64, accounts map[string]IAccount, stateRoot *types.Hash) error

	// FlushDirtyData flushes the dirty data
	FlushDirtyData() (map[string]IAccount, *types.Hash)

	// Clear
	Clear()
}

type IAccount interface {
	GetAddress() *types.Address

	GetState(key []byte) (bool, []byte)

	GetCommittedState(key []byte) []byte

	SetState(key []byte, value []byte)

	AddState(key []byte, value []byte)

	SetCodeAndHash(code []byte)

	Code() []byte

	CodeHash() []byte

	SetNonce(nonce uint64)

	GetNonce() uint64

	GetBalance() *big.Int

	SetBalance(balance *big.Int)

	SubBalance(amount *big.Int)

	AddBalance(amount *big.Int)

	Query(prefix string) (bool, [][]byte)

	IsEmpty() bool

	Suicided() bool

	SetSuicided(bool)
}

// StateDB is an EVM database for full state querying.
type StateDB interface {
	CreateEVMAccount(common.Address)

	SubEVMBalance(common.Address, *big.Int)
	AddEVMBalance(common.Address, *big.Int)
	GetEVMBalance(common.Address) *big.Int

	GetEVMNonce(common.Address) uint64
	SetEVMNonce(common.Address, uint64)

	GetEVMCodeHash(common.Address) common.Hash
	GetEVMCode(common.Address) []byte
	SetEVMCode(common.Address, []byte)
	GetEVMCodeSize(common.Address) int

	AddEVMRefund(uint64)
	SubEVMRefund(uint64)
	GetEVMRefund() uint64

	GetEVMCommittedState(common.Address, common.Hash) common.Hash
	GetEVMState(common.Address, common.Hash) common.Hash
	SetEVMState(common.Address, common.Hash, common.Hash)

	SuisideEVM(common.Address) bool
	HasSuisideEVM(common.Address) bool

	// Exist reports whether the given Account exists in state.
	// Notably this should also return true for suicided accounts.
	ExistEVM(common.Address) bool
	// Empty returns whether the given Account is empty. Empty
	// is defined according to EIP161 (balance = nonce = code = 0).
	EmptyEVM(common.Address) bool

	PrepareEVMAccessList(sender common.Address, dest *common.Address, precompiles []common.Address, txAccesses types2.AccessList)
	AddressInEVMAccessList(addr common.Address) bool
	SlotInEVMAceessList(addr common.Address, slot common.Hash) (addressOk bool, slotOk bool)
	// AddAddressToAccessList adds the given address to the access list. This operation is safe to perform
	// even if the feature/fork is not active yet
	AddAddressToEVMAccessList(addr common.Address)
	// AddSlotToAccessList adds the given (address,slot) to the access list. This operation is safe to perform
	// even if the feature/fork is not active yet
	AddSlotToEVMAccessList(addr common.Address, slot common.Hash)

	RevertToSnapshot(int)
	Snapshot() int

	AddEVMLog(log *types2.Log)
	AddEVMPreimage(common.Hash, []byte)

	//GetBlockEVMHash(uint64) common.Hash
	PrepareEVM(common.Hash, int)
}
