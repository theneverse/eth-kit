package ledger

import (
	"math/big"

	"github.com/ethereum/go-ethereum/common"
	etherTypes "github.com/ethereum/go-ethereum/core/types"
	"github.com/theneverse/neverse-kit/types"
	"github.com/theneverse/neverse-model/pb"
)

func (l *ComplexStateLedger) CreateEVMAccount(addr common.Address) {
	l.GetOrCreateAccount(types.NewAddress(addr.Bytes()))
}

func (l *ComplexStateLedger) SubEVMBalance(addr common.Address, amount *big.Int) {
	l.SubBalance(types.NewAddress(addr.Bytes()), amount)
}

func (l *ComplexStateLedger) AddEVMBalance(addr common.Address, amount *big.Int) {
	l.AddBalance(types.NewAddress(addr.Bytes()), amount)
}

func (l *ComplexStateLedger) GetEVMBalance(addr common.Address) *big.Int {
	return l.GetBalance(types.NewAddress(addr.Bytes()))
}

func (l *ComplexStateLedger) GetEVMNonce(addr common.Address) uint64 {
	return l.GetNonce(types.NewAddress(addr.Bytes()))
}

func (l *ComplexStateLedger) SetEVMNonce(addr common.Address, nonce uint64) {
	l.SetNonce(types.NewAddress(addr.Bytes()), nonce)
}

func (l *ComplexStateLedger) GetEVMCodeHash(addr common.Address) common.Hash {
	return common.BytesToHash(l.GetCodeHash(types.NewAddress(addr.Bytes())).Bytes())
}

func (l *ComplexStateLedger) GetEVMCode(addr common.Address) []byte {
	return l.GetCode(types.NewAddress(addr.Bytes()))
}

func (l *ComplexStateLedger) SetEVMCode(addr common.Address, code []byte) {
	l.SetCode(types.NewAddress(addr.Bytes()), code)
}

func (l *ComplexStateLedger) GetEVMCodeSize(addr common.Address) int {
	return l.GetCodeSize(types.NewAddress(addr.Bytes()))
}

func (l *ComplexStateLedger) AddEVMRefund(gas uint64) {
	l.AddRefund(gas)
}

func (l *ComplexStateLedger) SubEVMRefund(gas uint64) {
	l.SubRefund(gas)
}

func (l *ComplexStateLedger) GetEVMRefund() uint64 {
	return l.GetRefund()
}

func (l *ComplexStateLedger) GetEVMCommittedState(addr common.Address, hash common.Hash) common.Hash {
	ret := l.GetCommittedState(types.NewAddress(addr.Bytes()), hash.Bytes())
	return common.BytesToHash(ret)
}

func (l *ComplexStateLedger) GetEVMState(addr common.Address, hash common.Hash) common.Hash {
	ok, ret := l.GetState(types.NewAddress(addr.Bytes()), hash.Bytes())
	if !ok {
		return common.Hash{}
	}
	return common.BytesToHash(ret)
}

func (l *ComplexStateLedger) SetEVMState(addr common.Address, key, value common.Hash) {
	l.SetState(types.NewAddress(addr.Bytes()), key.Bytes(), value.Bytes())
}

func (l *ComplexStateLedger) SuisideEVM(addr common.Address) bool {
	return l.Suicide(types.NewAddress(addr.Bytes()))
}

func (l *ComplexStateLedger) HasSuisideEVM(addr common.Address) bool {
	return l.HasSuicided(types.NewAddress(addr.Bytes()))
}

func (l *ComplexStateLedger) ExistEVM(addr common.Address) bool {
	return l.Exist(types.NewAddress(addr.Bytes()))
}

func (l *ComplexStateLedger) EmptyEVM(addr common.Address) bool {
	return l.Empty(types.NewAddress(addr.Bytes()))
}

func (l *ComplexStateLedger) PrepareEVMAccessList(sender common.Address, dest *common.Address, preEVMcompiles []common.Address, txEVMAccesses etherTypes.AccessList) {
	var precompiles []types.Address
	for _, compile := range preEVMcompiles {
		precompiles = append(precompiles, *types.NewAddress(compile.Bytes()))
	}
	var txAccesses AccessTupleList
	for _, list := range txEVMAccesses {
		var storageKeys []types.Hash
		for _, keys := range list.StorageKeys {
			storageKeys = append(storageKeys, *types.NewHash(keys.Bytes()))
		}
		txAccesses = append(txAccesses, AccessTuple{Address: *types.NewAddress(list.Address.Bytes()), StorageKeys: storageKeys})
	}
	l.PrepareAccessList(*types.NewAddress(sender.Bytes()), types.NewAddress(dest.Bytes()), precompiles, txAccesses)
}

func (l *ComplexStateLedger) AddressInEVMAccessList(addr common.Address) bool {
	return l.AddressInAccessList(*types.NewAddress(addr.Bytes()))
}

func (l *ComplexStateLedger) SlotInEVMAceessList(addr common.Address, slot common.Hash) (bool, bool) {
	return l.SlotInAccessList(*types.NewAddress(addr.Bytes()), *types.NewHash(slot.Bytes()))
}

func (l *ComplexStateLedger) AddAddressToEVMAccessList(addr common.Address) {
	l.AddAddressToAccessList(*types.NewAddress(addr.Bytes()))
}

func (l *ComplexStateLedger) AddSlotToEVMAccessList(addr common.Address, slot common.Hash) {
	l.AddSlotToAccessList(*types.NewAddress(addr.Bytes()), *types.NewHash(slot.Bytes()))
}

func (l *ComplexStateLedger) AddEVMPreimage(hash common.Hash, data []byte) {
	l.AddPreimage(*types.NewHash(hash.Bytes()), data)
}

func (l *ComplexStateLedger) PrepareEVM(hash common.Hash, index int) {
	l.thash = types.NewHash(hash.Bytes())
	l.txIndex = index
	l.accessList = NewAccessList()
}

func (l *ComplexStateLedger) StateDB() StateDB {
	return l
}

func (l *ComplexStateLedger) AddEVMLog(log *etherTypes.Log) {
	var topics []types.Hash
	for _, topic := range log.Topics {
		topics = append(topics, *types.NewHash(topic.Bytes()))
	}
	logs := &pb.EvmLog{
		Address:          types.NewAddress(log.Address.Bytes()),
		Topics:           topics,
		Data:             log.Data,
		BlockNumber:      log.BlockNumber,
		TransactionHash:  types.NewHash(log.TxHash.Bytes()),
		TransactionIndex: uint64(log.TxIndex),
		BlockHash:        types.NewHash(log.BlockHash.Bytes()),
		LogIndex:         uint64(log.Index),
		Removed:          log.Removed,
	}
	l.AddLog(logs)
}

type EvmReceipts []*pb.Receipt

func CreateBloom(receipts EvmReceipts) *types.Bloom {
	var bin types.Bloom
	for _, receipt := range receipts {
		for _, log := range receipt.EvmLogs {
			bin.Add(log.Address.Bytes())
			for _, b := range log.Topics {
				bin.Add(b.Bytes())
			}
		}
	}
	return &bin
}
