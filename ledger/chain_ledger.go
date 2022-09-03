package ledger

import (
	"github.com/theneverse/neverse-kit/types"
	"github.com/theneverse/neverse-model/pb"
)

// BlockchainLedger handles block, transaction and receipt data.
//
//go:generate mockgen -destination mock_ledger/mock_chain_ledger.go -package mock_ledger -source chain_ledger.go
type ChainLedger interface {
	// PutBlock put block into store
	PutBlock(height uint64, block *pb.Block) error

	// GetBlock get block with height
	GetBlock(height uint64) (*pb.Block, error)

	// GetBlockSign get the signature of block
	GetBlockSign(height uint64) ([]byte, error)

	// GetBlockByHash get the block using block hash
	GetBlockByHash(hash *types.Hash) (*pb.Block, error)

	// GetTransaction get the transaction using transaction hash
	GetTransaction(hash *types.Hash) (pb.Transaction, error)

	// GetTransactionMeta get the transaction meta data
	GetTransactionMeta(hash *types.Hash) (*pb.TransactionMeta, error)

	// GetReceipt get the transaction receipt
	GetReceipt(hash *types.Hash) (*pb.Receipt, error)

	// GetInterchainMeta get interchain meta data
	GetInterchainMeta(height uint64) (*pb.InterchainMeta, error)

	// PersistExecutionResult persist the execution result
	PersistExecutionResult(block *pb.Block, receipts []*pb.Receipt, meta *pb.InterchainMeta) error

	// GetChainMeta get chain meta data
	GetChainMeta() *pb.ChainMeta

	// UpdateChainMeta update the chain meta data
	UpdateChainMeta(*pb.ChainMeta)

	// LoadChainMeta get chain meta data
	LoadChainMeta() *pb.ChainMeta

	// GetTxCountInBlock get the transaction count in a block
	GetTransactionCount(height uint64) (uint64, error)

	RollbackBlockChain(height uint64) error

	GetBlockHash(height uint64) *types.Hash

	Close()
}
