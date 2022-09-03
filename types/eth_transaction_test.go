package types

import (
	"fmt"
	"math/big"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/theneverse/neverse-kit/hexutil"
)

func TestEthTransaction_GetSignHash(t *testing.T) {
	rawTx := "0xf86c8085147d35700082520894f927bb571eaab8c9a361ab405c9e4891c5024380880de0b6b3a76400008025a00b8e3b66c1e7ae870802e3ef75f1ec741f19501774bd5083920ce181c2140b99a0040c122b7ebfb3d33813927246cbbad1c6bf210474f5d28053990abff0fd4f53"
	tx := &EthTransaction{}
	tx.Unmarshal(hexutil.Decode(rawTx))

	addr := "0xC63573cB77ec56e0A1cb40199bb85838D71e4dce"

	fmt.Println("tx hash:", tx.GetHash().String())

	fmt.Println(tx.GetRawSignature())
	InitEIP155Signer(big.NewInt(1))

	err := tx.VerifySignature()
	assert.Nil(t, err)

	sender, err := tx.sender()
	assert.Nil(t, err)
	assert.Equal(t, addr, sender.String())
}
