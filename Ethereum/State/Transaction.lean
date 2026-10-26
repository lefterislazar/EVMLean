import Mathlib.Data.List.AList

import Ethereum.UInt256
import Ethereum.Wheels
import Ethereum.State.TrieRoot
import Conform.Wheels
import Ethereum.State.Substate

namespace Ethereum

open Batteries (RBMap RBSet)

-- "All transaction types specify a number of common fields:"
/--
`BaseTransaction`. Section 4.3.

- `nonce`     `n`
- `gasLimit`  `g`
- `recipinet` `t`
- `value`     `v`
- `r`         `r`
- `s`         `s`
- `data`      `d/i`
-/
structure Transaction.Base where
  nonce           : UInt256
  gasLimit        : UInt256
  recipient       : Option AccountAddress
  value           : UInt256
  r               : ByteArray
  s               : ByteArray
  data            : ByteArray
deriving BEq, Repr

-- "EIP-2930 (type 1) and EIP-1559 (type 2) transactions also have:""
/--
`AccessList`. EIP-2930.
- `chainId`    `c`
- `accessList` `A`
- `yParity`    `y`
-/
structure Transaction.WithAccessList where
  chainId : UInt256
  accessList : List (AccountAddress × Array UInt256)
  yParity : UInt256
deriving BEq, Repr

-- "type 0 and type 1 transactions specify gas price as a single value:"
/--
`WithGasPrice`. Section 4.3.
- `gasPrice` `p`
-/
structure Transaction.WithGasPrice where
  gasPrice : UInt256
deriving BEq, Repr

-- Legacy transactions do not have an `accessList`, while `chainId` and `yParity` for legacy transactions are combined into a single value:
/--
Type 0: `LegacyTransaction`. Section 4.3.
- `nonce`     `n`
- `gasLimit`  `g`
- `recipinet` `t`
- `value`     `v`
- `r`         `r`
- `s`         `s`
- `data`      `d/i`
- `gasPrice` `p`
- `w` `w`
-/
structure LegacyTransaction extends Transaction.Base, Transaction.WithGasPrice where
  w: UInt256
deriving BEq, Repr

/-- Type 1: `AccessListTransaction`
- `nonce`     `n`
- `gasLimit`  `g`
- `recipinet` `t`
- `value`     `v`
- `r`         `r`
- `s`         `s`
- `data`      `d/i`
- `chainId`    `c`
- `accessList` `A`
- `yParity`    `y`
- `gasPrice` `p`
-/
structure AccessListTransaction
  extends Transaction.Base, Transaction.WithAccessList, Transaction.WithGasPrice
deriving BEq, Repr

/--
Type 2: `DynamicFeeTransaction`
- `nonce`                `n`
- `gasLimit`             `g`
- `recipinet`            `t`
- `value`                `v`
- `r`                    `r`
- `s`                    `s`
- `data`                 `d/i`
- `chainId`              `c`
- `accessList`           `A`
- `yParity`              `y`
- `maxFeePerGas`         `m`
- `maxPriorityFeePerGas` `f`
-/
structure DynamicFeeTransaction extends Transaction.Base, Transaction.WithAccessList where
  maxFeePerGas         : UInt256
  maxPriorityFeePerGas : UInt256
deriving BEq, Repr

structure BlobTransaction extends DynamicFeeTransaction where
  maxFeePerBlobGas  : UInt256
  blobVersionedHashes : List ByteArray
deriving BEq, Repr

/-- An EIP-7702 authorization tuple, signed by the delegating account. -/
structure Authorization where
  chainId : UInt256
  address : AccountAddress
  nonce   : UInt256
  yParity : UInt256
  r       : ByteArray
  s       : ByteArray
deriving BEq, Repr

/-- Type 4: EIP-7702 `SetCodeTransaction` (Prague). -/
structure SetCodeTransaction extends DynamicFeeTransaction where
  authorizationList : List Authorization
deriving BEq, Repr

inductive Transaction where
  | legacy  : LegacyTransaction → Transaction
  | access  : AccessListTransaction → Transaction
  | dynamic : DynamicFeeTransaction → Transaction
  | blob    : BlobTransaction → Transaction
  | setCode : SetCodeTransaction → Transaction
deriving BEq, Repr

def Transaction.base : Transaction → Transaction.Base
  | legacy t => t.toBase
  | access t => t.toBase
  | dynamic t => t.toBase
  | blob t => t.toBase
  | setCode t => t.toBase

def Transaction.getAccessList : Transaction → List (AccountAddress × Array UInt256)
  | legacy _ => []
  | access t => t.accessList
  | dynamic t => t.accessList
  | blob t => t.accessList
  | setCode t => t.accessList

def Transaction.type : Transaction → UInt8
  | .legacy  _ => 0
  | .access  _ => 1
  | .dynamic _ => 2
  | .blob _ => 3
  | .setCode _ => 4

def Transaction.authorizationList : Transaction → List Authorization
  | .setCode t => t.authorizationList
  | _ => []

def Transaction.toTriePair (t : ℕ × ByteArray) : Option (ByteArray × ByteArray) := do
  let rlpᵢ ← RLP (.𝔹 (BE t.1))
  pure (rlpᵢ, t.2)

def Transaction.computeTrieRoot (ts : Array ByteArray) : Option ByteArray := do
  Trie.root <$> Array.mapM Transaction.toTriePair ((Array.range ts.size).zip ts)

structure TransactionReceipt where
  type                     : UInt8     /- R_x -/
  statusCode               : Bool      /- R_z -/
  cumulativeGasUsedInBlock : ℕ         /- R_u -/
  bloomFilter              : ByteArray /- R_b -/
  logSeries                : LogSeries /- R_l -/
deriving BEq, Inhabited, Repr

def L_R : TransactionReceipt → 𝕋
  | ⟨_, statusCode, cumulativeGasUsedInBlock, bloomFilter, logSeries⟩ =>
  .𝕃
    [ if statusCode then .𝔹 (BE 1) else .𝔹 (BE 0)
    , .𝔹 (BE cumulativeGasUsedInBlock)
    , .𝔹 bloomFilter
    , logSeries.to𝕋
    ]

def TransactionReceipt.toTriePair (w : ℕ × ByteArray) : Option (ByteArray × ByteArray) := do
  let rlpᵢ ← RLP (.𝔹 (BE w.1))
  pure (rlpᵢ, w.2)

-- EIP-4895
def TransactionReceipt.computeTrieRoot (ws : Array ByteArray) : Option ByteArray := do
  Trie.root <$> Array.mapM TransactionReceipt.toTriePair ((Array.range ws.size).zip ws)

def TransactionReceipt.toTrieValue (r : TransactionReceipt) : ByteArray :=
  let rlp := Option.get! ∘ RLP ∘ L_R <| r
  if r.type = 0 then rlp else ⟨#[r.type]⟩ ++ rlp

end Ethereum
