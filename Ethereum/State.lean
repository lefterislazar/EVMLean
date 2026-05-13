import Batteries.Data.RBMap
import Mathlib.Data.Finset.Basic

import Ethereum.MachineState
import Ethereum.State.ExecutionEnv
import Ethereum.State.Substate
import Ethereum.State.Account
import Ethereum.State.Block
import Ethereum.State.Substate
import Ethereum.State.Transaction

import Ethereum.Maps.AccountMap

import Ethereum.UInt256
import Ethereum.Wheels

namespace Ethereum

/--
The `State`. Section 9.3.

- `accountMap`   `σ`
- `substate`     `A`
- `executionEnv` `I`
- `totalGasUsedInBlock` `Υᵍ`
-/
structure State where
  accountMap          : AccountMap
  σ₀                  : AccountMap
  totalGasUsedInBlock : ℕ
  transactionReceipts  : Array TransactionReceipt
  substate            : Substate
  executionEnv        : ExecutionEnv
  machineState        : MachineState
  blocks              : ProcessedBlocks
  genesisBlockHeader  : BlockHeader
  createdAccounts     : Batteries.RBSet AccountAddress compare
deriving Inhabited

inductive ExecutionResult (S : Type) where
  | success (state : S) (o : ByteArray)
  | revert (g : UInt256) (o : ByteArray)

def State.blockHashes (self : State) : Array UInt256 :=
  self.blocks.map ProcessedBlock.hash

end Ethereum
