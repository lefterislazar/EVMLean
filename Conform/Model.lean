import Lean.Data.Json

-- import Ethereum.Maps
import Ethereum.Operations
import Ethereum.Wheels
import Ethereum.State.Withdrawal
import Ethereum.State.Block
import Ethereum.Fork

import Ethereum.State

import Conform.Wheels

namespace Ethereum

namespace Conform

section Model

open Lean

abbrev Code := ByteArray

abbrev Pre := PersistentAccountMap

abbrev Post := PersistentAccountMap

/--
In theory, parts of the TestEntry could deserialise immediately into the underlying `EVM.State`.
-/

inductive PostState where
  | Hash : ByteArray → PostState
  | Map : Post → PostState
  deriving Inhabited

/--
A block of a fixture: its RLP encoding, and the names of the exceptions with
which it may be rejected. A block is expected to be valid when there are none.
-/
structure FixtureBlock where
  rlp             : ByteArray
  expectException : List String
deriving Inhabited

structure TestEntry where
  info               : Json := ""
  blocks             : Array FixtureBlock
  genesisRLP         : ByteArray
  lastblockhash      : UInt256
  network            : String
  config             : ChainConfig
  postState          : PostState
  pre                : Pre
  sealEngine         : Json := ""
  deriving Inhabited

abbrev TestMap := Batteries.RBMap String TestEntry compare

def TestResult := Option String
  deriving Repr, Inhabited

namespace TestResult

def mkFailed (reason : String := "") : TestResult := .some reason

end TestResult

end Model
