import Batteries.Data.RBMap

import Ethereum.State.Transaction
import Ethereum.State.ExecutionEnv
import Ethereum.State.Block
import Ethereum.State.BlockHeader
import Ethereum.State

import Ethereum.Exception
import Ethereum.Semantics

import Ethereum.Theory.OpcodeLemmas

import Ethereum.Symbolic.Expr

open Ethereum.EVM

namespace Ethereum

namespace Symbolic

-- abbrev Storage : Type := Batteries.RBMap UInt256 UInt256 compare

structure PersistentAccountState where
  nonce    : Expr .word
  balance  : Expr .word
  storage  : Expr .storage
  code     : RuntimeCode
  deriving BEq

structure Account extends PersistentAccountState where
  tstorage : Expr .storage
  deriving BEq

instance instOrdExprAddr : Ord (Expr .addr) where
  compare a1 a2 := 
  match a1, a2 with
  | .Caller, .Caller => .eq
  | .Caller, _ => .gt
  | .LitAddr _, .Caller => .lt
  | .LitAddr a1, .LitAddr a2 => compare a1 a2
  | .LitAddr _, _ => .gt
  | .Address, .Caller => .lt
  | .Address, .LitAddr _ => .lt
  | .Address, .Address => .eq
  | .Address, _ => .gt
  | .AddrOfWord a1, .AddrOfWord a2 => compare a1.consumeStack a2.consumeStack
  | .AddrOfWord _, .SymAddr _ => .gt
  | .AddrOfWord _, _ => .lt
  | .SymAddr s1, .SymAddr s2 => compare s1 s2
  | .SymAddr _, _ => .lt

abbrev AddrMap (α : Type) := Batteries.RBMap (Expr .addr) α compare
abbrev AccountMap := AddrMap Account

structure Substate where
  selfDestructSet     : List (Expr .addr)
  touchedAccounts     : List (Expr .addr)
  refundBalance       : Expr .word
  accessedAccounts    : List (Expr .addr)
  -- we do not track others' storage key changes
  -- since the are invisible to us
  accessedStorageKeys : List (Expr .word)
  logSeries           : List (Expr .log)
  deriving BEq

structure MachineState where
  pc                  : Expr .word
  stack               : Expr .stack
  execLength          : ℕ
  gasAvailable        : Expr .word -- TODO
  activeWords         : Expr .word
  memory              : Expr .buf
  returnData          : Expr .buf
  H_return            : Expr .buf
  deriving BEq

structure State where
  accountMap          : AccountMap
  -- currentAccount      : Account
  -- totalGasUsedInBlock : ℕ
  -- transactionReceipts : Array TransactionReceipt
  substate            : Substate
  -- executionEnv        : ExecutionEnv
  machineState        : MachineState
  -- blocks              : ProcessedBlocks
  -- genesisBlockHeader  : BlockHeader
  createdAccounts     : List (Expr .addr)
  deriving BEq

inductive Failure where
| exception : ExecutionException → Failure
-- | anything else?
  deriving BEq

inductive Uninterp where
| ThetaCall :
    List (Expr .addr)
  → AccountMap
  -- → AccountMap
  → Substate
  → Expr .addr -- caller
  → Expr .addr -- origin
  → Expr .addr -- recipient
  → Expr .addr -- code of
  → Expr .word -- gas
  → Expr .word -- gasprice
  → Expr .word -- value
  → Expr .word -- observed value
  → Expr .buf  -- calldata
  -- → Expr .word -- calldepth (could probably remove)
  → Bool -- right to modify state
  → Uninterp
-- | LambdaCall :
--     List (Expr .addr)
--   → AccountMap
--   → AccountMap
--   → Substate
--   → Expr .addr -- caller
--   → Expr .addr -- origin
--   → Expr .word -- gas
--   → Expr .word -- gasprice
--   → Expr .word -- value
--   → Expr .buf  -- calldata
--   -- → Expr .word -- calldepth (could probably remove)
--   → Expr .word -- salt
--   → Bool -- right to modify state
--   → Uninterp
  deriving BEq

def maxList : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxList xs)

def maxConsumesStackArray {τ : EType} (xs : Array (Expr τ)) : Nat :=
  xs.foldl (fun acc x => max acc (Expr.consumeStack x)) 0

def RuntimeCode.consumeStack : RuntimeCode → Nat
  | .concrete _ => 0
  | .symbolic code => maxConsumesStackArray code

def PersistentAccountState.consumeStack (account : PersistentAccountState) : Nat :=
  maxList [
    Expr.consumeStack account.nonce,
    Expr.consumeStack account.balance,
    Expr.consumeStack account.storage,
    account.code.consumeStack
  ]

def Account.consumeStack (account : Account) : Nat :=
  maxList [
    account.toPersistentAccountState.consumeStack,
    Expr.consumeStack account.tstorage
  ]

def maxConsumesStackAccountList : List (Expr .addr × Account) → Nat
  | [] => 0
  | account :: accounts =>
      max
        (max account.1.consumeStack account.2.consumeStack)
        (maxConsumesStackAccountList accounts)

def AccountMap.consumeStack (accounts : AccountMap) : Nat :=
  maxConsumesStackAccountList accounts.toList

-- def maxConsumesStackAccessedStorageKeys : List (Expr .addr × Expr .word) → Nat
--   | [] => 0
--   | key :: keys =>
--       max
--         (max (Expr.consumeStack key.1) (Expr.consumeStack key.2))
--         (maxConsumesStackAccessedStorageKeys keys)

def Substate.consumeStack (substate : Substate) : Nat :=
  maxList [
    Expr.maxConsumesStackList substate.selfDestructSet,
    Expr.maxConsumesStackList substate.touchedAccounts,
    Expr.consumeStack substate.refundBalance,
    Expr.maxConsumesStackList substate.accessedAccounts,
    Expr.maxConsumesStackList substate.accessedStorageKeys,
    Expr.maxConsumesStackList substate.logSeries
  ]

def MachineState.consumeStack (machineState : MachineState) : Nat :=
  maxList [
    Expr.consumeStack machineState.pc,
    Expr.consumeStack machineState.stack,
    Expr.consumeStack machineState.gasAvailable,
    Expr.consumeStack machineState.activeWords,
    Expr.consumeStack machineState.memory,
    Expr.consumeStack machineState.returnData,
    Expr.consumeStack machineState.H_return
  ]

def State.consumeStack (state : State) : Nat :=
  maxList [
    state.accountMap.consumeStack,
    state.substate.consumeStack,
    state.machineState.consumeStack,
    Expr.maxConsumesStackList state.createdAccounts
  ]

def Uninterp.consumeStack : Uninterp → Nat
  | .ThetaCall cA σ A Iₐ Iₒ Iᵣ Ic g p v v' i _ =>
      maxList [
        Expr.maxConsumesStackList cA,
        σ.consumeStack,
        A.consumeStack,
        Expr.consumeStack Iₐ,
        Expr.consumeStack Iₒ,
        Expr.consumeStack Iᵣ,
        Expr.consumeStack Ic,
        Expr.consumeStack g,
        Expr.consumeStack p,
        Expr.consumeStack v,
        Expr.consumeStack v',
        Expr.consumeStack i
      ]

def ConsumingAssertion n := { a : Assertion // n = a.consumeStack }

inductive Condition : (consumes : Nat) → (binds : Nat) → Type where
  | assert {n} : ConsumingAssertion n → Failure → Condition n 0
  | stackGE : (n : Nat) → Condition 0 n
  | stackLT : Nat → Condition 0 0
  | jumpValid : (e : Expr .word) → Condition e.consumeStack 0
  | jumpiValid : (e : Expr .word) → (jc : Expr .word) → Condition (max e.consumeStack jc.consumeStack) 0
  | staticMode : Condition 0 0

inductive ConditionChain : (binds : Nat) → Type where
  | nil {b} : Condition 0 b → ConditionChain b -- TODO: rename nil to last or smth
  | cons {n b ch_b' ch_b} :
    ConditionChain ch_b' →
    n ≤ ch_b' → --TODO: or lt?
    ch_b = max b ch_b' →
    Condition n b → ConditionChain ch_b


inductive InChain {n b ch_b} : (c : Condition n b) → (chain : ConditionChain ch_b) → Prop where
  | head {c ch_b'} {ch : ConditionChain ch_b'} :
    (h : n ≤ ch_b') →
    (h' : ch_b = max b ch_b') →
    --ch_b = max b ch_b' →
    --(h : n < ch_b') →
    InChain c (ConditionChain.cons ch h h' c)
  | tail {h h' ch c head} :
    InChain c ch →
    InChain c (ConditionChain.cons ch h h' head)

-- def BindingConditions n := { l : List Condition // n = (l.map bindsStack).max?.getD 0 }

def ConsumingState n := { e : State // n = e.consumeStack }

structure SymState where
  n : Nat -- abstract stack access, max depth
  conditions : ConditionChain n
  --evm : ConsumingState n
  evm : State
  hevm : evm.consumeStack ≤ n
  -- calls : List ((List Condition) × Uninterp)
