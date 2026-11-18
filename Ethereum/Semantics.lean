import Mathlib.Data.BitVec
import Mathlib.Init

import Mathlib.Data.Finmap
import Mathlib.Data.List.Defs
import Ethereum.Data.Stack

import Ethereum.Maps.AccountMap
import Ethereum.Maps.AccountMap

import Ethereum.State
import Ethereum.StateOps

import Ethereum.State.AccountOps
import Ethereum.State.ExecutionEnv
import Ethereum.State.Substate
import Ethereum.State.TransactionOps
import Ethereum.StateGas

import Ethereum.Exception
import Ethereum.Gas
import Ethereum.GasConstants
import Ethereum.Exception
import Ethereum.Instr
import Ethereum.PrecompiledContracts
import Ethereum.PrimOps

import Ethereum.Operations
import Ethereum.Pretty
import Ethereum.Wheels
import Ethereum.EllipticCurves
import Ethereum.UInt256
import Ethereum.MachineState


namespace Ethereum

namespace EVM

def argOnNBytesOfInstr : Operation → ℕ
  -- | .Push .PUSH0 => 0 is handled as default.
  | .Push .PUSH1 => 1
  | .Push .PUSH2 => 2
  | .Push .PUSH3 => 3
  | .Push .PUSH4 => 4
  | .Push .PUSH5 => 5
  | .Push .PUSH6 => 6
  | .Push .PUSH7 => 7
  | .Push .PUSH8 => 8
  | .Push .PUSH9 => 9
  | .Push .PUSH10 => 10
  | .Push .PUSH11 => 11
  | .Push .PUSH12 => 12
  | .Push .PUSH13 => 13
  | .Push .PUSH14 => 14
  | .Push .PUSH15 => 15
  | .Push .PUSH16 => 16
  | .Push .PUSH17 => 17
  | .Push .PUSH18 => 18
  | .Push .PUSH19 => 19
  | .Push .PUSH20 => 20
  | .Push .PUSH21 => 21
  | .Push .PUSH22 => 22
  | .Push .PUSH23 => 23
  | .Push .PUSH24 => 24
  | .Push .PUSH25 => 25
  | .Push .PUSH26 => 26
  | .Push .PUSH27 => 27
  | .Push .PUSH28 => 28
  | .Push .PUSH29 => 29
  | .Push .PUSH30 => 30
  | .Push .PUSH31 => 31
  | .Push .PUSH32 => 32
  -- EIP-8024 (Amsterdam)
  | .StackAccess _ => 1
  | _ => 0

/--
The bytes of code that the jump destination analysis skips after an
instruction: the data of a `PUSH`. As in the execution specs, the immediate of
the EIP-8024 instructions is not skipped: EIP-8024 leaves the analysis
unchanged.
-/
def pushDataWidth : Operation → ℕ
  | .Push p => argOnNBytesOfInstr (.Push p)
  | _ => 0

def N (pc : ℕ) (instr : Operation) := pc + 1 + (pushDataWidth instr)

/--
Returns the instruction from `arr` at `pc` assuming it is valid.

The `Push` instruction also returns the argument as an EVM word along with the width of the instruction.
-/
def decode (arr : ByteArray) (pc : UInt256) :
  Option (Operation × Option (UInt256 × Nat)) := do
  let instr ← arr.get? pc.toNat >>= Ethereum.EVM.parseInstr
  let argWidth := argOnNBytesOfInstr instr
  .some (
    instr,
    if argWidth == 0
    then .none
    else .some (Ethereum.uInt256OfByteArray (arr.readWithPadding pc.toNat.succ argWidth), argWidth)
  )

def fetchInstr (I : Ethereum.ExecutionEnv) (pc : UInt256) :
               Except EVM.ExecutionException (Operation × Option (UInt256 × Nat)) :=
  decode I.code pc |>.option (.error .StackUnderflow) Except.ok

def D_J_aux (c : ByteArray) (i : ℕ) (result : Array UInt256) : Array UInt256 :=
  match _hget : c.get? i >>= Ethereum.EVM.parseInstr with
    | none => result
    | some cᵢ => D_J_aux c (N i cᵢ) (if cᵢ = .JUMPDEST then result.push (UInt256.ofNat i) else result)
termination_by (c.size - i)
decreasing_by
  have hNincr : ∀ pc i, pc < N pc i := by
    intros; simp [N]; omega
  simp [bind, Option.bind] at _hget
  split at _hget; simp at _hget
  rename_i hget_some;
  simp [ByteArray.get?] at hget_some
  obtain ⟨hsize,_⟩ := hget_some
  apply Nat.sub_lt_sub_left hsize (hNincr i cᵢ)

def D_J (c : ByteArray) (i : ℕ) : Array UInt256 :=
  D_J_aux c i #[]

private def BitVec.ofFn {k} (x : Fin k → Bool) : BitVec k :=
  BitVec.ofNat k (natOfBools (Vector.ofFn x))
  where natOfBools (vec : Vector Bool k) : Nat :=
          (·.1) <| vec.toList.foldl (init := (0, 0)) λ (res, i) bit ↦ (res + 2^i * bit.toNat, i + 1)

def byteAt (μ₀ μ₁ : UInt256) : UInt256 :=
  let v₁ : BitVec 256 := BitVec.ofNat 256 μ₁.1
  let vᵣ : BitVec 256 := BitVec.ofFn (λ i => if i >= 248 && μ₀ < ⟨32⟩
                                             then v₁.getLsbD i
                                             else false)
  Ethereum.UInt256.ofNat (BitVec.toNat vᵣ)

def dup (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.machineState.stack.take n
  if top.length = n then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: s.machineState.stack)
  else
    .error .StackUnderflow

def swap (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.machineState.stack.take (n + 1)
  let bottom := s.machineState.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error .StackUnderflow

/-! ### EIP-8024 (Amsterdam): `DUPN`, `SWAPN` and `EXCHANGE` -/

/--
The stack depth `n`, `17 ≤ n ≤ 235`, that the immediate `x` of `DUPN` and
`SWAPN` encodes. The immediates `91` to `127`, which include `JUMPDEST` and
the `PUSH` instructions, encode none.
-/
def decodeSingle (x : ℕ) : Option ℕ :=
  if x ≤ 90 ∨ 128 ≤ x ∧ x ≤ 255 then some ((x + 145) % 256) else none

/--
The stack depths `(n, m)`, `1 ≤ n ≤ 14` and `n < m ≤ 30 - n`, that the
immediate `x` of `EXCHANGE` encodes. The immediates `82` to `127` encode none.
-/
def decodePair (x : ℕ) : Option (ℕ × ℕ) :=
  if x ≤ 81 ∨ 128 ≤ x ∧ x ≤ 255 then
    let k := x ^^^ 143
    let q := k / 16
    let r := k % 16
    some (if q < r then (q + 1, r + 1) else (r + 1, 29 - q))
  else none

/--
Swaps the stack items at depths `n` and `m`, the top being at depth `0`, and
moves past the instruction and its immediate.
-/
def exchange (n m : ℕ) : Transformer :=
  λ s ↦
  let stack := s.machineState.stack
  match stack[n]?, stack[m]? with
  | some a, some b => .ok <| s.replaceStackAndIncrPC ((stack.set n b).set m a) 2
  | _, _ => .error .StackUnderflow

/--
`DUPN`, `SWAPN` and `EXCHANGE` with the immediate `x`. `DUPN` duplicates the
item at depth `n - 1`, `SWAPN` swaps the top with the item at depth `n`, and
`EXCHANGE` the items at depths `n` and `m`. An immediate out of range is an
exceptional halt, and so is a stack too shallow for the depths.
-/
def stackAccess (op : Operation.SAccOp) (x : ℕ) : Transformer :=
  λ s ↦
  match op with
  | .DUPN =>
    match decodeSingle x with
    | some n =>
      match s.machineState.stack[n - 1]? with
      | some a => .ok <| s.replaceStackAndIncrPC (a :: s.machineState.stack) 2
      | none => .error .StackUnderflow
    | none => .error .InvalidParameter
  | .SWAPN =>
    match decodeSingle x with
    | some n => exchange 0 n s
    | none => .error .InvalidParameter
  | .EXCHANGE =>
    match decodePair x with
    | some (n, m) => exchange n m s
    | none => .error .InvalidParameter

instance instMonadLiftOptionExceptExecutionException : MonadLift Option (Except EVM.ExecutionException) :=
  ⟨Option.option (.error .StackUnderflow) .ok⟩

inductive HaltCause where
  | success
  | revert

/--
The substate of a message call to `t`: `t` is accessed and, from Prague on,
so is the target of a delegation designator held by `t` (EIP-7702).
-/
def callSubstate (fork : Fork) (σ : AccountMap) (t : AccountAddress) (A : Substate) : Substate :=
  let A := A.addAccessedAccount t
  if fork.spec.eip7702 then
    match delegationTarget? (σ.get? t |>.option .empty (·.code)) with
    | some target => A.addAccessedAccount target
    | none => A
  else A

/--
The gas a reverting frame returns to its caller: its execution gas, and from
EIP-8037 (Amsterdam) its own spill, the execution gas it spent on state that
the revert undoes (`restore_state_gas`).
-/
def revertGas (s : State) : UInt256 :=
  .ofNat <| s.machineState.gasAvailable.toNat
    + StateGas.ownSpill s.substate s.executionEnv.stateGasSpillBaseline

/--
EIP-8037 and EIP-2780 (Amsterdam): the costs of a transaction's top frame
that depend on the state, which the execution specs charge as they build it
(`create_evm`). A value transfer to the recipient `r` when it is not alive
creates it: `NEW_ACCOUNT` in state gas. A recipient that delegates its code
accesses the delegate, warm or cold, which warms it. `none` when the gas does
not cover them.
-/
def topFrameCallCharges
    (σ : AccountMap) (A : Substate) (gas : ℕ) (r : AccountAddress) (v : UInt256) :
    Option (ℕ × Substate) := do
  let (gas, A) ←
    if v != ⟨0⟩ ∧ State.dead σ r then StateGas.charge gas A StateGas.NEW_ACCOUNT
    else some (gas, A)
  match delegationTarget? (σ.get? r |>.option .empty (·.code)) with
  | some d =>
    let cost :=
      if A.accessedAccounts.contains d then GasConstants.Gwarmaccess
      else GasConstants.GcoldaccountaccessAmsterdam
    if gas < cost then none
    some (gas - cost, A.addAccessedAccount d)
  | none => some (gas, A)

/-- (96) The preimage of the address of a contract that `s` creates with
    nonce `n`, init code `i` and, for `CREATE2`, the salt `ζ`. -/
def L_A (s : AccountAddress) (n : UInt256) (ζ : Option ByteArray) (i : ByteArray) :
    ByteArray
  :=
    let ⟨s,hs⟩ := s.toByteArrayWithSizeProof
    let ⟨n',hn⟩ := BEwithSizeProof n.val
    let hn₃₃ : n'.size ≤ 32 + 1 := by
      have h_lt : (n.val < UInt256.size) := by exact n.1.2
      apply Nat.le_of_lt at h_lt
      apply Nat.log_mono_right (b := 2) at h_lt
      rw [← Nat.log2_eq_log_two] at h_lt
      apply Nat.div_le_div_right (c := 8) at h_lt
      simp [UInt256.size] at h_lt
      simp [Nat.log, Nat.log.go] at h_lt
      apply Nat.add_le_add_right (k := 1) at h_lt
      exact le_trans hn h_lt
    match ζ with
      | none   =>
        RLP_bounded (.𝕃 [.𝔹 s, .𝔹 n'])
          (by simp [𝕋.rlpBound, 𝕋.rlpBoundList, hs]; omega)
      | some ζ => BE 255 ++ s ++ ζ ++ KEC i

/-- (94) (95) The address of the contract that `s` creates in `σ`, where its
    nonce has already been incremented for the creation. -/
def creationAddress (σ : AccountMap) (s : AccountAddress) (ζ : Option ByteArray) (i : ByteArray) :
    AccountAddress :=
  let n : UInt256 := (σ.get? s |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩
  (KEC (L_A s n ζ i)).extract 12 32 /- 160 bits = 20 bytes -/
    |> fromByteArrayBigEndian |> Fin.ofNat _

/--
EIP-7610: a creation at `a` collides when the account there has a nonzero
nonce, a nonzero code length, or non-empty storage.
-/
def creationCollision (σ : AccountMap) (a : AccountAddress) : Bool :=
  let existentAccount := σ.getD a default
  existentAccount.nonce ≠ ⟨0⟩
    || existentAccount.code.size ≠ 0
    || existentAccount.storage != default

/--
EIP-8037 (Amsterdam): charges `amount` of state gas to the frame of `s`
(`charge_state_gas`), from the reservoir and then from its execution gas. Out
of gas when they do not cover it.
-/
def chargeStateGas (s : State) (amount : ℕ) : Except EVM.ExecutionException State :=
  if amount = 0 then .ok s else
  match StateGas.charge s.machineState.gasAvailable.toNat s.substate amount with
  | none => .error .OutOfGass
  | some (g, A) => .ok { s with machineState.gasAvailable := .ofNat g, substate := A }

/--
EIP-8037 (Amsterdam): credits back to the frame of `s` `amount` of state gas
that it charged for state that was not created (`credit_state_gas_refund`).
-/
def creditStateGas (s : State) (amount : ℕ) : State :=
  let (g, A) :=
    StateGas.credit s.machineState.gasAvailable.toNat s.substate
      s.executionEnv.stateGasSpillBaseline amount
  { s with machineState.gasAvailable := .ofNat g, substate := A }

/--
EIP-8037 (Amsterdam): after a child frame returned successfully, the frame of
`s` repays its spill from the reservoir the child returned
(`repay_state_gas_spill`).
-/
def repayStateGasSpill (s : State) : State :=
  let (g, A) :=
    StateGas.repaySpill s.machineState.gasAvailable.toNat s.substate
      s.executionEnv.stateGasSpillBaseline
  { s with machineState.gasAvailable := .ofNat g, substate := A }

/--
EIP-8037 (Amsterdam): the state charge of a call that creates its recipient
(`createsAccount`), on the execution gas `gas` left after the cost of the
call: the execution gas that it spills, and the substate.
-/
def callStateCharge (createsAccount : Bool) (gas : ℕ) (A : Substate) :
    Except EVM.ExecutionException (ℕ × Substate) :=
  if createsAccount then
    match StateGas.charge gas A StateGas.NEW_ACCOUNT with
    | none => .error .OutOfGass
    | some (g, A) => .ok (gas - g, A)
  else .ok (0, A)

/--
EIP-8037 (Amsterdam): the state gas of a frame `s` once its child, a call or
a creation, returned. After a child that succeeded, the frame repays its spill
from the reservoir (`incorporate_child`). After one that failed, the
`NEW_ACCOUNT` that the frame charged for the account the child would have
created, if it did (`charged`), is credited back.
-/
def settleChildStateGas (fork : Fork) (succeeded charged : Bool) (s : State) : State :=
  if fork.spec.eip8037 ∧ succeeded then repayStateGasSpill s
  else if charged then creditStateGas s StateGas.NEW_ACCOUNT
  else s

/--
EIP-8037 (Amsterdam): the state gas of `SSTORE`, before it stores. Setting a
slot that was zero at the start of the transaction, and still is, creates it:
`STORAGE_SET`. Clearing such a slot again credits that back.
-/
def sstoreStateGas (s : State) : Except EVM.ExecutionException State :=
  if ¬s.executionEnv.fork.spec.eip8037 then .ok s else
  let Iₐ := s.executionEnv.codeOwner
  let key := s.machineState.stack[0]!
  let v' := s.machineState.stack[1]!
  let v₀ : UInt256 := s.σ₀.get? Iₐ |>.option ⟨0⟩ (·.storage.getD key ⟨0⟩)
  let v : UInt256 := s.accountMap.get? Iₐ |>.option ⟨0⟩ (·.storage.getD key ⟨0⟩)
  if v₀ = ⟨0⟩ ∧ v = ⟨0⟩ ∧ v' ≠ ⟨0⟩ then chargeStateGas s StateGas.STORAGE_SET
  else if v₀ = ⟨0⟩ ∧ v ≠ ⟨0⟩ ∧ v' = ⟨0⟩ then .ok (creditStateGas s StateGas.STORAGE_SET)
  else .ok s

/--
EIP-7708 (Amsterdam): the logs of the frame of `s` after a `SELFDESTRUCT` to
`r`, which logs the transfer of the balance to another account.
-/
def selfDestructLogs (s : State) (r : AccountAddress) : LogSeries :=
  let Iₐ := s.executionEnv.codeOwner
  let balance : UInt256 := s.accountMap.get? Iₐ |>.option ⟨0⟩ (·.balance)
  if s.executionEnv.fork.spec.eip7708 ∧ r ≠ Iₐ ∧ balance ≠ ⟨0⟩ then
    s.substate.logSeries.push (LogEntry.transfer Iₐ r balance)
  else s.substate.logSeries

/--
EIP-8037 (Amsterdam): the state gas of `SELFDESTRUCT`: moving a balance to a
dead account creates it.
-/
def selfDestructStateGas (s : State) : ℕ :=
  let r := AccountAddress.ofUInt256 s.machineState.stack[0]!
  let balance : UInt256 := s.accountMap.get? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)
  if s.executionEnv.fork.spec.eip8037 ∧ State.dead s.accountMap r ∧ balance ≠ ⟨0⟩ then
    StateGas.NEW_ACCOUNT
  else 0

mutual

def call
  (gasCost : Nat)
  (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
  (permission : Bool)
  (evmState : State)
    :
  Except EVM.ExecutionException (UInt256 × State)
:= do
      let t : AccountAddress := AccountAddress.ofUInt256 t
      let recipient : AccountAddress := AccountAddress.ofUInt256 recipient
      let source : AccountAddress := AccountAddress.ofUInt256 source
      let Iₐ := evmState.executionEnv.codeOwner
      let σ := evmState.accountMap
      let Iₑ := evmState.executionEnv.depth
      let fork := evmState.executionEnv.fork
      let callgas := Ccallgas fork t recipient value gas σ evmState.machineState evmState.substate
      -- let evmState := evmState.subtractGas gasCost -- {evmState with machineState.gasAvailable := evmState.machineState.gasAvailable - gasCost}
      -- m[μs[3] . . . (μs[3] + μs[4] − 1)]
      let i := evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat
      /- EIP-8037 (Amsterdam): a call that moves value to a dead account
         creates it, in state gas. It is charged after the cost of the call
         and before the callee's gas, which is capped from what is left
         (`Cgascap`); `spill` is the execution gas it spends. -/
      let createsAccount := callCreatesAccount fork recipient value σ
      let (spill, A₀) ←
        callStateCharge createsAccount (evmState.machineState.gasAvailable.toNat - gasCost)
          evmState.substate
      let A' := callSubstate fork σ t A₀
      let (σ', g', A', z, o) :=
        if value ≤ (σ.get? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 then
            Θ (fork := fork)
              (σ  := σ)                                     -- σ in  Θ(σ, ..)
              (σ₀ := evmState.σ₀)
              (A  := A')                                    -- A* in Θ(.., A*, ..)
              (s  := source)
              (o  := evmState.executionEnv.sender)          -- Iₒ in Θ(.., Iₒ, ..)
              (r  := recipient)                             -- t in Θ(.., t, ..)
              (c  := toExecute fork σ t)
              (g  := .ofNat callgas)
              (p  := .ofNat evmState.executionEnv.gasPrice) -- Iₚ in Θ(.., Iₚ, ..)
              (v  := value)
              (v' := value')
              (d  := i)
              (e  := Iₑ + 1)
              (H := evmState.executionEnv.header)
              (blobVersionedHashes := evmState.executionEnv.blobVersionedHashes)
              (blocks := evmState.executionEnv.blocks)
              (w  := permission)                            -- I_w in Θ(.., I_W)
        else
          -- otherwise (σ, CCALLGAS(σ, μ, A), A, 0, ())
            (evmState.accountMap, .ofNat callgas, A', false, .empty)
      -- n ≡ min({μs[6], ‖o‖})
      let n : UInt256 := min outSize (.ofNat o.size)

      let μ'ₘ := writeBytes o 0 evmState.machineState outOffset.toNat n.toNat -- μ′_m[μs[5]  ... (μs[5] + n − 1)] = o[0 ... (n − 1)]
      let μ'ₒ := o -- μ′o = o
      -- let μ'_g := evmState.subtractGas (gasCost - g')

      let codeExecutionFailed   : Bool := !z
      let notEnoughFunds        : Bool := value > (σ.get? evmState.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) -- TODO - Unify condition with CREATE.
      let callDepthLimitReached : Bool := evmState.executionEnv.depth == 1024
      let x : UInt256 := if codeExecutionFailed || notEnoughFunds || callDepthLimitReached then ⟨0⟩ else ⟨1⟩ -- where x = 0 if the code execution for this operation failed, or if μs[2] > σ[Ia]b (not enough funds) or Ie = 1024 (call depth limit reached); x = 1 otherwise.

      -- NB. `MachineState` here does not contain the `Stack` nor the `PC`, thus incomplete.
      let μ'incomplete : MachineState :=
        { μ'ₘ with
            returnData   := μ'ₒ
            gasAvailable := evmState.machineState.gasAvailable.subNat (gasCost + spill - g'.toNat)
            activeWords :=
              let m : ℕ:= MachineState.M evmState.machineState.activeWords.toNat inOffset.toNat inSize.toNat
              .ofNat <| MachineState.M m outOffset.toNat outSize.toNat

        }

      let result : State := { evmState with accountMap := σ', substate := A' }
      let result := {
        result with machineState := μ'incomplete
      }
      .ok (x, settleChildStateGas fork z createsAccount result)
  termination_by (1024 - evmState.executionEnv.depth.val, 0, 0)
  decreasing_by
    omega

def create
  (value offset size : UInt256)
  (salt : Option ByteArray)
  (evmState : State)
  : Except EVM.ExecutionException (UInt256 × State)
:= do
  let i := evmState.machineState.memory.readWithPadding offset.toNat size.toNat
  let I := evmState.executionEnv
  let Iₐ := I.codeOwner
  let Iₒ := I.sender
  let Iₑ := I.depth
  let σ := evmState.accountMap
  let σ_Iₐ : Account := σ.get? Iₐ |>.getD default
  let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}
  /- EIP-8037 (Amsterdam): a creation that may proceed at an address whose
     account is dead creates it, in state gas, charged before the gas of the
     init code is withheld. A colliding creation keeps the charge. -/
  let a₀ := creationAddress σStar Iₐ salt i
  let createsAccount : Bool :=
    I.fork.spec.eip8037 && σ_Iₐ.nonce.toNat < 2^64-1
      && value ≤ (σ.get? Iₐ |>.option ⟨0⟩ (·.balance)) && Iₑ < 1024
      && i.size ≤ I.fork.maxInitCodeSize
      && State.dead σ a₀
  let evmState ← chargeStateGas evmState (if createsAccount then StateGas.NEW_ACCOUNT else 0)

  let (a, evmState', g', z, o) : (AccountAddress × State × UInt256 × Bool × ByteArray) :=
    if σ_Iₐ.nonce.toNat ≥ 2^64-1 then
      (default, evmState, .ofNat (L evmState.machineState.gasAvailable.toNat), false, .empty)
    else if hDepth :
        value ≤ (σ.get? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024
          ∧ i.size ≤ I.fork.maxInitCodeSize then
      let Λ :=
        Lambda
          I.fork
          σStar
          evmState.σ₀
          evmState.substate
          Iₐ
          Iₒ
          (.ofNat <| L evmState.machineState.gasAvailable.toNat)
          (.ofNat I.gasPrice)
          value
          i
          ⟨Iₑ.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
          salt
          I.header
          I.blobVersionedHashes
          I.blocks
          I.perm
      match Λ with
        | (a, σ', g', A', z, o) =>
          (a, {evmState with accountMap := σ', substate := A'}, g', z, o)
    else
      (0, evmState, .ofNat (L evmState.machineState.gasAvailable.toNat), false, .empty)

  let x : UInt256 :=
    let balance := σ.get? Iₐ |>.option ⟨0⟩ (·.balance)
    if z = false ∨ Iₑ = 1024 ∨ value > balance ∨ i.size > I.fork.maxInitCodeSize then ⟨0⟩
    else .ofNat a
  let newReturnData : ByteArray := if z then .empty else o
  if evmState.machineState.gasAvailable.toNat + g'.toNat < L evmState.machineState.gasAvailable.toNat then
    .error .OutOfGass
  let evmState' :=
    { evmState' with
      machineState.activeWords := .ofNat <| MachineState.M evmState.machineState.activeWords.toNat offset.toNat size.toNat
      machineState.returnData := newReturnData
      machineState.gasAvailable := evmState.machineState.gasAvailable.subNat (L evmState.machineState.gasAvailable.toNat - g'.toNat)
    }
  -- EIP-8037 (Amsterdam): a colliding creation keeps the `NEW_ACCOUNT` charge.
  .ok (x, settleChildStateGas I.fork z (createsAccount && !creationCollision σStar a₀) evmState')
  termination_by (1024 - evmState.executionEnv.depth.val, 0, 0)
  decreasing_by
    apply Prod.Lex.left
    exact Nat.sub_lt_sub_left hDepth.2.1 (Nat.lt_succ_self _)

def step (gasCost : ℕ) (instr : Operation × Option (UInt256 × Nat))
  : EVM.Transformer
:=
    λ (evmState : State) ↦ do
    -- This will normally be called from `Ξ` (or `X`) with `fetchInstr` already having been called.
    -- That said, we sometimes want a `step : EVM.Transformer` and as such, we can decode on demand.
    let (instr, arg) := (instr.1, instr.2)
    let evmState := { evmState with machineState.execLength := evmState.machineState.execLength + 1 }
    let evmStateCharged := { evmState with machineState.gasAvailable := evmState.machineState.gasAvailable.subNat gasCost }
    match instr with
      | .CREATE =>
        let (stack, value, offset, size) ← evmState.machineState.stack.pop3
        let (x, state') ← create value offset size none evmStateCharged
        .ok <| state'.replaceStackAndIncrPC (stack.push x)
      | .CREATE2 =>
        -- Exactly equivalent to CREATE except ζ ≡ μₛ[3]
        let (stack, value, offset, size, salt) ← evmState.machineState.stack.pop4
        let (x, state') ← create value offset size (some <| Ethereum.UInt256.toByteArray salt) evmStateCharged
        .ok <| state'.replaceStackAndIncrPC (stack.push x)
      | .CALL => do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.machineState.stack.pop7
        let (x, state') ←
          call gasCost μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .CALLCODE =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.machineState.stack.pop7
        let (x, state') ←
          call gasCost μ₀ (.ofNat evmState.executionEnv.codeOwner) (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .DELEGATECALL =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, /-μ₂,-/ μ₃, μ₄, μ₅, μ₆) ← evmState.machineState.stack.pop6
        let (x, state') ←
          call gasCost μ₀ (.ofNat evmState.executionEnv.source) (.ofNat evmState.executionEnv.codeOwner) μ₁ ⟨0⟩ evmState.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .STATICCALL =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, /- μ₂, -/ μ₃, μ₄, μ₅, μ₆) ← evmState.machineState.stack.pop6
        let (x, state') ←
          call gasCost μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩ μ₃ μ₄ μ₅ μ₆ false evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .STOP =>
          .ok <| {evmStateCharged with machineState := evmStateCharged.machineState.setReturnData .empty}
      | .ADD =>
        execBinOp UInt256.add evmStateCharged
      | .MUL =>
        execBinOp UInt256.mul evmStateCharged
      | .SUB =>
        execBinOp UInt256.sub evmStateCharged
      | .DIV =>
        execBinOp UInt256.div evmStateCharged
      | .SDIV =>
        execBinOp UInt256.sdiv evmStateCharged
      | .MOD =>
        execBinOp UInt256.mod evmStateCharged
      | .SMOD =>
        execBinOp UInt256.smod evmStateCharged
      | .ADDMOD =>
        execTriOp UInt256.addMod evmStateCharged
      | .MULMOD =>
        execTriOp UInt256.mulMod evmStateCharged
      | .EXP =>
        execBinOp UInt256.exp evmStateCharged
      | .SIGNEXTEND =>
        execBinOp UInt256.signextend evmStateCharged
      | .LT =>
        execBinOp UInt256.lt evmStateCharged
      | .GT =>
        execBinOp UInt256.gt evmStateCharged
      | .SLT =>
        execBinOp UInt256.slt evmStateCharged
      | .SGT =>
        execBinOp UInt256.sgt evmStateCharged
      | .EQ =>
        execBinOp UInt256.eq evmStateCharged
      | .ISZERO =>
        execUnOp UInt256.isZero evmStateCharged
      | .AND =>
        execBinOp UInt256.land evmStateCharged
      | .OR =>
        execBinOp UInt256.lor evmStateCharged
      | .XOR =>
        execBinOp UInt256.xor evmStateCharged
      | .NOT =>
        execUnOp UInt256.lnot evmStateCharged
      | .BYTE =>
        execBinOp UInt256.byteAt evmStateCharged
      | .SHL =>
        execBinOp (flip UInt256.shiftLeft) evmStateCharged
      | .SHR =>
        execBinOp (flip UInt256.shiftRight) evmStateCharged
      | .SAR =>
        execBinOp UInt256.sar evmStateCharged
      | .CLZ =>
        /- EIP-7939 (Osaka). Before Osaka `0x1e` is an invalid instruction.
           Rejecting it here rather than in `Z` is observationally the same:
           every exceptional halt reverts the frame and consumes its gas. -/
        if evmStateCharged.executionEnv.fork.spec.eip7939 then
          execUnOp UInt256.clz evmStateCharged
        else
          .error .InvalidInstruction

      | .KECCAK256 =>
        binaryMachineStateOp' MachineState.keccak256 evmStateCharged

      | .ADDRESS =>
        executionEnvOp (.ofNat ∘ Fin.val ∘ ExecutionEnv.codeOwner) evmStateCharged
      | .BALANCE =>
        unaryStateOp Ethereum.State.balance evmStateCharged
      | .ORIGIN =>
        executionEnvOp (.ofNat ∘ Fin.val ∘ ExecutionEnv.sender) evmStateCharged
      | .CALLER =>
        executionEnvOp (.ofNat ∘ Fin.val ∘ ExecutionEnv.source) evmStateCharged
      | .CALLVALUE =>
        executionEnvOp ExecutionEnv.weiValue evmStateCharged
      | .CALLDATALOAD =>
        unaryStateOp (λ s v ↦ (s, Ethereum.State.calldataload s v)) evmStateCharged
      | .CALLDATASIZE =>
        executionEnvOp (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.calldata) evmStateCharged
      | .CALLDATACOPY =>
        ternaryCopyOp calldatacopy evmStateCharged --is this correct?
      | .CODESIZE =>
        executionEnvOp (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code) evmStateCharged
      | .CODECOPY =>
        ternaryCopyOp codeCopy evmStateCharged
      | .GASPRICE =>
        executionEnvOp (.ofNat ∘ ExecutionEnv.gasPrice) evmStateCharged
      | .EXTCODESIZE =>
        unaryStateOp Ethereum.State.extCodeSize evmStateCharged
      | .EXTCODECOPY =>
        quaternaryCopyOp Ethereum.extCodeCopy' evmStateCharged
      | .RETURNDATASIZE =>
        machineStateOp Ethereum.MachineState.returndatasize evmStateCharged
      | .RETURNDATACOPY =>
          match evmStateCharged.machineState.stack.pop3 with
            | some ⟨stack', μ₀, μ₁, μ₂⟩ => do
              let mState' := evmStateCharged.machineState.returndatacopy μ₀ μ₁ μ₂
              let evmState' := {evmStateCharged with machineState := mState'}
              .ok <| evmState'.replaceStackAndIncrPC stack'
            | _ => .error .StackUnderflow
      | .EXTCODEHASH =>
        unaryStateOp Ethereum.State.extCodeHash evmStateCharged
      | .BLOCKHASH =>
        unaryStateOp (λ s v ↦ (s, Ethereum.State.blockHash s v)) evmStateCharged
      | .COINBASE =>
        stateOp (.ofNat ∘ Fin.val ∘ Ethereum.State.coinBase) evmStateCharged
      | .TIMESTAMP =>
        stateOp Ethereum.State.timeStamp evmStateCharged
      | .NUMBER => stateOp Ethereum.State.number evmStateCharged
      | .PREVRANDAO => executionEnvOp Ethereum.prevRandao evmStateCharged
      | .GASLIMIT => stateOp Ethereum.State.gasLimit evmStateCharged
      | .CHAINID => stateOp Ethereum.State.chainId evmStateCharged
      | .SELFBALANCE => stateOp Ethereum.State.selfbalance evmStateCharged
      | .BASEFEE => executionEnvOp Ethereum.basefee evmStateCharged
      | .BLOBHASH => unaryExecutionEnvOp blobhash evmStateCharged
      | .BLOBBASEFEE => executionEnvOp Ethereum.ExecutionEnv.getBlobGasprice evmStateCharged
      | .SLOTNUM =>
        /- EIP-7843 (Amsterdam). Before Amsterdam `0x4b` is an invalid
           instruction, rejected here as `CLZ` is. -/
        if evmStateCharged.executionEnv.fork.spec.eip7843 then
          executionEnvOp Ethereum.ExecutionEnv.slotNumber evmStateCharged
        else
          .error .InvalidInstruction
      | .POP =>
        match evmStateCharged.machineState.stack.pop with
          | some ⟨ s , _ ⟩ => .ok <| evmStateCharged.replaceStackAndIncrPC s
          | _ => .error .StackUnderflow

      | .MLOAD => 
        match evmStateCharged.machineState.stack.pop with
          | some ⟨ s , μ₀ ⟩ => Id.run do
            let (v, mState') := evmStateCharged.machineState.mload μ₀
            let evmState' := {evmStateCharged with machineState := mState'}
            .ok <| evmState'.replaceStackAndIncrPC (s.push v)
          | _ => .error .StackUnderflow
      | .MSTORE =>
        binaryMachineStateOp MachineState.mstore evmStateCharged
      | .MSTORE8 => binaryMachineStateOp MachineState.mstore8 evmStateCharged
      | .SLOAD =>
        unaryStateOp Ethereum.State.sload evmStateCharged
      | .SSTORE => do
        let evmStateCharged ← sstoreStateGas evmStateCharged
        binaryStateOp Ethereum.State.sstore evmStateCharged
      | .TLOAD => unaryStateOp Ethereum.State.tload evmStateCharged
      | .TSTORE => binaryStateOp Ethereum.State.tstore evmStateCharged
      | .MSIZE => machineStateOp MachineState.msize evmStateCharged
      | .GAS =>
        machineStateOp MachineState.gas evmStateCharged
      | .MCOPY => ternaryMachineStateOp MachineState.mcopy evmStateCharged

      | .LOG0 => log0Op evmStateCharged
      | .LOG1 => log1Op evmStateCharged
      | .LOG2 => log2Op evmStateCharged
      | .LOG3 => log3Op evmStateCharged
      | .LOG4 => log4Op evmStateCharged
      | .RETURN => binaryMachineStateOp MachineState.evmReturn evmStateCharged
      | .REVERT => binaryMachineStateOp MachineState.evmRevert evmStateCharged
      | .SELFDESTRUCT => do
          let evmStateCharged ← chargeStateGas evmStateCharged (selfDestructStateGas evmStateCharged)
          match evmStateCharged.machineState.stack.pop with
            | some ⟨ s , μ₁ ⟩ =>
              let Iₐ := evmStateCharged.executionEnv.codeOwner
              let r : AccountAddress := AccountAddress.ofUInt256 μ₁
              if evmStateCharged.substate.createdAccounts.contains Iₐ then
                -- When `SELFDESTRUCT` is executed in the same transaction as the contract was created
                let A' : Substate :=
                  { evmStateCharged.substate with
                      selfDestructSet :=
                        evmStateCharged.substate.selfDestructSet.insert Iₐ
                      accessedAccounts :=
                        evmStateCharged.substate.accessedAccounts.insert r
                      logSeries := selfDestructLogs evmStateCharged r
                  }
                let accountMap' :=
                  match evmStateCharged.lookupAccount Iₐ with
                    | none =>
                      dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; evmStateCharged.accountMap
                    | some σ_Iₐ  =>
                      match evmStateCharged.lookupAccount r with
                        | none =>
                          if σ_Iₐ.balance == ⟨0⟩ then
                            evmStateCharged.accountMap
                          else
                            evmStateCharged.accountMap.insert r
                              {(default : Account) with balance := σ_Iₐ.balance}
                                |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                        | some σ_r =>
                          if r ≠ Iₐ then
                            evmStateCharged.accountMap.insert r
                              {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                                |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                          else if evmStateCharged.executionEnv.fork.spec.eip8246 then
                            -- EIP-8246 (Amsterdam): no ether is burnt.
                            evmStateCharged.accountMap
                          else
                            -- if the target is the same as the contract calling `SELFDESTRUCT` that Ether will be burnt.
                            evmStateCharged.accountMap.insert r {σ_r with balance := ⟨0⟩}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                let evmState' :=
                  {evmStateCharged with
                    accountMap := accountMap'
                    substate := A'
                  }
                .ok <| evmState'.replaceStackAndIncrPC s
              else
                /- When SELFDESTRUCT is executed in a transaction that is not the
                  same as the contract calling SELFDESTRUCT was created:
                -/
                let A' : Substate :=
                  { evmStateCharged.substate with
                      accessedAccounts :=
                        evmStateCharged.substate.accessedAccounts.insert r
                      logSeries := selfDestructLogs evmStateCharged r
                  }
                let accountMap' :=
                  match evmStateCharged.lookupAccount Iₐ with
                    | none => dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; evmStateCharged.accountMap
                    | some σ_Iₐ  =>
                      match evmStateCharged.lookupAccount r with
                        | none =>
                          if σ_Iₐ.balance == ⟨0⟩ then
                            evmStateCharged.accountMap
                          else
                            evmStateCharged.accountMap.insert r
                              {(default : Account) with balance := σ_Iₐ.balance}
                                |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                        | some σ_r =>
                          if r ≠ Iₐ then
                            evmStateCharged.accountMap.insert r
                              {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                                |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                          else
                            -- Note that if the target is the same as the contract
                            -- calling SELFDESTRUCT there is no net change in balances.
                            -- Unlike the prior specification, Ether will not be burnt in this case.
                            evmStateCharged.accountMap
                let evmState' :=
                  {evmStateCharged with
                    accountMap := accountMap'
                    substate := A'
                  }
                .ok <| evmState'.replaceStackAndIncrPC s
            | _ => .error .StackUnderflow
      | .INVALID => .error .InvalidInstruction
      | .Push .PUSH0 =>
          .ok <|
            evmStateCharged.replaceStackAndIncrPC (evmStateCharged.machineState.stack.push ⟨0⟩)
      | .Push _ => do
          let some (arg, argWidth) := arg | .error .StackUnderflow
          .ok <| evmStateCharged.replaceStackAndIncrPC (evmStateCharged.machineState.stack.push arg) (pcΔ := argWidth.succ)
      | .JUMP =>
          match evmStateCharged.machineState.stack.pop with
            | some ⟨stack , μ₀⟩ =>
              let newPc := μ₀
              .ok <| {evmStateCharged with machineState.pc := newPc, machineState.stack := stack}
            | _ => .error .StackUnderflow
      | .JUMPI =>
          match evmStateCharged.machineState.stack.pop2 with
            | some ⟨stack , μ₀, μ₁⟩ =>
              let newPc := if μ₁ != ⟨0⟩ then μ₀ else evmStateCharged.machineState.pc + ⟨1⟩
              .ok <| {evmStateCharged with machineState.pc := newPc, machineState.stack := stack}
            | _ => .error .StackUnderflow
      | .PC => 
          .ok <| evmStateCharged.replaceStackAndIncrPC (evmStateCharged.machineState.stack.push evmStateCharged.machineState.pc)
      | .JUMPDEST => .ok <| evmStateCharged.incrPC
      | .DUP1 => dup 1 evmStateCharged
      | .DUP2 => dup 2 evmStateCharged
      | .DUP3 => dup 3 evmStateCharged
      | .DUP4 => dup 4 evmStateCharged
      | .DUP5 => dup 5 evmStateCharged
      | .DUP6 => dup 6 evmStateCharged
      | .DUP7 => dup 7 evmStateCharged
      | .DUP8 => dup 8 evmStateCharged
      | .DUP9 => dup 9 evmStateCharged
      | .DUP10 => dup 10 evmStateCharged
      | .DUP11 => dup 11 evmStateCharged
      | .DUP12 => dup 12 evmStateCharged
      | .DUP13 => dup 13 evmStateCharged
      | .DUP14 => dup 14 evmStateCharged
      | .DUP15 => dup 15 evmStateCharged
      | .DUP16 => dup 16 evmStateCharged
      | .SWAP1 => swap 1 evmStateCharged
      | .SWAP2 => swap 2 evmStateCharged
      | .SWAP3 => swap 3 evmStateCharged
      | .SWAP4 => swap 4 evmStateCharged
      | .SWAP5 => swap 5 evmStateCharged
      | .SWAP6 => swap 6 evmStateCharged
      | .SWAP7 => swap 7 evmStateCharged
      | .SWAP8 => swap 8 evmStateCharged
      | .SWAP9 => swap 9 evmStateCharged
      | .SWAP10 => swap 10 evmStateCharged
      | .SWAP11 => swap 11 evmStateCharged
      | .SWAP12 => swap 12 evmStateCharged
      | .SWAP13 => swap 13 evmStateCharged
      | .SWAP14 => swap 14 evmStateCharged
      | .SWAP15 => swap 15 evmStateCharged
      | .SWAP16 => swap 16 evmStateCharged
      | .StackAccess op =>
        /- EIP-8024 (Amsterdam). Before Amsterdam `0xe6` to `0xe8` are invalid
           instructions. Rejecting them here rather than in `Z` is
           observationally the same, as for `CLZ`. -/
        if evmStateCharged.executionEnv.fork.spec.eip8024 then
          stackAccess op (arg.option 0 (·.1.toNat)) evmStateCharged
        else
          .error .InvalidInstruction
    termination_by evmState => (1024 - evmState.executionEnv.depth.val, 1, 0)
    decreasing_by
      all_goals
        first
        | apply Prod.Lex.left
          omega
        | apply Prod.Lex.right
          apply Prod.Lex.left
          omega


-- Exceptional halting (158)
def Z (validJumps : Array UInt256) (w : Operation) (evmState : State)
    : Except EVM.ExecutionException (State × ℕ) :=
  let W (w : Operation) (s : Stack UInt256) : Bool :=
    w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
    (w = .CALL ∧ s[2]? ≠ some ⟨0⟩)
  if δ w = none then
    .error .InvalidInstruction
  else if evmState.machineState.stack.length < (δ w).getD 0 then
    .error .StackUnderflow
  else
    let cost₁ := memoryExpansionCost evmState w
    if evmState.machineState.gasAvailable.toNat < cost₁ then
      .error .OutOfGass
    else
      let evmState := { evmState with machineState.gasAvailable := evmState.machineState.gasAvailable.subNat cost₁ }
      let cost₂ := C' evmState w
      if evmState.machineState.gasAvailable.toNat < cost₂ then
        .error .OutOfGass
      else
        let invalidJump := notIn evmState.machineState.stack[0]? validJumps
        if w = .JUMP ∧ invalidJump then
          .error .BadJumpDestination
        else if w = .JUMPI ∧ (evmState.machineState.stack[1]? ≠ some ⟨0⟩) ∧ invalidJump then
          .error .BadJumpDestination
        else if w = .RETURNDATACOPY ∧ (evmState.machineState.stack.getD 1 ⟨0⟩).toNat + (evmState.machineState.stack.getD 2 ⟨0⟩).toNat > evmState.machineState.returnData.size then
          .error .InvalidMemoryAccess
        else if evmState.machineState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024 then
          .error .StackOverflow
        else if (¬ evmState.executionEnv.perm) ∧ W w evmState.machineState.stack then
          .error .StaticModeViolation
        else if (w = .SSTORE) ∧ evmState.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
          .error .OutOfGass
        else if w.isCreate ∧
            evmState.machineState.stack.getD 2 ⟨0⟩ > .ofNat evmState.executionEnv.fork.maxInitCodeSize then
          .error .OutOfGass
        else
          .ok (evmState, cost₂)
 where
  belongs (o : Option UInt256) (l : Array UInt256) : Bool :=
    match o with
      | none => false
      | some n => l.contains n
  notIn (o : Option UInt256) (l : Array UInt256) : Bool := not (belongs o l)

def Xstep (validJumps : Array UInt256) (evmState : State)
  : Except EVM.ExecutionException (State × Option (HaltCause × ByteArray))
:= do
  let evmState0 := evmState
  let I_b := evmState.executionEnv.code
  let instr@(w, _) := decode I_b evmState.machineState.pc |>.getD (.STOP, .none)
  let H (μ : MachineState) (w : Operation) : Option ByteArray :=
    if w ∈ [.RETURN, .REVERT] then
      some <| μ.H_return
    else
      if w ∈ [.STOP, .SELFDESTRUCT] then
        some .empty
      else none
  match Z validJumps w evmState with
    | .error e =>
      .error e
    | some (evmState, cost₂) =>
      -- depth reassignement bellow is ugly, but so is trying to prove that step does not change depth probably..
      let evmState' ← step cost₂ instr {evmState with executionEnv.depth := evmState0.executionEnv.depth}
      let evmState' := { evmState' with executionEnv := evmState0.executionEnv }
      -- Maybe we should restructure in a way such that it is more meaningful to compute
      -- gas independently, but the model has not been set up thusly and it seems
      -- that neither really was the YP.
      -- Similarly, we cannot reach a situation in which the stack elements are not available
      -- on the stack because this is guarded above. As such, `C` can be pure here.
      match H evmState'.machineState w with -- The YP does this in a weird way.
        | none => .ok ⟨evmState', .none⟩ -- X f validJumps evmState'
        | some o =>
          if w == .REVERT then
            /-
              The Yellow Paper says we don't call the "iterator function" "O" for `REVERT`,
              but we actually have to call the semantics of `REVERT` to pass the test
              EthereumTests/BlockchainTests/GeneralStateTests/stReturnDataTest/returndatacopy_after_revert_in_staticcall.json
              And the EEL spec does so too.
            -/
            .ok <| ⟨evmState', .some ⟨.revert, o⟩⟩
          else
            .ok <| ⟨evmState', .some ⟨.success, o⟩⟩
            termination_by (1024 - evmState.executionEnv.depth.val, 2, 0)
            decreasing_by
              apply Prod.Lex.right
              apply Prod.Lex.left
              omega

/--
  Iterative progression of `step`
-/
def X (fuel : ℕ) (validJumps : Array UInt256) (evmState : State)
  : Except EVM.ExecutionException (ExecutionResult State)
:= do
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f =>
      let ⟨evmState',ret⟩ ← Xstep validJumps evmState
      match ret with -- The YP does this in a weird way.
        | none => X f validJumps {evmState' with executionEnv.depth := evmState.executionEnv.depth}
        | some ⟨.revert, o⟩ =>
          .ok <| .revert (revertGas evmState') o
        | some ⟨.success, o⟩ =>
          .ok <| .success evmState' o
          termination_by (1024 - evmState.executionEnv.depth.val, 3, fuel)
          decreasing_by
            all_goals
              first
              | apply Prod.Lex.right
                apply Prod.Lex.left
                omega
              | apply Prod.Lex.right
                apply Prod.Lex.right
                omega

/--
  The code execution function
-/
def Ξ -- Type `Ξ` using `\GX` or `\Xi`
  (σ : AccountMap)
  (σ₀ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  Except
    EVM.ExecutionException
    (ExecutionResult (AccountMap × UInt256 × Substate))
:= do
      let defState : State := default
      let freshEvmState : State :=
        { defState with
            accountMap := σ
            σ₀ := σ₀
            executionEnv := I
            substate := A
            machineState.gasAvailable := .ofUInt256 g
        }
      /- The fuel exceeds the frame's gas, counting the execution gas that its
         state charges at entry spilled (EIP-8037), which it can get back:
         every step that continues spends some of it. -/
      let result ← X (UInt256.toNat g + StateGas.ownSpill A I.stateGasSpillBaseline + 1)
        (D_J I.code 0) freshEvmState
      match result with
        | .success evmState' o =>
          let finalGas := evmState'.machineState.gasAvailable
          .ok (ExecutionResult.success (evmState'.accountMap, finalGas.toUInt256, evmState'.substate) o)
        | .revert g' o => .ok (ExecutionResult.revert g' o)
    termination_by (1024 - I.depth.val, 4, 0)
    decreasing_by
      apply Prod.Lex.right
      apply Prod.Lex.left
      omega

def Lambda
  (fork : Fork)          -- the active fork
  (σ : AccountMap)
  (σ₀ : AccountMap)
  (A : Substate)
  (s : AccountAddress)   -- sender
  (o : AccountAddress)   -- original transactor
  (g : UInt256)          -- available gas
  (p : UInt256)          -- gas price
  (v : UInt256)          -- endowment
  (i : ByteArray)        -- the initialisation EVM code
  (e : Fin 1025)          -- depth of the message-call/contract-creation stack
  (ζ : Option ByteArray) -- the salt (92)
  (H : BlockHeader)      -- "I_H has no special treatment and is determined from the blockchain"
  (blobVersionedHashes : List ByteArray)
  (blocks : ProcessedBlocks)
  (w : Bool)             -- permission to make modifications to the state
  :
  ( AccountAddress
  × AccountMap
  × UInt256
  × Substate
  × Bool
  × ByteArray
  )
:=
  -- EIP-3860 (includes EIP-170)
  -- https://eips.ethereum.org/EIPS/eip-3860

  let a : AccountAddress := creationAddress σ s ζ i -- (94) (95)

  -- A* (97)
  let AStar := A.addAccessedAccount a
  -- σ*
  let existentAccount := σ.getD a default

  /-
    https://eips.ethereum.org/EIPS/eip-7610
    If a contract creation is attempted due to a creation transaction,
    the CREATE opcode, the CREATE2 opcode, or any other reason,
    and the destination address already has either a nonzero nonce,
    a nonzero code length, or non-empty storage, then the creation MUST throw
    as if the first byte in the init code were an invalid opcode.
  -/
  let collision : Bool := creationCollision σ a
  let (i, createdAccounts) :=
    if collision then
      (⟨#[0xfe]⟩, A.createdAccounts)
    else (i, A.createdAccounts.insert a)
  let AStar := { AStar with createdAccounts := createdAccounts }

  -- EIP-8037 (Amsterdam): the frame of a creation transaction (depth 0)
  -- creates an account that was empty before the transaction: `NEW_ACCOUNT`
  -- in state gas. A colliding creation fails anyway. When the gas does not
  -- cover it, the frame fails.
  let charged : Option (UInt256 × Substate) :=
    if fork.spec.eip8037 ∧ e.val = 0 ∧ ¬collision
        ∧ (σ₀.get? a |>.option true Account.emptyAccount) then
      (StateGas.charge g.toNat AStar StateGas.NEW_ACCOUNT).map fun (g, A) => (.ofNat g, A)
    else some (g, AStar)
  match charged with
  | none => (a, σ, ⟨0⟩, {AStar with createdAccounts := A.createdAccounts}, false, .empty)
  | some (gₜ, AStarₜ) =>
  -- EIP-7708 (Amsterdam): the endowment is logged in the creation's frame.
  let AStarₜ :=
    if fork.spec.eip7708 ∧ v ≠ ⟨0⟩ then
      { AStarₜ with logSeries := AStarₜ.logSeries.push (LogEntry.transfer s a v) }
    else AStarₜ

  let newAccount : Account :=
    { existentAccount with
        nonce := existentAccount.nonce + ⟨1⟩
        balance := v + existentAccount.balance
    }

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let σStar :=
    match σ.get? s with
      | none =>  σ
      | some ac =>
        σ.insert s {ac with balance := ac.balance - v}
          |>.insert a newAccount -- (99)
  -- I
  let exEnv : ExecutionEnv :=
    { codeOwner := a
    , sender    := o
    , source    := s
    , weiValue  := v
    , calldata := default
    , code      := i
    , gasPrice  := p.toNat
    , header    := H
    , depth     := e
    , perm      := w
    , blobVersionedHashes := blobVersionedHashes
    , blocks := blocks
    , fork := fork
    , stateGasSpillBaseline := A.stateGasSpilled
    }
  match Ξ σStar σ₀ gₜ AStarₜ exEnv with
    | .error _ =>
      -- if e == .OutOfFuel then throw .OutOfFuel
      (a, σ, ⟨0⟩, {AStar with createdAccounts := A.createdAccounts}, false, .empty)
    | .ok (.revert g' o) =>
      (a, σ, g', {AStar with createdAccounts := A.createdAccounts}, false, o)
    | .ok (.success (σStarStar, gStarStar, AStarStar) returnedData) =>
      -- The code-deposit cost (113)
      let c := GasConstants.Gcodedeposit * returnedData.size
      /- EIP-8037 (Amsterdam): the code deposit hashes the code, in execution
         gas, and stores it, in state gas per byte (`process_create`); `none`
         when the gas does not cover them. -/
      let deposit : Option (ℕ × Substate) :=
        let hashing := GasConstants.Gkeccak256word * ((returnedData.size + 31) / 32)
        if gStarStar.toNat < hashing then none
        else
          StateGas.charge (gStarStar.toNat - hashing) AStarStar
            (StateGas.COST_PER_STATE_BYTE * returnedData.size)

      let F : Bool := Id.run do -- (118)
        let F₀ : Bool :=
          match σ.get? a with
          | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ ⟨0⟩
          | .none => false
        let F₂ : Bool := if fork.spec.eip8037 then deposit.isNone else gStarStar.toNat < c
        let F₃ : Bool := returnedData.size > fork.maxCodeSize
        let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
        pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)

      let σ' : AccountMap := -- (115)
        if F then σ else
          let newAccount' := σStarStar.getD a default
          σStarStar.insert a {newAccount' with code := returnedData}

      -- (114)
      let g' := if F then 0 else
        if fork.spec.eip8037 then deposit.option 0 (·.1) else gStarStar.toNat - c

      -- (116)
      let A' := if F then AStar else
        if fork.spec.eip8037 then deposit.option AStarStar (·.2) else AStarStar
      -- (117)
      let z := not F
      (a, σ', .ofNat g', A', z, .empty) -- (93)
      termination_by (1024 - e.val, 5, 0)
      decreasing_by
        apply Prod.Lex.right
        apply Prod.Lex.left
        omega

/--
Message cal
`σ`  - evm state
`A`  - accrued substate
`s`  - sender
`o`  - transaction originator
`r`  - recipient
`c`  - the account whose code is to be called, usually the same as `r`
`g`  - available gas
`p`  - effective gas price
`v`  - value
`v'` - value in the execution context
`d`  - input data of the call
`e`  - depth of the message-call / contract-creation stack
`w`  - permissions to make modifications to the stack
`fork` - the active fork

NB - This is implemented using the 'boolean' fragment with ==, <=, ||, etc.
     The 'prop' version will come next once we have the comutable one.
-/
def Θ (fork : Fork)
      (σ  : AccountMap)
      (σ₀  : AccountMap)
      (A  : Substate)
      (s  : AccountAddress)
      (o  : AccountAddress)
      (r  : AccountAddress)
      (c  : ToExecute)
      (g  : UInt256)
      (p  : UInt256)
      (v  : UInt256)
      (v' : UInt256)
      (d  : ByteArray)
      (e  : Fin 1025)
      (H : BlockHeader)
      (blobVersionedHashes : List ByteArray)
      (blocks : ProcessedBlocks)
      (w  : Bool)
        :
      (AccountMap × UInt256 × Substate × Bool × ByteArray)
:=
  -- EIP-8037 (Amsterdam): the top frame (depth 0) first charges its costs
  -- that depend on the state; when the gas does not cover them, it fails.
  let charged : Option (UInt256 × Substate) :=
    if fork.spec.eip8037 ∧ e.val = 0 then
      (topFrameCallCharges σ A g.toNat r v).map fun (g, A) => (.ofNat g, A)
    else some (g, A)
  match charged with
  | none => (σ, ⟨0⟩, A, false, .empty)
  | some (gₜ, Aₜ) =>
  /- EIP-7708 (Amsterdam): a transfer to another account is logged in the
     callee's frame, before its own logs, and discarded with them when it
     fails. -/
  let Aₜ :=
    if fork.spec.eip7708 ∧ v ≠ ⟨0⟩ ∧ s ≠ r then
      { Aₜ with logSeries := Aₜ.logSeries.push (LogEntry.transfer s r v) }
    else Aₜ

  -- (124) (125) (126)
  let σ'₁ :=
    match σ.get? r with
      | none =>
        if v != UInt256.ofNat 0 then
          σ.insert r { (default : Account) with balance := v}
        else
          σ
      | some acc =>
        σ.insert r { acc with balance := acc.balance + v}

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let σ₁ :=
    match σ'₁.get? s with
      | none => σ'₁
      | some acc =>
        σ'₁.insert s { acc with balance := acc.balance - v}

  let I : ExecutionEnv :=
    {
      codeOwner := r        -- Equation (132)
      sender    := o        -- Equation (133)
      gasPrice  := p.toNat  -- Equation (134)
      calldata := d        -- Equation (135)
      source    := s        -- Equation (136)
      weiValue  := v'       -- Equation (137)
      depth     := e        -- Equation (138)
      perm      := w        -- Equation (139)
      -- Note that we don't use an address, but the actual code. Equation (141)-ish.
      code      :=
        match c with
          | ToExecute.Precompiled _ => default
          | ToExecute.Code code => code
      header    := H
      blobVersionedHashes := blobVersionedHashes
      blocks := blocks
      fork := fork
      stateGasSpillBaseline := A.stateGasSpilled
    }

  -- Equation (131)
  -- Note that the `c` used here is the actual code, not the address.
  let (σ'', g', A'', out) :=
    match c with
      | ToExecute.Precompiled p =>
        Ξ_PRECOMPILE p σ₁ gₜ Aₜ I
      | ToExecute.Code _ =>
        match Ξ σ₁ σ₀ gₜ Aₜ I with
          | .error _ =>
            -- Cannot techically happen
            -- if e == .OutOfFuel then throw .OutOfFuel
            (∅, ⟨0⟩, A, .empty)
          | .ok (.revert g' o) =>
            (∅, g', A, o)
          | .ok (.success (a, b, c) o) =>
            (a, b, c, o)

  -- Equation (127)
  let σ' := if σ'' == ∅ then σ else σ''

  -- Equation (129)
  let A' := if σ'' == ∅ then A else A''

  -- Equation (130)
  let z := if σ'' == ∅ then false else true

  -- Equation (119)
  (σ', g', A', z, out)
  termination_by (1024 - e.val, 5, 0)
  decreasing_by
    apply Prod.Lex.right
    apply Prod.Lex.left
    omega

end

open Batteries (RBMap RBSet)


/--
EIP-7702 (Prague): the authority that signed `auth`, or `none` when the tuple
is invalid for the chain `chainId` or its signature does not recover.
-/
def authorizationAuthority? (chainId : ℕ) (auth : Authorization) : Option AccountAddress := do
  if auth.chainId.toNat ≠ 0 ∧ auth.chainId.toNat ≠ chainId then none
  -- Applying an authorization increments the authority nonce (EIP-2681).
  if auth.nonce.toNat ≥ 2 ^ 64 - 1 then none
  if auth.yParity.toNat > 1 then none
  let r := fromByteArrayBigEndian auth.r
  let s := fromByteArrayBigEndian auth.s
  if r = 0 ∨ r ≥ secp256k1n ∨ s = 0 ∨ s > secp256k1n / 2 then none
  let payload ← RLP <| .𝕃
    [ .𝔹 (BE auth.chainId.toNat)
    , .𝔹 auth.address.toByteArray
    , .𝔹 (BE auth.nonce.toNat)
    ]
  let digest := KEC (⟨#[0x05]⟩ ++ payload)
  let publicKey ←
    (ECDSARECOVER digest ⟨#[.ofNat auth.yParity.toNat]⟩ auth.r auth.s).toOption
  pure <| .ofNat <| fromByteArrayBigEndian ((KEC publicKey).extract 12 32)

/--
EIP-7702 (Prague): apply an authorization list in order. Returns the new
state, the authorities to add to the accessed accounts, and the refund for
authorities that already existed.
-/
def applyAuthorizations
    (chainId : ℕ) (auths : List Authorization) (σ : AccountMap) :
    AccountMap × Batteries.RBSet AccountAddress compare × ℕ :=
  auths.foldl (init := (σ, ∅, 0)) λ (σ, accessed, refund) auth ↦
    match authorizationAuthority? chainId auth with
    | none => (σ, accessed, refund)
    | some authority =>
      let accessed := accessed.insert authority
      let account := σ.get? authority |>.getD default
      if (account.code.size ≠ 0 ∧ ¬isDelegationDesignation account.code)
          ∨ account.nonce ≠ auth.nonce then
        (σ, accessed, refund)
      else
        let refund :=
          if (σ.get? authority).isSome then
            refund + (GasConstants.Gnewaccount - GasConstants.Gauthbase)
          else refund
        let code :=
          if auth.address = 0 then .empty else delegationDesignation auth.address
        (σ.insert authority { account with nonce := account.nonce + ⟨1⟩, code }, accessed, refund)

/--
EIP-7702 from Amsterdam: applies the authorization list as `applyAuthorizations`
does, charging the transaction's meter as the execution specs' `set_delegation`
(EIP-8037, EIP-8038). An authority without an account is created, in state gas;
a write to an authority whose account the transaction does not otherwise pay to
write (`paidWrites`) costs `ACCOUNT_WRITE`; and a delegation that the authority
did not have before the transaction (`σPre`) costs `AUTH_BASE` in state gas,
once per authority. The refund of Prague is gone. Returns the state, the
authorities to warm, the execution gas and the meter, or `none` when the gas
does not cover the charges.
-/
def applyAuthorizationsAmsterdam
    (chainId : ℕ) (auths : List Authorization) (σPre σ : AccountMap)
    (paidWrites : Batteries.RBSet AccountAddress compare) (gas : ℕ) (A : Substate) :
    Option (AccountMap × Batteries.RBSet AccountAddress compare × ℕ × Substate) := do
  let mut σ := σ
  let mut accessed : Batteries.RBSet AccountAddress compare := ∅
  let mut paid := paidWrites
  let mut delegated : Batteries.RBSet AccountAddress compare := ∅
  let mut gas := gas
  let mut A := A
  for auth in auths do
    let some authority := authorizationAuthority? chainId auth | continue
    accessed := accessed.insert authority
    let account := σ.get? authority |>.getD default
    if (account.code.size ≠ 0 ∧ ¬isDelegationDesignation account.code)
        ∨ account.nonce ≠ auth.nonce then
      continue
    if (σ.get? authority).isNone then
      let (g, A') ← StateGas.charge gas A StateGas.NEW_ACCOUNT
      gas := g
      A := A'
    if ¬paid.contains authority then
      guard (GasConstants.Gaccountwrite ≤ gas)
      gas := gas - GasConstants.Gaccountwrite
      paid := paid.insert authority
    let mut code := ByteArray.empty
    if auth.address ≠ 0 then
      let delegatedBefore := isDelegationDesignation (σPre.get? authority |>.option .empty (·.code))
      if ¬delegatedBefore ∧ ¬delegated.contains authority then
        let (g, A') ← StateGas.charge gas A StateGas.AUTH_BASE
        gas := g
        A := A'
      delegated := delegated.insert authority
      code := delegationDesignation auth.address
    σ := σ.insert authority { account with nonce := account.nonce + ⟨1⟩, code }
  return (σ, accessed, gas, A)

/--
The accounts that destroyed themselves in the transaction (EIP-6780: those it
created) are deleted at its end. From EIP-8246 (Amsterdam), their balance
stays: their nonce, code and storage are cleared, and the account is deleted
only if it is then empty.
-/
def destroyAccounts (fork : Fork) (A : Substate) (σ : AccountMap) : AccountMap :=
  if fork.spec.eip8246 then
    A.selfDestructSet.1.foldl (init := σ) fun σ a =>
      match σ.get? a with
      | none => σ
      | some acc =>
        let acc := { acc with nonce := ⟨0⟩, code := .empty, storage := default }
        if acc.balance = ⟨0⟩ then σ.erase a else σ.insert a acc
  else A.selfDestructSet.1.foldl Std.ExtTreeMap.erase σ

/--
The outcome of a transaction (`Υ`): the state, the substate, whether it
succeeded, and its gas.
-/
structure TransactionOutcome where
  σ : AccountMap
  A : Substate
  status : Bool
  /-- The gas the sender pays for, which the receipts accumulate. -/
  gasUsed : ℕ
  /-- EIP-7778 (Amsterdam): the execution gas the block counts, before
      refunds. Before Amsterdam, `gasUsed`. -/
  executionGasUsed : ℕ
  /-- EIP-7778 (Amsterdam): the state gas the block counts. -/
  stateGasUsed : ℕ := 0

/--
The transaction-level state transition from Amsterdam (EIP-8037, with EIP-2780,
EIP-7778, EIP-7976, EIP-7981 and EIP-8038), as the execution specs'
`process_transaction`.

- Of the gas left after the intrinsic cost, at most `TX_MAX_GAS_LIMIT` less
  the intrinsic cost is the top frame's execution gas; the rest is its
  state-gas reservoir.
- The sender pays the gas limit up front, and its nonce increases.
- The authorizations are applied, charging the meter, and their charges stay
  even if the frame fails (`commit_state_gas`).
- The top frame runs. `Θ` and `Lambda` charge its costs that depend on the
  state at depth 0. If the gas does not cover them or the authorizations, the
  transaction is included but runs nothing: the delegations are undone, the
  execution gas is spent, and the reservoir is left whole.
- The sender pays for the gas used before refunds, less the refund, and at
  least the floor. The block counts execution and state gas separately.
-/
def ΥAmsterdam
  (fork : Fork)
  (σ : AccountMap)
  (H_f : ℕ)
  (H : BlockHeader)
  (blocks : ProcessedBlocks)
  (T : Transaction)
  (S_T : AccountAddress)
  : TransactionOutcome
:=
  let cost := EVM.intrinsicCost T S_T
  let gasLimit := T.base.gasLimit.toNat
  let evmGas := gasLimit - cost.execution
  let executionGrant := min (GasConstants.TX_MAX_GAS_LIMIT - cost.execution) evmGas
  let reservoir := evmGas - executionGrant
  let senderAccount := (σ.get? S_T).get!
  -- The priority fee and the effective gas price
  let f :=
    match T with
      | .legacy t | .access t => t.gasPrice - .ofNat H_f
      | .dynamic t | .blob t | .setCode t => min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)
  let p :=
    match T with
      | .legacy t | .access t => t.gasPrice
      | .dynamic _ | .blob _ | .setCode _ => f + .ofNat H_f
  let senderAccount :=
    { senderAccount with
        balance := senderAccount.balance - T.base.gasLimit * p - .ofNat (calcBlobFee fork H T)
        nonce := senderAccount.nonce + ⟨1⟩ }
  let σ₀ := σ.insert S_T senderAccount
  let meter : Substate := { (default : Substate) with stateGasReservoir := reservoir }
  let paidWrites : Batteries.RBSet AccountAddress compare :=
    match T.base.recipient with
    | some t =>
      if T.base.value != ⟨0⟩ then (∅ : Batteries.RBSet AccountAddress compare).insert S_T |>.insert t
      else (∅ : Batteries.RBSet AccountAddress compare).insert S_T
    | none => (∅ : Batteries.RBSet AccountAddress compare).insert S_T
  let authorized :=
    if T.authorizationList.isEmpty then some (σ₀, ∅, executionGrant, meter)
    else applyAuthorizationsAmsterdam chainId T.authorizationList σ σ₀ paidWrites executionGrant meter
  let accessList := T.getAccessList
  let AStar_K : List (AccountAddress × UInt256) := do
    let ⟨Eₐ, Eₛ⟩ ← accessList
    let eₛ ← Eₛ.toList
    pure (Eₐ, eₛ)
  -- The prepared top frame: its state, substate and execution gas.
  let prepared : Option (AccountMap × Substate × ℕ) := do
    let (σ₁, authorities, gas, meter) ← authorized
    let accessed :=
      (A0 fork).accessedAccounts.insert S_T
        |>.insert H.beneficiary
        |>.union (Batteries.RBSet.ofList (accessList.map Prod.fst) compare)
        |>.union authorities
    let accessed := match T.base.recipient with
      | some t => accessed.insert t
      | none => accessed
    let AStar :=
      { meter with
          accessedAccounts := accessed
          accessedStorageKeys := Batteries.RBSet.ofList AStar_K Substate.storageKeysCmp }
    -- The top frame's costs that depend on the state must be covered.
    if let some t := T.base.recipient then
      let _ ← topFrameCallCharges σ₁ AStar gas t T.base.value
    pure (σ₁, AStar, gas)
  let (σ_P, g', A, z) : AccountMap × ℕ × Substate × Bool :=
    match prepared with
    | none => (σ₀, 0, meter, false)
    | some (σ₁, AStar, gas) =>
      match T.base.recipient with
      | none =>
        match
          Lambda fork σ₁ σ₁ AStar S_T S_T (.ofNat gas) p T.base.value T.base.data 0 none H
            T.blobVersionedHashes blocks true
        with
        | (_, σ_P, g', A, z, _) => (σ_P, g'.toNat, A, z)
      | some t =>
        match
          Θ fork σ₁ σ₁ AStar S_T S_T t (toExecute fork σ₁ t) (.ofNat gas) p T.base.value
            T.base.value T.base.data 0 H T.blobVersionedHashes blocks true
        with
        | (σ_P, g', A, z, _) => (σ_P, g'.toNat, A, z)
  -- Settlement (`settle_transaction_gas`)
  let gasUsedBeforeRefund := gasLimit - g' - A.stateGasReservoir
  let refund := min (gasUsedBeforeRefund / 5) A.refundBalance.toNat
  let gasUsed := max (gasUsedBeforeRefund - refund) cost.floor
  let stateGasUsed := reservoir + A.stateGasSpilled - A.stateGasReservoir
  let executionGasUsed := max (gasUsedBeforeRefund - stateGasUsed) cost.floor
  let σStar := σ_P.increaseBalance S_T (.ofNat (gasLimit - gasUsed) * p)
  let beneficiaryFee := .ofNat gasUsed * f
  let σStar' :=
    if beneficiaryFee != UInt256.ofNat 0 then σStar.increaseBalance H.beneficiary beneficiaryFee
    else σStar
  let σ' := destroyAccounts fork A σStar'
  let deadAccounts := A.touchedAccounts.filter (State.dead σStar' ·)
  let σ' := deadAccounts.foldl Std.ExtTreeMap.erase σ'
  let σ' := σ'.map λ _ acc ↦ { acc with tstorage := .empty }
  { σ := σ', A, status := z, gasUsed, executionGasUsed, stateGasUsed }

-- Type Υ using \Upsilon or \GU
/--
The transaction-level state transition `Υ` (Yellow Paper, Section 6).

It assumes that `T` is valid and that `S_T` is its sender, as established by
`validateTransaction` (`Ethereum/Transaction.lean`); `applyTransaction`
combines the two.
-/
def Υ
  (fork : Fork)
  (σ : AccountMap)
  (H_f : ℕ)
  (H : BlockHeader)
  (blocks : ProcessedBlocks)
  (T : Transaction)
  (S_T : AccountAddress)
  : Except EVM.Exception TransactionOutcome
:= do
  if fork.spec.eip8037 then return ΥAmsterdam fork σ H_f H blocks T S_T
  let g₀ : ℕ := EVM.intrinsicGas fork T
  -- "here can be no invalid transactions from this point"
  let senderAccount := (σ.get? S_T).get!
  -- The priority fee (67)
  let f :=
    match T with
      | .legacy t | .access t =>
            t.gasPrice - .ofNat H_f
      | .dynamic t | .blob t | .setCode t =>
            min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)
  -- The effective gas price
  let p := -- (66)
    match T with
      | .legacy t | .access t => t.gasPrice
      | .dynamic _ | .blob _ | .setCode _ => f + .ofNat H_f
  let senderAccount :=
    { senderAccount with
        /-
          https://eips.ethereum.org/EIPS/eip-4844
          "The actual blob_fee as calculated via calc_blob_fee is deducted from
          the sender balance before transaction execution and burned, and is not
          refunded in case of transaction failure."
        -/
        balance := senderAccount.balance - T.base.gasLimit * p - .ofNat (calcBlobFee fork H T)  -- (74)
        nonce := senderAccount.nonce + ⟨1⟩ -- (75)
    }
  -- The checkpoint state (73)
  let σ₀ := σ.insert S_T senderAccount
  -- EIP-7702 (Prague): authorizations are applied after the sender's nonce
  -- increment and persist even when execution fails.
  let (σ₀, authorities, authRefund) :=
    if fork.spec.eip7702 then applyAuthorizations chainId T.authorizationList σ₀
    else (σ₀, ∅, 0)
  let accessList := T.getAccessList
  let AStar_K : List (AccountAddress × UInt256) := do -- (78)
    let ⟨Eₐ, Eₛ⟩ ← accessList
    let eₛ ← Eₛ.toList
    pure (Eₐ, eₛ)
  let a := -- (80)
    (A0 fork).accessedAccounts.insert S_T
      |>.insert H.beneficiary
      |>.union <| Batteries.RBSet.ofList (accessList.map Prod.fst) compare
  let a := a.union authorities
  -- (81)
  let g := .ofNat <| T.base.gasLimit.toNat - g₀
  let AStarₐ := -- (79)
    match T.base.recipient with
      | some t =>
        -- EIP-7702 (Prague): the delegation target of the recipient is warm.
        let delegate :=
          if fork.spec.eip7702 then delegationTarget? (σ₀.get? t |>.option .empty (·.code)) else none
        match delegate with
        | some d => (a.insert t).insert d
        | none => a.insert t
      | none => a
  let AStar := -- (77)
    { A0 fork with
        accessedAccounts := AStarₐ
        accessedStorageKeys := Batteries.RBSet.ofList AStar_K Substate.storageKeysCmp
        refundBalance := .ofNat authRefund }
  let (/- provisional state -/ σ_P, g', A, z) ← -- (76)
    match T.base.recipient with
      | none => do
        match
          Lambda
            fork
            σ₀
            σ₀
            AStar
            S_T
            S_T
            g
            p
            T.base.value
            T.base.data
            0
            none
            H
            T.blobVersionedHashes
            blocks
            true
        with
          | (_, σ_P, g', A, z, _) => pure (σ_P, g', A, z)
      | some t =>
        -- Proposition (71) suggests the recipient can be inexistent
        match
          Θ fork
            σ₀
            σ₀
            AStar
            S_T
            S_T
            t
            (toExecute fork σ₀ t)
            g
            p
            T.base.value
            T.base.value
            T.base.data
            0
            H
            T.blobVersionedHashes
            blocks
            true
        with
          | (σ_P, g',  A, z, _) => pure (σ_P, g', A, z)
  -- The amount to be refunded (82)
  let gStar := g' + min ((T.base.gasLimit - g') / ⟨5⟩) A.refundBalance
  -- EIP-7623 (Prague): the gas used is at least the calldata floor.
  let floor := EVM.calldataFloorGas fork T
  let gStar :=
    if T.base.gasLimit.toNat - gStar.toNat < floor then T.base.gasLimit - .ofNat floor else gStar
  -- The pre-final state (83)
  let σStar :=
    σ_P.increaseBalance S_T (gStar * p)

  let beneficiaryFee := (T.base.gasLimit - gStar) * f
  let σStar' :=
    if beneficiaryFee != UInt256.ofNat 0 then
      σStar.increaseBalance H.beneficiary beneficiaryFee
    else σStar
  let σ' := destroyAccounts fork A σStar' -- (87)
  let deadAccounts := A.touchedAccounts.filter (State.dead σStar' ·)
  let σ' := deadAccounts.foldl Std.ExtTreeMap.erase σ' -- (88)
  let σ' := σ'.map λ _ acc ↦ { acc with tstorage := .empty }
  let gasUsed := (T.base.gasLimit - gStar).toNat
  .ok { σ := σ', A, status := z, gasUsed, executionGasUsed := gasUsed }
end EVM

end Ethereum
