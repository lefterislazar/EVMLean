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

import Conform.Wheels

open Ethereum.DebuggingAndProfiling

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
  | _ => 0

def N (pc : UInt256) (instr : Operation) := pc + ⟨1⟩ + .ofNat (argOnNBytesOfInstr instr)

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
    else .some (Ethereum.uInt256OfByteArray (arr.extract' pc.toNat.succ (pc.toNat.succ + argWidth)), argWidth)
  )

def fetchInstr (I : Ethereum.ExecutionEnv) (pc : UInt256) :
               Except EVM.ExecutionException (Operation × Option (UInt256 × Nat)) :=
  decode I.code pc |>.option (.error .StackUnderflow) Except.ok

partial def D_J_aux (c : ByteArray) (i : UInt256) (result : Array UInt256) : Array UInt256 :=
  match c.get? i.toNat >>= Ethereum.EVM.parseInstr with
    | none => result
    | some cᵢ => D_J_aux c (N i cᵢ) (if cᵢ = .JUMPDEST then result.push i else result)

def D_J (c : ByteArray) (i : UInt256) : Array UInt256 :=
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
  let top := s.stack.take n
  if top.length = n then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: s.stack)
  else
    .error .StackUnderflow

def swap (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.stack.take (n + 1)
  let bottom := s.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error .StackUnderflow

local instance : MonadLift Option (Except EVM.ExecutionException) :=
  ⟨Option.option (.error .StackUnderflow) .ok⟩

mutual

def call (fuel : Nat)
  (gasCost : Nat)
  (blobVersionedHashes : List ByteArray)
  (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
  (permission : Bool)
  (evmState : State)
    :
  Except EVM.ExecutionException (UInt256 × State)
:= do
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f =>
      let t : AccountAddress := AccountAddress.ofUInt256 t
      let recipient : AccountAddress := AccountAddress.ofUInt256 recipient
      let source : AccountAddress := AccountAddress.ofUInt256 source
      let Iₐ := evmState.executionEnv.codeOwner
      let σ := evmState.accountMap
      let Iₑ := evmState.executionEnv.depth
      let callgas := Ccallgas t recipient value gas σ evmState.gasAvailable evmState.substate
      let evmState := {evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost}
      -- m[μs[3] . . . (μs[3] + μs[4] − 1)]
      let i := evmState.memory.readWithPadding inOffset.toNat inSize.toNat
      let A' := evmState.addAccessedAccount t |>.substate
      let (cA, σ', g', A', z, o) ← do
        if value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 then
          let resultOfΘ ←
            Θ (fuel := f)
              blobVersionedHashes
              (createdAccounts := evmState.createdAccounts)
              (genesisBlockHeader := evmState.genesisBlockHeader)
              (blocks := evmState.blocks)
              (σ  := σ)                                     -- σ in  Θ(σ, ..)
              (σ₀ := evmState.σ₀)
              (A  := A')                                    -- A* in Θ(.., A*, ..)
              (s  := source)
              (o  := evmState.executionEnv.sender)          -- Iₒ in Θ(.., Iₒ, ..)
              (r  := recipient)                             -- t in Θ(.., t, ..)
              (c  := toExecute σ t)
              (g  := .ofNat callgas)
              (p  := .ofNat evmState.executionEnv.gasPrice) -- Iₚ in Θ(.., Iₚ, ..)
              (v  := value)
              (v' := value')
              (d  := i)
              (e  := Iₑ + 1)
              (H := evmState.executionEnv.header)
              (w  := permission)                            -- I_w in Θ(.., I_W)
          pure resultOfΘ
        else
          -- otherwise (σ, CCALLGAS(σ, μ, A), A, 0, ())
          .ok
            (evmState.createdAccounts, evmState.accountMap, .ofNat callgas, A', false, .empty)
      -- n ≡ min({μs[6], ‖o‖})
      let n : UInt256 := min outSize (.ofNat o.size)

      let μ'ₘ := o.write 0 evmState.memory outOffset.toNat n.toNat -- μ′_m[μs[5]  ... (μs[5] + n − 1)] = o[0 ... (n − 1)]
      let μ'ₒ := o -- μ′o = o
      let μ'_g := evmState.gasAvailable + g' -- Ccall is subtracted in X as part of C

      let codeExecutionFailed   : Bool := !z
      let notEnoughFunds        : Bool := value > (σ.find? evmState.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) -- TODO - Unify condition with CREATE.
      let callDepthLimitReached : Bool := evmState.executionEnv.depth == 1024
      let x : UInt256 := if codeExecutionFailed || notEnoughFunds || callDepthLimitReached then ⟨0⟩ else ⟨1⟩ -- where x = 0 if the code execution for this operation failed, or if μs[2] > σ[Ia]b (not enough funds) or Ie = 1024 (call depth limit reached); x = 1 otherwise.

      let activeWords :=
        let m : ℕ:= MachineState.M evmState.activeWords.toNat inOffset.toNat inSize.toNat
        .ofNat <| MachineState.M m outOffset.toNat outSize.toNat

      let result : State :=
        { evmState with
            accountMap := σ'
            substate := A'
            createdAccounts := cA
            memory := μ'ₘ
            returnData := μ'ₒ
            gasAvailable := μ'_g
            activeWords := activeWords
        }
      .ok (x, result)
termination_by fuel

def step (fuel : ℕ) (gasCost : ℕ) (instr : Option (Operation × Option (UInt256 × Nat)) := .none)
  : EVM.Transformer
:=
  match fuel with
    | 0 => λ _ ↦ .error .OutOfFuel
    | .succ f =>
    λ (evmState : State) ↦ do
    -- This will normally be called from `Ξ` (or `X`) with `fetchInstr` already having been called.
    -- That said, we sometimes want a `step : EVM.Transformer` and as such, we can decode on demand.
    let (instr, arg) ←
      match instr with
        | .none => fetchInstr evmState.executionEnv evmState.pc
        | .some (instr, arg) => pure (instr, arg)
    let evmState := { evmState with execLength := evmState.execLength + 1 }
    let evmStateCharged := {evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost}
    match instr with
      | .CREATE =>
        let evmState := evmStateCharged
        match evmState.stack.pop3 with
          | some ⟨stack, μ₀, μ₁, μ₂⟩ => do
            let i := evmState.memory.readWithPadding μ₁.toNat μ₂.toNat
            let ζ := none
            let I := evmState.executionEnv
            let Iₐ := evmState.executionEnv.codeOwner
            let Iₒ := evmState.executionEnv.sender
            let Iₑ := evmState.executionEnv.depth
            let σ := evmState.accountMap
            let σ_Iₐ : Account := σ.find? Iₐ |>.getD default
            let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}

            let (a, evmState', g', z, o)
                  : (AccountAddress × State × UInt256 × Bool × ByteArray)
              :=
              if σ_Iₐ.nonce.toNat ≥ 2^64-1 then (default, evmState, .ofNat (L evmState.gasAvailable.toNat), False, .empty) else
              if μ₀ ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧ i.size ≤ 49152 then
                let Λ :=
                  Lambda f
                    evmState.executionEnv.blobVersionedHashes
                    evmState.createdAccounts
                    evmState.genesisBlockHeader
                    evmState.blocks
                    σStar
                    evmState.σ₀
                    evmState.substate
                    Iₐ
                    Iₒ
                    (.ofNat <| L evmState.gasAvailable.toNat)
                    (.ofNat I.gasPrice)
                    μ₀
                    i
                    (.ofNat <| Iₑ + 1)
                    ζ
                    I.header
                    I.perm
                match Λ with
                  | .ok (a, cA, σ', g', A', z, o) =>
                    ( a
                    , { evmState with
                          accountMap := σ'
                          substate := A'
                          createdAccounts := cA
                      }
                    , g'
                    , z
                    , o
                    )
                  | _ => (0, {evmState with accountMap := ∅}, ⟨0⟩, False, .empty)
              else
                (0, evmState, .ofNat (L evmState.gasAvailable.toNat), False, .empty)
            let x : UInt256 :=
              let balance := σ.find? Iₐ |>.option ⟨0⟩ (·.balance)
                if z = false ∨ Iₑ = 1024 ∨ μ₀ > balance ∨ i.size > 49152 then ⟨0⟩ else .ofNat a
            let newReturnData : ByteArray := if z then .empty else o
            if (evmState.gasAvailable + g').toNat < L (evmState.gasAvailable.toNat) then
              .error .OutOfGass
            let evmState' :=
              { evmState' with
                  activeWords := .ofNat <| MachineState.M evmState.activeWords.toNat μ₁.toNat μ₂.toNat
                  returnData := newReturnData
                  gasAvailable :=
                    .ofNat <| evmState.gasAvailable.toNat - L (evmState.gasAvailable.toNat) + g'.toNat
              }
            .ok <| evmState'.replaceStackAndIncrPC (stack.push x)
          | _ =>
          .error .StackUnderflow
      | .CREATE2 =>
        -- Exactly equivalent to CREATE except ζ ≡ μₛ[3]
        let evmState := evmStateCharged
        match evmState.stack.pop4 with
          | some ⟨stack, μ₀, μ₁, μ₂, μ₃⟩ => do
            let i := evmState.memory.readWithPadding μ₁.toNat μ₂.toNat
            let ζ := Ethereum.UInt256.toByteArray μ₃
            let I := evmState.executionEnv
            let Iₐ := evmState.executionEnv.codeOwner
            let Iₒ := evmState.executionEnv.sender
            let Iₑ := evmState.executionEnv.depth
            let σ := evmState.accountMap
            let σ_Iₐ : Account := σ.find? Iₐ |>.getD default
            let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}
            let (a, evmState', g', z, o) : (AccountAddress × State × UInt256 × Bool × ByteArray) :=
              if σ_Iₐ.nonce.toNat ≥ 2^64-1 then (default, evmState, .ofNat (L evmState.gasAvailable.toNat), False, .empty) else
              if μ₀ ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧ i.size ≤ 49152 then
                let Λ :=
                  Lambda f
                    evmState.executionEnv.blobVersionedHashes
                    evmState.createdAccounts
                    evmState.genesisBlockHeader
                    evmState.blocks
                    σStar
                    evmState.σ₀
                    evmState.substate
                    Iₐ
                    Iₒ
                    (.ofNat <| L evmState.gasAvailable.toNat)
                    (.ofNat I.gasPrice)
                    μ₀
                    i
                    (.ofNat <| Iₑ + 1)
                    ζ
                    I.header
                    I.perm
                match Λ with
                  | .ok (a, cA, σ', g', A', z, o) =>
                    (a, {evmState with accountMap := σ', substate := A', createdAccounts := cA}, g', z, o)
                  | _ => (0, {evmState with accountMap := ∅}, ⟨0⟩, False, .empty)
              else
                (0, evmState, .ofNat (L evmState.gasAvailable.toNat), False, .empty)
            let x : UInt256 :=
              let balance := σ.find? Iₐ |>.option ⟨0⟩ (·.balance)
                if z = false ∨ Iₑ = 1024 ∨ μ₀ > balance ∨ i.size > 49152 then ⟨0⟩ else .ofNat a
            let newReturnData : ByteArray := if z then .empty else o
            if (evmState.gasAvailable + g').toNat < L evmState.gasAvailable.toNat then
              .error .OutOfGass
            let evmState' :=
              { evmState' with
                activeWords := .ofNat <| MachineState.M evmState.activeWords.toNat μ₁.toNat μ₂.toNat
                returnData := newReturnData
                gasAvailable := .ofNat <| evmState.gasAvailable.toNat - L (evmState.gasAvailable.toNat) + g'.toNat
              }
            .ok <| evmState'.replaceStackAndIncrPC (stack.push x)
          | _ =>
          .error .StackUnderflow
      | .CALL => do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
        let (x, state') ←
          call f gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
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
        let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
        let (x, state') ←
          call f gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
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
        let (stack, μ₀, μ₁, /-μ₂,-/ μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop6
        let (x, state') ←
          call f gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.source) (.ofNat evmState.executionEnv.codeOwner) μ₁ ⟨0⟩ evmState.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
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
        let (stack, μ₀, μ₁, /- μ₂, -/ μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop6
        let (x, state') ←
          call f gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩ μ₃ μ₄ μ₅ μ₆ false evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .STOP =>
          .ok <| setReturnData evmStateCharged .empty
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

      | .KECCAK256 =>
        binaryMachineStateOp' keccak256 evmStateCharged

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
        stateReadOp returndatasize evmStateCharged
      | .RETURNDATACOPY =>
          match evmStateCharged.stack.pop3 with
            | some ⟨stack', μ₀, μ₁, μ₂⟩ => do
              let evmState' := returndatacopy evmStateCharged μ₀ μ₁ μ₂
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
      | .POP =>
        match evmStateCharged.stack.pop with
          | some ⟨ s , _ ⟩ => .ok <| evmStateCharged.replaceStackAndIncrPC s
          | _ => .error .StackUnderflow

      | .MLOAD => 
        match evmStateCharged.stack.pop with
          | some ⟨ s , μ₀ ⟩ => Id.run do
            let (v, evmState') := mload evmStateCharged μ₀
            .ok <| evmState'.replaceStackAndIncrPC (s.push v)
          | _ => .error .StackUnderflow
      | .MSTORE =>
        binaryMachineStateOp mstore evmStateCharged
      | .MSTORE8 => binaryMachineStateOp mstore8 evmStateCharged
      | .SLOAD =>
        unaryStateOp Ethereum.State.sload evmStateCharged
      | .SSTORE =>
        binaryStateOp Ethereum.State.sstore evmStateCharged
      | .TLOAD => unaryStateOp Ethereum.State.tload evmStateCharged
      | .TSTORE => binaryStateOp Ethereum.State.tstore evmStateCharged
      | .MSIZE => stateReadOp msize evmStateCharged
      | .GAS =>
        stateReadOp gas evmStateCharged
      | .MCOPY => ternaryMachineStateOp mcopy evmStateCharged

      | .LOG0 => log0Op evmStateCharged
      | .LOG1 => log1Op evmStateCharged
      | .LOG2 => log2Op evmStateCharged
      | .LOG3 => log3Op evmStateCharged
      | .LOG4 => log4Op evmStateCharged
      | .RETURN => binaryMachineStateOp evmReturn evmStateCharged
      | .REVERT => binaryMachineStateOp evmRevert evmStateCharged
      | .SELFDESTRUCT =>
          match evmStateCharged.stack.pop with
            | some ⟨ s , μ₁ ⟩ =>
              let Iₐ := evmStateCharged.executionEnv.codeOwner
              let r : AccountAddress := AccountAddress.ofUInt256 μ₁
              if evmStateCharged.createdAccounts.contains Iₐ then
                -- When `SELFDESTRUCT` is executed in the same transaction as the contract was created
                let A' : Substate :=
                  { evmStateCharged.substate with
                      selfDestructSet :=
                        evmStateCharged.substate.selfDestructSet.insert Iₐ
                      accessedAccounts :=
                        evmStateCharged.substate.accessedAccounts.insert r
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
            evmStateCharged.replaceStackAndIncrPC (evmStateCharged.stack.push ⟨0⟩)
      | .Push _ => do
          let some (arg, argWidth) := arg | .error .StackUnderflow
          .ok <| evmStateCharged.replaceStackAndIncrPC (evmStateCharged.stack.push arg) (pcΔ := argWidth.succ)
      | .JUMP =>
          match evmStateCharged.stack.pop with
            | some ⟨stack , μ₀⟩ =>
              let newPc := μ₀
              .ok <| {evmStateCharged with pc := newPc, stack := stack}
            | _ => .error .StackUnderflow
      | .JUMPI =>
          match evmStateCharged.stack.pop2 with
            | some ⟨stack , μ₀, μ₁⟩ =>
              let newPc := if μ₁ != ⟨0⟩ then μ₀ else evmStateCharged.pc + ⟨1⟩
              .ok <| {evmStateCharged with pc := newPc, stack := stack}
            | _ => .error .StackUnderflow
      | .PC => 
          .ok <| evmStateCharged.replaceStackAndIncrPC (evmStateCharged.stack.push evmStateCharged.pc)
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
termination_by fuel

/--
  Iterative progression of `step`
-/
def X (fuel : ℕ) (validJumps : Array UInt256) (evmState : State)
  : Except EVM.ExecutionException (ExecutionResult State)
:= do
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f =>
      let I_b := evmState.executionEnv.code
      let instr@(w, _) := decode I_b evmState.pc |>.getD (.STOP, .none)
      -- (159)
      let W (w : Operation) (s : Stack UInt256) : Bool :=
        w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
        (w = .CALL ∧ s[2]? ≠ some ⟨0⟩)
      -- Exceptional halting (158)
      let Z (evmState : State) : Except EVM.ExecutionException (State × ℕ) := do
        if δ w = none then
          .error .InvalidInstruction

        if evmState.stack.length < (δ w).getD 0 then
          .error .StackUnderflow

        let cost₁ := memoryExpansionCost evmState w
        if evmState.gasAvailable.toNat < cost₁ then
          .error .OutOfGass
        let gasAvailable := evmState.gasAvailable - .ofNat cost₁
        let evmState := { evmState with gasAvailable := gasAvailable}
        let cost₂ := C' evmState w

        if evmState.gasAvailable.toNat < cost₂ then
          .error .OutOfGass

        let invalidJump := notIn evmState.stack[0]? validJumps

        if w = .JUMP ∧ invalidJump then
          .error .BadJumpDestination

        if w = .JUMPI ∧ (evmState.stack[1]? ≠ some ⟨0⟩) ∧ invalidJump then
          .error .BadJumpDestination

        if w = .RETURNDATACOPY ∧ (evmState.stack.getD 1 ⟨0⟩).toNat + (evmState.stack.getD 2 ⟨0⟩).toNat > evmState.returnData.size then
          .error .InvalidMemoryAccess

        if evmState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024 then
          .error .StackOverflow

        if (¬ evmState.executionEnv.perm) ∧ W w evmState.stack then
          .error .StaticModeViolation

        if (w = .SSTORE) ∧ evmState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
          .error .OutOfGass

        if
          w.isCreate ∧ evmState.stack.getD 2 ⟨0⟩ > ⟨49152⟩
        then
          .error .OutOfGass

        pure (evmState, cost₂)
      let H (evmState : State) (w : Operation) : Option ByteArray :=
        if w ∈ [.RETURN, .REVERT] then
          some <| evmState.H_return
        else
          if w ∈ [.STOP, .SELFDESTRUCT] then
            some .empty
          else none
      match Z evmState with
        | .error e =>
          .error e
        | some (evmState, cost₂) =>
          let evmState' ← step f cost₂ instr evmState
          -- Maybe we should restructure in a way such that it is more meaningful to compute
          -- gas independently, but the model has not been set up thusly and it seems
          -- that neither really was the YP.
          -- Similarly, we cannot reach a situation in which the stack elements are not available
          -- on the stack because this is guarded above. As such, `C` can be pure here.
          match H evmState' w with -- The YP does this in a weird way.
            | none => X f validJumps evmState'
            | some o =>
              if w == .REVERT then
                /-
                  The Yellow Paper says we don't call the "iterator function" "O" for `REVERT`,
                  but we actually have to call the semantics of `REVERT` to pass the test
                  EthereumTests/BlockchainTests/GeneralStateTests/stReturnDataTest/returndatacopy_after_revert_in_staticcall.json
                  And the EEL spec does so too.
                -/
                .ok <| .revert evmState'.gasAvailable o
              else
                .ok <| .success evmState' o
termination_by fuel
 where
  belongs (o : Option UInt256) (l : Array UInt256) : Bool :=
    match o with
      | none => false
      | some n => l.contains n
  notIn (o : Option UInt256) (l : Array UInt256) : Bool := not (belongs o l)

/--
  The code execution function
-/
def Ξ -- Type `Ξ` using `\GX` or `\Xi`
  (fuel : ℕ)
  (createdAccounts : Batteries.RBSet AccountAddress compare)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (σ : AccountMap)
  (σ₀ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  Except
    EVM.ExecutionException
    (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))
:= do
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f =>
      let defState : State := default
      let freshEvmState : State :=
        { defState with
            accountMap := σ
            σ₀ := σ₀
            executionEnv := I
            substate := A
            createdAccounts := createdAccounts
            gasAvailable := g
            blocks := blocks
            genesisBlockHeader := genesisBlockHeader
        }
      let result ← X f (D_J I.code ⟨0⟩) freshEvmState
      match result with
        | .success evmState' o =>
          let finalGas := evmState'.gasAvailable
          .ok (ExecutionResult.success (evmState'.createdAccounts, evmState'.accountMap, finalGas, evmState'.substate) o)
        | .revert g' o => .ok (ExecutionResult.revert g' o)
termination_by fuel

def Lambda
  (fuel : ℕ)
  (blobVersionedHashes : List ByteArray)
  (createdAccounts : Batteries.RBSet AccountAddress compare) -- needed for EIP-6780
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (σ : AccountMap)
  (σ₀ : AccountMap)
  (A : Substate)
  (s : AccountAddress)   -- sender
  (o : AccountAddress)   -- original transactor
  (g : UInt256)          -- available gas
  (p : UInt256)          -- gas price
  (v : UInt256)          -- endowment
  (i : ByteArray)        -- the initialisation EVM code
  (e : UInt256)          -- depth of the message-call/contract-creation stack
  (ζ : Option ByteArray) -- the salt (92)
  (H : BlockHeader)      -- "I_H has no special treatment and is determined from the blockchain"
  (w : Bool)             -- permission to make modifications to the state
  :
  Except EVM.ExecutionException
    ( AccountAddress
    × Batteries.RBSet AccountAddress compare
    × AccountMap
    × UInt256
    × Substate
    × Bool
    × ByteArray
    )
:=
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f => do

  -- EIP-3860 (includes EIP-170)
  -- https://eips.ethereum.org/EIPS/eip-3860

  let n : UInt256 := (σ.find? s |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩
  let lₐ ← L_A s n ζ i
  let a : AccountAddress := -- (94) (95)
    (ffi.KEC lₐ).extract 12 32 /- 160 bits = 20 bytes -/
      |> fromByteArrayBigEndian |> Fin.ofNat _

  -- A* (97)
  let AStar := A.addAccessedAccount a
  -- σ*
  let existentAccount := σ.findD a default

  /-
    https://eips.ethereum.org/EIPS/eip-7610
    If a contract creation is attempted due to a creation transaction,
    the CREATE opcode, the CREATE2 opcode, or any other reason,
    and the destination address already has either a nonzero nonce,
    a nonzero code length, or non-empty storage, then the creation MUST throw
    as if the first byte in the init code were an invalid opcode.
  -/
  let (i, createdAccounts) :=
    if
      existentAccount.nonce ≠ ⟨0⟩
        || existentAccount.code.size ≠ 0
        || existentAccount.storage != default
    then
      (⟨#[0xfe]⟩, createdAccounts)
    else (i, createdAccounts.insert a)

  let newAccount : Account :=
    { existentAccount with
        nonce := existentAccount.nonce + ⟨1⟩
        balance := v + existentAccount.balance
    }

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let σStar :=
    match σ.find? s with
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
    , depth     := e.toNat
    , perm      := w
    , blobVersionedHashes := blobVersionedHashes
    }
  match Ξ f createdAccounts genesisBlockHeader blocks σStar σ₀ g AStar exEnv with
    | .error e =>
      if e == .OutOfFuel then throw .OutOfFuel
      .ok (a, createdAccounts, σ, ⟨0⟩, AStar, false, .empty)
    | .ok (.revert g' o) =>
      .ok (a, createdAccounts, σ, g', AStar, false, o)
    | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
      -- The code-deposit cost (113)
      let c := GasConstants.Gcodedeposit * returnedData.size

      let F : Bool := Id.run do -- (118)
        let F₀ : Bool :=
          match σ.find? a with
          | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ ⟨0⟩
          | .none => false
        let F₂ : Bool := gStarStar.toNat < c
        let MAX_CODE_SIZE := 24576
        let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
        let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
        pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)

      let σ' : AccountMap := -- (115)
        if F then σ else
          let newAccount' := σStarStar.findD a default
          σStarStar.insert a {newAccount' with code := returnedData}

      -- (114)
      let g' := if F then 0 else gStarStar.toNat - c

      -- (116)
      let A' := if F then AStar else AStarStar
      -- (117)
      let z := not F
      .ok (a, createdAccounts', σ', .ofNat g', A', z, .empty) -- (93)
termination_by fuel
 where
  L_A (s : AccountAddress) (n : UInt256) (ζ : Option ByteArray) (i : ByteArray) :
    Option ByteArray
  := -- (96)
    let s := s.toByteArray
    let n := BE n.toNat
    match ζ with
      | none   => RLP <| .𝕃 [.𝔹 s, .𝔹 n]
      | some ζ => .some <| BE 255 ++ s ++ ζ ++ ffi.KEC i

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

NB - This is implemented using the 'boolean' fragment with ==, <=, ||, etc.
     The 'prop' version will come next once we have the comutable one.
-/
def Θ (fuel : Nat)
      (blobVersionedHashes : List ByteArray)
      (createdAccounts : Batteries.RBSet AccountAddress compare)
      (genesisBlockHeader : BlockHeader)
      (blocks : ProcessedBlocks)
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
      (e  : Nat)
      (H : BlockHeader)
      (w  : Bool)
        :
      Except EVM.ExecutionException (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × Bool × ByteArray)
:=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 => do

  -- (124) (125) (126)
  let σ'₁ :=
    match σ.find? r with
      | none =>
        if v != UInt256.ofNat 0 then
          σ.insert r { (default : Account) with balance := v}
        else
          σ
      | some acc =>
        σ.insert r { acc with balance := acc.balance + v}

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let σ₁ :=
    match σ'₁.find? s with
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
    }

  -- Equation (131)
  -- Note that the `c` used here is the actual code, not the address. TODO - Handle precompiled contracts.
  let (createdAccounts, z, σ'', g', A'', out) ←
    match c with
      | ToExecute.Precompiled p =>
        match p with
          | 1  => .ok <| (∅, Ξ_ECREC σ₁ g A I)
          | 2  => .ok <| (∅, Ξ_SHA256 σ₁ g A I)
          | 3  => .ok <| (∅, Ξ_RIP160 σ₁ g A I)
          | 4  => .ok <| (∅, Ξ_ID σ₁ g A I)
          | 5  => .ok <| (∅, Ξ_EXPMOD σ₁ g A I)
          | 6  => .ok <| (∅, Ξ_BN_ADD σ₁ g A I)
          | 7  => .ok <| (∅, Ξ_BN_MUL σ₁ g A I)
          | 8  => .ok <| (∅, Ξ_SNARKV σ₁ g A I)
          | 9  => .ok <| (∅, Ξ_BLAKE2_F σ₁ g A I)
          | 10 => .ok <| (∅, Ξ_PointEval σ₁ g A I)
          | _ => default
      | ToExecute.Code _ =>
        match Ξ fuel createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I with
          | .error e =>
            if e == .OutOfFuel then throw .OutOfFuel
            pure (createdAccounts, false, σ, ⟨0⟩, A, .empty)
          | .ok (.revert g' o) =>
            pure (createdAccounts, false, σ, g', A, o)
          | .ok (.success (a, b, c, d) o) =>
            pure (a, true, b, c, d, o)

  -- Equation (127)
  let σ' := if σ'' == ∅ then σ else σ''

  -- Equation (129)
  let A' := if σ'' == ∅ then A else A''

  -- Equation (119)
  .ok (createdAccounts, σ', g', A', z, out)
termination_by fuel

end

open Batteries (RBMap RBSet)


-- Type Υ using \Upsilon or \GU
def Υ (fuel : ℕ)
  (σ : AccountMap)
  (H_f : ℕ)
  (H : BlockHeader)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (T : Transaction)
  (S_T : AccountAddress)
  : Except EVM.Exception (AccountMap × Substate × Bool × UInt256)
:= do
  let g₀ : ℕ := EVM.intrinsicGas T
  -- "here can be no invalid transactions from this point"
  let senderAccount := (σ.find? S_T).get!
  -- The priority fee (67)
  let f :=
    match T with
      | .legacy t | .access t =>
            t.gasPrice - .ofNat H_f
      | .dynamic t | .blob t =>
            min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)
  -- The effective gas price
  let p := -- (66)
    match T with
      | .legacy t | .access t => t.gasPrice
      | .dynamic _ | .blob _ => f + .ofNat H_f
  let senderAccount :=
    { senderAccount with
        /-
          https://eips.ethereum.org/EIPS/eip-4844
          "The actual blob_fee as calculated via calc_blob_fee is deducted from
          the sender balance before transaction execution and burned, and is not
          refunded in case of transaction failure."
        -/
        balance := senderAccount.balance - T.base.gasLimit * p - .ofNat (calcBlobFee H T)  -- (74)
        nonce := senderAccount.nonce + ⟨1⟩ -- (75)
    }
  -- The checkpoint state (73)
  let σ₀ := σ.insert S_T senderAccount
  let accessList := T.getAccessList
  let AStar_K : List (AccountAddress × UInt256) := do -- (78)
    let ⟨Eₐ, Eₛ⟩ ← accessList
    let eₛ ← Eₛ.toList
    pure (Eₐ, eₛ)
  let a := -- (80)
    A0.accessedAccounts.insert S_T
      |>.insert H.beneficiary
      |>.union <| Batteries.RBSet.ofList (accessList.map Prod.fst) compare
  -- (81)
  let g := .ofNat <| T.base.gasLimit.toNat - g₀
  let AStarₐ := -- (79)
    match T.base.recipient with
      | some t => a.insert t
      | none => a
  let AStar := -- (77)
    { A0 with accessedAccounts := AStarₐ, accessedStorageKeys := Batteries.RBSet.ofList AStar_K Substate.storageKeysCmp}
  let createdAccounts : Batteries.RBSet AccountAddress compare := .empty
  let (/- provisional state -/ σ_P, g', A, z) ← -- (76)
    match T.base.recipient with
      | none => do
        match
          Lambda fuel
            T.blobVersionedHashes
            createdAccounts
            genesisBlockHeader
            blocks
            σ₀
            σ₀
            AStar
            S_T
            S_T
            g
            p
            T.base.value
            T.base.data
            ⟨0⟩
            none
            H
            true
        with
          | .ok (_, _, σ_P, g', A, z, _) => pure (σ_P, g', A, z)
          | .error e => .error <| .ExecutionException e
      | some t =>
        -- Proposition (71) suggests the recipient can be inexistent
        match
          Θ fuel
            T.blobVersionedHashes
            createdAccounts
            genesisBlockHeader
            blocks
            σ₀
            σ₀
            AStar
            S_T
            S_T
            t
            (toExecute σ₀ t)
            g
            p
            T.base.value
            T.base.value
            T.base.data
            0
            H
            true
        with
          | .ok (_, σ_P, g',  A, z, _) => pure (σ_P, g', A, z)
          | .error e => .error <| .ExecutionException e
  -- The amount to be refunded (82)
  let gStar := g' + min ((T.base.gasLimit - g') / ⟨5⟩) A.refundBalance
  -- The pre-final state (83)
  let σStar :=
    σ_P.increaseBalance S_T (gStar * p)

  let beneficiaryFee := (T.base.gasLimit - gStar) * f
  let σStar' :=
    if beneficiaryFee != UInt256.ofNat 0 then
      σStar.increaseBalance H.beneficiary beneficiaryFee
    else σStar
  let σ' := A.selfDestructSet.1.foldl Batteries.RBMap.erase σStar' -- (87)
  let deadAccounts := A.touchedAccounts.filter (State.dead σStar' ·)
  let σ' := deadAccounts.foldl Batteries.RBMap.erase σ' -- (88)
  let σ' := σ'.map λ (addr, acc) ↦ (addr, { acc with tstorage := .empty})
  .ok (σ', A, z, T.base.gasLimit - gStar)
end EVM

end Ethereum
