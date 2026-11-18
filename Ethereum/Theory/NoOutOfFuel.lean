import Ethereum.Semantics
import Ethereum.UInt256
import Ethereum.Data.Stack

import Ethereum.Theory.GasLemmas

namespace Ethereum

namespace EVM

set_option maxHeartbeats 2000000 in
lemma Z_no_OutOfFuel {w s} validJumps :
  -- Z validJumps w s = .error e → e ≠ .OutOfFuel := by
  Z validJumps w s ≠ .error .OutOfFuel := by
    intro h
    simp [Z] at h
    cases hd : δ w
    · simp [hd] at h
    · simp [hd] at h
      rename_i val
      by_cases hd' : List.length s.machineState.stack < val
      · simp [hd'] at h
      · simp [hd'] at h
        repeat (split at h <;> try simp at h)

@[simp] private lemma execUnOp_no_OutOfFuel (f : Primop.Unary) (s : State) :
    execUnOp f s ≠ .error .OutOfFuel := by
  unfold execUnOp
  split <;> simp

@[simp] private lemma execBinOp_no_OutOfFuel (f : Primop.Binary) (s : State) :
    execBinOp f s ≠ .error .OutOfFuel := by
  unfold execBinOp
  split <;> simp

@[simp] private lemma execTriOp_no_OutOfFuel (f : Primop.Ternary) (s : State) :
    execTriOp f s ≠ .error .OutOfFuel := by
  unfold execTriOp
  split <;> simp

@[simp] private lemma executionEnvOp_no_OutOfFuel (op : ExecutionEnv → UInt256) (s : State) :
    executionEnvOp op s ≠ .error .OutOfFuel := by
  unfold executionEnvOp
  simp

@[simp] private lemma unaryExecutionEnvOp_no_OutOfFuel
    (op : ExecutionEnv → UInt256 → UInt256) (s : State) :
    unaryExecutionEnvOp op s ≠ .error .OutOfFuel := by
  unfold unaryExecutionEnvOp
  split <;> simp

@[simp] private lemma machineStateOp_no_OutOfFuel (op : MachineState → UInt256) (s : State) :
    machineStateOp op s ≠ .error .OutOfFuel := by
  unfold machineStateOp
  simp

@[simp] private lemma binaryMachineStateOp_no_OutOfFuel
    (op : MachineState → UInt256 → UInt256 → MachineState) (s : State) :
    binaryMachineStateOp op s ≠ .error .OutOfFuel := by
  unfold binaryMachineStateOp
  split <;> simp

@[simp] private lemma binaryMachineStateOp'_no_OutOfFuel
    (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) (s : State) :
    binaryMachineStateOp' op s ≠ .error .OutOfFuel := by
  unfold binaryMachineStateOp'
  split <;> simp

@[simp] private lemma ternaryMachineStateOp_no_OutOfFuel
    (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) (s : State) :
    ternaryMachineStateOp op s ≠ .error .OutOfFuel := by
  unfold ternaryMachineStateOp
  split <;> simp

@[simp] private lemma binaryStateOp_no_OutOfFuel
    (op : State → UInt256 → UInt256 → State) (s : State) :
    binaryStateOp op s ≠ .error .OutOfFuel := by
  unfold binaryStateOp
  split <;> simp

@[simp] private lemma stateOp_no_OutOfFuel (op : State → UInt256) (s : State) :
    stateOp op s ≠ .error .OutOfFuel := by
  unfold stateOp
  simp

@[simp] private lemma unaryStateOp_no_OutOfFuel
    (op : State → UInt256 → State × UInt256) (s : State) :
    unaryStateOp op s ≠ .error .OutOfFuel := by
  unfold unaryStateOp
  split <;> simp

@[simp] private lemma ternaryCopyOp_no_OutOfFuel
    (op : State → UInt256 → UInt256 → UInt256 → State) (s : State) :
    ternaryCopyOp op s ≠ .error .OutOfFuel := by
  unfold ternaryCopyOp
  split <;> simp

@[simp] private lemma quaternaryCopyOp_no_OutOfFuel
    (op : State → UInt256 → UInt256 → UInt256 → UInt256 → State) (s : State) :
    quaternaryCopyOp op s ≠ .error .OutOfFuel := by
  unfold quaternaryCopyOp
  split <;> simp

@[simp] private lemma log0Op_no_OutOfFuel (s : State) :
    log0Op s ≠ .error .OutOfFuel := by
  unfold log0Op
  split <;> simp

@[simp] private lemma log1Op_no_OutOfFuel (s : State) :
    log1Op s ≠ .error .OutOfFuel := by
  unfold log1Op
  split <;> simp

@[simp] private lemma log2Op_no_OutOfFuel (s : State) :
    log2Op s ≠ .error .OutOfFuel := by
  unfold log2Op
  split <;> simp

@[simp] private lemma log3Op_no_OutOfFuel (s : State) :
    log3Op s ≠ .error .OutOfFuel := by
  unfold log3Op
  split <;> simp

@[simp] private lemma log4Op_no_OutOfFuel (s : State) :
    log4Op s ≠ .error .OutOfFuel := by
  unfold log4Op
  split <;> simp

@[simp] private lemma dup_no_OutOfFuel (n : ℕ) (s : State) :
    dup n s ≠ .error .OutOfFuel := by
  simp [dup]
  by_cases h : n ≤ s.machineState.stack.length <;> simp [h]

@[simp] private lemma swap_no_OutOfFuel (n : ℕ) (s : State) :
    swap n s ≠ .error .OutOfFuel := by
  simp [swap]
  by_cases h : n + 1 ≤ s.machineState.stack.length <;> simp [h]

@[simp] private lemma chargeStateGas_no_OutOfFuel (s : State) (amount : ℕ) :
    chargeStateGas s amount ≠ .error .OutOfFuel := by
  unfold chargeStateGas
  split
  · simp
  · split <;> simp

@[simp] private lemma sstoreStateGas_no_OutOfFuel (s : State) :
    sstoreStateGas s ≠ .error .OutOfFuel := by
  unfold sstoreStateGas
  split
  · simp
  · simp only
    split
    · exact chargeStateGas_no_OutOfFuel _ _
    · split <;> simp

@[simp] private lemma callStateCharge_no_OutOfFuel (c : Bool) (gas : ℕ) (A : Substate) :
    callStateCharge c gas A ≠ .error .OutOfFuel := by
  unfold callStateCharge
  split
  · split <;> simp
  · simp

@[simp] private lemma call_no_OutOfFuel
    (gasCost : Nat)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (permission : Bool)
    (evmState : State) :
    call gasCost gas source recipient t value value' inOffset inSize
        outOffset outSize permission evmState ≠ .error .OutOfFuel := by
  intro h
  unfold call at h
  simp only [bind, Except.bind] at h
  split at h
  · rename_i heq; simp at h; subst h; exact callStateCharge_no_OutOfFuel _ _ _ heq
  · simp at h

@[simp] private lemma create_no_OutOfFuel
    (value offset size : UInt256) (salt : Option ByteArray) (evmState : State) :
    create value offset size salt evmState ≠ .error .OutOfFuel := by
  intro h
  unfold create at h
  simp [bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h <;> try simp at h)
  all_goals simp_all

private lemma step_create_no_OutOfFuel {g state arg} :
    step g (.CREATE, arg) state ≠ .error .OutOfFuel := by
  intro h
  simp [step, bind, Except.bind, liftM, monadLift, MonadLift.monadLift] at h
  cases hpop : state.machineState.stack.pop3 <;> simp [hpop, Option.option] at h
  split at h <;> simp_all

private lemma step_create2_no_OutOfFuel {g state arg} :
    step g (.CREATE2, arg) state ≠ .error .OutOfFuel := by
  intro h
  simp [step, bind, Except.bind, liftM, monadLift, MonadLift.monadLift] at h
  cases hpop : state.machineState.stack.pop4 <;> simp [hpop, Option.option] at h
  split at h <;> simp_all

private lemma step_call_no_OutOfFuel {g state arg} :
    step g (.CALL, arg) state ≠ .error .OutOfFuel := by
  intro h
  simp [step, bind, Except.bind, liftM, monadLift, MonadLift.monadLift] at h
  cases hpop : state.machineState.stack.pop7 <;> simp [hpop, Option.option] at h
  split at h <;> simp_all

private lemma step_callcode_no_OutOfFuel {g state arg} :
    step g (.CALLCODE, arg) state ≠ .error .OutOfFuel := by
  intro h
  simp [step, bind, Except.bind, liftM, monadLift, MonadLift.monadLift] at h
  cases hpop : state.machineState.stack.pop7 <;> simp [hpop, Option.option] at h
  split at h <;> simp_all

private lemma step_delegatecall_no_OutOfFuel {g state arg} :
    step g (.DELEGATECALL, arg) state ≠ .error .OutOfFuel := by
  intro h
  simp [step, bind, Except.bind, liftM, monadLift, MonadLift.monadLift] at h
  cases hpop : state.machineState.stack.pop6 <;> simp [hpop, Option.option] at h
  split at h <;> simp_all

private lemma step_staticcall_no_OutOfFuel {g state arg} :
    step g (.STATICCALL, arg) state ≠ .error .OutOfFuel := by
  intro h
  simp [step, bind, Except.bind, liftM, monadLift, MonadLift.monadLift] at h
  cases hpop : state.machineState.stack.pop6 <;> simp [hpop, Option.option] at h
  split at h <;> simp_all

private lemma step_selfdestruct_no_OutOfFuel {g state arg} :
    step g (.SELFDESTRUCT, arg) state ≠ .error .OutOfFuel := by
  intro h
  simp only [step, bind, Except.bind] at h
  split at h
  · rename_i heq; simp at h; subst h; exact chargeStateGas_no_OutOfFuel _ _ heq
  · rename_i s' _
    cases hpop : s'.machineState.stack.pop <;> simp [hpop] at h
    repeat (split at h <;> simp at h)

private lemma step_sstore_no_OutOfFuel {g state arg} :
    step g (.SSTORE, arg) state ≠ .error .OutOfFuel := by
  intro h
  simp only [step, bind, Except.bind] at h
  split at h
  · rename_i heq; simp at h; subst h; exact sstoreStateGas_no_OutOfFuel _ heq
  · simp_all

set_option maxHeartbeats 2000000 in
lemma step_no_OutOfFuel {g state} instr :
  step g instr state ≠ .error .OutOfFuel := by
  rcases instr with ⟨instr, arg⟩
  cases instr with
  | StopArith op =>
      cases op <;> intro h <;> simp [step] at h
  | CompBit op =>
      cases op <;> intro h <;> simp [step] at h <;> split at h <;> simp at h
  | Keccak op =>
      cases op
      intro h
      simp [step] at h
  | Env op =>
      cases op <;> intro h <;>
        simp [step] at h;
        repeat (split at h) <;>
        simp at h
  | Block op =>
      cases op <;> intro h <;> simp [step] at h
      all_goals (split at h <;> simp at h)
  | StackMemFlow op =>
      cases op
      case SSTORE => exact step_sstore_no_OutOfFuel
      all_goals
        intro h
        simp [step] at h <;>
        repeat (split at h) <;>
        simp at h
  | Push op =>
      cases op <;> intro h <;>
        simp [step] at h <;>
        repeat (split at h) <;>
        simp at h
  | Dup op =>
      cases op <;> intro h <;> simp [step] at h
  | Exchange op =>
      cases op <;> intro h <;> simp [step] at h
  | StackAccess op =>
      cases op <;> intro h <;> simp [step, stackAccess, exchange] at h
      all_goals repeat' (split at h <;> try simp at h)
  | Log op =>
      cases op <;> intro h <;> simp [step] at h
  | System op =>
      cases op
      · exact step_create_no_OutOfFuel
      · exact step_call_no_OutOfFuel
      · exact step_callcode_no_OutOfFuel
      · intro h
        simp [step] at h
      · exact step_delegatecall_no_OutOfFuel
      · exact step_create2_no_OutOfFuel
      · exact step_staticcall_no_OutOfFuel
      · intro h
        simp [step] at h
      · intro h
        simp [step] at h
      · exact step_selfdestruct_no_OutOfFuel


lemma Xstep_no_OutOfFuel {state} validJumps :
  Xstep validJumps state ≠ .error .OutOfFuel := by
    simp [Xstep]
    intro hstep
    split at hstep
    · rename_i heq; simp at hstep; rw [hstep] at heq; simp [Z_no_OutOfFuel] at heq
    · split at hstep <;>
      · simp [bind, Except.bind] at hstep
        split at hstep
        · rename_i heq; simp at hstep; simp [hstep] at heq
          apply step_no_OutOfFuel; exact heq
        · repeat (split at hstep <;> try simp at hstep)

/-- `X` never runs out of fuel when given more fuel than the frame's gas
(`frameGas`, its execution gas plus its own state gas spill), which strictly
decreases with every step that continues. `Ξ` gives `X` exactly
`frameGas + 1` of the fresh frame. -/
lemma X_no_OufOfFuel_of_gas_lt_fuel {f s} validJumps
    (hb : s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled) :
  frameGas s < f →
  X f validJumps s ≠ .error .OutOfFuel := by
  intro h
  revert s
  induction f with
  | zero => intro s _ h; simp at h
  | succ f' ih =>
    intro s hb h
    unfold X
    simp [bind, Except.bind]
    split
    · rename_i hstep;
      simp
      have h' : Xstep validJumps s ≠ .error .OutOfFuel := Xstep_no_OutOfFuel validJumps
      simp [hstep] at h'
      assumption
    · rename_i is hstep
      obtain ⟨state', ret⟩ := is
      split
      · rename_i hret
        simp at hret; rw [hret] at hstep
        have := Xstep_gas_decreases_of_continues hb hstep
        have hb' := Xstep_baseline_le hb hstep
        apply ih
        · exact hb'
        · show frameGas state' < f'
          omega
      · simp
      · simp
