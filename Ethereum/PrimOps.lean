import Ethereum.Data.Stack

import Ethereum.State
import Ethereum.StateOps
import Ethereum.Exception

namespace Ethereum

namespace EVM

def Transformer := State → Except EVM.ExecutionException State

def execUnOp (f : Primop.Unary) : Transformer :=
  λ s ↦
    match s.machineState.stack.pop with
      | some ⟨stack, μ₀⟩ => Id.run do
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀)
      | _ =>
        .error .StackUnderflow

def execBinOp (f : Primop.Binary) : Transformer :=
  λ s ↦
    match s.machineState.stack.pop2 with
      | some ⟨stack, μ₀, μ₁⟩ => Id.run do
        let result := f μ₀ μ₁
        .ok <| s.replaceStackAndIncrPC (stack.push result)
      | _ =>
        .error .StackUnderflow

def execTriOp (f : Primop.Ternary) : Transformer :=
  λ s ↦
    match s.machineState.stack.pop3 with
      | some ⟨stack, μ₀, μ₁, μ₂⟩ => Id.run do
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀ μ₁ μ₂)
      | _ =>
        .error .StackUnderflow

def execQuadOp (f : Primop.Quaternary) : Transformer :=
  λ s ↦
    match s.machineState.stack.pop4 with
      | some ⟨ stack , μ₀ , μ₁ , μ₂, μ₃ ⟩ => Id.run do
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀ μ₁ μ₂ μ₃)
      | _ =>
        .error .StackUnderflow

def executionEnvOp (op : ExecutionEnv → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    let result := op evmState.executionEnv
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.machineState.stack.push result)

def unaryExecutionEnvOp (op : ExecutionEnv → UInt256 → UInt256) : Transformer :=
  λ evmState ↦
    match evmState.machineState.stack.pop with
    | some ⟨ s , μ₀⟩ => Id.run do
      let result := op evmState.executionEnv μ₀
      .ok <|
        evmState.replaceStackAndIncrPC (s.push result)
    | _ => .error .StackUnderflow

def machineStateOp (op : MachineState → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    let result := op evmState.machineState
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.machineState.stack.push result)

def binaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.machineState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ => Id.run do
      let mState' := op evmState.machineState μ₀ μ₁
      let evmState' := {evmState with machineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error .StackUnderflow

def binaryMachineStateOp'
  (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.machineState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ => Id.run do
      let (val, mState') := op evmState.machineState μ₀ μ₁
      let evmState' := {evmState with machineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC (s.push val)
    | _ => .error .StackUnderflow

def ternaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.machineState.stack.pop3 with
    | some ⟨ s , μ₀, μ₁, μ₂ ⟩ => Id.run do
      let mState' := op evmState.machineState μ₀ μ₁ μ₂
      let evmState' := {evmState with machineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error .StackUnderflow

def binaryStateOp
  (op : Ethereum.State → UInt256 → UInt256 → Ethereum.State)
    :
  Transformer
:= λ evmState ↦
  match evmState.machineState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ => Id.run do
      let evmState' := op evmState μ₀ μ₁
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error .StackUnderflow

def stateOp (op : Ethereum.State → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.machineState.stack.push <| op evmState)

def unaryStateOp
  (op : Ethereum.State → UInt256 → Ethereum.State × UInt256)
    :
  Transformer
:= λ evmState ↦
      match evmState.machineState.stack.pop with
        | some ⟨stack' , μ₀ ⟩ => Id.run do
          let (evmState', b) := op evmState μ₀
          .ok <| evmState'.replaceStackAndIncrPC (stack'.push b)
        | _ => .error .StackUnderflow

def ternaryCopyOp
  (op : State → UInt256 → UInt256 → UInt256 → State)
    :
  Transformer
:= λ evmState ↦
  match evmState.machineState.stack.pop3 with
    | some ⟨ stack' , μ₀, μ₁, μ₂⟩ => Id.run do
      let evmState' := op evmState μ₀ μ₁ μ₂
      .ok <| evmState'.replaceStackAndIncrPC stack'
    | _ => .error .StackUnderflow

def quaternaryCopyOp
  (op : State → UInt256 → UInt256 → UInt256 → UInt256 → State)
    :
  Transformer
:=  λ evmState ↦
      match evmState.machineState.stack.pop4 with
        | some ⟨ stack' , μ₀, μ₁, μ₂, μ₃⟩ => Id.run do
          let evmState' := op evmState μ₀ μ₁ μ₂ μ₃
          .ok <| evmState'.replaceStackAndIncrPC stack'
        | _ => .error .StackUnderflow

def evmLogOp (evmState : State) (μ₀ μ₁ : UInt256) (t : Array UInt256) : State :=
  let evmState' := logOp μ₀ μ₁ t evmState
  evmState'

def log0Op : Transformer :=
  λ evmState ↦
    match evmState.machineState.stack.pop2 with
      | some ⟨stack', μ₀, μ₁⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

def log1Op : Transformer :=
  λ evmState ↦
    match evmState.machineState.stack.pop3 with
      | some ⟨stack', μ₀, μ₁, μ₂⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[μ₂]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

def log2Op : Transformer :=
  λ evmState ↦
    match evmState.machineState.stack.pop4 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[μ₂, μ₃]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

def log3Op : Transformer :=
  λ evmState ↦
    match evmState.machineState.stack.pop5 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃, μ₄⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[μ₂, μ₃, μ₄]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

def log4Op : Transformer :=
  λ evmState ↦
    match evmState.machineState.stack.pop6 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃, μ₄, μ₅⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[μ₂, μ₃, μ₄, μ₅]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

end EVM

end Ethereum
