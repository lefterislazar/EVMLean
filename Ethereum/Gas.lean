import Mathlib.Data.Nat.Log

import Ethereum.State
import Ethereum.StateOps
import Ethereum.MachineStateOps
import Ethereum.GasConstants
import Ethereum.StateGas

namespace Ethereum

namespace EVM

/-
Appendix G. Fee Schedule
-/

namespace InstructionGasGroups

def Wzero : List (Operation) := [.STOP, .RETURN, .REVERT]

def Wbase : List (Operation) := [
  .ADDRESS, .ORIGIN, .CALLER, .CALLVALUE, .CALLDATASIZE, .CODESIZE, .GASPRICE, .COINBASE,
  .TIMESTAMP, .NUMBER, .PREVRANDAO, .GASLIMIT, .CHAINID, .RETURNDATASIZE, .POP, .PC, .MSIZE, .GAS,
  .BASEFEE, .BLOBBASEFEE, .SLOTNUM, .PUSH0]

def Wverylow : List (Operation) := [
  .ADD, .SUB, .NOT, .LT, .GT, .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .BYTE, .SHL, .SHR, .SAR,
  .CALLDATALOAD, .MLOAD, .MSTORE, .MSTORE8
  ] ++ pushInstrsWithoutZero
    ++ dupInstrs
    ++ swapInstrs
    -- EIP-8024 (Amsterdam)
    ++ [.DUPN, .SWAPN, .EXCHANGE]
  where
    pushInstrsWithoutZero : List (Operation) := [
      .PUSH1, .PUSH2, .PUSH3, .PUSH4, .PUSH5,
      .PUSH6, .PUSH7, .PUSH8, .PUSH9, .PUSH10,
      .PUSH11, .PUSH12, .PUSH13, .PUSH14, .PUSH15,
      .PUSH16, .PUSH17, .PUSH18, .PUSH19, .PUSH20,
      .PUSH21, .PUSH22, .PUSH23, .PUSH24, .PUSH25,
      .PUSH26, .PUSH27, .PUSH28, .PUSH29, .PUSH30,
      .PUSH31, .PUSH32
    ]
    dupInstrs : List (Operation) := [
      .DUP1, .DUP2, .DUP3, .DUP4, .DUP5,
      .DUP6, .DUP7, .DUP8, .DUP9, .DUP10,
      .DUP11, .DUP12, .DUP13, .DUP14, .DUP15,
      .DUP16
    ]
    swapInstrs : List (Operation) := [
      .SWAP1, .SWAP2, .SWAP3, .SWAP4, .SWAP5,
      .SWAP6, .SWAP7, .SWAP8, .SWAP9, .SWAP10,
      .SWAP11, .SWAP12, .SWAP13, .SWAP14, .SWAP15,
      .SWAP16
    ]

def Wlow : List (Operation) := [
  .MUL, .DIV, .SDIV, .MOD, .SMOD, .SIGNEXTEND, .SELFBALANCE, .CLZ
]

def Wmid : List (Operation) := [
  .ADDMOD, .MULMOD, .JUMP
]

def Whigh : List (Operation) := [
  .JUMPI
]

def Wcopy : List (Operation) := [
  .CALLDATACOPY, .CODECOPY, .RETURNDATACOPY, .MCOPY
]

def Wcall : List (Operation) := [
  .CALL, .CALLCODE, .DELEGATECALL, .STATICCALL
]

def Wextaccount : List (Operation) := [
  .BALANCE, .EXTCODESIZE, .EXTCODEHASH
]

end InstructionGasGroups

section Gas

open GasConstants InstructionGasGroups

/--
(328)
-/
def Cₘ (a : UInt256) : ℕ :=
  let a : ℕ := a.toNat
  Gmemory * a + ((a * a) / QuadraticCeofficient)
  where QuadraticCeofficient : ℕ := 512

/--
NB we currently run in 'this' monad because of the way YP interleaves the definition of `C`
with the definition of `C_<>` functions that are described inline along with their operations.

It would be worth restructing everything to obtain cleaner separation of concerns.
-/
def Csstore (s : State) : ℕ :=
  let { machineState.stack := μₛ, accountMap := σ, σ₀ := σ₀, executionEnv.codeOwner := Iₐ, .. } := s
  let { storage := σ_Iₐ, .. } := σ.get! Iₐ
  let storeAddr := μₛ[0]!
  let v₀ :=
    match σ₀.get? Iₐ with
      | none => ⟨0⟩
      | some acc => acc.storage.getD storeAddr ⟨0⟩
  let v := σ_Iₐ.getD storeAddr ⟨0⟩
  let v' := μₛ[1]!
  let warm := s.substate.accessedStorageKeys.contains (Iₐ, storeAddr)
  if s.executionEnv.fork.spec.eip8038 then
    /- EIP-8038 (Amsterdam): the access, warm or cold, and a write when the
       slot moves away from its value at the start of the transaction. Setting
       a slot from zero costs state gas (EIP-8037), charged by `SSTORE`. -/
    (if warm then Gwarmaccess else Gcoldsload)
      + if v₀ = v ∧ v ≠ v' then GasConstants.Gstoragewrite else 0
  else
  let loadComponent :=
    if warm then
      0
    else
      Gcoldsload
  let storeComponent := if v = v' || v₀ ≠ v             then Gwarmaccess else
                        if v ≠ v' && v₀ = v && v₀ = ⟨0⟩ then Gsset else
                        /- v ≠ v' ∧ v₀ = v ∧ v₀ ≠ 0 -/     Gsreset
  loadComponent + storeComponent

def Ctstore : ℕ :=
  let loadComponent := 0
  let storeComponent := Gwarmaccess
  loadComponent + storeComponent

/-- The cold account access cost, repriced by EIP-8038 (Amsterdam). -/
def Gcoldaccount (fork : Fork) : ℕ :=
  if fork.spec.eip8038 then GasConstants.GcoldaccountaccessAmsterdam else Gcoldaccountaccess

/--
(328)
-/
def Caccess (fork : Fork) (a : AccountAddress) (A : Substate) : ℕ :=
  if A.accessedAccounts.contains a
  then Gwarmaccess
  else Gcoldaccount fork

/--
CHECK -
In YP we have `Cselfdestruct(σ, μ)`; if we were to compute `Aₐ` that we need, we would need an
address in `σ` - is this address supposed to be obvious?
CURRENT SOLUTION -
We take `EVM.State`.
-/
def Cselfdestruct (s : State) : ℕ :=
  let r := AccountAddress.ofUInt256 s.machineState.stack[0]!
  let { substate.accessedAccounts := Aₐ, accountMap := σ, executionEnv.codeOwner := Iₐ, .. } := s
  let fork := s.executionEnv.fork
  let c_cold := if Aₐ.contains r then 0 else Gcoldaccount fork
  /- Moving a balance to a dead account creates it: `Gnewaccount`, until
     EIP-8037 (Amsterdam) charges it in state gas; and from EIP-8038
     (Amsterdam), the write of the account. -/
  let c_new :=
    if State.dead σ r ∧ (σ.get? Iₐ |>.option ⟨0⟩ (·.balance)) ≠ ⟨0⟩ then
      (if fork.spec.eip8037 then 0 else Gnewaccount)
        + if fork.spec.eip8038 then GasConstants.Gaccountwrite else 0
    else 0
  Gselfdestruct + c_cold + c_new

/--
NB Assumes.machineState.stack coherency.
-/
def Csload (μₛ : Stack UInt256) (A : Substate) (I : ExecutionEnv) : ℕ :=
  if A.accessedStorageKeys.contains (I.codeOwner, μₛ[0]!)
  then Gwarmaccess
  else Gcoldsload

def Ctload : ℕ :=
  Gwarmaccess

/--
(331)
-/
def L (n : ℕ) : ℕ := n - (n / 64)

/--
A call that moves value to a dead account creates it: `Gnewaccount`, until
EIP-8037 (Amsterdam) charges it in state gas (`callCreatesAccount`).
-/
def Cnew (fork : Fork) (t : AccountAddress) (val : UInt256) (σ : AccountMap) : ℕ :=
  if fork.spec.eip8037 then 0
  else if Ethereum.State.dead σ t && val != ⟨0⟩ then Gnewaccount else 0

/-- A call that moves value: from EIP-8038 (Amsterdam), the write of the
    recipient's account and the stipend. -/
def Cxfer (fork : Fork) (val : UInt256) : ℕ :=
  if val != ⟨0⟩ then
    if fork.spec.eip8038 then GasConstants.GcallvalueAmsterdam else Gcallvalue
  else 0

/-- EIP-8037 (Amsterdam): a call that moves value to the dead account `t`
    creates it, and is charged `StateGas.NEW_ACCOUNT` in state gas. -/
def callCreatesAccount (fork : Fork) (t : AccountAddress) (val : UInt256) (σ : AccountMap) : Bool :=
  fork.spec.eip8037 && Ethereum.State.dead σ t && val != ⟨0⟩

/--
EIP-8037 (Amsterdam): the execution gas that the state charge of a call that
creates its recipient spends, where the reservoir does not cover it. The call
charges it before it gives gas to the callee, so the callee's gas is capped
from what is left.
-/
def CcallStateSpill (fork : Fork) (t : AccountAddress) (val : UInt256) (σ : AccountMap) (A : Substate) : ℕ :=
  if callCreatesAccount fork t val σ then StateGas.NEW_ACCOUNT - A.stateGasReservoir else 0

/--
EIP-7702 (Prague): the access cost of the delegation target when the callee
`t` holds a delegation designator. The callee itself is accessed first, so a
self-delegation finds its target warm.
-/
def Cdelegation (fork : Fork) (t : AccountAddress) (σ : AccountMap) (A : Substate) : ℕ :=
  if fork.spec.eip7702 then
    match delegationTarget? (σ.get? t |>.option .empty (·.code)) with
    | some target => if target = t then Gwarmaccess else Caccess fork target A
    | none => 0
  else 0

def Cextra (fork : Fork) (t r : AccountAddress) (val : UInt256) (σ : AccountMap) (A : Substate) : ℕ :=
  Caccess fork t A + Cdelegation fork t σ A + Cxfer fork val + Cnew fork r val σ

def Cgascap (fork : Fork) (t r : AccountAddress) (val g : UInt256) (σ : AccountMap) (μ : MachineState) (A : Substate) :=
  let c := Cextra fork t r val σ A + CcallStateSpill fork r val σ A
  if μ.gasAvailable.toNat >= c then
    min (L <| (μ.gasAvailable.subNat c).toNat) g.toNat
  else
    g.toNat

def Ccallgas (fork : Fork) (t r : AccountAddress) (val g : UInt256) (σ : AccountMap) (μ : MachineState) (A : Substate) : ℕ :=
  match val with
    | ⟨0⟩ => Cgascap fork t r val g σ μ A
    | _ => Cgascap fork t r val g σ μ A + GasConstants.Gcallstipend

/--
NB Assumes.machineState.stack coherence.
-/
def Ccall (fork : Fork) (t r : AccountAddress) (val g : UInt256) (σ : AccountMap) (μ : MachineState) (A : Substate) : ℕ :=
  Cgascap fork t r val g σ μ A + Cextra fork t r val σ A

/--
The cost of `CREATE` and `CREATE2` before their init code: from EIP-8037
(Amsterdam), the access and write of the new account (EIP-8038); its creation
is charged in state gas.
-/
def Ccreate (fork : Fork) : ℕ :=
  if fork.spec.eip8037 then GasConstants.Gcreateaccess else Gcreate

/-- EIP-8038 (Amsterdam): `EXTCODESIZE` and `EXTCODECOPY` read the code as
    well as the account. -/
def Ccoderead (fork : Fork) : ℕ :=
  if fork.spec.eip8038 then Gwarmaccess else 0

/--
(65)
-/
def R (x : ℕ) : ℕ := Ginitcodeword * ((x + 31) / 32)

def intrinsicGas (fork : Fork) (T : Transaction) : ℕ :=
  let g₀_data :=
    T.base.data.foldl
      (λ acc b ↦
        acc +
          if b == 0 then
            GasConstants.Gtxdatazero
          else GasConstants.Gtxdatanonzero
      )
      0
  let g₀_create : ℕ :=
    if T.base.recipient == none then
      GasConstants.Gtxcreate + R (T.base.data.size)
    else 0

  let g₀_accessList : ℕ :=
    T.getAccessList.foldl
      (λ acc (_, s) ↦
        acc + GasConstants.Gaccesslistaddress + s.size * GasConstants.Gaccessliststorage
      )
      0
  -- EIP-7702 (Prague): each authorization is charged as a new account.
  let g₀_authorizations : ℕ :=
    if fork.spec.eip7702 then GasConstants.Gnewaccount * T.authorizationList.length else 0
  g₀_data + g₀_create + GasConstants.Gtransaction + g₀_accessList + g₀_authorizations

/--
EIP-7623 (Prague): the minimum gas a transaction is charged, from its calldata
tokens. Zero before Prague, where there is no floor.
-/
def calldataFloorGas (fork : Fork) (T : Transaction) : ℕ :=
  if fork.spec.eip7623 then
    let tokens := T.base.data.foldl (λ acc b ↦ acc + if b == 0 then 1 else 4) 0
    GasConstants.Gtransaction + GasConstants.Gfloorpertoken * tokens
  else 0

/-- The intrinsic cost of a transaction from Amsterdam: the execution gas
    charged before execution, and the floor, the least gas it pays. -/
structure IntrinsicCost where
  execution : ℕ
  floor     : ℕ

/--
The intrinsic cost of `T` from `sender` from Amsterdam: EIP-2780's cost by
the resources the transaction uses, with the parts of EIP-7976, EIP-7981 and
EIP-8038 that the execution specs compute with it (`calculate_intrinsic_cost`).

- The base cost, and the recipient's: a creation accesses and writes a new
  account, a call to another account accesses it and, when value moves, writes
  it, and a self-transfer costs neither. The state gas of a new account is
  charged at the top frame (EIP-8037).
- The calldata, the init code of a creation, the access list (EIP-8038), its
  data surcharge (EIP-7981), and the authorizations.

The floor is the base and recipient cost, 64 gas per calldata byte
(EIP-7976), and the access list surcharge.
-/
def intrinsicCost (T : Transaction) (sender : AccountAddress) : IntrinsicCost :=
  let tokens := T.base.data.foldl (λ acc b ↦ acc + if b == 0 then 1 else 4) 0
  let recipient : ℕ :=
    match T.base.recipient with
    | none => GasConstants.Gcreateaccess
    | some target =>
      if target = sender then 0
      else
        GasConstants.GcoldaccountaccessAmsterdam
          + if T.base.value != ⟨0⟩ then GasConstants.Gtxvalue else 0
  let initCode := if T.base.recipient.isNone then R T.base.data.size else 0
  let accessList :=
    T.getAccessList.foldl
      (λ acc (_, s) ↦
        acc + GasConstants.GaccesslistaddressAmsterdam
          + s.size * GasConstants.GaccessliststorageAmsterdam)
      0
  let accessListTokens :=
    T.getAccessList.foldl
      (λ acc (_, s) ↦
        acc + GasConstants.Gaccesslistaddresstokens
          + s.size * GasConstants.Gaccessliststoragetokens)
      0
  let accessListData := accessListTokens * GasConstants.GfloorpertokenAmsterdam
  let base := GasConstants.GtxbaseAmsterdam + recipient
  { execution :=
      base + initCode + GasConstants.Gtxdatazero * tokens + accessList + accessListData
        + GasConstants.GauthexecutionAmsterdam * T.authorizationList.length
    floor :=
      base + T.base.data.size * 4 * GasConstants.GfloorpertokenAmsterdam + accessListData }

/--
H.1. Gas Cost - the third summand.

NB Stack accesses are assumed guarded here and we access with `!`.
This is for keeping in sync with the way the YP is structures, at least for the time being.
-/
def C' (s : State) (instr : Operation) : ℕ :=
  let { accountMap := σ, substate := A, machineState := μ, executionEnv := I, ..} := s
  let { stack := μₛ, .. } := μ
  match instr with
    | .SSTORE => Csstore s
    | .TSTORE => Ctstore
    | .EXP => let μ₁ := μₛ[1]!; if μ₁ == ⟨0⟩ then Gexp else Gexp + Gexpbyte * (1 + Nat.log 256 μ₁.toNat) -- TODO(check) I think this floors by itself. cf. H.1. YP.
    | .EXTCODECOPY => Caccess I.fork (AccountAddress.ofUInt256 μₛ[0]!) A + Ccoderead I.fork + Gcopy * ((μₛ[3]!.toNat + 31) / 32)
    | .EXTCODESIZE => Caccess I.fork (AccountAddress.ofUInt256 μₛ[0]!) A + Ccoderead I.fork
    | .LOG0 => Glog + Glogdata * μₛ[1]!.toNat
    | .LOG1 => Glog + Glogdata * μₛ[1]!.toNat +     Glogtopic
    | .LOG2 => Glog + Glogdata * μₛ[1]!.toNat + 2 * Glogtopic
    | .LOG3 => Glog + Glogdata * μₛ[1]!.toNat + 3 * Glogtopic
    | .LOG4 => Glog + Glogdata * μₛ[1]!.toNat + 4 * Glogtopic
    | .SELFDESTRUCT => Cselfdestruct s
    | .CREATE => Ccreate I.fork + R μₛ[2]!.toNat
    | .CREATE2 => let μ₂ := μₛ[2]!; Ccreate I.fork + Gkeccak256word * ((μ₂.toNat + 31) / 32) + R μ₂.toNat
    | .KECCAK256 => Gkeccak256 + Gkeccak256word * ((μₛ[1]!.toNat + 31) / 32)
    | .JUMPDEST => Gjumpdest
    | .SLOAD => Csload μₛ A I
    | .TLOAD => Ctload
    | .BLOCKHASH => Gblockhash
    /-
      By `μₛ[2]` the YP means the value that is to be transferred,
      not what happens to be on the stack at index 2. Therefore it is 0 for
      `DELEGATECALL` and `STATICCALL`.
    -/
    | .CALL =>         Ccall I.fork (AccountAddress.ofUInt256 μₛ[1]!) (AccountAddress.ofUInt256 μₛ[1]!) μₛ[2]! μₛ[0]! σ μ A
    | .CALLCODE =>     Ccall I.fork (AccountAddress.ofUInt256 μₛ[1]!)          s.executionEnv.codeOwner μₛ[2]! μₛ[0]! σ μ A
    | .DELEGATECALL => Ccall I.fork (AccountAddress.ofUInt256 μₛ[1]!)          s.executionEnv.codeOwner    ⟨0⟩ μₛ[0]! σ μ A
    | .STATICCALL =>   Ccall I.fork (AccountAddress.ofUInt256 μₛ[1]!) (AccountAddress.ofUInt256 μₛ[1]!)    ⟨0⟩ μₛ[0]! σ μ A
    | .BLOBHASH => HASH_OPCODE_GAS
    | w =>
      if w ∈ Wcopy then Gverylow + Gcopy * ((μₛ[2]!.toNat + 31) / 32) else
      if w ∈ Wextaccount then Caccess I.fork (AccountAddress.ofUInt256 μₛ[0]!) A else
      if w ∈ Wzero then Gzero else
      if w ∈ Wbase then Gbase else
      if w ∈ Wverylow then Gverylow else
      if w ∈ Wlow then Glow else
      if w ∈ Wmid then Gmid else
      if w ∈ Whigh then Ghigh else
      0

/--
H.1. Gas Cost

NB this differs ever so slightly from how it is defined in the YP, please refer to
`EVM/Semantics.lean`, function `X` for further discussion.
-/

def memoryExpansionCost (s : State) (instr : Operation) : ℕ :=
  Cₘ μᵢ' - Cₘ s.machineState.activeWords
 where
  μᵢ' : UInt256 :=
    match instr with
      | .KECCAK256 => .ofNat <| MachineState.M s.machineState.activeWords.toNat s.machineState.stack[0]!.toNat s.machineState.stack[1]!.toNat
      | .CALLDATACOPY | .CODECOPY => .ofNat <| MachineState.M s.machineState.activeWords.toNat s.machineState.stack[0]!.toNat s.machineState.stack[2]!.toNat
      | .MCOPY => .ofNat <| MachineState.M s.machineState.activeWords.toNat (max s.machineState.stack[0]!.toNat s.machineState.stack[1]!.toNat) s.machineState.stack[2]!.toNat
      | .EXTCODECOPY => .ofNat <| MachineState.M s.machineState.activeWords.toNat s.machineState.stack[1]!.toNat s.machineState.stack[3]!.toNat
      | .RETURNDATACOPY => .ofNat <| MachineState.M s.machineState.activeWords.toNat s.machineState.stack[0]!.toNat s.machineState.stack[2]!.toNat
      | .MLOAD | .MSTORE => .ofNat <| MachineState.M s.machineState.activeWords.toNat s.machineState.stack[0]!.toNat 32
      | .MSTORE8 => .ofNat <| MachineState.M s.machineState.activeWords.toNat s.machineState.stack[0]!.toNat 1
      | .LOG0 | .LOG1 | .LOG2 | .LOG3 | .LOG4 =>
        .ofNat <| MachineState.M s.machineState.activeWords.toNat s.machineState.stack[0]!.toNat s.machineState.stack[1]!.toNat
      | .CREATE | .CREATE2 => .ofNat <| MachineState.M s.machineState.activeWords.toNat s.machineState.stack[1]!.toNat s.machineState.stack[2]!.toNat
      | .CALL | .CALLCODE =>
        let m : ℕ := MachineState.M s.machineState.activeWords.toNat s.machineState.stack[3]!.toNat s.machineState.stack[4]!.toNat
        .ofNat <| MachineState.M m s.machineState.stack[5]!.toNat s.machineState.stack[6]!.toNat
      | .DELEGATECALL | .STATICCALL =>
        let m : ℕ:= MachineState.M s.machineState.activeWords.toNat s.machineState.stack[2]!.toNat s.machineState.stack[3]!.toNat
        .ofNat <| MachineState.M m s.machineState.stack[4]!.toNat s.machineState.stack[5]!.toNat
      | .RETURN | .REVERT => .ofNat <| MachineState.M s.machineState.activeWords.toNat s.machineState.stack[0]!.toNat s.machineState.stack[1]!.toNat
      | _ => s.machineState.activeWords

end Gas

end EVM

end Ethereum
