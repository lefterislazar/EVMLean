import Ethereum.Semantics
import Ethereum.Theory.StateGasLemmas

namespace Ethereum

namespace State

def subtractGas (self : State) (d : Nat) : State :=
  { self with machineState.gasAvailable := self.machineState.gasAvailable.subNat d }

end State

namespace EVM

variable {fork : Fork}

open GasConstants InstructionGasGroups

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

def ContinuesAfterXStep (w : Operation) : Prop :=
  δ w ≠ none ∧ w ∉ [.STOP, .RETURN, .REVERT, .SELFDESTRUCT]

def RecursiveSystemStep (w : Operation) : Prop :=
  w ∈ ([.CREATE, .CREATE2, .CALL, .CALLCODE, .DELEGATECALL, .STATICCALL] : List Operation)

lemma Caccess_pos (fork a A) : 0 < Caccess fork a A := by
  unfold Caccess Gcoldaccount
  split <;> (try split) <;>
    simp [Gwarmaccess, Gcoldaccountaccess, GasConstants.GcoldaccountaccessAmsterdam]

lemma Cextra_pos (fork t r val σ A) : 0 < Cextra fork t r val σ A := by
  unfold Cextra
  have h := Caccess_pos fork t A
  omega

/-- A call that moves value costs more than the stipend it gives. -/
lemma Gcallstipend_lt_Cxfer (fork : Fork) {val : UInt256} (h : val ≠ ⟨0⟩) :
    Gcallstipend < Cxfer fork val := by
  have hbne : (val != (⟨0⟩ : UInt256)) = true := by simpa [bne] using h
  unfold Cxfer
  simp only [hbne, if_true]
  split <;> simp [Gcallstipend, Gcallvalue, GasConstants.GcallvalueAmsterdam,
    GasConstants.Gaccountwrite]

lemma Ccall_pos (fork t r val g σ μ A) : 0 < Ccall fork t r val g σ μ A := by
  unfold Ccall
  have h := Cextra_pos fork t r val σ A
  omega

lemma Ccallgas_lt_Ccall (fork t r val g σ μ A) :
    Ccallgas fork t r val g σ μ A < Ccall fork t r val g σ μ A := by
  have hpos := Cextra_pos fork t r val σ A
  unfold Ccall Ccallgas
  split
  · omega
  · rename_i hval
    have hne : val ≠ ⟨0⟩ := fun h => hval h
    have hx := Gcallstipend_lt_Cxfer fork hne
    have hle : Cxfer fork val ≤ Cextra fork t r val σ A := by
      unfold Cextra; omega
    omega

lemma L_le_self (n : Nat) : L n ≤ n := by
  unfold L
  omega

lemma option_liftM_eq_some {α : Type} {x : Option α} {y : α}
    (h : (liftM x : Except ExecutionException α) = .ok y) :
    x = some y := by
  cases hx : x with
  | none =>
      simp [hx, liftM, MonadLift.monadLift, MonadLiftT.monadLift, Option.option] at h
  | some z =>
      simp [hx, liftM, MonadLift.monadLift, MonadLiftT.monadLift, Option.option] at h
      exact congrArg some h

lemma Stack.pop7_get! {stack rest : Stack UInt256} {x0 x1 x2 x3 x4 x5 x6 : UInt256}
    (h : stack.pop7 = some (rest, x0, x1, x2, x3, x4, x5, x6)) :
    stack[0]! = x0 ∧ stack[1]! = x1 ∧ stack[2]! = x2 := by
  cases stack with
  | nil => simp [Stack.pop7] at h
  | cons y0 ys0 =>
      cases ys0 with
      | nil => simp [Stack.pop7] at h
      | cons y1 ys1 =>
          cases ys1 with
          | nil => simp [Stack.pop7] at h
          | cons y2 ys2 =>
              cases ys2 with
              | nil => simp [Stack.pop7] at h
              | cons y3 ys3 =>
                  cases ys3 with
                  | nil => simp [Stack.pop7] at h
                  | cons y4 ys4 =>
                      cases ys4 with
                      | nil => simp [Stack.pop7] at h
                      | cons y5 ys5 =>
                          cases ys5 with
                          | nil => simp [Stack.pop7] at h
                          | cons y6 ys6 =>
                              simp [Stack.pop7] at h
                              rcases h with ⟨_, h0, h1, h2, _, _, _, _⟩
                              exact ⟨h0, h1, h2⟩

lemma Stack.pop6_get! {stack rest : Stack UInt256} {x0 x1 x2 x3 x4 x5 : UInt256}
    (h : stack.pop6 = some (rest, x0, x1, x2, x3, x4, x5)) :
    stack[0]! = x0 ∧ stack[1]! = x1 := by
  cases stack with
  | nil => simp [Stack.pop6] at h
  | cons y0 ys0 =>
      cases ys0 with
      | nil => simp [Stack.pop6] at h
      | cons y1 ys1 =>
          cases ys1 with
          | nil => simp [Stack.pop6] at h
          | cons y2 ys2 =>
              cases ys2 with
              | nil => simp [Stack.pop6] at h
              | cons y3 ys3 =>
                  cases ys3 with
                  | nil => simp [Stack.pop6] at h
                  | cons y4 ys4 =>
                      cases ys4 with
                      | nil => simp [Stack.pop6] at h
                      | cons y5 ys5 =>
                          simp [Stack.pop6] at h
                          rcases h with ⟨_, h0, h1, _, _, _, _⟩
                          exact ⟨h0, h1⟩

lemma Csload_pos (μₛ A I) : 0 < Csload μₛ A I := by
  unfold Csload
  split <;> simp [Gwarmaccess, Gcoldsload]

lemma Csstore_storeComponent_pos (v v₀ v' : UInt256) :
    0 < (if v = v' || v₀ ≠ v then Gwarmaccess else
      if v ≠ v' && v₀ = v && v₀ = ⟨0⟩ then Gsset else Gsreset) := by
  by_cases h₁ : v = v' ∨ v₀ ≠ v
  · simp [h₁, Gwarmaccess]
  · by_cases h₂ : (v ≠ v' ∧ v₀ = v) ∧ v₀ = ⟨0⟩
    · simp [h₂]
      split <;> simp [Gsset, Gsreset]
    · simp [h₁, h₂, Gsreset]

lemma Csstore_pos (s : State) : 0 < Csstore s := by
  unfold Csstore
  dsimp only
  split
  · apply Nat.lt_of_lt_of_le _ (Nat.le_add_right _ _)
    split <;> simp [Gwarmaccess, Gcoldsload]
  · exact Nat.lt_of_lt_of_le (Csstore_storeComponent_pos _ _ _) (Nat.le_add_left _ _)

lemma Cselfdestruct_pos (s : State) : 0 < Cselfdestruct s := by
  unfold Cselfdestruct
  simp only [Gselfdestruct]
  omega

set_option maxHeartbeats 800000 in
lemma C'_pos_of_continuesAfterXStep (s : State) {w : Operation}
    (h : ContinuesAfterXStep w) : 0 < C' s w := by
  cases w <;> rename_i a <;> cases a <;>
    simp [ContinuesAfterXStep, δ, C', Wzero, Wbase, Wverylow, Wlow, Wmid, Whigh,
      Wcopy, Wextaccount, Wverylow.pushInstrsWithoutZero, Wverylow.dupInstrs,
      Wverylow.swapInstrs, Caccess_pos, Ccall_pos, Csload_pos, Csstore_pos,
      Ctstore, Ctload, Gjumpdest, Gbase, Gverylow, Glow, Gmid, Ghigh, Gexp,
      Gexpbyte, Gcopy, Glog, Glogdata, Glogtopic, Gcreate, Ccreate, Gkeccak256,
      GasConstants.Gcreateaccess, GasConstants.Gaccountwrite,
      GasConstants.GcoldaccountaccessAmsterdam,
      Gkeccak256word, Gblockhash, HASH_OPCODE_GAS] at h ⊢ <;>
    repeat split
  all_goals
    try unfold GasConstants.Gwarmaccess at h ⊢
    norm_num [GasConstants.Gexp, GasConstants.Gexpbyte, GasConstants.Gwarmaccess,
      Gverylow, Glow, Gmid, Ghigh] at h ⊢

@[simp] lemma State.subtractGas_gasAvailable (self : State) (d : Nat) :
    (self.subtractGas d).machineState.gasAvailable =
      self.machineState.gasAvailable.subNat d := by
  rfl

@[simp] lemma State.subtractGas_gasAvailable_toNat (self : State) (d : Nat) :
    (self.subtractGas d).machineState.gasAvailable.toNat =
      self.machineState.gasAvailable.toNat - d := by
  rfl

lemma State.subtractGas_le_gasAvailable (self : State) (d : Nat) :
    (self.subtractGas d).machineState.gasAvailable.toNat ≤
      self.machineState.gasAvailable.toNat := by
  simp [State.subtractGas]

lemma State.subtractGas_decreases_of_pos_of_le
    (self : State) {d : Nat} (hpos : 0 < d)
    (hle : d ≤ self.machineState.gasAvailable.toNat) :
    (self.subtractGas d).machineState.gasAvailable.toNat + 1 ≤
      self.machineState.gasAvailable.toNat := by
  simp [State.subtractGas]
  omega

lemma gas_sub_refund_decreases {available cost refund : Nat}
    (hrefund : refund < cost)
    (hcost : cost ≤ available) :
    available - (cost - refund) + 1 ≤ available := by
  omega

lemma gas_sub_sub_le (available cost extra : Nat) :
    available - cost - extra ≤ available := by
  omega

lemma gas_sub_sub_decreases {available cost extra : Nat}
    (hpos : 0 < cost) (hle : cost ≤ available) :
    available - cost - extra + 1 ≤ available := by
  omega

@[simp] lemma writeBytes_gasAvailable (source : ByteArray) (sourceAddr : Nat)
    (self : MachineState) (destAddr len : Nat) :
    (writeBytes source sourceAddr self destAddr len).gasAvailable = self.gasAvailable := by
  rfl

@[simp] lemma MachineState.writeWord_gasAvailable
    (self : MachineState) (addr val : UInt256) :
    (self.writeWord addr val).gasAvailable = self.gasAvailable := by
  simp [MachineState.writeWord]

@[simp] lemma MachineState.mload_gasAvailable (self : MachineState) (spos : UInt256) :
    (self.mload spos).2.gasAvailable = self.gasAvailable := by
  simp [MachineState.mload]

@[simp] lemma MachineState.mstore_gasAvailable (self : MachineState) (spos sval : UInt256) :
    (self.mstore spos sval).gasAvailable = self.gasAvailable := by
  simp [MachineState.mstore]

@[simp] lemma MachineState.mstore8_gasAvailable (self : MachineState) (spos sval : UInt256) :
    (self.mstore8 spos sval).gasAvailable = self.gasAvailable := by
  simp [MachineState.mstore8]

@[simp] lemma MachineState.mcopy_gasAvailable
    (self : MachineState) (writeStart readStart size : UInt256) :
    (self.mcopy writeStart readStart size).gasAvailable = self.gasAvailable := by
  simp [MachineState.mcopy]

@[simp] lemma MachineState.returndatacopy_gasAvailable
    (self : MachineState) (mstart rstart size : UInt256) :
    (self.returndatacopy mstart rstart size).gasAvailable = self.gasAvailable := by
  simp [MachineState.returndatacopy]

@[simp] lemma MachineState.evmReturn_gasAvailable
    (self : MachineState) (mstart size : UInt256) :
    (self.evmReturn mstart size).gasAvailable = self.gasAvailable := by
  simp [MachineState.evmReturn]

@[simp] lemma MachineState.evmRevert_gasAvailable
    (self : MachineState) (mstart size : UInt256) :
    (self.evmRevert mstart size).gasAvailable = self.gasAvailable := by
  simp [MachineState.evmRevert]

@[simp] lemma MachineState.keccak256_gasAvailable
    (self : MachineState) (mstart size : UInt256) :
    (self.keccak256 mstart size).2.gasAvailable = self.gasAvailable := by
  simp [MachineState.keccak256]

@[simp] lemma State.addAccessedAccount_gasAvailable (self : State) (addr : AccountAddress) :
    (self.addAccessedAccount addr).machineState.gasAvailable = self.machineState.gasAvailable := by
  simp [Ethereum.State.addAccessedAccount]

@[simp] lemma State.addAccessedStorageKey_gasAvailable
    (self : State) (sk : AccountAddress × UInt256) :
    (self.addAccessedStorageKey sk).machineState.gasAvailable =
      self.machineState.gasAvailable := by
  simp [Ethereum.State.addAccessedStorageKey]

@[simp] lemma State.setAccount_gasAvailable
    (self : State) (addr : AccountAddress) (acc : Account) :
    (self.setAccount addr acc).machineState.gasAvailable = self.machineState.gasAvailable := by
  simp [Ethereum.State.setAccount]

@[simp] lemma State.updateAccount_gasAvailable
    (addr : AccountAddress) (acc : Account) (self : State) :
    (self.updateAccount addr acc).machineState.gasAvailable = self.machineState.gasAvailable := by
  simp [Ethereum.State.updateAccount]

@[simp] lemma State.balance_state_gasAvailable (self : State) (k : UInt256) :
    (self.balance k).1.machineState.gasAvailable = self.machineState.gasAvailable := by
  simp [Ethereum.State.balance]

@[simp] lemma State.extCodeSize_state_gasAvailable (self : State) (a : UInt256) :
    (self.extCodeSize a).1.machineState.gasAvailable = self.machineState.gasAvailable := by
  simp [Ethereum.State.extCodeSize]

@[simp] lemma State.extCodeHash_state_gasAvailable (self : State) (v : UInt256) :
    (self.extCodeHash v).1.machineState.gasAvailable = self.machineState.gasAvailable := by
  unfold Ethereum.State.extCodeHash
  cases hdead : Ethereum.State.dead self.accountMap (AccountAddress.ofUInt256 v) <;>
    simp [hdead]

@[simp] lemma State.sload_state_gasAvailable (self : State) (spos : UInt256) :
    (self.sload spos).1.machineState.gasAvailable = self.machineState.gasAvailable := by
  simp [Ethereum.State.sload]

@[simp] lemma State.sstore_gasAvailable (self : State) (spos sval : UInt256) :
    (self.sstore spos sval).machineState.gasAvailable = self.machineState.gasAvailable := by
  unfold Ethereum.State.sstore
  cases hlookup : self.lookupAccount self.executionEnv.codeOwner <;>
    simp [Option.option, hlookup]

@[simp] lemma State.tload_state_gasAvailable (self : State) (spos : UInt256) :
    (self.tload spos).1.machineState.gasAvailable = self.machineState.gasAvailable := by
  simp [Ethereum.State.tload]

@[simp] lemma State.tstore_gasAvailable (self : State) (spos sval : UInt256) :
    (self.tstore spos sval).machineState.gasAvailable = self.machineState.gasAvailable := by
  unfold Ethereum.State.tstore
  cases hlookup : self.lookupAccount self.executionEnv.codeOwner <;>
    simp [Option.option, hlookup]

@[simp] lemma State.incrPC_gasAvailable (self : State) (pcΔ : Nat := 1) :
    (self.incrPC pcΔ).machineState.gasAvailable = self.machineState.gasAvailable := by
  simp [Ethereum.State.incrPC]

@[simp] lemma State.replaceStackAndIncrPC_gasAvailable
    (self : State) (stack : Stack UInt256) (pcΔ : Nat := 1) :
    (self.replaceStackAndIncrPC stack pcΔ).machineState.gasAvailable =
      self.machineState.gasAvailable := by
  simp [Ethereum.State.replaceStackAndIncrPC]

@[simp] lemma calldatacopy_gasAvailable (self : State) (mstart datastart size : UInt256) :
    (calldatacopy self mstart datastart size).machineState.gasAvailable =
      self.machineState.gasAvailable := by
  simp [calldatacopy]

@[simp] lemma codeCopy_gasAvailable (self : State) (mstart cstart size : UInt256) :
    (codeCopy self mstart cstart size).machineState.gasAvailable =
      self.machineState.gasAvailable := by
  simp [codeCopy]

@[simp] lemma extCodeCopy'_gasAvailable
    (self : State) (acc mstart cstart size : UInt256) :
    (extCodeCopy' self acc mstart cstart size).machineState.gasAvailable =
      self.machineState.gasAvailable := by
  simp [extCodeCopy']

@[simp] lemma logOp_gasAvailable (μ₀ μ₁ : UInt256) (t : Array UInt256) (sState : State) :
    (logOp μ₀ μ₁ t sState).machineState.gasAvailable =
      sState.machineState.gasAvailable := by
  simp [logOp]

@[simp] lemma Substate.addAccessedAccount_stateGasSpilled (A : Substate) (addr : AccountAddress) :
    (A.addAccessedAccount addr).stateGasSpilled = A.stateGasSpilled := by
  simp [Substate.addAccessedAccount]

@[simp] lemma Substate.addAccessedStorageKey_stateGasSpilled
    (A : Substate) (sk : AccountAddress × UInt256) :
    (A.addAccessedStorageKey sk).stateGasSpilled = A.stateGasSpilled := by
  simp [Substate.addAccessedStorageKey]

@[simp] lemma State.addAccessedAccount_stateGasSpilled (self : State) (addr : AccountAddress) :
    (self.addAccessedAccount addr).substate.stateGasSpilled = self.substate.stateGasSpilled := by
  simp [Ethereum.State.addAccessedAccount]


@[simp] lemma State.addAccessedStorageKey_stateGasSpilled
    (self : State) (sk : AccountAddress × UInt256) :
    (self.addAccessedStorageKey sk).substate.stateGasSpilled =
      self.substate.stateGasSpilled := by
  simp [Ethereum.State.addAccessedStorageKey]


@[simp] lemma State.setAccount_stateGasSpilled
    (self : State) (addr : AccountAddress) (acc : Account) :
    (self.setAccount addr acc).substate.stateGasSpilled = self.substate.stateGasSpilled := by
  simp [Ethereum.State.setAccount]


@[simp] lemma State.updateAccount_stateGasSpilled
    (addr : AccountAddress) (acc : Account) (self : State) :
    (self.updateAccount addr acc).substate.stateGasSpilled = self.substate.stateGasSpilled := by
  simp [Ethereum.State.updateAccount]


@[simp] lemma State.balance_state_stateGasSpilled (self : State) (k : UInt256) :
    (self.balance k).1.substate.stateGasSpilled = self.substate.stateGasSpilled := by
  simp [Ethereum.State.balance]


@[simp] lemma State.extCodeSize_state_stateGasSpilled (self : State) (a : UInt256) :
    (self.extCodeSize a).1.substate.stateGasSpilled = self.substate.stateGasSpilled := by
  simp [Ethereum.State.extCodeSize]


@[simp] lemma State.extCodeHash_state_stateGasSpilled (self : State) (v : UInt256) :
    (self.extCodeHash v).1.substate.stateGasSpilled = self.substate.stateGasSpilled := by
  unfold Ethereum.State.extCodeHash
  cases hdead : Ethereum.State.dead self.accountMap (AccountAddress.ofUInt256 v) <;>
    simp [hdead]


@[simp] lemma State.sload_state_stateGasSpilled (self : State) (spos : UInt256) :
    (self.sload spos).1.substate.stateGasSpilled = self.substate.stateGasSpilled := by
  simp [Ethereum.State.sload]


@[simp] lemma State.sstore_stateGasSpilled (self : State) (spos sval : UInt256) :
    (self.sstore spos sval).substate.stateGasSpilled = self.substate.stateGasSpilled := by
  unfold Ethereum.State.sstore
  cases hlookup : self.lookupAccount self.executionEnv.codeOwner <;>
    simp [Option.option, hlookup]


@[simp] lemma State.tload_state_stateGasSpilled (self : State) (spos : UInt256) :
    (self.tload spos).1.substate.stateGasSpilled = self.substate.stateGasSpilled := by
  simp [Ethereum.State.tload]


@[simp] lemma State.tstore_stateGasSpilled (self : State) (spos sval : UInt256) :
    (self.tstore spos sval).substate.stateGasSpilled = self.substate.stateGasSpilled := by
  unfold Ethereum.State.tstore
  cases hlookup : self.lookupAccount self.executionEnv.codeOwner <;>
    simp [Option.option, hlookup]


@[simp] lemma State.incrPC_stateGasSpilled (self : State) (pcΔ : Nat := 1) :
    (self.incrPC pcΔ).substate.stateGasSpilled = self.substate.stateGasSpilled := by
  simp [Ethereum.State.incrPC]


@[simp] lemma State.replaceStackAndIncrPC_stateGasSpilled
    (self : State) (stack : Stack UInt256) (pcΔ : Nat := 1) :
    (self.replaceStackAndIncrPC stack pcΔ).substate.stateGasSpilled =
      self.substate.stateGasSpilled := by
  simp [Ethereum.State.replaceStackAndIncrPC]


@[simp] lemma calldatacopy_stateGasSpilled (self : State) (mstart datastart size : UInt256) :
    (calldatacopy self mstart datastart size).substate.stateGasSpilled =
      self.substate.stateGasSpilled := by
  simp [calldatacopy]


@[simp] lemma codeCopy_stateGasSpilled (self : State) (mstart cstart size : UInt256) :
    (codeCopy self mstart cstart size).substate.stateGasSpilled =
      self.substate.stateGasSpilled := by
  simp [codeCopy]


@[simp] lemma extCodeCopy'_stateGasSpilled
    (self : State) (acc mstart cstart size : UInt256) :
    (extCodeCopy' self acc mstart cstart size).substate.stateGasSpilled =
      self.substate.stateGasSpilled := by
  simp [extCodeCopy']


@[simp] lemma logOp_stateGasSpilled (μ₀ μ₁ : UInt256) (t : Array UInt256) (sState : State) :
    (logOp μ₀ μ₁ t sState).substate.stateGasSpilled =
      sState.substate.stateGasSpilled := by
  simp [logOp]

set_option linter.unusedSimpArgs false in
lemma step_stoparith_gas {gasCost : Nat} {op : Operation.SAOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.StopArith op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, execBinOp, execTriOp,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_stoparith_spill {gasCost : Nat} {op : Operation.SAOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.StopArith op, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, execBinOp, execTriOp,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_compbit_gas {gasCost : Nat} {op : Operation.CBLOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.CompBit op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, execUnOp, execBinOp,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_compbit_spill {gasCost : Nat} {op : Operation.CBLOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.CompBit op, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, execUnOp, execBinOp,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_keccak_gas {gasCost : Nat} {op : Operation.KOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Keccak op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, binaryMachineStateOp',
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      MachineState.keccak256] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_keccak_spill {gasCost : Nat} {op : Operation.KOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Keccak op, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, binaryMachineStateOp',
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      MachineState.keccak256] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_env_gas {gasCost : Nat} {op : Operation.EOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Env op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, executionEnvOp, unaryExecutionEnvOp,
      unaryStateOp, ternaryCopyOp, quaternaryCopyOp, machineStateOp,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      Ethereum.State.balance, Ethereum.State.calldataload, Ethereum.State.extCodeSize,
      Ethereum.State.extCodeHash, calldatacopy, codeCopy, extCodeCopy'] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_env_spill {gasCost : Nat} {op : Operation.EOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Env op, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, executionEnvOp, unaryExecutionEnvOp,
      unaryStateOp, ternaryCopyOp, quaternaryCopyOp, machineStateOp,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      Ethereum.State.balance, Ethereum.State.calldataload, Ethereum.State.extCodeSize,
      Ethereum.State.extCodeHash, calldatacopy, codeCopy, extCodeCopy'] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_block_gas {gasCost : Nat} {op : Operation.BOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Block op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, executionEnvOp, unaryExecutionEnvOp,
      stateOp, unaryStateOp, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      Ethereum.State.blockHash, Ethereum.State.coinBase, Ethereum.State.timeStamp,
      Ethereum.State.number, Ethereum.State.gasLimit, Ethereum.State.chainId,
      Ethereum.State.selfbalance] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_block_spill {gasCost : Nat} {op : Operation.BOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Block op, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, executionEnvOp, unaryExecutionEnvOp,
      stateOp, unaryStateOp, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      Ethereum.State.blockHash, Ethereum.State.coinBase, Ethereum.State.timeStamp,
      Ethereum.State.number, Ethereum.State.gasLimit, Ethereum.State.chainId,
      Ethereum.State.selfbalance] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_stackmemflow_gas {gasCost : Nat} {op : Operation.SMSFOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hop : op ≠ .SSTORE)
    (h : step gasCost (Operation.StackMemFlow op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases op <;> (try exact absurd rfl hop) <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, machineStateOp, binaryMachineStateOp,
      binaryMachineStateOp', ternaryMachineStateOp, binaryStateOp, unaryStateOp,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, MachineState.mload,
      MachineState.mstore, MachineState.mstore8, MachineState.mcopy, MachineState.msize,
      MachineState.gas, MachineState.returndatacopy, Ethereum.State.sload,
      Ethereum.State.tload] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_stackmemflow_spill {gasCost : Nat} {op : Operation.SMSFOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hop : op ≠ .SSTORE)
    (h : step gasCost (Operation.StackMemFlow op, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases op <;> (try exact absurd rfl hop) <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, machineStateOp, binaryMachineStateOp,
      binaryMachineStateOp', ternaryMachineStateOp, binaryStateOp, unaryStateOp,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, MachineState.mload,
      MachineState.mstore, MachineState.mstore8, MachineState.mcopy, MachineState.msize,
      MachineState.gas, MachineState.returndatacopy, Ethereum.State.sload,
      Ethereum.State.tload] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_push_gas {gasCost : Nat} {op : Operation.POp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Push op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_push_spill {gasCost : Nat} {op : Operation.POp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Push op, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_dup_gas {gasCost : Nat} {op : Operation.DOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Dup op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, dup,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_dup_spill {gasCost : Nat} {op : Operation.DOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Dup op, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, dup,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_exchange_gas {gasCost : Nat} {op : Operation.ExOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Exchange op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, swap,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_exchange_spill {gasCost : Nat} {op : Operation.ExOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Exchange op, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, swap,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_stackaccess_gas {gasCost : Nat} {op : Operation.SAccOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.StackAccess op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, stackAccess, exchange,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_stackaccess_spill {gasCost : Nat} {op : Operation.SAccOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.StackAccess op, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, stackAccess, exchange,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_log_gas {gasCost : Nat} {op : Operation.LOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Log op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, log0Op, log1Op, log2Op, log3Op,
      log4Op, evmLogOp, logOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_log_spill {gasCost : Nat} {op : Operation.LOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Log op, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases op <;> rw [step.eq_1] at h <;>
    simp [Id.run, bind, Except.bind, pure, Except.pure, log0Op, log1Op, log2Op, log3Op,
      log4Op, evmLogOp, logOp, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
  all_goals
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_system_nonrecursive_gas {gasCost : Nat} {op : Operation.SOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hop : Operation.System op ∉
      ([Operation.CREATE, Operation.CREATE2, Operation.CALL, Operation.CALLCODE,
        Operation.DELEGATECALL, Operation.STATICCALL, Operation.SELFDESTRUCT] : List Operation))
    (h : step gasCost (Operation.System op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases op <;> first | (exfalso; simpa using hop) | skip
  all_goals
    rw [step.eq_1] at h
    simp [Id.run, bind, Except.bind, pure, Except.pure, binaryMachineStateOp,
      MachineState.evmReturn, MachineState.evmRevert, MachineState.setReturnData,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

set_option linter.unusedSimpArgs false in
lemma step_system_nonrecursive_spill {gasCost : Nat} {op : Operation.SOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hop : Operation.System op ∉
      ([Operation.CREATE, Operation.CREATE2, Operation.CALL, Operation.CALLCODE,
        Operation.DELEGATECALL, Operation.STATICCALL, Operation.SELFDESTRUCT] : List Operation))
    (h : step gasCost (Operation.System op, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases op <;> first | (exfalso; simpa using hop) | skip
  all_goals
    rw [step.eq_1] at h
    simp [Id.run, bind, Except.bind, pure, Except.pure, binaryMachineStateOp,
      MachineState.evmReturn, MachineState.evmRevert, MachineState.setReturnData,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
    repeat split at h
    all_goals try contradiction
    all_goals try (rw [← h]; simp)
    all_goals try (subst s'; rfl)
    all_goals try (injection h with hs; rw [← hs]; simp)
    all_goals try (injection h with hs; subst s'; rfl)

/-!
## The gas of a frame under EIP-8037

From Amsterdam a step can add to the execution gas of its frame: clearing a
slot that the transaction set credits its state gas back, a frame repays its
spill from the reservoir after a successful child, and a reverting child
returns its own spill. What does not grow is the execution gas of a frame
together with its own spill, `frameGas`: every state charge, credit and
repayment moves gas between the two, and every other step only spends.

A call or a creation returns the gas and the spill of its child, so the bound
of a step needs the bound of its children: `ChildGasBound n` is the bound of
the children whose depth is `1024 - n`, and `childGasBound` proves it for
every `n` by induction. The lemmas `..._of_children` take the bound of the
children of the frame as a hypothesis (`ChildrenGasBound`); the lemmas
without the suffix, at the end, do not.
-/

theorem _root_.Ethereum.Sat256.toNat_ofNat_le (n : ℕ) : (Sat256.ofNat n).toNat ≤ n := by
  simp [Sat256.ofNat, Sat256.toNat]

/-- A state charge moves execution gas into the spill. -/
lemma StateGas.charge_spill {gas gas' amount : ℕ} {A A' : Substate}
    (h : StateGas.charge gas A amount = some (gas', A')) :
    gas' + A'.stateGasSpilled = gas + A.stateGasSpilled ∧
      A.stateGasSpilled ≤ A'.stateGasSpilled ∧ gas' ≤ gas := by
  unfold StateGas.charge at h
  split at h
  · cases h; simp
  · dsimp only at h
    split at h
    · cases h; simp; omega
    · cases h

lemma chargeStateGas_gas_spill {s s' : State} {a : ℕ}
    (h : chargeStateGas s a = .ok s') :
    s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled ≤
        s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled ∧
      s.substate.stateGasSpilled ≤ s'.substate.stateGasSpilled := by
  unfold chargeStateGas at h
  split at h
  · cases h; simp
  · split at h
    · cases h
    · rename_i _ g A hc
      cases h
      obtain ⟨h1, h2, _⟩ := StateGas.charge_spill hc
      have := Sat256.toNat_ofNat_le g
      exact ⟨by simp only; omega, h2⟩

/-- The fact that a state-gas operation of a frame keeps: it does not add to
    the frame's execution gas and spill, and keeps the spill above the
    frame's baseline. -/
lemma creditStateGas_gas_spill (s : State) (a : ℕ) :
    (creditStateGas s a).machineState.gasAvailable.toNat +
        (creditStateGas s a).substate.stateGasSpilled ≤
      s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled ∧
    (s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled →
      s.executionEnv.stateGasSpillBaseline ≤ (creditStateGas s a).substate.stateGasSpilled) := by
  unfold creditStateGas StateGas.credit StateGas.ownSpill
  simp only
  have := Sat256.toNat_ofNat_le
    (s.machineState.gasAvailable.toNat +
      min a (s.substate.stateGasSpilled - s.executionEnv.stateGasSpillBaseline))
  constructor
  · omega
  · intro; omega

lemma repayStateGasSpill_gas_spill (s : State) :
    (repayStateGasSpill s).machineState.gasAvailable.toNat +
        (repayStateGasSpill s).substate.stateGasSpilled ≤
      s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled ∧
    (s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled →
      s.executionEnv.stateGasSpillBaseline ≤ (repayStateGasSpill s).substate.stateGasSpilled) := by
  unfold repayStateGasSpill StateGas.repaySpill StateGas.ownSpill
  simp only
  have := Sat256.toNat_ofNat_le
    (s.machineState.gasAvailable.toNat +
      min s.substate.stateGasReservoir
        (s.substate.stateGasSpilled - s.executionEnv.stateGasSpillBaseline))
  constructor
  · omega
  · intro; omega

lemma settleChildStateGas_gas_spill (fork : Fork) (z c : Bool) (s : State) :
    (settleChildStateGas fork z c s).machineState.gasAvailable.toNat +
        (settleChildStateGas fork z c s).substate.stateGasSpilled ≤
      s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled ∧
    (s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled →
      s.executionEnv.stateGasSpillBaseline ≤
        (settleChildStateGas fork z c s).substate.stateGasSpilled) := by
  unfold settleChildStateGas
  split
  · exact repayStateGasSpill_gas_spill s
  · split
    · exact creditStateGas_gas_spill s _
    · exact ⟨le_refl _, id⟩

lemma sstoreStateGas_gas_spill {s s' : State}
    (h : sstoreStateGas s = .ok s') :
    s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled ≤
        s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled ∧
    (s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled →
      s.executionEnv.stateGasSpillBaseline ≤ s'.substate.stateGasSpilled) := by
  unfold sstoreStateGas at h
  split at h
  · cases h; exact ⟨le_refl _, id⟩
  · dsimp only at h
    split at h
    · have := chargeStateGas_gas_spill h
      exact ⟨this.1, fun hb => le_trans hb this.2⟩
    · split at h
      · cases h; exact creditStateGas_gas_spill s _
      · cases h; exact ⟨le_refl _, id⟩

lemma settleChildStateGas_bound {fork : Fork} {z c : Bool} {S : State} {b B : ℕ}
    (hb : S.executionEnv.stateGasSpillBaseline = b)
    (h1 : b ≤ S.substate.stateGasSpilled)
    (h2 : S.machineState.gasAvailable.toNat + S.substate.stateGasSpilled ≤ B) :
    b ≤ (settleChildStateGas fork z c S).substate.stateGasSpilled ∧
      (settleChildStateGas fork z c S).machineState.gasAvailable.toNat +
          (settleChildStateGas fork z c S).substate.stateGasSpilled ≤ B := by
  subst hb
  obtain ⟨hs1, hs2⟩ := settleChildStateGas_gas_spill fork z c S
  exact ⟨hs2 h1, le_trans hs1 h2⟩

/-- A call's state charge spills `spill`, at most the gas it is given. -/
lemma callStateCharge_spill {c : Bool} {gas spill : ℕ} {A A' : Substate}
    (h : callStateCharge c gas A = .ok (spill, A')) :
    A'.stateGasSpilled = A.stateGasSpilled + spill ∧ spill ≤ gas := by
  unfold callStateCharge at h
  split at h
  · split at h
    · cases h
    · rename_i g A₁ hc
      cases h
      obtain ⟨h1, _, h3⟩ := StateGas.charge_spill hc
      omega
  · cases h; simp

@[simp] lemma callSubstate_stateGasSpilled (fork : Fork) (σ : AccountMap) (t : AccountAddress)
    (A : Substate) : (callSubstate fork σ t A).stateGasSpilled = A.stateGasSpilled := by
  unfold callSubstate
  split
  · split <;> simp
  · simp

lemma topFrameCallCharges_spill {σ : AccountMap} {A A' : Substate} {gas gas' : ℕ}
    {r : AccountAddress} {v : UInt256}
    (h : topFrameCallCharges σ A gas r v = some (gas', A')) :
    gas' + A'.stateGasSpilled ≤ gas + A.stateGasSpilled ∧
      A.stateGasSpilled ≤ A'.stateGasSpilled := by
  unfold topFrameCallCharges at h
  simp only [bind, Option.bind] at h
  split at h
  · split at h
    · cases h
    · rename_i p hc
      rcases p with ⟨g₁, A₁⟩
      obtain ⟨h1, h2, _⟩ := StateGas.charge_spill hc
      dsimp only at h
      split at h
      · split_ifs at h <;>
          simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
          obtain ⟨rfl, rfl⟩ := h <;> simp <;> omega
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        omega
  · split at h
    · split_ifs at h <;>
        simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
        obtain ⟨rfl, rfl⟩ := h <;> simp <;> omega
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      omega


/-- The gas bound of a child frame at the depth whose distance to the depth
    limit is `n` (`1024 - e.val = n`), a message call (`Θ`) or a contract
    creation (`Lambda`): it does not lower the spill of the substate it is
    given, and the gas it returns and its spill are at most the gas and the
    spill it was given. -/
def ChildGasBound (n : ℕ) : Prop :=
  (∀ (fork : Fork) (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress) (c : ToExecute)
      (g p v v' : UInt256) (d : ByteArray) (e : Fin 1025) (H : BlockHeader)
      (blobVersionedHashes : List ByteArray) (blocks : ProcessedBlocks) (w : Bool),
    1024 - e.val = n →
    let res := Θ fork σ σ₀ A s o r c g p v v' d e H blobVersionedHashes blocks w
    A.stateGasSpilled ≤ res.2.2.1.stateGasSpilled ∧
      res.2.1.toNat + res.2.2.1.stateGasSpilled ≤ g.toNat + A.stateGasSpilled) ∧
  (∀ (fork : Fork) (σ σ₀ : AccountMap) (A : Substate) (s o : AccountAddress)
      (g p v : UInt256) (i : ByteArray) (e : Fin 1025) (ζ : Option ByteArray) (H : BlockHeader)
      (blobVersionedHashes : List ByteArray) (blocks : ProcessedBlocks) (w : Bool),
    1024 - e.val = n →
    let res := Lambda fork σ σ₀ A s o g p v i e ζ H blobVersionedHashes blocks w
    A.stateGasSpilled ≤ res.2.2.2.1.stateGasSpilled ∧
      res.2.2.1.toNat + res.2.2.2.1.stateGasSpilled ≤ g.toNat + A.stateGasSpilled)

/-- The gas bound of every child of a frame at depth `d`. -/
def ChildrenGasBound (d : ℕ) : Prop := ∀ n, n < 1024 - d → ChildGasBound n

lemma ChildrenGasBound.theta {d : ℕ} (hchild : ChildrenGasBound d)
    {fork : Fork} {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress} {c : ToExecute}
    {g p v v' : UInt256} {dd : ByteArray} {e : Fin 1025} {H : BlockHeader}
    {blobVersionedHashes : List ByteArray} {blocks : ProcessedBlocks} {w : Bool}
    {R : AccountMap × UInt256 × Substate × Bool × ByteArray}
    (he : d < e.val)
    (hR : Θ fork σ σ₀ A s o r c g p v v' dd e H blobVersionedHashes blocks w = R) :
    A.stateGasSpilled ≤ R.2.2.1.stateGasSpilled ∧
      R.2.1.toNat + R.2.2.1.stateGasSpilled ≤ g.toNat + A.stateGasSpilled := by
  subst hR
  exact (hchild (1024 - e.val) (by omega)).1 fork σ σ₀ A s o r c g p v v' dd e H
    blobVersionedHashes blocks w rfl

lemma ChildrenGasBound.lambda {d : ℕ} (hchild : ChildrenGasBound d)
    {fork : Fork} {σ σ₀ : AccountMap} {A : Substate} {s o : AccountAddress}
    {g p v : UInt256} {i : ByteArray} {e : Fin 1025} {ζ : Option ByteArray} {H : BlockHeader}
    {blobVersionedHashes : List ByteArray} {blocks : ProcessedBlocks} {w : Bool}
    {R : AccountAddress × AccountMap × UInt256 × Substate × Bool × ByteArray}
    (he : d < e.val)
    (hR : Lambda fork σ σ₀ A s o g p v i e ζ H blobVersionedHashes blocks w = R) :
    A.stateGasSpilled ≤ R.2.2.2.1.stateGasSpilled ∧
      R.2.2.1.toNat + R.2.2.2.1.stateGasSpilled ≤ g.toNat + A.stateGasSpilled := by
  subst hR
  exact (hchild (1024 - e.val) (by omega)).2 fork σ σ₀ A s o g p v i e ζ H
    blobVersionedHashes blocks w rfl

lemma call_gas_spill {gasCost : Nat}
    {gas source recipient t value value' inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {evmState state' : State} {x : UInt256}
    (hb : evmState.executionEnv.stateGasSpillBaseline ≤ evmState.substate.stateGasSpilled)
    (hchild : ChildrenGasBound evmState.executionEnv.depth.val)
    (h : call gasCost gas source recipient t value value'
      inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    evmState.executionEnv.stateGasSpillBaseline ≤ state'.substate.stateGasSpilled ∧
      state'.machineState.gasAvailable.toNat + state'.substate.stateGasSpilled ≤
        evmState.machineState.gasAvailable.toNat - gasCost +
          Ccallgas evmState.executionEnv.fork (AccountAddress.ofUInt256 t)
            (AccountAddress.ofUInt256 recipient) value gas evmState.accountMap
            evmState.machineState evmState.substate +
          evmState.substate.stateGasSpilled := by
  unfold call at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hcs
    rcases p with ⟨spill, A₀⟩
    obtain ⟨hA₀, hspill⟩ := callStateCharge_spill hcs
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    generalize hR : (if value ≤ (evmState.accountMap.get? evmState.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
          evmState.executionEnv.depth < 1024 then
        Θ evmState.executionEnv.fork evmState.accountMap evmState.σ₀
          (callSubstate evmState.executionEnv.fork evmState.accountMap (AccountAddress.ofUInt256 t) A₀)
          (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
          (AccountAddress.ofUInt256 recipient)
          (toExecute evmState.executionEnv.fork evmState.accountMap (AccountAddress.ofUInt256 t))
          (UInt256.ofNat (Ccallgas evmState.executionEnv.fork (AccountAddress.ofUInt256 t)
            (AccountAddress.ofUInt256 recipient) value gas evmState.accountMap
            evmState.machineState evmState.substate))
          (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
          (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evmState.executionEnv.depth + 1) evmState.executionEnv.header
          evmState.executionEnv.blobVersionedHashes evmState.executionEnv.blocks permission
      else
        (evmState.accountMap,
          UInt256.ofNat (Ccallgas evmState.executionEnv.fork (AccountAddress.ofUInt256 t)
            (AccountAddress.ofUInt256 recipient) value gas evmState.accountMap
            evmState.machineState evmState.substate),
          callSubstate evmState.executionEnv.fork evmState.accountMap (AccountAddress.ofUInt256 t) A₀,
          false, ByteArray.empty)) = R at *
    have hRb : A₀.stateGasSpilled ≤ R.2.2.1.stateGasSpilled ∧
        R.2.1.toNat + R.2.2.1.stateGasSpilled ≤
          Ccallgas evmState.executionEnv.fork (AccountAddress.ofUInt256 t)
            (AccountAddress.ofUInt256 recipient) value gas evmState.accountMap
            evmState.machineState evmState.substate + A₀.stateGasSpilled := by
      split at hR
      · rename_i hcond
        have he : evmState.executionEnv.depth.val < (evmState.executionEnv.depth + 1).val := by
          have := hcond.2
          rw [Fin.val_add]
          simp only [Fin.lt_def] at this
          simp
          omega
        have := hchild.theta he hR
        simp only [callSubstate_stateGasSpilled] at this
        have := UInt256.toNat_ofNat_le (Ccallgas evmState.executionEnv.fork (AccountAddress.ofUInt256 t)
            (AccountAddress.ofUInt256 recipient) value gas evmState.accountMap
            evmState.machineState evmState.substate)
        omega
      · subst hR
        simp only [callSubstate_stateGasSpilled]
        have := UInt256.toNat_ofNat_le (Ccallgas evmState.executionEnv.fork (AccountAddress.ofUInt256 t)
            (AccountAddress.ofUInt256 recipient) value gas evmState.accountMap
            evmState.machineState evmState.substate)
        omega
    clear hR
    rcases R with ⟨σR, gR, AR, zR, oR⟩
    dsimp only at hRb
    refine settleChildStateGas_bound rfl ?_ ?_
    · dsimp only; omega
    · dsimp only; simp only [Sat256.subNat_toNat]; omega

lemma create_gas_spill
    {value offset size : UInt256} {salt : Option ByteArray}
    {evmState state' : State} {x : UInt256}
    (hb : evmState.executionEnv.stateGasSpillBaseline ≤ evmState.substate.stateGasSpilled)
    (hchild : ChildrenGasBound evmState.executionEnv.depth.val)
    (h : create value offset size salt evmState = .ok (x, state')) :
    evmState.executionEnv.stateGasSpillBaseline ≤ state'.substate.stateGasSpilled ∧
      state'.machineState.gasAvailable.toNat + state'.substate.stateGasSpilled ≤
        evmState.machineState.gasAvailable.toNat + evmState.substate.stateGasSpilled := by
  unfold create at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i S1 hS1
    obtain ⟨hc1, hc2⟩ := chargeStateGas_gas_spill hS1
    have hE := (chargeStateGas_sameButGas hS1).executionEnv
    have hL := L_le_self S1.machineState.gasAvailable.toNat
    have hL' := UInt256.toNat_ofNat_le (L S1.machineState.gasAvailable.toNat)
    split at h
    · split at h
      · cases h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine settleChildStateGas_bound ?_ ?_ ?_
        · dsimp only; rw [hE]
        · dsimp only; omega
        · dsimp only; simp only [Sat256.subNat_toNat]; omega
    · split at h
      · rename_i hd
        generalize hR : Lambda _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = R at h
        have hRb := hchild.lambda (by dsimp only; omega) hR
        clear hR
        rcases R with ⟨a, σR, gR, AR, zR, oR⟩
        dsimp only at hRb h
        split at h
        · cases h
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          refine settleChildStateGas_bound ?_ ?_ ?_
          · dsimp only; rw [hE]
          · dsimp only; omega
          · dsimp only; simp only [Sat256.subNat_toNat]; omega
      · split at h
        · cases h
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          refine settleChildStateGas_bound ?_ ?_ ?_
          · dsimp only; rw [hE]
          · dsimp only; omega
          · dsimp only; simp only [Sat256.subNat_toNat]; omega

lemma step_sstore_gas_spill {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.SSTORE, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled ≤
        s.machineState.gasAvailable.toNat - gasCost + s.substate.stateGasSpilled ∧
      (s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled →
        s.executionEnv.stateGasSpillBaseline ≤ s'.substate.stateGasSpilled) := by
  rw [step.eq_1] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i s1 hs1
    obtain ⟨h1, h2⟩ := sstoreStateGas_gas_spill hs1
    unfold binaryStateOp at h
    split at h
    · simp only [Id.run, Except.ok.injEq] at h
      subst h
      simp only [State.replaceStackAndIncrPC_gasAvailable, State.sstore_gasAvailable,
        State.replaceStackAndIncrPC_stateGasSpilled, State.sstore_stateGasSpilled]
      simp only [Sat256.subNat_toNat] at h1 h2
      exact ⟨h1, h2⟩
    · cases h

lemma step_selfdestruct_gas_spill {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.SELFDESTRUCT, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled ≤
        s.machineState.gasAvailable.toNat - gasCost + s.substate.stateGasSpilled ∧
      s.substate.stateGasSpilled ≤ s'.substate.stateGasSpilled := by
  rw [step.eq_1] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i s1 hs1
    obtain ⟨h1, h2⟩ := chargeStateGas_gas_spill hs1
    simp only [Sat256.subNat_toNat] at h1 h2
    split at h
    · split at h
      · simp only [Except.ok.injEq] at h
        subst h
        simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
        exact ⟨h1, h2⟩
      · simp only [Except.ok.injEq] at h
        subst h
        simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
        exact ⟨h1, h2⟩
    · cases h

lemma step_nonrecursive_gas {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hnrec : ¬ RecursiveSystemStep w) (hsstore : w ≠ .SSTORE) (hsd : w ≠ .SELFDESTRUCT)
    (h : step gasCost (w, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.subNat gasCost := by
  cases w with
  | StopArith op => exact step_stoparith_gas h
  | CompBit op => exact step_compbit_gas h
  | Keccak op => exact step_keccak_gas h
  | Env op => exact step_env_gas h
  | Block op => exact step_block_gas h
  | StackMemFlow op => exact step_stackmemflow_gas (fun hop => hsstore (by rw [hop])) h
  | Push op => exact step_push_gas h
  | Dup op => exact step_dup_gas h
  | Exchange op => exact step_exchange_gas h
  | StackAccess op => exact step_stackaccess_gas h
  | Log op => exact step_log_gas h
  | System op =>
      refine step_system_nonrecursive_gas ?_ h
      cases op <;> simp_all [RecursiveSystemStep]

lemma step_nonrecursive_spill {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hnrec : ¬ RecursiveSystemStep w) (hsstore : w ≠ .SSTORE) (hsd : w ≠ .SELFDESTRUCT)
    (h : step gasCost (w, arg) s = .ok s') :
    s'.substate.stateGasSpilled = s.substate.stateGasSpilled := by
  cases w with
  | StopArith op => exact step_stoparith_spill h
  | CompBit op => exact step_compbit_spill h
  | Keccak op => exact step_keccak_spill h
  | Env op => exact step_env_spill h
  | Block op => exact step_block_spill h
  | StackMemFlow op => exact step_stackmemflow_spill (fun hop => hsstore (by rw [hop])) h
  | Push op => exact step_push_spill h
  | Dup op => exact step_dup_spill h
  | Exchange op => exact step_exchange_spill h
  | StackAccess op => exact step_stackaccess_spill h
  | Log op => exact step_log_spill h
  | System op =>
      refine step_system_nonrecursive_spill ?_ h
      cases op <;> simp_all [RecursiveSystemStep]

set_option linter.unusedSimpArgs false in
lemma step_create_gas_spill {gasCost : Nat} {w : Operation} {arg : Option (UInt256 × Nat)}
    {s s' : State}
    (hw : w = .CREATE ∨ w = .CREATE2)
    (hb : s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled)
    (hchild : ChildrenGasBound s.executionEnv.depth.val)
    (h : step gasCost (w, arg) s = .ok s') :
    s.executionEnv.stateGasSpillBaseline ≤ s'.substate.stateGasSpilled ∧
      s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled ≤
        s.machineState.gasAvailable.toNat - gasCost + s.substate.stateGasSpilled := by
  rcases hw with rfl | rfl
  all_goals
    rw [step.eq_1] at h
    simp [bind, Except.bind, pure, Except.pure,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
    repeat (first | simp at h | split at h)
    rename_i _ _ _ _ vCreate hCreate
    rcases vCreate with ⟨_, _⟩
    have hout := create_gas_spill (by simpa using hb) (by simpa using hchild) hCreate
    rw [← h]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at hout ⊢
    exact hout

/-- A step that is not a call: it charges `gasCost`, and its state gas moves
    gas between the execution gas and the spill, keeping the spill above the
    frame's baseline. -/
lemma step_noncall_gas_spill {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hb : s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled)
    (hchild : ChildrenGasBound s.executionEnv.depth.val)
    (hcall : w ∉ ([.CALL, .CALLCODE, .DELEGATECALL, .STATICCALL] : List Operation))
    (h : step gasCost (w, arg) s = .ok s') :
    s.executionEnv.stateGasSpillBaseline ≤ s'.substate.stateGasSpilled ∧
      s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled ≤
        s.machineState.gasAvailable.toNat - gasCost + s.substate.stateGasSpilled := by
  by_cases hsstore : w = .SSTORE
  · subst hsstore
    obtain ⟨h1, h2⟩ := step_sstore_gas_spill h
    exact ⟨h2 hb, h1⟩
  by_cases hsd : w = .SELFDESTRUCT
  · subst hsd
    obtain ⟨h1, h2⟩ := step_selfdestruct_gas_spill h
    exact ⟨le_trans hb h2, h1⟩
  by_cases hcreate : w = .CREATE ∨ w = .CREATE2
  · exact step_create_gas_spill hcreate hb hchild h
  have hnrec : ¬ RecursiveSystemStep w := by
    simp only [RecursiveSystemStep, List.mem_cons, List.not_mem_nil] at hcall ⊢
    tauto
  have hg := step_nonrecursive_gas hnrec hsstore hsd h
  have hsp := step_nonrecursive_spill hnrec hsstore hsd h
  rw [hg, hsp, Sat256.subNat_toNat]
  exact ⟨hb, le_refl _⟩

lemma call_gas_spill_decreases {gasCost : Nat}
    {gas source recipient t value value' inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {evmState state' : State} {x : UInt256}
    (hb : evmState.executionEnv.stateGasSpillBaseline ≤ evmState.substate.stateGasSpilled)
    (hchild : ChildrenGasBound evmState.executionEnv.depth.val)
    (hgasCost : gasCost ≤ evmState.machineState.gasAvailable.toNat)
    (hcallgasLt :
      Ccallgas evmState.executionEnv.fork (AccountAddress.ofUInt256 t)
        (AccountAddress.ofUInt256 recipient) value gas evmState.accountMap
        evmState.machineState evmState.substate < gasCost)
    (h : call gasCost gas source recipient t value value'
      inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    evmState.executionEnv.stateGasSpillBaseline ≤ state'.substate.stateGasSpilled ∧
      state'.machineState.gasAvailable.toNat + state'.substate.stateGasSpilled + 1 ≤
        evmState.machineState.gasAvailable.toNat + evmState.substate.stateGasSpilled := by
  have := call_gas_spill hb hchild h
  exact ⟨this.1, by omega⟩

set_option linter.unusedSimpArgs false in
lemma step_CALL_gas_spill {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (hb : s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled)
    (hchild : ChildrenGasBound s.executionEnv.depth.val)
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s .CALL)
    (h : step gasCost (.CALL, arg) s = .ok s') :
    s.executionEnv.stateGasSpillBaseline ≤ s'.substate.stateGasSpilled ∧
      s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled + 1 ≤
        s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ vPop hPop _ vCall hCall
  rcases vCall with ⟨xCall, stateCall⟩
  let sExec : State := { s with
    machineState.execLength := s.machineState.execLength + 1 }
  have hPop' : s.machineState.stack.pop7 = some vPop := by
    exact option_liftM_eq_some hPop
  have hidx := Stack.pop7_get! hPop'
  rcases hidx with ⟨h0, h1, h2⟩
  have hcallgasLt :
      Ccallgas s.executionEnv.fork (AccountAddress.ofUInt256 vPop.2.2.1)
        (AccountAddress.ofUInt256 vPop.2.2.1) vPop.2.2.2.1 vPop.2.1
        sExec.accountMap sExec.machineState sExec.substate < gasCost := by
    have hbase :
        Ccallgas s.executionEnv.fork (AccountAddress.ofUInt256 vPop.2.2.1)
          (AccountAddress.ofUInt256 vPop.2.2.1) vPop.2.2.2.1 vPop.2.1
          s.accountMap s.machineState s.substate <
        Ccall s.executionEnv.fork (AccountAddress.ofUInt256 vPop.2.2.1)
          (AccountAddress.ofUInt256 vPop.2.2.1) vPop.2.2.2.1 vPop.2.1
          s.accountMap s.machineState s.substate :=
      Ccallgas_lt_Ccall _ _ _ _ _ _ _ _
    rw [hcost]
    simpa [sExec, C', Ccallgas, Cgascap, h0, h1, h2] using hbase
  have hout := call_gas_spill_decreases (evmState := sExec)
    (by simpa [sExec] using hb) (by simpa [sExec] using hchild) (by simpa [sExec] using hle)
    hcallgasLt (by simpa [sExec] using hCall)
  rw [← h]
  simpa [sExec] using hout

set_option linter.unusedSimpArgs false in
lemma step_CALLCODE_gas_spill {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (hb : s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled)
    (hchild : ChildrenGasBound s.executionEnv.depth.val)
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s .CALLCODE)
    (h : step gasCost (.CALLCODE, arg) s = .ok s') :
    s.executionEnv.stateGasSpillBaseline ≤ s'.substate.stateGasSpilled ∧
      s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled + 1 ≤
        s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ vPop hPop _ vCall hCall
  rcases vCall with ⟨xCall, stateCall⟩
  let sExec : State := { s with
    machineState.execLength := s.machineState.execLength + 1 }
  have hPop' : s.machineState.stack.pop7 = some vPop := by
    exact option_liftM_eq_some hPop
  have hidx := Stack.pop7_get! hPop'
  rcases hidx with ⟨h0, h1, h2⟩
  have hcallgasLt :
      Ccallgas s.executionEnv.fork (AccountAddress.ofUInt256 vPop.2.2.1)
        (AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner.val))
        vPop.2.2.2.1 vPop.2.1
        sExec.accountMap sExec.machineState sExec.substate < gasCost := by
    have hbase :
        Ccallgas s.executionEnv.fork (AccountAddress.ofUInt256 vPop.2.2.1)
          s.executionEnv.codeOwner vPop.2.2.2.1 vPop.2.1
          s.accountMap s.machineState s.substate <
        Ccall s.executionEnv.fork (AccountAddress.ofUInt256 vPop.2.2.1)
          s.executionEnv.codeOwner vPop.2.2.2.1 vPop.2.1
          s.accountMap s.machineState s.substate :=
      Ccallgas_lt_Ccall _ _ _ _ _ _ _ _
    rw [hcost]
    simpa [sExec, C', Ccallgas, Cgascap, h0, h1, h2,
      AccountAddress.ofUInt256_ofNat] using hbase
  have hout := call_gas_spill_decreases (evmState := sExec)
    (by simpa [sExec] using hb) (by simpa [sExec] using hchild) (by simpa [sExec] using hle)
    hcallgasLt (by simpa [sExec] using hCall)
  rw [← h]
  simpa [sExec] using hout

set_option linter.unusedSimpArgs false in
lemma step_DELEGATECALL_gas_spill {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (hb : s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled)
    (hchild : ChildrenGasBound s.executionEnv.depth.val)
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s .DELEGATECALL)
    (h : step gasCost (.DELEGATECALL, arg) s = .ok s') :
    s.executionEnv.stateGasSpillBaseline ≤ s'.substate.stateGasSpilled ∧
      s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled + 1 ≤
        s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ vPop hPop _ vCall hCall
  rcases vCall with ⟨xCall, stateCall⟩
  let sExec : State := { s with
    machineState.execLength := s.machineState.execLength + 1 }
  have hPop' : s.machineState.stack.pop6 = some vPop := by
    exact option_liftM_eq_some hPop
  have hidx := Stack.pop6_get! hPop'
  rcases hidx with ⟨h0, h1⟩
  have hcallgasLt :
      Ccallgas s.executionEnv.fork (AccountAddress.ofUInt256 vPop.2.2.1)
        (AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner.val))
        (⟨0⟩ : UInt256) vPop.2.1
        sExec.accountMap sExec.machineState sExec.substate < gasCost := by
    have hbase :
        Ccallgas s.executionEnv.fork (AccountAddress.ofUInt256 vPop.2.2.1)
          s.executionEnv.codeOwner (⟨0⟩ : UInt256) vPop.2.1
          s.accountMap s.machineState s.substate <
        Ccall s.executionEnv.fork (AccountAddress.ofUInt256 vPop.2.2.1)
          s.executionEnv.codeOwner (⟨0⟩ : UInt256) vPop.2.1
          s.accountMap s.machineState s.substate :=
      Ccallgas_lt_Ccall _ _ _ _ _ _ _ _
    rw [hcost]
    simpa [sExec, C', Ccallgas, Cgascap, h0, h1,
      AccountAddress.ofUInt256_ofNat] using hbase
  have hout := call_gas_spill_decreases (evmState := sExec)
    (by simpa [sExec] using hb) (by simpa [sExec] using hchild) (by simpa [sExec] using hle)
    hcallgasLt (by simpa [sExec] using hCall)
  rw [← h]
  simpa [sExec] using hout

set_option linter.unusedSimpArgs false in
lemma step_STATICCALL_gas_spill {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (hb : s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled)
    (hchild : ChildrenGasBound s.executionEnv.depth.val)
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s .STATICCALL)
    (h : step gasCost (.STATICCALL, arg) s = .ok s') :
    s.executionEnv.stateGasSpillBaseline ≤ s'.substate.stateGasSpilled ∧
      s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled + 1 ≤
        s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ vPop hPop _ vCall hCall
  rcases vCall with ⟨xCall, stateCall⟩
  let sExec : State := { s with
    machineState.execLength := s.machineState.execLength + 1 }
  have hPop' : s.machineState.stack.pop6 = some vPop := by
    exact option_liftM_eq_some hPop
  have hidx := Stack.pop6_get! hPop'
  rcases hidx with ⟨h0, h1⟩
  have hcallgasLt :
      Ccallgas s.executionEnv.fork (AccountAddress.ofUInt256 vPop.2.2.1)
        (AccountAddress.ofUInt256 vPop.2.2.1)
        (⟨0⟩ : UInt256) vPop.2.1
        sExec.accountMap sExec.machineState sExec.substate < gasCost := by
    have hbase :
        Ccallgas s.executionEnv.fork (AccountAddress.ofUInt256 vPop.2.2.1)
          (AccountAddress.ofUInt256 vPop.2.2.1) (⟨0⟩ : UInt256) vPop.2.1
          s.accountMap s.machineState s.substate <
        Ccall s.executionEnv.fork (AccountAddress.ofUInt256 vPop.2.2.1)
          (AccountAddress.ofUInt256 vPop.2.2.1) (⟨0⟩ : UInt256) vPop.2.1
          s.accountMap s.machineState s.substate :=
      Ccallgas_lt_Ccall _ _ _ _ _ _ _ _
    rw [hcost]
    simpa [sExec, C', Ccallgas, Cgascap, h0, h1] using hbase
  have hout := call_gas_spill_decreases (evmState := sExec)
    (by simpa [sExec] using hb) (by simpa [sExec] using hchild) (by simpa [sExec] using hle)
    hcallgasLt (by simpa [sExec] using hCall)
  rw [← h]
  simpa [sExec] using hout

/-- A step of a frame whose spill is above its baseline, and whose children
    keep the gas bound, charges its cost `C'`: it keeps the spill above the
    baseline and does not add to the execution gas and spill; it takes at
    least one from them when its cost is positive. -/
lemma step_gas_spill_of_children {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hb : s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled)
    (hchild : ChildrenGasBound s.executionEnv.depth.val)
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s w)
    (h : step gasCost (w, arg) s = .ok s') :
    s.executionEnv.stateGasSpillBaseline ≤ s'.substate.stateGasSpilled ∧
      s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled + min gasCost 1 ≤
        s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled := by
  by_cases hcall : w ∈ ([.CALL, .CALLCODE, .DELEGATECALL, .STATICCALL] : List Operation)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcall
    rcases hcall with rfl | rfl | rfl | rfl
    · have := step_CALL_gas_spill hb hchild hle hcost h
      exact ⟨this.1, by omega⟩
    · have := step_CALLCODE_gas_spill hb hchild hle hcost h
      exact ⟨this.1, by omega⟩
    · have := step_DELEGATECALL_gas_spill hb hchild hle hcost h
      exact ⟨this.1, by omega⟩
    · have := step_STATICCALL_gas_spill hb hchild hle hcost h
      exact ⟨this.1, by omega⟩
  · have := step_noncall_gas_spill hb hchild hcall h
    exact ⟨this.1, by omega⟩
theorem Z_cost_le {validJumps : Array UInt256} {w : Operation}
    {evmState evmState' : State} {cost : Nat}
    (h : Z validJumps w evmState = .ok (evmState', cost)) :
    cost ≤ evmState'.machineState.gasAvailable.toNat := by
  unfold Z at h
  by_cases hδ : δ w = none
  · rw [if_pos hδ] at h
    contradiction
  rw [if_neg hδ] at h
  by_cases hstack : evmState.machineState.stack.length < (δ w).getD 0
  · rw [if_pos hstack] at h
    contradiction
  rw [if_neg hstack] at h
  by_cases hcost₁ : evmState.machineState.gasAvailable.toNat < memoryExpansionCost evmState w
  · rw [if_pos hcost₁] at h
    contradiction
  rw [if_neg hcost₁] at h
  by_cases hcost₂ :
      (evmState.subtractGas (memoryExpansionCost evmState w)).machineState.gasAvailable.toNat <
        C' (evmState.subtractGas (memoryExpansionCost evmState w)) w
  · rw [if_pos (by simpa [State.subtractGas] using hcost₂)] at h
    contradiction
  rw [if_neg (by simpa [State.subtractGas] using hcost₂)] at h
  set evmState₁ : State := evmState.subtractGas (memoryExpansionCost evmState w)
  by_cases hjump :
      w = Operation.JUMP ∧
        Z.notIn evmState₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [evmState₁] using hjump)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hjump)] at h
  by_cases hjumpi :
      w = Operation.JUMPI ∧
        evmState₁.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
        Z.notIn evmState₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [evmState₁] using hjumpi)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hjumpi)] at h
  by_cases hreturndata :
      w = Operation.RETURNDATACOPY ∧
        (evmState₁.machineState.stack.getD 1 (⟨0⟩ : UInt256)).toNat +
            (evmState₁.machineState.stack.getD 2 (⟨0⟩ : UInt256)).toNat >
          evmState₁.machineState.returnData.size
  · rw [if_pos (by simpa [evmState₁] using hreturndata)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hreturndata)] at h
  by_cases hoverflow :
      evmState₁.machineState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024
  · rw [if_pos (by simpa [evmState₁] using hoverflow)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hoverflow)] at h
  by_cases hstatic :
      ¬ evmState₁.executionEnv.perm ∧
        (w ∈ ([.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2,
            .LOG3, .LOG4, .TSTORE] : List Operation) ∨
          (w = .CALL ∧ ¬evmState₁.machineState.stack[2]? = some (⟨0⟩ : UInt256)))
  · rw [if_pos (by simpa [evmState₁] using hstatic)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hstatic)] at h
  by_cases hsstore :
      w = Operation.SSTORE ∧
        evmState₁.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos (by simpa [evmState₁] using hsstore)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hsstore)] at h
  by_cases hcreate :
      w.isCreate ∧ evmState₁.machineState.stack[2]?.getD (⟨0⟩ : UInt256) > ⟨49152⟩
  · rw [if_pos (by simpa [evmState₁] using hcreate)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hcreate)] at h
  injection h with hp
  have hstate : evmState₁ = evmState' := congrArg Prod.fst hp
  have hcost : C' evmState₁ w = cost := congrArg Prod.snd hp
  rw [← hstate, ← hcost]
  exact Nat.le_of_not_gt hcost₂

theorem Z_cost_eq_C' {validJumps : Array UInt256} {w : Operation}
    {evmState evmState' : State} {cost : Nat}
    (h : Z validJumps w evmState = .ok (evmState', cost)) :
    cost = C' evmState' w := by
  unfold Z at h
  by_cases hδ : δ w = none
  · rw [if_pos hδ] at h
    contradiction
  rw [if_neg hδ] at h
  by_cases hstack : evmState.machineState.stack.length < (δ w).getD 0
  · rw [if_pos hstack] at h
    contradiction
  rw [if_neg hstack] at h
  by_cases hcost₁ : evmState.machineState.gasAvailable.toNat < memoryExpansionCost evmState w
  · rw [if_pos hcost₁] at h
    contradiction
  rw [if_neg hcost₁] at h
  by_cases hcost₂ :
      (evmState.subtractGas (memoryExpansionCost evmState w)).machineState.gasAvailable.toNat <
        C' (evmState.subtractGas (memoryExpansionCost evmState w)) w
  · rw [if_pos (by simpa [State.subtractGas] using hcost₂)] at h
    contradiction
  rw [if_neg (by simpa [State.subtractGas] using hcost₂)] at h
  set evmState₁ : State := evmState.subtractGas (memoryExpansionCost evmState w)
  by_cases hjump :
      w = Operation.JUMP ∧
        Z.notIn evmState₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [evmState₁] using hjump)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hjump)] at h
  by_cases hjumpi :
      w = Operation.JUMPI ∧
        evmState₁.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
        Z.notIn evmState₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [evmState₁] using hjumpi)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hjumpi)] at h
  by_cases hreturndata :
      w = Operation.RETURNDATACOPY ∧
        (evmState₁.machineState.stack.getD 1 (⟨0⟩ : UInt256)).toNat +
            (evmState₁.machineState.stack.getD 2 (⟨0⟩ : UInt256)).toNat >
          evmState₁.machineState.returnData.size
  · rw [if_pos (by simpa [evmState₁] using hreturndata)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hreturndata)] at h
  by_cases hoverflow :
      evmState₁.machineState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024
  · rw [if_pos (by simpa [evmState₁] using hoverflow)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hoverflow)] at h
  by_cases hstatic :
      ¬ evmState₁.executionEnv.perm ∧
        (w ∈ ([.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2,
            .LOG3, .LOG4, .TSTORE] : List Operation) ∨
          (w = .CALL ∧ ¬evmState₁.machineState.stack[2]? = some (⟨0⟩ : UInt256)))
  · rw [if_pos (by simpa [evmState₁] using hstatic)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hstatic)] at h
  by_cases hsstore :
      w = Operation.SSTORE ∧
        evmState₁.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos (by simpa [evmState₁] using hsstore)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hsstore)] at h
  by_cases hcreate :
      w.isCreate ∧ evmState₁.machineState.stack[2]?.getD (⟨0⟩ : UInt256) > ⟨49152⟩
  · rw [if_pos (by simpa [evmState₁] using hcreate)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hcreate)] at h
  injection h with hp
  have hstate : evmState₁ = evmState' := congrArg Prod.fst hp
  have hcost : C' evmState₁ w = cost := congrArg Prod.snd hp
  rw [← hstate]
  exact hcost.symm

theorem Z_cost_pos_of_continues {validJumps : Array UInt256} {w : Operation}
    {evmState evmState' : State} {cost : Nat}
    (hcont : ContinuesAfterXStep w)
    (h : Z validJumps w evmState = .ok (evmState', cost)) :
    0 < cost := by
  unfold Z at h
  by_cases hδ : δ w = none
  · rw [if_pos hδ] at h
    contradiction
  rw [if_neg hδ] at h
  by_cases hstack : evmState.machineState.stack.length < (δ w).getD 0
  · rw [if_pos hstack] at h
    contradiction
  rw [if_neg hstack] at h
  by_cases hcost₁ : evmState.machineState.gasAvailable.toNat < memoryExpansionCost evmState w
  · rw [if_pos hcost₁] at h
    contradiction
  rw [if_neg hcost₁] at h
  by_cases hcost₂ :
      (evmState.subtractGas (memoryExpansionCost evmState w)).machineState.gasAvailable.toNat <
        C' (evmState.subtractGas (memoryExpansionCost evmState w)) w
  · rw [if_pos (by simpa [State.subtractGas] using hcost₂)] at h
    contradiction
  rw [if_neg (by simpa [State.subtractGas] using hcost₂)] at h
  set evmState₁ : State := evmState.subtractGas (memoryExpansionCost evmState w)
  by_cases hjump :
      w = Operation.JUMP ∧
        Z.notIn evmState₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [evmState₁] using hjump)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hjump)] at h
  by_cases hjumpi :
      w = Operation.JUMPI ∧
        evmState₁.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
        Z.notIn evmState₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [evmState₁] using hjumpi)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hjumpi)] at h
  by_cases hreturndata :
      w = Operation.RETURNDATACOPY ∧
        (evmState₁.machineState.stack.getD 1 (⟨0⟩ : UInt256)).toNat +
            (evmState₁.machineState.stack.getD 2 (⟨0⟩ : UInt256)).toNat >
          evmState₁.machineState.returnData.size
  · rw [if_pos (by simpa [evmState₁] using hreturndata)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hreturndata)] at h
  by_cases hoverflow :
      evmState₁.machineState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024
  · rw [if_pos (by simpa [evmState₁] using hoverflow)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hoverflow)] at h
  by_cases hstatic :
      ¬ evmState₁.executionEnv.perm ∧
        (w ∈ ([.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2,
            .LOG3, .LOG4, .TSTORE] : List Operation) ∨
          (w = .CALL ∧ ¬evmState₁.machineState.stack[2]? = some (⟨0⟩ : UInt256)))
  · rw [if_pos (by simpa [evmState₁] using hstatic)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hstatic)] at h
  by_cases hsstore :
      w = Operation.SSTORE ∧
        evmState₁.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos (by simpa [evmState₁] using hsstore)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hsstore)] at h
  by_cases hcreate :
      w.isCreate ∧ evmState₁.machineState.stack[2]?.getD (⟨0⟩ : UInt256) > ⟨49152⟩
  · rw [if_pos (by simpa [evmState₁] using hcreate)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hcreate)] at h
  injection h with hp
  have hcost : C' evmState₁ w = cost := congrArg Prod.snd hp
  rw [← hcost]
  exact C'_pos_of_continuesAfterXStep evmState₁ hcont

/-- `Z` only charges the memory expansion. -/
theorem Z_ok_state {validJumps : Array UInt256} {w : Operation}
    {evmState evmState' : State} {cost : Nat}
    (h : Z validJumps w evmState = .ok (evmState', cost)) :
    evmState' = evmState.subtractGas (memoryExpansionCost evmState w) := by
  unfold Z at h
  by_cases hδ : δ w = none
  · rw [if_pos hδ] at h
    contradiction
  rw [if_neg hδ] at h
  by_cases hstack : evmState.machineState.stack.length < (δ w).getD 0
  · rw [if_pos hstack] at h
    contradiction
  rw [if_neg hstack] at h
  by_cases hcost₁ : evmState.machineState.gasAvailable.toNat < memoryExpansionCost evmState w
  · rw [if_pos hcost₁] at h
    contradiction
  rw [if_neg hcost₁] at h
  by_cases hcost₂ :
      (evmState.subtractGas (memoryExpansionCost evmState w)).machineState.gasAvailable.toNat <
        C' (evmState.subtractGas (memoryExpansionCost evmState w)) w
  · rw [if_pos (by simpa [State.subtractGas] using hcost₂)] at h
    contradiction
  rw [if_neg (by simpa [State.subtractGas] using hcost₂)] at h
  set evmState₁ : State := evmState.subtractGas (memoryExpansionCost evmState w)
  by_cases hjump :
      w = Operation.JUMP ∧
        Z.notIn evmState₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [evmState₁] using hjump)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hjump)] at h
  by_cases hjumpi :
      w = Operation.JUMPI ∧
        evmState₁.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
        Z.notIn evmState₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [evmState₁] using hjumpi)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hjumpi)] at h
  by_cases hreturndata :
      w = Operation.RETURNDATACOPY ∧
        (evmState₁.machineState.stack.getD 1 (⟨0⟩ : UInt256)).toNat +
            (evmState₁.machineState.stack.getD 2 (⟨0⟩ : UInt256)).toNat >
          evmState₁.machineState.returnData.size
  · rw [if_pos (by simpa [evmState₁] using hreturndata)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hreturndata)] at h
  by_cases hoverflow :
      evmState₁.machineState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024
  · rw [if_pos (by simpa [evmState₁] using hoverflow)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hoverflow)] at h
  by_cases hstatic :
      ¬ evmState₁.executionEnv.perm ∧
        (w ∈ ([.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2,
            .LOG3, .LOG4, .TSTORE] : List Operation) ∨
          (w = .CALL ∧ ¬evmState₁.machineState.stack[2]? = some (⟨0⟩ : UInt256)))
  · rw [if_pos (by simpa [evmState₁] using hstatic)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hstatic)] at h
  by_cases hsstore :
      w = Operation.SSTORE ∧
        evmState₁.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos (by simpa [evmState₁] using hsstore)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hsstore)] at h
  by_cases hcreate :
      w.isCreate ∧ evmState₁.machineState.stack[2]?.getD (⟨0⟩ : UInt256) > ⟨49152⟩
  · rw [if_pos (by simpa [evmState₁] using hcreate)] at h
    contradiction
  rw [if_neg (by simpa [evmState₁] using hcreate)] at h
  injection h with hp
  exact (congrArg Prod.fst hp).symm

theorem Z_state_gas_le {validJumps : Array UInt256} {w : Operation}
    {evmState evmState' : State} {cost : Nat}
    (h : Z validJumps w evmState = .ok (evmState', cost)) :
    evmState'.machineState.gasAvailable.toNat ≤ evmState.machineState.gasAvailable.toNat := by
  rw [Z_ok_state h]
  exact State.subtractGas_le_gasAvailable _ _

/-- `Z` keeps the substate. -/
theorem Z_substate {validJumps : Array UInt256} {w : Operation}
    {evmState evmState' : State} {cost : Nat}
    (h : Z validJumps w evmState = .ok (evmState', cost)) :
    evmState'.substate = evmState.substate := by
  rw [Z_ok_state h]; rfl

/-- `Z` keeps the execution environment. -/
theorem Z_executionEnv {validJumps : Array UInt256} {w : Operation}
    {evmState evmState' : State} {cost : Nat}
    (h : Z validJumps w evmState = .ok (evmState', cost)) :
    evmState'.executionEnv = evmState.executionEnv := by
  rw [Z_ok_state h]; rfl


lemma C'_set_depth (s : State) (d : Fin 1025) (w : Operation) :
    C' {s with executionEnv.depth := d} w = C' s w := by
  cases w <;> rename_i a <;> cases a <;>
    simp [C', Csload, Csstore, Cselfdestruct]

lemma Xstep_continues_of_halt_none
    {validJumps : Array UInt256} {state state' : State}
    (h : Xstep validJumps state = .ok (state', none)) :
    ContinuesAfterXStep
      (decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none)).1 := by
  intros
  simp [Xstep] at h
  split at h; simp at h
  · simp [bind, Except.bind] at h
    cases hdecode : ((decode state.executionEnv.code state.machineState.pc).getD (Operation.STOP, none)).1 <;> simp [hdecode] at h
    · rename_i op
      cases op <;> simp at h <;>
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
    · rename_i op
      cases op <;> 
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
    · rename_i op
      cases op <;>
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
    · rename_i op
      cases op <;>
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
    · rename_i op
      cases op <;>
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
    · rename_i op
      cases op <;>
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
    · rename_i op
      cases op <;>
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
    · rename_i op
      cases op <;>
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
    · rename_i op
      cases op <;>
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
    · rename_i op
      cases op <;>
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
    · rename_i op
      cases op <;>
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
    · rename_i op
      cases op <;> simp at h <;>
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
      · rename_i heq
        simp [Z,hdecode,δ] at heq

/-- The execution gas of the frame of `s` and its own spill: the gas the frame
    has, counting the execution gas it spent on state, which it gets back
    when the state is not created (EIP-8037). -/
def frameGas (s : State) : ℕ :=
  s.machineState.gasAvailable.toNat +
    StateGas.ownSpill s.substate s.executionEnv.stateGasSpillBaseline

lemma frameGas_add_baseline {s : State}
    (hb : s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled) :
    frameGas s + s.executionEnv.stateGasSpillBaseline =
      s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled := by
  unfold frameGas StateGas.ownSpill
  omega

/-- What an `Xstep` that returns does: `Z`, then the step, then the frame's
    execution environment is restored. -/
theorem Xstep_ok_inv {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)}
    (h : Xstep validJumps state = .ok (state', ret)) :
    ∃ stateZ cost stepped,
      Z validJumps (decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none)).1
          state = .ok (stateZ, cost) ∧
      step cost (decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none))
          { stateZ with executionEnv.depth := state.executionEnv.depth } = .ok stepped ∧
      state' = { stepped with executionEnv := state.executionEnv } := by
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨w, arg⟩
  simp [Xstep, ← hinstr] at h
  split at h
  · contradiction
  · rename_i stateZ cost hZ
    simp [bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i stepped hstep
      refine ⟨stateZ, cost, stepped, by simpa [← hinstr] using hZ,
        by simpa [← hinstr] using hstep, ?_⟩
      repeat' split at h
      all_goals
        injection h with hpair
        exact (congrArg Prod.fst hpair).symm

/-- `Xstep` in a frame whose spill is above its baseline and whose children
    keep the gas bound: it keeps the execution environment and the spill above
    the baseline, and does not add to the execution gas and the spill; when
    the frame continues, it takes at least one from them. -/
theorem Xstep_gas_spill_of_children {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)}
    (hb : state.executionEnv.stateGasSpillBaseline ≤ state.substate.stateGasSpilled)
    (hchild : ChildrenGasBound state.executionEnv.depth.val)
    (h : Xstep validJumps state = .ok (state', ret)) :
    state'.executionEnv = state.executionEnv ∧
      state.executionEnv.stateGasSpillBaseline ≤ state'.substate.stateGasSpilled ∧
      state'.machineState.gasAvailable.toNat + state'.substate.stateGasSpilled +
          (if ret = none then 1 else 0) ≤
        state.machineState.gasAvailable.toNat + state.substate.stateGasSpilled := by
  obtain ⟨stateZ, cost, stepped, hZ, hstep, hstate⟩ := Xstep_ok_inv h
  have hcostLe := Z_cost_le hZ
  have hcostEq := Z_cost_eq_C' hZ
  have hsub := Z_substate hZ
  have hE := Z_executionEnv hZ
  have hZLe := Z_state_gas_le hZ
  have hpos : ret = none → 0 < cost := fun hr =>
    Z_cost_pos_of_continues (Xstep_continues_of_halt_none (hr ▸ h)) hZ
  have hs := step_gas_spill_of_children (s := { stateZ with executionEnv.depth := state.executionEnv.depth })
    (by simpa [hsub, hE] using hb) (by simpa using hchild) (by simpa using hcostLe)
    (by rw [C'_set_depth]; exact hcostEq) hstep
  simp only [hsub, hE] at hs
  subst hstate
  refine ⟨rfl, hs.1, ?_⟩
  dsimp only
  split
  · have := hpos ‹_›
    omega
  · omega

theorem Xstep_frameGas_le_of_children {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)}
    (hb : state.executionEnv.stateGasSpillBaseline ≤ state.substate.stateGasSpilled)
    (hchild : ChildrenGasBound state.executionEnv.depth.val)
    (h : Xstep validJumps state = .ok (state', ret)) :
    frameGas state' ≤ frameGas state := by
  obtain ⟨hE, hb', hle⟩ := Xstep_gas_spill_of_children hb hchild h
  have h1 := frameGas_add_baseline hb
  have h2 := frameGas_add_baseline (s := state') (by rw [hE]; exact hb')
  rw [hE] at h2
  split at hle <;> omega

theorem Xstep_frameGas_decreases_of_children {validJumps : Array UInt256}
    {state state' : State}
    (hb : state.executionEnv.stateGasSpillBaseline ≤ state.substate.stateGasSpilled)
    (hchild : ChildrenGasBound state.executionEnv.depth.val)
    (h : Xstep validJumps state = .ok (state', none)) :
    frameGas state' + 1 ≤ frameGas state := by
  obtain ⟨hE, hb', hle⟩ := Xstep_gas_spill_of_children hb hchild h
  have h1 := frameGas_add_baseline hb
  have h2 := frameGas_add_baseline (s := state') (by rw [hE]; exact hb')
  rw [hE] at h2
  simp only [if_true] at hle
  omega

/-- The bound of a result of `X`, for a frame with execution environment `E`
    whose execution gas and spill are at most `B`. -/
def XResultBound (E : ExecutionEnv) (B : ℕ) : ExecutionResult State → Prop
  | .success s' _ =>
    s'.executionEnv = E ∧ E.stateGasSpillBaseline ≤ s'.substate.stateGasSpilled ∧
      s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled ≤ B
  | .revert g _ => g.toNat + E.stateGasSpillBaseline ≤ B

theorem X_gas_spill_of_children {fuel : Nat} {validJumps : Array UInt256} {state : State}
    {result : ExecutionResult State}
    (hb : state.executionEnv.stateGasSpillBaseline ≤ state.substate.stateGasSpilled)
    (hchild : ChildrenGasBound state.executionEnv.depth.val)
    (h : X fuel validJumps state = .ok result) :
    XResultBound state.executionEnv
      (state.machineState.gasAvailable.toNat + state.substate.stateGasSpilled) result := by
  induction fuel generalizing state result with
  | zero =>
      simp [X] at h
  | succ fuel ih =>
      simp [X, bind, Except.bind] at h
      split at h
      · contradiction
      · rename_i stepResult hstep
        rcases stepResult with ⟨state', ret⟩
        obtain ⟨hE, hb', hle⟩ := Xstep_gas_spill_of_children hb hchild hstep
        cases ret with
        | none =>
            have hrec := ih (state := { state' with executionEnv.depth := state.executionEnv.depth })
              (by simpa [hE] using hb') (by simpa using hchild) h
            have hEnv : ({ state' with executionEnv.depth := state.executionEnv.depth } : State).executionEnv =
                state.executionEnv := by
              simp [hE]
            rw [hEnv] at hrec
            simp only [if_true] at hle
            cases result with
            | success s' o =>
                obtain ⟨h1, h2, h3⟩ := hrec
                exact ⟨h1, h2, by simp at h3; omega⟩
            | revert g o =>
                simp only [XResultBound] at hrec ⊢
                omega
        | some ro =>
            rcases ro with ⟨hc, o⟩
            simp only [reduceCtorEq, if_false] at hle
            cases hc <;> simp at h
            · subst h
              exact ⟨hE, hb', by omega⟩
            · subst h
              simp only [XResultBound, revertGas, hE]
              have := UInt256.toNat_ofNat_le (state'.machineState.gasAvailable.toNat +
                StateGas.ownSpill state'.substate state.executionEnv.stateGasSpillBaseline)
              unfold StateGas.ownSpill at this ⊢
              omega

/-- The bound of a result of `Ξ`, for a frame with execution environment `I`
    whose gas and spill are at most `B`. -/
def XiResultBound (I : ExecutionEnv) (B : ℕ) :
    ExecutionResult (AccountMap × UInt256 × Substate) → Prop
  | .success (_, g', A') _ =>
    I.stateGasSpillBaseline ≤ A'.stateGasSpilled ∧ g'.toNat + A'.stateGasSpilled ≤ B
  | .revert g' _ => g'.toNat + I.stateGasSpillBaseline ≤ B

theorem Xi_gas_spill_of_children {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {result : ExecutionResult (AccountMap × UInt256 × Substate)}
    (hb : I.stateGasSpillBaseline ≤ A.stateGasSpilled)
    (hchild : ChildrenGasBound I.depth.val)
    (h : Ξ σ σ₀ g A I = .ok result) :
    XiResultBound I (g.toNat + A.stateGasSpilled) result := by
  unfold Ξ at h
  simp [bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i x hx
    have hX := X_gas_spill_of_children (by simpa using hb) (by simpa using hchild) hx
    cases x with
    | success evmState' o =>
        cases h
        obtain ⟨_, h2, h3⟩ := hX
        simp at h2 h3
        exact ⟨h2, by simpa using h3⟩
    | revert g' o =>
        cases h
        simpa [XResultBound] using hX

lemma precompile_ECREC_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_ECREC σ g A I).2.1.toNat ≤ g.toNat := by
  unfold Ξ_ECREC
  by_cases hgas : g.toNat < 3000
  · simp [hgas]
  · simp [hgas, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_SHA256_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_SHA256 σ g A I).2.1.toNat ≤ g.toNat := by
  unfold Ξ_SHA256
  by_cases hgas : g.toNat < 60 + 12 * ((I.calldata.size + 31) / 32)
  · simp [hgas]
  · cases SHA256 I.calldata <;>
      simp [hgas, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_RIP160_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_RIP160 σ g A I).2.1.toNat ≤ g.toNat := by
  unfold Ξ_RIP160
  by_cases hgas : g.toNat < 600 + 120 * ((I.calldata.size + 31) / 32)
  · simp [hgas]
  · cases RIP160 I.calldata <;>
      simp [hgas, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_ID_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_ID σ g A I).2.1.toNat ≤ g.toNat := by
  unfold Ξ_ID
  by_cases hgas : g.toNat < 15 + 3 * ((I.calldata.size + 31) / 32)
  · simp [hgas]
  · simp [hgas, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_EXPMOD_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_EXPMOD σ g A I).2.1.toNat ≤ g.toNat := by
  unfold Ξ_EXPMOD
  cases hreq : expmodRequiredGas I.fork I.calldata with
  | none => simp [hreq]
  | some gᵣ =>
    by_cases hgas : g.toNat < gᵣ
    · simp [hreq, hgas]
    · simp [hreq, hgas, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_BN_ADD_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_BN_ADD σ g A I).2.1.toNat ≤ g.toNat := by
  unfold Ξ_BN_ADD
  by_cases hgas : g.toNat < 150
  · simp [hgas]
  · cases hres : BN_ADD (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
      (I.calldata.readBytes 64 32) (I.calldata.readBytes 96 32) with
    | ok o =>
        simp [hgas, hres, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
        simp [hgas, hres, dbgTrace]

lemma precompile_BN_MUL_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_BN_MUL σ g A I).2.1.toNat ≤ g.toNat := by
  unfold Ξ_BN_MUL
  by_cases hgas : g.toNat < 6000
  · simp [hgas]
  · cases hres : BN_MUL (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
      (I.calldata.readBytes 64 32) with
    | ok o =>
        simp [hgas, hres, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
        simp [hgas, hres, dbgTrace]

lemma precompile_SNARKV_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_SNARKV σ g A I).2.1.toNat ≤ g.toNat := by
  unfold Ξ_SNARKV
  by_cases hgas : g.toNat < 34000 * (I.calldata.size / 192) + 45000
  · simp [hgas]
  · cases hres : SNARKV I.calldata with
    | ok o =>
        simp [hgas, hres, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
        simp [hgas, hres, dbgTrace]

lemma precompile_BLAKE2_F_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_BLAKE2_F σ g A I).2.1.toNat ≤ g.toNat := by
  unfold Ξ_BLAKE2_F
  by_cases hgas : g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4)
  · simp [hgas, dbgTrace]
  · cases hres : BLAKE2_F I.calldata with
    | ok o =>
        simp [hgas, hres, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
        simp [hgas, hres, dbgTrace]

lemma precompile_PointEval_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_PointEval σ g A I).2.1.toNat ≤ g.toNat := by
  unfold Ξ_PointEval
  by_cases hgas : g.toNat < 50000
  · simp [hgas]
  · cases hres : PointEval I.calldata with
    | ok o =>
        simp [hgas, hres, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
        simp [hgas, hres, dbgTrace]

lemma precompile_BLS12_381_gas_le (op : ℕ) (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_BLS12_381 op σ g A I).2.1.toNat ≤ g.toNat := by
  unfold Ξ_BLS12_381
  by_cases hgas : g.toNat < blsRequiredGas op I.calldata.size
  · simp [hgas]
  · cases BLS12_381 op I.calldata <;>
      simp [hgas, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_P256VERIFY_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_P256VERIFY σ g A I).2.1.toNat ≤ g.toNat := by
  unfold Ξ_P256VERIFY
  by_cases hgas : g.toNat < 6900
  · simp [hgas]
  · cases P256Verify I.calldata <;>
      simp [hgas, dbgTrace, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_dispatch_gas_le (p : AccountAddress) (σ : AccountMap)
    (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_PRECOMPILE p σ g A I).2.1.toNat ≤ g.toNat :=
  Ξ_PRECOMPILE_induction (fun r => r.2.1.toNat ≤ g.toNat)
    (precompile_ECREC_gas_le σ g A I) (precompile_SHA256_gas_le σ g A I)
    (precompile_RIP160_gas_le σ g A I) (precompile_ID_gas_le σ g A I)
    (precompile_EXPMOD_gas_le σ g A I) (precompile_BN_ADD_gas_le σ g A I)
    (precompile_BN_MUL_gas_le σ g A I) (precompile_SNARKV_gas_le σ g A I)
    (precompile_BLAKE2_F_gas_le σ g A I) (precompile_PointEval_gas_le σ g A I)
    (fun op => precompile_BLS12_381_gas_le op σ g A I) (precompile_P256VERIFY_gas_le σ g A I)
    (by change (default : UInt256).toNat ≤ g.toNat; simp)


lemma precompile_ECREC_substate (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_ECREC σ g A I).2.2.1 = A := by
  simp only [Ξ_ECREC]
  repeat' split
  all_goals first | rfl | simp

lemma precompile_SHA256_substate (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_SHA256 σ g A I).2.2.1 = A := by
  simp only [Ξ_SHA256]
  repeat' split
  all_goals first | rfl | simp

lemma precompile_RIP160_substate (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_RIP160 σ g A I).2.2.1 = A := by
  simp only [Ξ_RIP160]
  repeat' split
  all_goals first | rfl | simp

lemma precompile_ID_substate (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_ID σ g A I).2.2.1 = A := by
  simp only [Ξ_ID]
  repeat' split
  all_goals first | rfl | simp

lemma precompile_EXPMOD_substate (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_EXPMOD σ g A I).2.2.1 = A := by
  simp only [Ξ_EXPMOD]
  repeat' split
  all_goals first | rfl | simp

lemma precompile_BN_ADD_substate (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_BN_ADD σ g A I).2.2.1 = A := by
  simp only [Ξ_BN_ADD]
  repeat' split
  all_goals first | rfl | simp

lemma precompile_BN_MUL_substate (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_BN_MUL σ g A I).2.2.1 = A := by
  simp only [Ξ_BN_MUL]
  repeat' split
  all_goals first | rfl | simp

lemma precompile_SNARKV_substate (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_SNARKV σ g A I).2.2.1 = A := by
  simp only [Ξ_SNARKV]
  repeat' split
  all_goals first | rfl | simp

lemma precompile_BLAKE2_F_substate (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_BLAKE2_F σ g A I).2.2.1 = A := by
  simp only [Ξ_BLAKE2_F]
  repeat' split
  all_goals first | rfl | simp

lemma precompile_PointEval_substate (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_PointEval σ g A I).2.2.1 = A := by
  simp only [Ξ_PointEval]
  repeat' split
  all_goals first | rfl | simp

lemma precompile_P256VERIFY_substate (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_P256VERIFY σ g A I).2.2.1 = A := by
  simp only [Ξ_P256VERIFY]
  repeat' split
  all_goals first | rfl | simp

lemma precompile_BLS12_381_substate (op : ℕ) (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_BLS12_381 op σ g A I).2.2.1 = A := by
  simp only [Ξ_BLS12_381]
  repeat' split
  all_goals first | rfl | simp

/-- A precompile returns the substate it is given, unless it fails with an
    empty account map. -/
lemma precompile_dispatch_substate (p : AccountAddress) (σ : AccountMap)
    (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_PRECOMPILE p σ g A I).2.2.1 = A ∨ ((Ξ_PRECOMPILE p σ g A I).1 == ∅) = true :=
  Ξ_PRECOMPILE_induction (fun r => r.2.2.1 = A ∨ (r.1 == ∅) = true)
    (.inl (precompile_ECREC_substate σ g A I)) (.inl (precompile_SHA256_substate σ g A I))
    (.inl (precompile_RIP160_substate σ g A I)) (.inl (precompile_ID_substate σ g A I))
    (.inl (precompile_EXPMOD_substate σ g A I)) (.inl (precompile_BN_ADD_substate σ g A I))
    (.inl (precompile_BN_MUL_substate σ g A I)) (.inl (precompile_SNARKV_substate σ g A I))
    (.inl (precompile_BLAKE2_F_substate σ g A I)) (.inl (precompile_PointEval_substate σ g A I))
    (fun op => .inl (precompile_BLS12_381_substate op σ g A I))
    (.inl (precompile_P256VERIFY_substate σ g A I))
    (.inr rfl)

/-- The result of `Θ` from the result `(σ'', g', A'')` of its code: the
    substate is `A` when the account map is empty. -/
lemma theta_result_bound {A A'' : Substate} {g g' : UInt256} {σ'' : AccountMap}
    (hg : g'.toNat ≤ g.toNat)
    (h : (σ'' == ∅) = true ∨
      (A.stateGasSpilled ≤ A''.stateGasSpilled ∧
        g'.toNat + A''.stateGasSpilled ≤ g.toNat + A.stateGasSpilled)) :
    A.stateGasSpilled ≤ (if (σ'' == ∅) = true then A else A'').stateGasSpilled ∧
      g'.toNat + (if (σ'' == ∅) = true then A else A'').stateGasSpilled ≤
        g.toNat + A.stateGasSpilled := by
  split
  · omega
  · rename_i hne
    rcases h with h | h
    · exact absurd h hne
    · exact h

theorem Theta_gas_spill_of_lt {n : ℕ} (ih : ∀ m, m < n → ChildGasBound m)
    {fork : Fork} {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress} {c : ToExecute}
    {g p v v' : UInt256} {d : ByteArray} {e : Fin 1025} {H : BlockHeader}
    {blobVersionedHashes : List ByteArray} {blocks : ProcessedBlocks} {w : Bool}
    (he : 1024 - e.val = n) :
    let res := Θ fork σ σ₀ A s o r c g p v v' d e H blobVersionedHashes blocks w
    A.stateGasSpilled ≤ res.2.2.1.stateGasSpilled ∧
      res.2.1.toNat + res.2.2.1.stateGasSpilled ≤ g.toNat + A.stateGasSpilled := by
  have hchild : ChildrenGasBound e.val := fun m hm => ih m (by omega)
  intro res
  unfold res Θ
  dsimp only
  split
  · simp
  · rename_i gₜ Aₜ hch
    have hT : gₜ.toNat + Aₜ.stateGasSpilled ≤ g.toNat + A.stateGasSpilled ∧
        A.stateGasSpilled ≤ Aₜ.stateGasSpilled := by
      split at hch
      · rw [Option.map_eq_some_iff] at hch
        obtain ⟨⟨g₁, A₁⟩, h1, h2⟩ := hch
        simp only [Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨h3, h4⟩ := topFrameCallCharges_spill h1
        have := Sat256.toNat_ofNat_le g₁
        have := UInt256.toNat_ofNat_le g₁
        exact ⟨by omega, h4⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at hch
        obtain ⟨rfl, rfl⟩ := hch
        exact ⟨le_refl _, le_refl _⟩
    split
    · rename_i pc
      refine theta_result_bound (le_trans (precompile_dispatch_gas_le _ _ _ _ _) (by omega)) ?_
      refine (precompile_dispatch_substate _ _ _ _ _).elim (fun hA => Or.inr ?_) (fun hA => Or.inl hA)
      rw [hA]
      refine ⟨hT.2, le_trans (Nat.add_le_add_right (precompile_dispatch_gas_le _ _ _ _ _) _) ?_⟩
      omega
    · split
      · exact theta_result_bound (by simp) (Or.inl rfl)
      · rename_i g' o' hXi
        have hX := Xi_gas_spill_of_children (by simpa using hT.2) (by simpa using hchild) hXi
        simp only [XiResultBound] at hX
        exact theta_result_bound (by dsimp only; omega) (Or.inl rfl)
      · rename_i σ'' g' A'' o' hXi
        have hX := Xi_gas_spill_of_children (by simpa using hT.2) (by simpa using hchild) hXi
        simp only [XiResultBound] at hX
        refine theta_result_bound (by dsimp only; omega) (Or.inr ⟨hX.1, by dsimp only; omega⟩)

/-- The result of a successful creation, from its code's result `(gSS, ASS)`
    and its code deposit `dep` (EIP-8037). -/
lemma lambda_success_bound {A AStar ASS : Substate} {g : UInt256} {gSS B : ℕ}
    (F e8 : Prop) [Decidable F] [Decidable e8] (dep : Option (ℕ × Substate)) (c : ℕ)
    (hAStar : AStar.stateGasSpilled = A.stateGasSpilled)
    (hX : A.stateGasSpilled ≤ ASS.stateGasSpilled ∧ gSS + ASS.stateGasSpilled ≤ B)
    (hB : B ≤ g.toNat + A.stateGasSpilled)
    (hdep : ∀ q, dep = some q →
      q.1 + q.2.stateGasSpilled ≤ gSS + ASS.stateGasSpilled ∧
        ASS.stateGasSpilled ≤ q.2.stateGasSpilled) :
    A.stateGasSpilled ≤
        (if F then AStar else if e8 then dep.option ASS (·.2) else ASS).stateGasSpilled ∧
      (UInt256.ofNat (if F then 0 else if e8 then dep.option 0 (·.1) else gSS - c)).toNat +
          (if F then AStar else if e8 then dep.option ASS (·.2) else ASS).stateGasSpilled ≤
        g.toNat + A.stateGasSpilled := by
  have h0 : (UInt256.ofNat 0).toNat = 0 := rfl
  split
  · omega
  · split
    · cases hd : dep with
      | none => simp only [Option.option]; omega
      | some q =>
        obtain ⟨h1, h2⟩ := hdep q hd
        have := UInt256.toNat_ofNat_le q.1
        simp only [Option.option]
        omega
    · have := UInt256.toNat_ofNat_le (gSS - c)
      omega

theorem Lambda_gas_spill_of_lt {n : ℕ} (ih : ∀ m, m < n → ChildGasBound m)
    {fork : Fork} {σ σ₀ : AccountMap} {A : Substate} {s o : AccountAddress}
    {g p v : UInt256} {i : ByteArray} {e : Fin 1025} {ζ : Option ByteArray} {H : BlockHeader}
    {blobVersionedHashes : List ByteArray} {blocks : ProcessedBlocks} {w : Bool}
    (he : 1024 - e.val = n) :
    let res := Lambda fork σ σ₀ A s o g p v i e ζ H blobVersionedHashes blocks w
    A.stateGasSpilled ≤ res.2.2.2.1.stateGasSpilled ∧
      res.2.2.1.toNat + res.2.2.2.1.stateGasSpilled ≤ g.toNat + A.stateGasSpilled := by
  have hchild : ChildrenGasBound e.val := fun m hm => ih m (by omega)
  intro res
  unfold res Lambda
  dsimp only
  split
  · simp
  · rename_i gₜ Aₜ hch
    have hT : gₜ.toNat + Aₜ.stateGasSpilled ≤ g.toNat + A.stateGasSpilled ∧
        A.stateGasSpilled ≤ Aₜ.stateGasSpilled := by
      split at hch
      · rw [Option.map_eq_some_iff] at hch
        obtain ⟨⟨g₁, A₁⟩, h1, h2⟩ := hch
        simp only [Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨h3, h4, h5⟩ := StateGas.charge_spill h1
        simp only [Substate.addAccessedAccount_stateGasSpilled] at h3 h4
        have := UInt256.toNat_ofNat_le g₁
        exact ⟨by omega, h4⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at hch
        obtain ⟨rfl, rfl⟩ := hch
        simp
    split
    · simp
    · rename_i g' o' hXi
      have hX := Xi_gas_spill_of_children (by simpa using hT.2) (by simpa using hchild) hXi
      simp only [XiResultBound] at hX
      simp
      omega
    · rename_i σSS gSS ASS out hXi
      have hX := Xi_gas_spill_of_children (by simpa using hT.2) (by simpa using hchild) hXi
      simp only [XiResultBound] at hX
      dsimp only
      refine lambda_success_bound _ _ _ _ (by simp) hX hT.1 ?_
      intro q hq
      split at hq
      · cases hq
      · obtain ⟨h1, h2, h3⟩ := StateGas.charge_spill hq
        exact ⟨by omega, h2⟩

/-- Every message call and contract creation keeps the gas bound, by
    induction on the distance of its depth to the depth limit. -/
theorem childGasBound : ∀ n, ChildGasBound n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    exact ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he => Theta_gas_spill_of_lt ih he,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he => Lambda_gas_spill_of_lt ih he⟩

theorem childrenGasBound (d : ℕ) : ChildrenGasBound d := fun n _ => childGasBound n

/-! ### The gas bounds, unconditionally -/

/-- A message call does not lower the spill of the substate it is given, and
    returns at most the gas and the spill it was given. -/
theorem Theta_gas_spill {σ σ₀ A s o r c g p v v' d e H
    blobVersionedHashes blocks w} :
    A.stateGasSpilled ≤
        (Θ fork σ σ₀ A s o r c g p v v' d e H blobVersionedHashes blocks w).2.2.1.stateGasSpilled ∧
      (Θ fork σ σ₀ A s o r c g p v v' d e H blobVersionedHashes blocks w).2.1.toNat +
          (Θ fork σ σ₀ A s o r c g p v v' d e H blobVersionedHashes blocks w).2.2.1.stateGasSpilled ≤
        g.toNat + A.stateGasSpilled :=
  (childGasBound _).1 fork σ σ₀ A s o r c g p v v' d e H blobVersionedHashes blocks w rfl

theorem Theta_gas_le {σ σ₀ A s o r c g p v v' d e H
    blobVersionedHashes blocks w} :
    (Θ fork σ σ₀ A s o r c
      g p v v' d e H blobVersionedHashes blocks w).2.1.toNat ≤ g.toNat := by
  have := Theta_gas_spill (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (s := s) (o := o) (r := r)
    (c := c) (g := g) (p := p) (v := v) (v' := v') (d := d) (e := e) (H := H)
    (blobVersionedHashes := blobVersionedHashes) (blocks := blocks) (w := w)
  omega

/-- A contract creation does not lower the spill of the substate it is
    given, and returns at most the gas and the spill it was given. -/
theorem Lambda_gas_spill {σ σ₀ A s o g p v i e ζ H blobVersionedHashes blocks w} :
    A.stateGasSpilled ≤
        (Lambda fork σ σ₀ A s o g p v i e ζ H blobVersionedHashes blocks w).2.2.2.1.stateGasSpilled ∧
      (Lambda fork σ σ₀ A s o g p v i e ζ H blobVersionedHashes blocks w).2.2.1.toNat +
          (Lambda fork σ σ₀ A s o g p v i e ζ H blobVersionedHashes blocks w).2.2.2.1.stateGasSpilled ≤
        g.toNat + A.stateGasSpilled :=
  (childGasBound _).2 fork σ σ₀ A s o g p v i e ζ H blobVersionedHashes blocks w rfl

theorem Lambda_gas_le {σ σ₀ A s o g p v i e ζ H blobVersionedHashes blocks w} :
    (Lambda fork σ σ₀ A s o g p v i e ζ H blobVersionedHashes blocks w).2.2.1.toNat ≤ g.toNat := by
  have := Lambda_gas_spill (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (s := s) (o := o)
    (g := g) (p := p) (v := v) (i := i) (e := e) (ζ := ζ) (H := H)
    (blobVersionedHashes := blobVersionedHashes) (blocks := blocks) (w := w)
  omega

/-- A step charges its cost `C'` (when it is at most the gas): it keeps the
    frame's spill above its baseline and does not add to the frame's
    execution gas and spill (see `step_gas_spill_of_children`). -/
theorem step_gas_spill {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hb : s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled)
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s w)
    (h : step gasCost (w, arg) s = .ok s') :
    s.executionEnv.stateGasSpillBaseline ≤ s'.substate.stateGasSpilled ∧
      s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled + min gasCost 1 ≤
        s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled :=
  step_gas_spill_of_children hb (childrenGasBound _) hle hcost h

/-- The form of `step_gas_spill` without the decrease. -/
theorem step_gas_spill_le {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hb : s.executionEnv.stateGasSpillBaseline ≤ s.substate.stateGasSpilled)
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s w)
    (h : step gasCost (w, arg) s = .ok s') :
    s.executionEnv.stateGasSpillBaseline ≤ s'.substate.stateGasSpilled ∧
      s'.machineState.gasAvailable.toNat + s'.substate.stateGasSpilled ≤
        s.machineState.gasAvailable.toNat + s.substate.stateGasSpilled := by
  have := step_gas_spill hb hle hcost h
  exact ⟨this.1, by omega⟩

/-- `Xstep` restores the frame's execution environment. -/
theorem Xstep_executionEnv {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)}
    (h : Xstep validJumps state = .ok (state', ret)) :
    state'.executionEnv = state.executionEnv := by
  obtain ⟨_, _, _, _, _, rfl⟩ := Xstep_ok_inv h
  rfl

theorem Xstep_gas_spill {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)}
    (hb : state.executionEnv.stateGasSpillBaseline ≤ state.substate.stateGasSpilled)
    (h : Xstep validJumps state = .ok (state', ret)) :
    state'.executionEnv = state.executionEnv ∧
      state.executionEnv.stateGasSpillBaseline ≤ state'.substate.stateGasSpilled ∧
      state'.machineState.gasAvailable.toNat + state'.substate.stateGasSpilled +
          (if ret = none then 1 else 0) ≤
        state.machineState.gasAvailable.toNat + state.substate.stateGasSpilled :=
  Xstep_gas_spill_of_children hb (childrenGasBound _) h

/-- `Xstep` keeps the frame's spill above its baseline. -/
theorem Xstep_baseline_le {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)}
    (hb : state.executionEnv.stateGasSpillBaseline ≤ state.substate.stateGasSpilled)
    (h : Xstep validJumps state = .ok (state', ret)) :
    state'.executionEnv.stateGasSpillBaseline ≤ state'.substate.stateGasSpilled := by
  obtain ⟨hE, hb', _⟩ := Xstep_gas_spill hb h
  rw [hE]
  exact hb'

/-- `Xstep` does not add to the frame's gas (`frameGas`). -/
theorem Xstep_gas_le {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)}
    (hb : state.executionEnv.stateGasSpillBaseline ≤ state.substate.stateGasSpilled)
    (h : Xstep validJumps state = .ok (state', ret)) :
    frameGas state' ≤ frameGas state :=
  Xstep_frameGas_le_of_children hb (childrenGasBound _) h

/-- An `Xstep` after which the frame continues takes at least one from the
    frame's gas (`frameGas`). -/
theorem Xstep_gas_decreases_of_continues
    {validJumps : Array UInt256} {state state' : State}
    (hb : state.executionEnv.stateGasSpillBaseline ≤ state.substate.stateGasSpilled)
    (h : Xstep validJumps state = .ok (state', none)) :
    frameGas state' + 1 ≤ frameGas state :=
  Xstep_frameGas_decreases_of_children hb (childrenGasBound _) h

theorem X_gas_spill {fuel : Nat} {validJumps : Array UInt256} {state : State}
    {result : ExecutionResult State}
    (hb : state.executionEnv.stateGasSpillBaseline ≤ state.substate.stateGasSpilled)
    (h : X fuel validJumps state = .ok result) :
    XResultBound state.executionEnv
      (state.machineState.gasAvailable.toNat + state.substate.stateGasSpilled) result :=
  X_gas_spill_of_children hb (childrenGasBound _) h

/-- The gas of a result of `X`: the frame's gas (`frameGas`) when it
    succeeds, the gas it returns when it reverts. -/
def ExecutionResultGas : ExecutionResult State → Nat
  | .success state _ => frameGas state
  | .revert g _ => g.toNat

/-- `X` does not add to the frame's gas (`frameGas`); when it succeeds, its
    state keeps the frame's spill above its baseline. -/
theorem X_gas_le {fuel : Nat} {validJumps : Array UInt256} {state : State}
    {result : ExecutionResult State}
    (hb : state.executionEnv.stateGasSpillBaseline ≤ state.substate.stateGasSpilled)
    (h : X fuel validJumps state = .ok result) :
    ExecutionResultGas result ≤ frameGas state ∧
      ∀ state' o, result = .success state' o →
        state'.executionEnv.stateGasSpillBaseline ≤ state'.substate.stateGasSpilled := by
  have hX := X_gas_spill hb h
  have h1 := frameGas_add_baseline hb
  cases result with
  | success state' o =>
      obtain ⟨hE, hb', hle⟩ := hX
      have h2 := frameGas_add_baseline (s := state') (by rw [hE]; exact hb')
      rw [hE] at h2
      refine ⟨?_, fun s o' hs => ?_⟩
      · simp only [ExecutionResultGas]; omega
      · cases hs; rw [hE]; exact hb'
  | revert g o =>
      simp only [XResultBound] at hX
      refine ⟨?_, fun _ _ hs => by cases hs⟩
      simp only [ExecutionResultGas]
      omega

/-- `Ξ`, in a frame whose spill baseline is at most the spill of its substate,
    returns at most the gas and the spill it was given, and keeps the spill
    above the baseline; when it reverts, it returns at most the gas and the
    frame's own spill. -/
theorem Xi_gas_le {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {result : ExecutionResult (AccountMap × UInt256 × Substate)}
    (hb : I.stateGasSpillBaseline ≤ A.stateGasSpilled)
    (h : Ξ σ σ₀ g A I = .ok result) :
    XiResultBound I (g.toNat + A.stateGasSpilled) result :=
  Xi_gas_spill_of_children hb (childrenGasBound _) h

end EVM

end Ethereum
