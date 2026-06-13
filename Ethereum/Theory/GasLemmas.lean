import Ethereum.Semantics

namespace Ethereum

namespace State

def subtractGas (self : State) (d : Nat) : State :=
  { self with machineState.gasAvailable := self.machineState.gasAvailable.natSub d }

end State

namespace EVM

open GasConstants InstructionGasGroups

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

instance : LawfulBEq UInt256 where
  eq_of_beq := by
    intro a b h
    cases a with
    | mk aval =>
    cases b with
    | mk bval =>
    change (aval == bval) = true at h
    have hv : aval = bval := beq_iff_eq.mp h
    subst hv
    rfl
  rfl := by
    intro a
    cases a with
    | mk aval =>
    change (aval == aval) = true
    exact BEq.rfl

def ContinuesAfterXStep (w : Operation) : Prop :=
  δ w ≠ none ∧ w ∉ [.STOP, .RETURN, .REVERT, .SELFDESTRUCT]

def RecursiveSystemStep (w : Operation) : Prop :=
  w ∈ ([.CREATE, .CREATE2, .CALL, .CALLCODE, .DELEGATECALL, .STATICCALL] : List Operation)

lemma Caccess_pos (a A) : 0 < Caccess a A := by
  unfold Caccess
  split <;> simp [Gwarmaccess, Gcoldaccountaccess]

lemma Cextra_pos (t r val σ A) : 0 < Cextra t r val σ A := by
  unfold Cextra
  have h := Caccess_pos t A
  omega

lemma Ccall_pos (t r val g σ μ A) : 0 < Ccall t r val g σ μ A := by
  unfold Ccall
  have h := Cextra_pos t r val σ A
  omega

lemma Ccallgas_lt_Ccall (t r val g σ μ A) :
    Ccallgas t r val g σ μ A < Ccall t r val g σ μ A := by
  by_cases hval : val = (⟨0⟩ : UInt256)
  · subst val
    unfold Ccall Ccallgas Cextra Cxfer Cnew Caccess
    simp [bne, GasConstants.Gwarmaccess, GasConstants.Gcoldaccountaccess]
    split
    · split <;> omega
    · rename_i hneq
      exact False.elim (hneq rfl)
  · have hbne : (val != (⟨0⟩ : UInt256)) = true := by
      have hbeq : (val == (⟨0⟩ : UInt256)) = false := by
        by_cases hbeq : val == (⟨0⟩ : UInt256)
        · exact False.elim (hval (beq_iff_eq.mp hbeq))
        · simpa using hbeq
      simp [bne, hbeq]
    unfold Ccall Ccallgas Cextra Cxfer Cnew Caccess
    simp [hbne, GasConstants.Gwarmaccess, GasConstants.Gcoldaccountaccess,
      GasConstants.Gcallvalue, GasConstants.Gcallstipend, GasConstants.Gnewaccount]
    split <;> omega

lemma L_le_self (n : Nat) : L n ≤ n := by
  unfold L
  omega

lemma UInt256.toNat_ofNat_of_lt {n : Nat} (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  unfold UInt256.ofNat UInt256.toNat
  simp [Id.run, Nat.mod_eq_of_lt h]

lemma UInt256.toNat_ofNat_le (n : Nat) :
    (UInt256.ofNat n).toNat ≤ n := by
  unfold UInt256.ofNat UInt256.toNat
  simp [Id.run]
  exact Nat.mod_le n UInt256.size

lemma AccountAddress.ofUInt256_ofNat (a : AccountAddress) :
    AccountAddress.ofUInt256 (UInt256.ofNat a.val) = a := by
  ext
  unfold AccountAddress.ofUInt256 UInt256.ofNat
  simp [Id.run, AccountAddress.size, UInt256.size]

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

@[simp] lemma UInt256.zero_toNat : (⟨0⟩ : UInt256).toNat = 0 := by
  rfl

@[simp] lemma UInt256.default_toNat : (default : UInt256).toNat = 0 := by
  rfl

lemma UInt256.toNat_sub_ofNat_of_le {g : UInt256} {n : Nat}
    (h : n ≤ g.toNat) :
    (g - UInt256.ofNat n).toNat = g.toNat - n := by
  change (UInt256.sub g (UInt256.ofNat n)).toNat = g.toNat - n
  unfold UInt256.toNat UInt256.ofNat UInt256.sub
  rw [Fin.sub_val_of_le]
  · simp [Id.run, Nat.mod_eq_of_lt (lt_of_le_of_lt h g.val.isLt)]
  · change (Fin.ofNat UInt256.size n).val ≤ g.val.val
    simp [Nat.mod_eq_of_lt (lt_of_le_of_lt h g.val.isLt)]
    simpa [UInt256.toNat] using h

lemma UInt256.toNat_sub_ofNat_le {g : UInt256} {n : Nat}
    (h : n ≤ g.toNat) :
    (g - UInt256.ofNat n).toNat ≤ g.toNat := by
  rw [UInt256.toNat_sub_ofNat_of_le h]
  exact Nat.sub_le _ _

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
  exact Nat.lt_of_lt_of_le (Csstore_storeComponent_pos _ _ _) (Nat.le_add_left _ _)

lemma Cselfdestruct_pos (s : State) : 0 < Cselfdestruct s := by
  unfold Cselfdestruct
  repeat split <;> simp [Gselfdestruct, Gcoldaccountaccess, Gnewaccount]

set_option maxHeartbeats 800000 in
lemma C'_pos_of_continuesAfterXStep (s : State) {w : Operation}
    (h : ContinuesAfterXStep w) : 0 < C' s w := by
  cases w <;> rename_i a <;> cases a <;>
    simp [ContinuesAfterXStep, δ, C', Wzero, Wbase, Wverylow, Wlow, Wmid, Whigh,
      Wcopy, Wextaccount, Wverylow.pushInstrsWithoutZero, Wverylow.dupInstrs,
      Wverylow.swapInstrs, Caccess_pos, Ccall_pos, Csload_pos, Csstore_pos,
      Ctstore, Ctload, Gjumpdest, Gbase, Gverylow, Glow, Gmid, Ghigh, Gexp,
      Gexpbyte, Gcopy, Glog, Glogdata, Glogtopic, Gcreate, Gkeccak256,
      Gkeccak256word, Gblockhash, HASH_OPCODE_GAS] at h ⊢ <;>
    repeat split
  all_goals
    try unfold GasConstants.Gwarmaccess at h ⊢
    norm_num [GasConstants.Gexp, GasConstants.Gexpbyte, GasConstants.Gwarmaccess,
      Gverylow, Glow, Gmid, Ghigh] at h ⊢

@[simp] lemma State.subtractGas_gasAvailable (self : State) (d : Nat) :
    (self.subtractGas d).machineState.gasAvailable =
      self.machineState.gasAvailable.natSub d := by
  rfl

@[simp] lemma Sat256.natSub_toNat (self : Sat256) (d : Nat) :
    (self.natSub d).toNat = self.toNat - d := by
  rfl

@[simp] lemma Sat256.toUInt256_toNat (self : Sat256) :
    self.toUInt256.toNat = self.toNat := by
  rfl

@[simp] lemma Sat256.ofUInt256_toNat (self : UInt256) :
    (Sat256.ofUInt256 self).toNat = self.toNat := by
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

set_option linter.unusedSimpArgs false in
lemma step_stoparith_gas {gasCost : Nat} {op : Operation.SAOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.StopArith op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.natSub gasCost := by
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
    s'.machineState.gasAvailable = s.machineState.gasAvailable.natSub gasCost := by
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
    s'.machineState.gasAvailable = s.machineState.gasAvailable.natSub gasCost := by
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
    s'.machineState.gasAvailable = s.machineState.gasAvailable.natSub gasCost := by
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
    s'.machineState.gasAvailable = s.machineState.gasAvailable.natSub gasCost := by
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
    (h : step gasCost (Operation.StackMemFlow op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.natSub gasCost := by
  cases op <;> rw [step.eq_1] at h <;>
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
    s'.machineState.gasAvailable = s.machineState.gasAvailable.natSub gasCost := by
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
    s'.machineState.gasAvailable = s.machineState.gasAvailable.natSub gasCost := by
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
    s'.machineState.gasAvailable = s.machineState.gasAvailable.natSub gasCost := by
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
lemma step_log_gas {gasCost : Nat} {op : Operation.LOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (Operation.Log op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.natSub gasCost := by
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
        Operation.DELEGATECALL, Operation.STATICCALL] : List Operation))
    (h : step gasCost (Operation.System op, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.natSub gasCost := by
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
lemma call_gas_le {gasCost : Nat} {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {evmState state' : State} {x : UInt256}
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
      inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    state'.machineState.gasAvailable.toNat ≤ evmState.machineState.gasAvailable.toNat := by
  unfold call at h
  simp [Id.run, bind, Except.bind, pure, Except.pure,
    Ethereum.State.addAccessedAccount, Ethereum.State.replaceStackAndIncrPC,
    Ethereum.State.incrPC] at h
  repeat split at h
  all_goals
    try contradiction
    rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp

set_option linter.unusedSimpArgs false in
lemma step_create_gas_le {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {s s' : State}
    (h : step gasCost (Operation.CREATE, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    first
    | rw [← h]
      simp
      omega
    | injection h with hs
      rw [← hs]
      simp
      omega

set_option linter.unusedSimpArgs false in
lemma step_create_gas_decreases {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {s s' : State}
    (hpos : 0 < gasCost)
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (h : step gasCost (Operation.CREATE, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat + 1 ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    first
    | rw [← h]
      simp
      omega
    | injection h with hs
      rw [← hs]
      simp
      omega

set_option linter.unusedSimpArgs false in
lemma step_create2_gas_le {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {s s' : State}
    (h : step gasCost (Operation.CREATE2, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    first
    | rw [← h]
      simp
      omega
    | injection h with hs
      rw [← hs]
      simp
      omega

set_option linter.unusedSimpArgs false in
lemma step_create2_gas_decreases {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {s s' : State}
    (hpos : 0 < gasCost)
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (h : step gasCost (Operation.CREATE2, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat + 1 ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat' (split at h <;> try simp at h)
  all_goals
    try contradiction
    first
    | rw [← h]
      simp
      omega
    | injection h with hs
      rw [← hs]
      simp
      omega

set_option linter.unusedSimpArgs false in
lemma step_call_gas_le {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {s s' : State}
    (h : step gasCost (Operation.CALL, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ _ _ _ vCall hCall
  rcases vCall with ⟨_, _⟩
  have hle := call_gas_le hCall
  rw [← h]
  simpa using hle

set_option linter.unusedSimpArgs false in
lemma step_callcode_gas_le {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {s s' : State}
    (h : step gasCost (Operation.CALLCODE, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ _ _ _ vCall hCall
  rcases vCall with ⟨_, _⟩
  have hle := call_gas_le hCall
  rw [← h]
  simpa using hle

set_option linter.unusedSimpArgs false in
lemma step_delegatecall_gas_le {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {s s' : State}
    (h : step gasCost (Operation.DELEGATECALL, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ _ _ _ vCall hCall
  rcases vCall with ⟨_, _⟩
  have hle := call_gas_le hCall
  rw [← h]
  simpa using hle

set_option linter.unusedSimpArgs false in
lemma step_staticcall_gas_le {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {s s' : State}
    (h : step gasCost (Operation.STATICCALL, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ _ _ _ vCall hCall
  rcases vCall with ⟨_, _⟩
  have hle := call_gas_le hCall
  rw [← h]
  simpa using hle

lemma step_nonrecursive_gas {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hnrec : ¬ RecursiveSystemStep w)
    (h : step gasCost (w, arg) s = .ok s') :
    s'.machineState.gasAvailable = s.machineState.gasAvailable.natSub gasCost := by
  cases w with
  | StopArith op => exact step_stoparith_gas h
  | CompBit op => exact step_compbit_gas h
  | Keccak op => exact step_keccak_gas h
  | Env op => exact step_env_gas h
  | Block op => exact step_block_gas h
  | StackMemFlow op => exact step_stackmemflow_gas h
  | Push op => exact step_push_gas h
  | Dup op => exact step_dup_gas h
  | Exchange op => exact step_exchange_gas h
  | Log op => exact step_log_gas h
  | System op =>
      apply step_system_nonrecursive_gas
      · simpa [RecursiveSystemStep] using hnrec
      · exact h

lemma step_gas_le {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (w, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat ≤ s.machineState.gasAvailable.toNat := by
  by_cases hnrec : RecursiveSystemStep w
  · cases w with
    | StopArith op => simp [RecursiveSystemStep] at hnrec
    | CompBit op => simp [RecursiveSystemStep] at hnrec
    | Keccak op => simp [RecursiveSystemStep] at hnrec
    | Env op => simp [RecursiveSystemStep] at hnrec
    | Block op => simp [RecursiveSystemStep] at hnrec
    | StackMemFlow op => simp [RecursiveSystemStep] at hnrec
    | Push op => simp [RecursiveSystemStep] at hnrec
    | Dup op => simp [RecursiveSystemStep] at hnrec
    | Exchange op => simp [RecursiveSystemStep] at hnrec
    | Log op => simp [RecursiveSystemStep] at hnrec
    | System op =>
        cases op with
        | CREATE => exact step_create_gas_le h
        | CALL => exact step_call_gas_le h
        | CALLCODE => exact step_callcode_gas_le h
        | RETURN => simp [RecursiveSystemStep] at hnrec
        | DELEGATECALL => exact step_delegatecall_gas_le h
        | CREATE2 => exact step_create2_gas_le h
        | STATICCALL => exact step_staticcall_gas_le h
        | REVERT => simp [RecursiveSystemStep] at hnrec
        | INVALID => simp [RecursiveSystemStep] at hnrec
        | SELFDESTRUCT => simp [RecursiveSystemStep] at hnrec
  · rw [step_nonrecursive_gas hnrec h]
    exact Nat.sub_le _ _

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

theorem Z_state_gas_le {validJumps : Array UInt256} {w : Operation}
    {evmState evmState' : State} {cost : Nat}
    (h : Z validJumps w evmState = .ok (evmState', cost)) :
    evmState'.machineState.gasAvailable.toNat ≤ evmState.machineState.gasAvailable.toNat := by
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
  rw [← hstate]
  simp [evmState₁, State.subtractGas]

theorem Xstep_gas_le
    {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)}
    (h : Xstep validJumps state = .ok (state', ret)) :
    state'.machineState.gasAvailable.toNat ≤ state.machineState.gasAvailable.toNat := by
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
      have hZ' : Z validJumps w state = .ok (stateZ, cost) := by
        simpa [← hinstr] using hZ
      have hstep' :
          step cost (w, arg)
            { stateZ with executionEnv.depth := state.executionEnv.depth } = .ok stepped := by
        simpa [← hinstr] using hstep
      have hstepLe :
          stepped.machineState.gasAvailable.toNat ≤ stateZ.machineState.gasAvailable.toNat := by
        simpa using step_gas_le hstep'
      have hZLe :
          stateZ.machineState.gasAvailable.toNat ≤ state.machineState.gasAvailable.toNat :=
        Z_state_gas_le hZ'
      repeat split at h
      all_goals
        try contradiction
        try
          injection h with hpair
          have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
            congrArg Prod.fst hpair
          rw [← hstateEq]
          simp
          exact Nat.le_trans hstepLe hZLe
        try
          split at h
          · injection h with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            simp
            exact Nat.le_trans hstepLe hZLe
          · injection h with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            simp
            exact Nat.le_trans hstepLe hZLe

def ExecutionResultGas : ExecutionResult State → Nat
  | .success state _ => state.machineState.gasAvailable.toNat
  | .revert g _ => g.toNat

theorem X_gas_le {fuel : Nat} {validJumps : Array UInt256} {state : State}
    {result : ExecutionResult State}
    (h : X fuel validJumps state = .ok result) :
    ExecutionResultGas result ≤ state.machineState.gasAvailable.toNat := by
  induction fuel generalizing state result with
  | zero =>
      simp [X] at h
  | succ fuel ih =>
      simp [X, bind, Except.bind] at h
      split at h
      · contradiction
      · rename_i stepResult hstep
        rcases stepResult with ⟨state', ret⟩
        have hstepLe : state'.machineState.gasAvailable.toNat ≤ state.machineState.gasAvailable.toNat :=
          Xstep_gas_le hstep
        cases ret with
        | none =>
            have hrec :
                ExecutionResultGas result ≤
                  ({ state' with executionEnv.depth := state.executionEnv.depth }).machineState.gasAvailable.toNat :=
              ih h
            simp at hrec
            exact Nat.le_trans hrec hstepLe
        | some ro =>
            rcases ro with ⟨HaltSuccess.success, o⟩
            cases HaltSuccess.success <;> simp at h
            · cases h
              simpa using hstepLe
            · cases h
              simpa using hstepLe

def XiResultGas :
    ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate) →
      Nat
  | .success (_, _, g, _) _ => g.toNat
  | .revert g _ => g.toNat

theorem Xi_gas_le {createdAccounts genesisBlockHeader blocks σ σ₀ g A I result}
    (h : Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok result) :
    XiResultGas result ≤ g.toNat := by
  unfold Ξ at h
  simp [bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i x hx
    cases x with
    | success evmState' o =>
        have hxGas := X_gas_le hx
        simp [ExecutionResultGas] at hxGas
        cases h
        simp [XiResultGas]
        simpa using hxGas
    | revert g' o =>
        cases h
        simpa [XiResultGas, ExecutionResultGas] using X_gas_le hx

lemma precompile_ECREC_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_ECREC σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_ECREC
  by_cases hgas : g.toNat < 3000
  · simp [hgas]
  · simp [hgas, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_SHA256_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_SHA256 σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_SHA256
  by_cases hgas : g.toNat < 60 + 12 * ((I.calldata.size + 31) / 32)
  · simp [hgas]
  · cases ffi.SHA256 I.calldata <;>
      simp [hgas, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_RIP160_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_RIP160 σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_RIP160
  by_cases hgas : g.toNat < 600 + 120 * ((I.calldata.size + 31) / 32)
  · simp [hgas]
  · cases RIP160 I.calldata <;>
      simp [hgas, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_ID_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_ID σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_ID
  by_cases hgas : g.toNat < 15 + 3 * ((I.calldata.size + 31) / 32)
  · simp [hgas]
  · simp [hgas, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_EXPMOD_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_EXPMOD σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_EXPMOD
  set foo : Nat :=
    ((max (nat_of_slice I.calldata 0 32) (nat_of_slice I.calldata 64 32) + 7) / 8) ^ 2 *
      max
        (if
            nat_of_slice I.calldata 32 32 ≤ 32 ∧
              nat_of_slice I.calldata (96 + nat_of_slice I.calldata 0 32)
                (nat_of_slice I.calldata 32 32) = 0 then
            0
          else if nat_of_slice I.calldata 32 32 ≤ 32 then
            Nat.log 2
              (nat_of_slice I.calldata (96 + nat_of_slice I.calldata 0 32)
                (nat_of_slice I.calldata 32 32))
          else
            8 * (nat_of_slice I.calldata 32 32 - 32) +
              if
                  32 < nat_of_slice I.calldata 32 32 ∧
                    ¬ nat_of_slice I.calldata (96 + nat_of_slice I.calldata 0 32) 32 = 0 then
                Nat.log 2 (nat_of_slice I.calldata (96 + nat_of_slice I.calldata 0 32) 32)
              else 0)
        1 /
      3
  by_cases hgas : g.toNat < 200 ∨ g.toNat < foo
  · simp [hgas, foo]
  · have hle : max 200 foo ≤ g.toNat := by
      have h200 : ¬ g.toNat < 200 := by
        intro h
        exact hgas (Or.inl h)
      have hfoo : ¬ g.toNat < foo := by
        intro h
        exact hgas (Or.inr h)
      omega
    simp [hgas, foo, UInt256.toNat_sub_ofNat_le hle]

lemma precompile_BN_ADD_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_BN_ADD σ g A I).2.2.1.toNat ≤ g.toNat := by
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
    (I : ExecutionEnv) : (Ξ_BN_MUL σ g A I).2.2.1.toNat ≤ g.toNat := by
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
    (I : ExecutionEnv) : (Ξ_SNARKV σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_SNARKV
  by_cases hgas : g.toNat < 34000 * (I.calldata.size / 192) + 45000
  · simp [hgas]
  · cases hres : SNARKV I.calldata with
    | ok o =>
        simp [hgas, hres, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
        simp [hgas, hres, dbgTrace]

lemma precompile_BLAKE2_F_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_BLAKE2_F σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_BLAKE2_F
  by_cases hgas : g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4)
  · simp [hgas, dbgTrace]
  · cases hres : ffi.BLAKE2 I.calldata with
    | ok o =>
        simp [hgas, hres, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
        simp [hgas, hres, dbgTrace]

lemma precompile_PointEval_gas_le (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : (Ξ_PointEval σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_PointEval
  by_cases hgas : g.toNat < 50000
  · simp [hgas]
  · cases hres : PointEval I.calldata with
    | ok o =>
        simp [hgas, hres, UInt256.toNat_sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
        simp [hgas, hres, dbgTrace]

lemma precompile_dispatch_gas_le (p : AccountAddress) (σ : AccountMap)
    (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (match p with
      | 1 => ((∅ : Batteries.RBSet AccountAddress compare), Ξ_ECREC σ g A I)
      | 2 => ((∅ : Batteries.RBSet AccountAddress compare), Ξ_SHA256 σ g A I)
      | 3 => ((∅ : Batteries.RBSet AccountAddress compare), Ξ_RIP160 σ g A I)
      | 4 => ((∅ : Batteries.RBSet AccountAddress compare), Ξ_ID σ g A I)
      | 5 => ((∅ : Batteries.RBSet AccountAddress compare), Ξ_EXPMOD σ g A I)
      | 6 => ((∅ : Batteries.RBSet AccountAddress compare), Ξ_BN_ADD σ g A I)
      | 7 => ((∅ : Batteries.RBSet AccountAddress compare), Ξ_BN_MUL σ g A I)
      | 8 => ((∅ : Batteries.RBSet AccountAddress compare), Ξ_SNARKV σ g A I)
      | 9 => ((∅ : Batteries.RBSet AccountAddress compare), Ξ_BLAKE2_F σ g A I)
      | 10 => ((∅ : Batteries.RBSet AccountAddress compare), Ξ_PointEval σ g A I)
      | _ => default).2.2.2.1.toNat ≤ g.toNat := by
  by_cases h1 : p = 1
  · subst p
    change (Ξ_ECREC σ g A I).2.2.1.toNat ≤ g.toNat
    exact precompile_ECREC_gas_le _ _ _ _
  by_cases h2 : p = 2
  · subst p
    change (Ξ_SHA256 σ g A I).2.2.1.toNat ≤ g.toNat
    exact precompile_SHA256_gas_le _ _ _ _
  by_cases h3 : p = 3
  · subst p
    change (Ξ_RIP160 σ g A I).2.2.1.toNat ≤ g.toNat
    exact precompile_RIP160_gas_le _ _ _ _
  by_cases h4 : p = 4
  · subst p
    change (Ξ_ID σ g A I).2.2.1.toNat ≤ g.toNat
    exact precompile_ID_gas_le _ _ _ _
  by_cases h5 : p = 5
  · subst p
    change (Ξ_EXPMOD σ g A I).2.2.1.toNat ≤ g.toNat
    exact precompile_EXPMOD_gas_le _ _ _ _
  by_cases h6 : p = 6
  · subst p
    change (Ξ_BN_ADD σ g A I).2.2.1.toNat ≤ g.toNat
    exact precompile_BN_ADD_gas_le _ _ _ _
  by_cases h7 : p = 7
  · subst p
    change (Ξ_BN_MUL σ g A I).2.2.1.toNat ≤ g.toNat
    exact precompile_BN_MUL_gas_le _ _ _ _
  by_cases h8 : p = 8
  · subst p
    change (Ξ_SNARKV σ g A I).2.2.1.toNat ≤ g.toNat
    exact precompile_SNARKV_gas_le _ _ _ _
  by_cases h9 : p = 9
  · subst p
    change (Ξ_BLAKE2_F σ g A I).2.2.1.toNat ≤ g.toNat
    exact precompile_BLAKE2_F_gas_le _ _ _ _
  by_cases h10 : p = 10
  · subst p
    change (Ξ_PointEval σ g A I).2.2.1.toNat ≤ g.toNat
    exact precompile_PointEval_gas_le _ _ _ _
  repeat split
  all_goals try contradiction
  · change (default : UInt256).toNat ≤ g.toNat
    simp

set_option maxHeartbeats 800000 in
theorem Theta_gas_le {blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c
    g p v v' d e H w} :
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c
      g p v v' d e H w).2.2.1.toNat ≤ g.toNat := by
  cases c with
  | Code code =>
      unfold Θ
      simp
      repeat split
      all_goals
        try simp
        try
          rename_i hxi
          have hle := Xi_gas_le hxi
          simpa [XiResultGas] using hle
  | Precompiled p =>
      unfold Θ
      simp
      exact precompile_dispatch_gas_le p _ g A _

lemma call_gas_decreases {gasCost : Nat} {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {evmState state' : State} {x : UInt256}
    (hgasCost : gasCost ≤ evmState.machineState.gasAvailable.toNat)
    (hcallgasLt :
      Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
        value gas evmState.accountMap evmState.machineState evmState.substate < gasCost)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
      inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    state'.machineState.gasAvailable.toNat + 1 ≤ evmState.machineState.gasAvailable.toNat := by
  unfold call at h
  simp [Ethereum.State.addAccessedAccount] at h
  split at h
  · split at h
    · rcases h with ⟨_, hstate⟩
      rw [← hstate]
      simp
      have htheta := Theta_gas_le
        (blobVersionedHashes := blobVersionedHashes)
        (createdAccounts := evmState.createdAccounts)
        (genesisBlockHeader := evmState.genesisBlockHeader)
        (blocks := evmState.blocks)
        (σ := evmState.accountMap)
        (σ₀ := evmState.σ₀)
        (A := evmState.substate.addAccessedAccount (AccountAddress.ofUInt256 t))
        (s := AccountAddress.ofUInt256 source)
        (o := evmState.executionEnv.sender)
        (r := AccountAddress.ofUInt256 recipient)
        (c := toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (g := UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (p := UInt256.ofNat evmState.executionEnv.gasPrice)
        (v := value)
        (v' := value')
        (d := evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (e := evmState.executionEnv.depth + 1)
        (H := evmState.executionEnv.header)
        (w := permission)
      have hretLe :
          ((Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader evmState.blocks
              evmState.accountMap evmState.σ₀
              (evmState.substate.addAccessedAccount (AccountAddress.ofUInt256 t))
              (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
              (AccountAddress.ofUInt256 recipient)
              (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
              (UInt256.ofNat
                (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
                  value gas evmState.accountMap evmState.machineState evmState.substate))
              (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
              (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).2.2.1.toNat) ≤
            Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
              value gas evmState.accountMap evmState.machineState evmState.substate := by
        exact Nat.le_trans htheta
          (UInt256.toNat_ofNat_le
            (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
              value gas evmState.accountMap evmState.machineState evmState.substate))
      exact gas_sub_refund_decreases (lt_of_le_of_lt hretLe hcallgasLt) hgasCost
    · rcases h with ⟨_, hstate⟩
      rw [← hstate]
      simp
      have htheta := Theta_gas_le
        (blobVersionedHashes := blobVersionedHashes)
        (createdAccounts := evmState.createdAccounts)
        (genesisBlockHeader := evmState.genesisBlockHeader)
        (blocks := evmState.blocks)
        (σ := evmState.accountMap)
        (σ₀ := evmState.σ₀)
        (A := evmState.substate.addAccessedAccount (AccountAddress.ofUInt256 t))
        (s := AccountAddress.ofUInt256 source)
        (o := evmState.executionEnv.sender)
        (r := AccountAddress.ofUInt256 recipient)
        (c := toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (g := UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (p := UInt256.ofNat evmState.executionEnv.gasPrice)
        (v := value)
        (v' := value')
        (d := evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (e := evmState.executionEnv.depth + 1)
        (H := evmState.executionEnv.header)
        (w := permission)
      have hretLe :
          ((Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader evmState.blocks
              evmState.accountMap evmState.σ₀
              (evmState.substate.addAccessedAccount (AccountAddress.ofUInt256 t))
              (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
              (AccountAddress.ofUInt256 recipient)
              (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
              (UInt256.ofNat
                (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
                  value gas evmState.accountMap evmState.machineState evmState.substate))
              (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
              (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
              (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).2.2.1.toNat) ≤
            Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
              value gas evmState.accountMap evmState.machineState evmState.substate := by
        exact Nat.le_trans htheta
          (UInt256.toNat_ofNat_le
            (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
              value gas evmState.accountMap evmState.machineState evmState.substate))
      exact gas_sub_refund_decreases (lt_of_le_of_lt hretLe hcallgasLt) hgasCost
  · split at h
    · rcases h with ⟨_, hstate⟩
      rw [← hstate]
      simp
      have hofNat :=
        UInt256.toNat_ofNat_le
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate)
      exact gas_sub_refund_decreases (lt_of_le_of_lt hofNat hcallgasLt) hgasCost
    · rcases h with ⟨_, hstate⟩
      rw [← hstate]
      simp
      have hofNat :=
        UInt256.toNat_ofNat_le
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate)
      exact gas_sub_refund_decreases (lt_of_le_of_lt hofNat hcallgasLt) hgasCost

set_option linter.unusedSimpArgs false in
lemma step_gas_decreases_of_cost_eq_C'
    {gasCost : Nat} {w : Operation} {arg : Option (UInt256 × Nat)}
    {s s' : State}
    (hpos : 0 < gasCost)
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s w)
    (h : step gasCost (w, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat + 1 ≤ s.machineState.gasAvailable.toNat := by
  by_cases hnrec : RecursiveSystemStep w
  · cases w with
    | StopArith op => simp [RecursiveSystemStep] at hnrec
    | CompBit op => simp [RecursiveSystemStep] at hnrec
    | Keccak op => simp [RecursiveSystemStep] at hnrec
    | Env op => simp [RecursiveSystemStep] at hnrec
    | Block op => simp [RecursiveSystemStep] at hnrec
    | StackMemFlow op => simp [RecursiveSystemStep] at hnrec
    | Push op => simp [RecursiveSystemStep] at hnrec
    | Dup op => simp [RecursiveSystemStep] at hnrec
    | Exchange op => simp [RecursiveSystemStep] at hnrec
    | Log op => simp [RecursiveSystemStep] at hnrec
    | System op =>
        cases op with
        | CREATE => exact step_create_gas_decreases hpos hle h
        | CALL =>
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
                Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
                  (AccountAddress.ofUInt256 vPop.2.2.1) vPop.2.2.2.1 vPop.2.1
                  sExec.accountMap sExec.machineState sExec.substate < gasCost := by
              have hbase :
                  Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
                    (AccountAddress.ofUInt256 vPop.2.2.1) vPop.2.2.2.1 vPop.2.1
                    s.accountMap s.machineState s.substate <
                  Ccall (AccountAddress.ofUInt256 vPop.2.2.1)
                    (AccountAddress.ofUInt256 vPop.2.2.1) vPop.2.2.2.1 vPop.2.1
                    s.accountMap s.machineState s.substate :=
                Ccallgas_lt_Ccall _ _ _ _ _ _ _
              rw [hcost]
              simpa [sExec, C', Ccallgas, Cgascap, h0, h1, h2] using hbase
            have hdec := call_gas_decreases
              (evmState := sExec)
              (x := xCall)
              (state' := stateCall)
              (hgasCost := by simpa [sExec] using hle)
              (hcallgasLt := hcallgasLt)
              (h := by simpa [sExec] using hCall)
            rw [← h]
            simpa [sExec] using hdec
        | CALLCODE =>
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
                Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
                  (AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner.val))
                  vPop.2.2.2.1 vPop.2.1
                  sExec.accountMap sExec.machineState sExec.substate < gasCost := by
              have hbase :
                  Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
                    s.executionEnv.codeOwner vPop.2.2.2.1 vPop.2.1
                    s.accountMap s.machineState s.substate <
                  Ccall (AccountAddress.ofUInt256 vPop.2.2.1)
                    s.executionEnv.codeOwner vPop.2.2.2.1 vPop.2.1
                    s.accountMap s.machineState s.substate :=
                Ccallgas_lt_Ccall _ _ _ _ _ _ _
              rw [hcost]
              simpa [sExec, C', Ccallgas, Cgascap, h0, h1, h2,
                AccountAddress.ofUInt256_ofNat] using hbase
            have hdec := call_gas_decreases
              (evmState := sExec)
              (x := xCall)
              (state' := stateCall)
              (hgasCost := by simpa [sExec] using hle)
              (hcallgasLt := hcallgasLt)
              (h := by simpa [sExec] using hCall)
            rw [← h]
            simpa [sExec] using hdec
        | RETURN => simp [RecursiveSystemStep] at hnrec
        | DELEGATECALL =>
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
                Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
                  (AccountAddress.ofUInt256 (UInt256.ofNat s.executionEnv.codeOwner.val))
                  (⟨0⟩ : UInt256) vPop.2.1
                  sExec.accountMap sExec.machineState sExec.substate < gasCost := by
              have hbase :
                  Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
                    s.executionEnv.codeOwner (⟨0⟩ : UInt256) vPop.2.1
                    s.accountMap s.machineState s.substate <
                  Ccall (AccountAddress.ofUInt256 vPop.2.2.1)
                    s.executionEnv.codeOwner (⟨0⟩ : UInt256) vPop.2.1
                    s.accountMap s.machineState s.substate :=
                Ccallgas_lt_Ccall _ _ _ _ _ _ _
              rw [hcost]
              simpa [sExec, C', Ccallgas, Cgascap, h0, h1,
                AccountAddress.ofUInt256_ofNat] using hbase
            have hdec := call_gas_decreases
              (evmState := sExec)
              (x := xCall)
              (state' := stateCall)
              (hgasCost := by simpa [sExec] using hle)
              (hcallgasLt := hcallgasLt)
              (h := by simpa [sExec] using hCall)
            rw [← h]
            simpa [sExec] using hdec
        | CREATE2 => exact step_create2_gas_decreases hpos hle h
        | STATICCALL =>
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
                Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
                  (AccountAddress.ofUInt256 vPop.2.2.1)
                  (⟨0⟩ : UInt256) vPop.2.1
                  sExec.accountMap sExec.machineState sExec.substate < gasCost := by
              have hbase :
                  Ccallgas (AccountAddress.ofUInt256 vPop.2.2.1)
                    (AccountAddress.ofUInt256 vPop.2.2.1) (⟨0⟩ : UInt256) vPop.2.1
                    s.accountMap s.machineState s.substate <
                  Ccall (AccountAddress.ofUInt256 vPop.2.2.1)
                    (AccountAddress.ofUInt256 vPop.2.2.1) (⟨0⟩ : UInt256) vPop.2.1
                    s.accountMap s.machineState s.substate :=
                Ccallgas_lt_Ccall _ _ _ _ _ _ _
              rw [hcost]
              simpa [sExec, C', Ccallgas, Cgascap, h0, h1] using hbase
            have hdec := call_gas_decreases
              (evmState := sExec)
              (x := xCall)
              (state' := stateCall)
              (hgasCost := by simpa [sExec] using hle)
              (hcallgasLt := hcallgasLt)
              (h := by simpa [sExec] using hCall)
            rw [← h]
            simpa [sExec] using hdec
        | REVERT => simp [RecursiveSystemStep] at hnrec
        | INVALID => simp [RecursiveSystemStep] at hnrec
        | SELFDESTRUCT => simp [RecursiveSystemStep] at hnrec
  · rw [step_nonrecursive_gas hnrec h]
    rw [Sat256.natSub_toNat]
    omega

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
      cases op <;> simp at h <;>
      first 
      | split at h
        · simp at h
        · simp at h
      | simp [ContinuesAfterXStep, δ]
      · rename_i heq
        simp [Z,hdecode,δ] at heq

theorem Xstep_gas_decreases_of_continues
    {validJumps : Array UInt256} {state state' : State}
    (h : Xstep validJumps state = .ok (state', none)) :
    state'.machineState.gasAvailable.toNat + 1 ≤ state.machineState.gasAvailable.toNat := by
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨w, arg⟩
  have hcont : ContinuesAfterXStep
           (decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none)).1 :=
    Xstep_continues_of_halt_none h
  have hcont' : ContinuesAfterXStep w := by
    simpa [← hinstr] using hcont
  simp [Xstep, ← hinstr] at h
  split at h
  · contradiction
  · rename_i stateZ cost hZ
    simp [bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i stepped hstep
      have hZ' : Z validJumps w state = .ok (stateZ, cost) := by
        simpa [← hinstr] using hZ
      have hstep' :
          step cost (w, arg)
            { stateZ with executionEnv.depth := state.executionEnv.depth } = .ok stepped := by
        simpa [← hinstr] using hstep
      have hcostLe : cost ≤ stateZ.machineState.gasAvailable.toNat := Z_cost_le hZ'
      have hcostPos : 0 < cost := Z_cost_pos_of_continues hcont' hZ'
      have hcostEqStateZ : cost = C' stateZ w := Z_cost_eq_C' hZ'
      have hcostEqStep :
          cost = C' { stateZ with executionEnv.depth := state.executionEnv.depth } w := by
        rw [hcostEqStateZ]
        exact (C'_set_depth stateZ state.executionEnv.depth w).symm
      have hstepGas :
          stepped.machineState.gasAvailable.toNat + 1 ≤ stateZ.machineState.gasAvailable.toNat := by
        have hstepDecrease :=
          step_gas_decreases_of_cost_eq_C'
            (s := { stateZ with executionEnv.depth := state.executionEnv.depth })
            (hpos := hcostPos)
            (hle := by simpa using hcostLe)
            (hcost := hcostEqStep)
            (h := hstep')
        simpa using hstepDecrease
      have hstateZLe : stateZ.machineState.gasAvailable.toNat ≤ state.machineState.gasAvailable.toNat :=
        Z_state_gas_le hZ'
      split at h
      · injection h with hpair
        have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
          congrArg Prod.fst hpair
        rw [← hstateEq]
        simp
        exact Nat.le_trans hstepGas hstateZLe
      · split at h
        · injection h with hpair
          have hret := congrArg Prod.snd hpair
          simp at hret
        · injection h with hpair
          have hret := congrArg Prod.snd hpair
          simp at hret

end EVM

end Ethereum
