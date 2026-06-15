import Ethereum.Semantics
import Ethereum.Wheels
import Batteries.Data.RBMap.Lemmas

namespace Ethereum
namespace EVM

variable {blobVersionedHashes : List ByteArray}
variable {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
variable {genesisBlockHeader : BlockHeader}
variable {blocks : ProcessedBlocks}
variable {σ σ₀ σ' : AccountMap}
variable {A A' : Substate}
variable {s o r acc pc : AccountAddress}
variable {g g' p v v' : UInt256}
variable {d i o' : ByteArray}
variable {e : Fin 1025}
variable {H : BlockHeader}
variable {w z : Bool}
variable {ζ : Option ByteArray}
variable {f n : Nat}
variable {validJumps : Array UInt256}
variable {state state' : State}
variable {I : ExecutionEnv}

-- This accepts changes to previously nonexisting accounts
inductive unchanged (l : AccountAddress) (s s' : AccountMap) : Prop where
  | null :
    s.find? l = .none →
    -- s'.find? l = .none →
    unchanged l s s'
  | empty : ∀ acc,
    s.find? l = .some acc →
    acc.nonce = ⟨0⟩ → acc.code.size = 0 → acc.storage = default →
    unchanged l s s'
  | present : ∀ acc acc',
    -- Should I know that if the account exists at σ then
    -- it also exists at σ'?
    s.find? l  = .some acc →
    s'.find? l = .some acc' →
    acc.nonce  = acc'.nonce →
    acc.code  = acc'.code →
    acc.storage  = acc'.storage →
    acc.tstorage = acc'.tstorage →
    acc.balance ≤ acc'.balance →
    unchanged l s s'

theorem unchanged_rfl : ∀ l s,
  unchanged l s s := by
  intros l s
  match hacc : (s.find? l) with
  | some v => apply unchanged.present v v hacc hacc <;> rfl
  | none => apply unchanged.null hacc

theorem accountAddress_compare_ne_eq_of_ne {a b : AccountAddress}
    (h : a ≠ b) : compare a b ≠ .eq := by
  intro hcmp
  apply h
  apply Fin.ext
  exact Nat.compare_eq_eq.mp (by simpa [compare, instOrdAccountAddress] using hcmp)

theorem unchanged_insert_of_same_core
    (l k : AccountAddress) (s : AccountMap) (new : Account)
    (hnew : ∀ old, s.find? k = some old →
      old.nonce = new.nonce ∧ old.code = new.code ∧
      old.storage = new.storage ∧ old.tstorage = new.tstorage ∧ old.balance ≤ new.balance) :
    unchanged l s (s.insert k new) := by
  match hacc : s.find? l with
  | none =>
      exact unchanged.null hacc
  | some acc =>
      by_cases hcmp : compare l k = .eq
      · have hfind : s.find? k = some acc := by
          have hcongr := Batteries.RBMap.find?_congr s hcmp
          rw [hacc] at hcongr
          exact hcongr.symm
        have hfields := hnew acc hfind
        exact unchanged.present acc new hacc
          (Batteries.RBMap.find?_insert_of_eq s hcmp)
          hfields.1 hfields.2.1 hfields.2.2.1 hfields.2.2.2.1 hfields.2.2.2.2
      · apply unchanged.present acc acc hacc
          (by simp [Batteries.RBMap.find?_insert_of_ne s hcmp]; exact hacc)
        repeat rfl

theorem unchanged_insert_of_different_core
    (l k : AccountAddress) (s : AccountMap) (new : Account)
    (h_diff_acc : l ≠ k)
      :
    unchanged l s (s.insert k new) := by
  match hacc : s.find? l with
  | none =>
      exact unchanged.null hacc
  | some acc =>
        apply unchanged.present acc acc hacc
        · rw [Batteries.RBMap.find?_insert_of_ne]
          · exact hacc
          · simp [compare, compareOfLessAndEq]
            repeat (split; simp; grind)
        repeat rfl

theorem unchanged_trans : ∀ l s s' s'',
  unchanged l s s' → unchanged l s' s'' → unchanged l s s'' := by
  intros l s s' s'' hs hs'
  cases hs with
  | null hs1 =>
    apply unchanged.null hs1
  | empty acc hs1 hs2 hs3 hs4 =>
    apply unchanged.empty acc hs1 hs2 hs3 hs4
  | present acc1 acc2 hs1 hs2 eq1 eq2 eq3 eq4 =>
    cases hs' with
    | null hs'1 =>
      rw [hs'1] at hs2
      contradiction
    | empty acc' hs'1 hs'2 hs'3 hs'4 =>
      have : acc2 = acc' := by grind
      rw [← this] at hs'2 hs'3 hs'4
      rw [← eq1] at hs'2
      rw [← eq2] at hs'3
      rw [← eq3] at hs'4
      apply unchanged.empty acc1 hs1 hs'2 hs'3 hs'4
    | present acc1' acc2' hs'1 hs'2 eq1' eq2' b1 b2 =>
      apply unchanged.present
      · exact hs1
      · exact hs'2
      · grind
      · grind
      · grind
      · grind
      · grind

theorem unchanged_insert_insert_of_same_core
    (l k₁ k₂ : AccountAddress) (s : AccountMap)
    (new₁ new₂ : Account)
    (hnew₁ : ∀ old, s.find? k₁ = some old →
      old.nonce = new₁.nonce ∧ old.code = new₁.code ∧
      old.storage = new₁.storage ∧ old.tstorage = new₁.tstorage ∧ old.balance ≤ new₁.balance)
    (hnew₂ : ∀ old, (s.insert k₁ new₁).find? k₂ = some old →
      old.nonce = new₂.nonce ∧ old.code = new₂.code ∧
      old.storage = new₂.storage ∧ old.tstorage = new₂.tstorage ∧ old.balance ≤ new₂.balance) :
    unchanged l s ((s.insert k₁ new₁).insert k₂ new₂) :=
  unchanged_trans l s (s.insert k₁ new₁) ((s.insert k₁ new₁).insert k₂ new₂)
    (unchanged_insert_of_same_core l k₁ s new₁ hnew₁)
    (unchanged_insert_of_same_core l k₂ (s.insert k₁ new₁) new₂ hnew₂)

def sendEth (r s : AccountAddress) (v : UInt256) (z : Bool) (σ : AccountMap) : AccountMap :=
  if z then
    let σ'₁ := match Batteries.RBMap.find? σ r with
      | none =>
        if (v != UInt256.ofNat 0) = true then
          Batteries.RBMap.insert σ r
            (let __src := (default : Account);
            { nonce := __src.nonce, balance := v, storage := __src.storage, code := __src.code,
              tstorage := __src.tstorage })
        else σ
      | some acc =>
        Batteries.RBMap.insert σ r
          { nonce := acc.nonce, balance := acc.balance + v, storage := acc.storage, code := acc.code,
            tstorage := acc.tstorage };
    match σ'₁.find? s with
    | none => σ'₁
    | some acc =>
      σ'₁.insert s
        { nonce := acc.nonce, balance := acc.balance - v, storage := acc.storage, code := acc.code,
          tstorage := acc.tstorage }
  else σ

def sendEthCreate (a s : AccountAddress) (v : UInt256) (z : Bool) (σ : AccountMap) : AccountMap :=
  if z then
    let existentAccount := σ.findD a default

    let newAccount : Account :=
      { existentAccount with
          nonce := existentAccount.nonce + ⟨1⟩
          balance := v + existentAccount.balance
      }
    match σ.find? s with
      | none =>  σ
      | some ac =>
        σ.insert s {ac with balance := ac.balance - v}
          |>.insert a newAccount -- (99)
  else σ

@[simp] lemma sendEthCreate_false (a s : AccountAddress) (v : UInt256) (σ : AccountMap) :
    sendEthCreate a s v false σ = σ := by
  simp [sendEthCreate]

@[simp] lemma sendEthCreate_true_find?_none
    (a s : AccountAddress) (v : UInt256) (σ : AccountMap)
    (h : σ.find? s = none) :
    sendEthCreate a s v true σ = σ := by
  simp [sendEthCreate, h]

@[simp] lemma sendEthCreate_true_find?_some
    (a s : AccountAddress) (v : UInt256) (σ : AccountMap) (ac : Account)
    (h : σ.find? s = some ac) :
    sendEthCreate a s v true σ =
      (σ.insert s {ac with balance := ac.balance - v}).insert a
        { (σ.findD a default) with
          nonce := (σ.findD a default).nonce + ⟨1⟩
          balance := v + (σ.findD a default).balance } := by
  simp [sendEthCreate, h]

def account_dead (σ : AccountMap) (a : AccountAddress) : Prop :=
  match σ.find? a with
  | none => True
  | some acc => acc.nonce = ⟨0⟩ ∧ acc.code.size = 0 ∧ acc.storage = default

inductive account_change_consistent (acc : AccountAddress) : AccountMap → AccountMap → Prop where
  | unchanged {σ σ'}:
    unchanged acc σ σ'
    → account_change_consistent acc σ σ'

  | init_dead {σ σ'}:
    account_dead σ acc
    → account_change_consistent acc σ σ'

  | call_prelude {σ r s v z}:
    account_change_consistent acc σ (sendEth r s v z σ)

  | create_prelude {σ a s v z}:
    account_change_consistent acc σ (sendEthCreate a s v z σ)

  | by_own_code
    {blobVersionedHashes : List ByteArray}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap}
    {A A' : Substate}
    {s o : AccountAddress}
    {g g' p v v' : UInt256}
    {d o' : ByteArray}
    {e : Fin 1025}
    {H : BlockHeader}
    {w z : Bool} :
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀  A s o acc (toExecute σ acc) g p v v' d e H w = (createdAccounts', σ', g', A', z, o')
    → account_change_consistent acc (sendEth acc s v z σ) σ'

  | by_own_code_from_start
    {blobVersionedHashes : List ByteArray}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap}
    {A A' : Substate}
    {s o : AccountAddress}
    {g g' p v v' : UInt256}
    {d o' : ByteArray}
    {e : Fin 1025}
    {H : BlockHeader}
    {w z : Bool} :
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o acc
        (toExecute σ acc) g p v v' d e H w =
      (createdAccounts', σ', g', A', z, o')
    → account_change_consistent acc σ σ'

def account_changes_consistent (acc : AccountAddress) :=
  Relation.ReflTransGen (account_change_consistent acc)

private lemma rbNode_consume_self_stream {α} [BEq α] [ReflBEq α] :
    ∀ (xs : List α) (s : Batteries.RBNode.Stream α),
      s.toList = xs →
      (match StateT.run (s := s)
          (xs.forM (m := StateT (Batteries.RBNode.Stream α) Option) fun a s => do
            let (b, s) ← Batteries.RBNode.Stream.next? s
            bif a == b then some (PUnit.unit, s) else none) with
       | some (_, Batteries.RBNode.Stream.nil) => true
       | _ => false) = true := by
  intro xs
  induction xs with
  | nil =>
      intro s h
      cases s <;> simp [Batteries.RBNode.Stream.toList] at h ⊢
  | cons x xs ih =>
      intro s h
      cases s with
      | nil => simp [Batteries.RBNode.Stream.toList] at h
      | cons v r tail =>
          simp [Batteries.RBNode.Stream.toList, Batteries.RBNode.Stream.next?] at h ⊢
          rcases h with ⟨hv, htail⟩
          subst v
          have htailStream : (Batteries.RBNode.toStream r tail).toList = xs := by
            rw [Batteries.RBNode.toStream_toList']
            simpa [Batteries.RBNode.foldr_cons, Batteries.RBNode.Stream.toList] using htail
          simp only [StateT.run, BEq.rfl, cond_true, Option.bind_some]
          exact ih (Batteries.RBNode.toStream r tail) htailStream

private lemma rbNode_all₂_self {α} [BEq α] [ReflBEq α] (t : Batteries.RBNode α) :
    t.all₂ (· == ·) t = true := by
  unfold Batteries.RBNode.all₂
  rw [Batteries.RBNode.forM_eq_forM_toList]
  exact rbNode_consume_self_stream t.toList t.toStream (by simp)

private lemma rbSet_all₂_self {α} {cmp : α → α → Ordering} [BEq α] [ReflBEq α]
    (t : Batteries.RBSet α cmp) : t.all₂ (· == ·) t = true := by
  exact rbNode_all₂_self t.1

instance {α} {cmp : α → α → Ordering} [BEq α] [ReflBEq α] :
    ReflBEq (Batteries.RBSet α cmp) where
  rfl := by
    intro a
    exact rbSet_all₂_self a

instance instRBMapReflBEq{α β} {cmp : α → α → Ordering} [BEq α] [BEq β] [ReflBEq α] [ReflBEq β] :
    ReflBEq (Batteries.RBMap α β cmp) where
  rfl := by
    intro a
    exact rbSet_all₂_self a

@[simp] lemma rbMap_empty_beq_empty {α β} {cmp : α → α → Ordering} [BEq α] [BEq β] :
    ((∅ : Batteries.RBMap α β cmp) == ∅) = true := by
  rfl

lemma addr_neq_compare : ∀ (a b : AccountAddress), a ≠ b → ¬ compare a b = Ordering.eq := by
  intros a b hneq
  simp [compare, compareOfLessAndEq]
  split
  · simp
  · split
    · grind
    · simp

-- instance : ReflBEq AccountAddress := inferInstance
-- instance : ReflBEq Account := inferInstance
lemma account_changes_consistent_rfl :
    ∀ acc, account_changes_consistent acc σ σ := by
  intro
  simp [account_changes_consistent]
  apply Relation.ReflTransGen.single
  apply account_change_consistent.unchanged
  apply unchanged_rfl

lemma account_changes_consistent_insert_ne
    (acc k : AccountAddress) (σ : AccountMap) (new : Account)
    (h : acc ≠ k) :
    account_changes_consistent acc σ (σ.insert k new) := by
  simp [account_changes_consistent]
  apply Relation.ReflTransGen.single
  apply account_change_consistent.unchanged
  exact unchanged_insert_of_different_core acc k σ new h

lemma account_changes_consistent_of_accountMap_eq
    (acc : AccountAddress) {σ σ' : AccountMap}
    (h : σ' = σ) :
    account_changes_consistent acc σ σ' := by
  subst h
  exact account_changes_consistent_rfl acc

lemma account_changes_consistent_insert_same_core
    (acc k : AccountAddress) (σ : AccountMap) (new : Account)
    (hnew : ∀ old, σ.find? k = some old →
      old.nonce = new.nonce ∧ old.code = new.code ∧
      old.storage = new.storage ∧ old.tstorage = new.tstorage ∧ old.balance ≤ new.balance) :
    account_changes_consistent acc σ (σ.insert k new) := by
  simp [account_changes_consistent]
  apply Relation.ReflTransGen.single
  apply account_change_consistent.unchanged
  exact unchanged_insert_of_same_core acc k σ new hnew

lemma account_changes_consistent_insert_insert_same_core
    (acc k₁ k₂ : AccountAddress) (σ : AccountMap)
    (new₁ new₂ : Account)
    (hnew₁ : ∀ old, σ.find? k₁ = some old →
      old.nonce = new₁.nonce ∧ old.code = new₁.code ∧
      old.storage = new₁.storage ∧ old.tstorage = new₁.tstorage ∧ old.balance ≤ new₁.balance)
    (hnew₂ : ∀ old, (σ.insert k₁ new₁).find? k₂ = some old →
      old.nonce = new₂.nonce ∧ old.code = new₂.code ∧
      old.storage = new₂.storage ∧ old.tstorage = new₂.tstorage ∧ old.balance ≤ new₂.balance) :
    account_changes_consistent acc σ ((σ.insert k₁ new₁).insert k₂ new₂) := by
  simp [account_changes_consistent]
  apply Relation.ReflTransGen.single
  apply account_change_consistent.unchanged
  exact unchanged_insert_insert_of_same_core acc k₁ k₂ σ new₁ new₂ hnew₁ hnew₂

lemma account_changes_consistent_init_dead
    (hdead : account_dead σ acc) :
    account_changes_consistent acc σ σ' := by
  simp [account_changes_consistent]
  apply Relation.ReflTransGen.single
  exact account_change_consistent.init_dead hdead

lemma account_changes_consistent_sendEth_prelude
    (acc r s : AccountAddress) (v : UInt256) (z : Bool) (σ : AccountMap) :
    account_changes_consistent acc σ (sendEth r s v z σ) := by
  simp [account_changes_consistent]
  apply Relation.ReflTransGen.single
  exact account_change_consistent.call_prelude

lemma account_changes_consistent_sendEthCreate_prelude
    (acc a s : AccountAddress) (v : UInt256) (z : Bool) (σ : AccountMap) :
    account_changes_consistent acc σ (sendEthCreate a s v z σ) := by
  simp [account_changes_consistent]
  apply Relation.ReflTransGen.single
  exact account_change_consistent.create_prelude

lemma account_changes_consistent_trans
    (h₁ : account_changes_consistent acc σ σ')
    (h₂ : account_changes_consistent acc σ' σ₀) :
    account_changes_consistent acc σ σ₀ :=
  Relation.ReflTransGen.trans h₁ h₂

private lemma account_changes_consistent_insert_fresh_then_insert_ne
    (acc k owner : AccountAddress) (σ : AccountMap) (new newOwner : Account)
    (hk : σ.find? k = none) (hacc : acc ≠ owner) :
    account_changes_consistent acc σ ((σ.insert k new).insert owner newOwner) :=
  account_changes_consistent_trans
    (account_changes_consistent_insert_same_core acc k σ new
      (by
        intro old hold
        rw [hk] at hold
        contradiction))
    (account_changes_consistent_insert_ne acc owner (σ.insert k new) newOwner hacc)

private lemma sendEth_true_find?_some_find?_some_ne
    (r s : AccountAddress) (v : UInt256) (σ : AccountMap) (racc sacc : Account)
    (hr : σ.find? r = some racc) (hs : σ.find? s = some sacc) (hne : r ≠ s) :
    sendEth r s v true σ =
      (σ.insert r
          { nonce := racc.nonce, balance := racc.balance + v, storage := racc.storage,
            code := racc.code, tstorage := racc.tstorage }).insert s
        { nonce := sacc.nonce, balance := sacc.balance - v, storage := sacc.storage,
          code := sacc.code, tstorage := sacc.tstorage } := by
  have hcmp : compare s r ≠ .eq := accountAddress_compare_ne_eq_of_ne (by
    intro hsr
    exact hne hsr.symm)
  simp [sendEth, hr, Batteries.RBMap.find?_insert_of_ne, hcmp, hs]

@[simp] private lemma UInt256_sub_self (a : UInt256) :
    a - a = UInt256.ofNat 0 := by
  cases a with
  | mk v =>
      change ({ val := v - v } : UInt256) = { val := (0 : Fin UInt256.size) }
      simp

private lemma depth_succ_measure {e : Fin 1025} {n : Nat}
    (hdepth : 1024 - e.val = n + 1) (hlt : e < 1024) :
    1024 - (e + 1).val = n := by
  have hltVal : e.val < 1024 := by simpa using hlt
  have hval : (e + 1).val = e.val + 1 := by
    rw [Fin.val_add_eq_of_add_lt]
    simp
    omega
  omega

private lemma accountAddress_ofUInt256_ofNat (a : AccountAddress) :
    AccountAddress.ofUInt256 (UInt256.ofNat a.val) = a := by
  ext
  unfold AccountAddress.ofUInt256 UInt256.ofNat
  simp [Id.run, AccountAddress.size, UInt256.size]

private lemma account_changes_consistent_of_call_except_recipient_succ_depth
    {gasCost n : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State} {acc : AccountAddress}
    (hdepth : 1024 - evmState.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H w
        createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H w =
            (createdAccounts', σ', g', A', z, o') →
          acc ≠ r →
          account_changes_consistent acc σ σ')
    (hacc : acc ≠ AccountAddress.ofUInt256 recipient)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    account_changes_consistent acc evmState.accountMap state'.accountMap := by
  unfold call at h
  simp at h
  split at h
  · rename_i hcall
    rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp
    exact ihTheta
      blobVersionedHashes evmState.genesisBlockHeader evmState.blocks
      evmState.createdAccounts (evmState.executionEnv.depth + 1)
      evmState.accountMap evmState.σ₀
      ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
      (AccountAddress.ofUInt256 source)
      evmState.executionEnv.sender
      (AccountAddress.ofUInt256 recipient)
      (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
      (UInt256.ofNat
        (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
          value gas evmState.accountMap evmState.machineState evmState.substate))
      (UInt256.ofNat evmState.executionEnv.gasPrice)
      value value'
      (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
      evmState.executionEnv.header permission
      (Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader evmState.blocks
        evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).1
      (Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader evmState.blocks
        evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).2.1
      (Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader evmState.blocks
        evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).2.2.1
      (Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader evmState.blocks
        evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).2.2.2.1
      (Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader evmState.blocks
        evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).2.2.2.2.1
      (Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader evmState.blocks
        evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).2.2.2.2.2
      (depth_succ_measure hdepth hcall.2)
      rfl
      hacc
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp
    exact account_changes_consistent_rfl acc

private lemma account_changes_consistent_of_call_recipient_own_code_succ_depth
    {gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State} {acc : AccountAddress}
    (hsame : AccountAddress.ofUInt256 t = AccountAddress.ofUInt256 recipient)
    (hacc : acc = AccountAddress.ofUInt256 recipient)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    account_changes_consistent acc evmState.accountMap state'.accountMap := by
  subst acc
  unfold call at h
  simp at h
  split at h
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp
    rw [hsame]
    simp [account_changes_consistent]
    exact Relation.ReflTransGen.single
      (account_change_consistent.by_own_code_from_start rfl)
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp
    exact account_changes_consistent_rfl (AccountAddress.ofUInt256 recipient)

private lemma lambda_create_not_failed_bool
    (b : Bool) (P Q R S : Prop) [Decidable P] [Decidable Q] [Decidable R] [Decidable S] :
    (!b && (!decide P && (!decide Q && (!decide R || !decide S)))) =
      decide (¬ (b = true ∨ P ∨ Q ∨ R ∧ S)) := by
  by_cases hb : b = true <;> by_cases hP : P <;> by_cases hQ : Q <;>
    by_cases hR : R <;> by_cases hS : S <;> simp [hb, hP, hQ, hR, hS]

private lemma execUnOp_accountMap_eq
    {f : Primop.Unary} {state state' : State}
    (h : execUnOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold execUnOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

private lemma execBinOp_accountMap_eq
    {f : Primop.Binary} {state state' : State}
    (h : execBinOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold execBinOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

private lemma execTriOp_accountMap_eq
    {f : Primop.Ternary} {state state' : State}
    (h : execTriOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold execTriOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

private lemma machineStateOp_accountMap_eq
    {f : MachineState → UInt256} {state state' : State}
    (h : machineStateOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold machineStateOp at h
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

private lemma executionEnvOp_accountMap_eq
    {f : ExecutionEnv → UInt256} {state state' : State}
    (h : executionEnvOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold executionEnvOp at h
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

private lemma unaryExecutionEnvOp_accountMap_eq
    {f : ExecutionEnv → UInt256 → UInt256} {state state' : State}
    (h : unaryExecutionEnvOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold unaryExecutionEnvOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

private lemma unaryStateOp_sameState_accountMap_eq
    {f : State → UInt256 → UInt256} {state state' : State}
    (h : unaryStateOp (fun s v => (s, f s v)) state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold unaryStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

private lemma unaryStateOp_accountMap_eq
    {f : State → UInt256 → State × UInt256} {state state' : State}
    (hf : ∀ s v, (f s v).1.accountMap = s.accountMap)
    (h : unaryStateOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold unaryStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hf]

private lemma stateOp_accountMap_eq
    {f : State → UInt256} {state state' : State}
    (h : stateOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold stateOp at h
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

private lemma binaryMachineStateOp_accountMap_eq
    {f : MachineState → UInt256 → UInt256 → MachineState} {state state' : State}
    (h : binaryMachineStateOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold binaryMachineStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

private lemma binaryMachineStateOp'_accountMap_eq
    {f : MachineState → UInt256 → UInt256 → UInt256 × MachineState} {state state' : State}
    (h : binaryMachineStateOp' f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold binaryMachineStateOp' at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

private lemma ternaryMachineStateOp_accountMap_eq
    {f : MachineState → UInt256 → UInt256 → UInt256 → MachineState} {state state' : State}
    (h : ternaryMachineStateOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold ternaryMachineStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

private lemma ternaryCopyOp_accountMap_eq
    {f : State → UInt256 → UInt256 → UInt256 → State} {state state' : State}
    (hcopy : ∀ s a b c, (f s a b c).accountMap = s.accountMap)
    (h : ternaryCopyOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold ternaryCopyOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hcopy]

private lemma quaternaryCopyOp_accountMap_eq
    {f : State → UInt256 → UInt256 → UInt256 → UInt256 → State} {state state' : State}
    (hcopy : ∀ s a b c d, (f s a b c d).accountMap = s.accountMap)
    (h : quaternaryCopyOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold quaternaryCopyOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hcopy]

private lemma calldatacopy_accountMap_eq
    (state : State) (mstart datastart size : UInt256) :
    (calldatacopy state mstart datastart size).accountMap = state.accountMap := by
  simp [calldatacopy]

private lemma codeCopy_accountMap_eq
    (state : State) (mstart cstart size : UInt256) :
    (codeCopy state mstart cstart size).accountMap = state.accountMap := by
  simp [codeCopy]

private lemma extCodeCopy'_accountMap_eq
    (state : State) (a mstart cstart size : UInt256) :
    (extCodeCopy' state a mstart cstart size).accountMap = state.accountMap := by
  simp [extCodeCopy', Ethereum.State.lookupAccount]

private lemma sstore_account_changes_consistent_ne
    {state : State} {acc : AccountAddress} (key value : UInt256)
    (hacc : acc ≠ state.executionEnv.codeOwner) :
    account_changes_consistent acc state.accountMap
      (Ethereum.State.sstore state key value).accountMap := by
  cases hfind : state.accountMap.find? state.executionEnv.codeOwner with
  | none =>
      simp [Ethereum.State.sstore, Ethereum.State.lookupAccount, hfind]
      exact account_changes_consistent_rfl acc
  | some owner =>
      simp [Ethereum.State.sstore, Ethereum.State.lookupAccount,
        Ethereum.State.setAccount, Ethereum.State.addAccessedStorageKey, hfind]
      split
      · exact account_changes_consistent_insert_ne acc state.executionEnv.codeOwner _ _ hacc
      · exact account_changes_consistent_insert_ne acc state.executionEnv.codeOwner _ _ hacc

private lemma tstore_account_changes_consistent_ne
    {state : State} {acc : AccountAddress} (key value : UInt256)
    (hacc : acc ≠ state.executionEnv.codeOwner) :
    account_changes_consistent acc state.accountMap
      (Ethereum.State.tstore state key value).accountMap := by
  cases hfind : state.accountMap.find? state.executionEnv.codeOwner with
  | none =>
      simp [Ethereum.State.tstore, Ethereum.State.lookupAccount, hfind]
      exact account_changes_consistent_rfl acc
  | some owner =>
      simp [Ethereum.State.tstore, Ethereum.State.lookupAccount,
        Ethereum.State.updateAccount, hfind]
      exact account_changes_consistent_insert_ne acc state.executionEnv.codeOwner _ _ hacc

private lemma binaryStateOp_account_changes_consistent
    {op : State → UInt256 → UInt256 → State} {state state' : State} {acc : AccountAddress}
    (hop : ∀ a b, account_changes_consistent acc state.accountMap (op state a b).accountMap)
    (h : binaryStateOp op state = .ok state') :
    account_changes_consistent acc state.accountMap state'.accountMap := by
  unfold binaryStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  exact hop _ _

private lemma dup_accountMap_eq
    {n : Nat} {state state' : State}
    (h : dup n state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold dup at h
  by_cases hlen : (List.take n state.machineState.stack).length = n
  · rw [if_pos hlen] at h
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
  · rw [if_neg hlen] at h
    contradiction

private lemma swap_accountMap_eq
    {n : Nat} {state state' : State}
    (h : swap n state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold swap at h
  by_cases hlen : (List.take (n + 1) state.machineState.stack).length = n + 1
  · rw [if_pos hlen] at h
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
  · rw [if_neg hlen] at h
    contradiction

private lemma logOp_accountMap_eq
    {μ₀ μ₁ : UInt256} {topics : Array UInt256} {state : State} :
    (logOp μ₀ μ₁ topics state).accountMap = state.accountMap := by
  simp [logOp]

private lemma evmLogOp_accountMap_eq
    {μ₀ μ₁ : UInt256} {topics : Array UInt256} {state : State} :
    (evmLogOp state μ₀ μ₁ topics).accountMap = state.accountMap := by
  simp [evmLogOp, logOp_accountMap_eq]

private lemma step_stoparith_accountMap_eq
    {op : Operation.SAOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.StopArith op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op with
  | STOP =>
      simp [step] at h
      rw [← h]
  | ADD =>
      simp [step] at h
      have hm := execBinOp_accountMap_eq h
      simpa using hm
  | MUL =>
      simp [step] at h
      have hm := execBinOp_accountMap_eq h
      simpa using hm
  | SUB =>
      simp [step] at h
      have hm := execBinOp_accountMap_eq h
      simpa using hm
  | DIV =>
      simp [step] at h
      have hm := execBinOp_accountMap_eq h
      simpa using hm
  | SDIV =>
      simp [step] at h
      have hm := execBinOp_accountMap_eq h
      simpa using hm
  | MOD =>
      simp [step] at h
      have hm := execBinOp_accountMap_eq h
      simpa using hm
  | SMOD =>
      simp [step] at h
      have hm := execBinOp_accountMap_eq h
      simpa using hm
  | ADDMOD =>
      simp [step] at h
      have hm := execTriOp_accountMap_eq h
      simpa using hm
  | MULMOD =>
      simp [step] at h
      have hm := execTriOp_accountMap_eq h
      simpa using hm
  | EXP =>
      simp [step] at h
      have hm := execBinOp_accountMap_eq h
      simpa using hm
  | SIGNEXTEND =>
      simp [step] at h
      have hm := execBinOp_accountMap_eq h
      simpa using hm

private lemma step_compbit_accountMap_eq
    {op : Operation.CBLOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.CompBit op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op <;> simp [step] at h
  · have hm := execBinOp_accountMap_eq h; simpa using hm
  · have hm := execBinOp_accountMap_eq h; simpa using hm
  · have hm := execBinOp_accountMap_eq h; simpa using hm
  · have hm := execBinOp_accountMap_eq h; simpa using hm
  · have hm := execBinOp_accountMap_eq h; simpa using hm
  · have hm := execUnOp_accountMap_eq h; simpa using hm
  · have hm := execBinOp_accountMap_eq h; simpa using hm
  · have hm := execBinOp_accountMap_eq h; simpa using hm
  · have hm := execBinOp_accountMap_eq h; simpa using hm
  · have hm := execUnOp_accountMap_eq h; simpa using hm
  · have hm := execBinOp_accountMap_eq h; simpa using hm
  · have hm := execBinOp_accountMap_eq h; simpa using hm
  · have hm := execBinOp_accountMap_eq h; simpa using hm
  · have hm := execBinOp_accountMap_eq h; simpa using hm

private lemma step_keccak_accountMap_eq
    {op : Operation.KOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.Keccak op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op
  simp [step] at h
  have hm := binaryMachineStateOp'_accountMap_eq h
  simpa using hm

private lemma step_env_accountMap_eq
    {op : Operation.EOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.Env op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op <;> simp [step] at h
  · have hm := executionEnvOp_accountMap_eq h; simpa using hm
  · have hm := unaryStateOp_accountMap_eq
      (f := Ethereum.State.balance)
      (by intro s v; simp [Ethereum.State.balance, Ethereum.State.addAccessedAccount])
      h
    simpa using hm
  · have hm := executionEnvOp_accountMap_eq h; simpa using hm
  · have hm := executionEnvOp_accountMap_eq h; simpa using hm
  · have hm := executionEnvOp_accountMap_eq h; simpa using hm
  · have hm := unaryStateOp_sameState_accountMap_eq h; simpa using hm
  · have hm := executionEnvOp_accountMap_eq h; simpa using hm
  · have hm := ternaryCopyOp_accountMap_eq calldatacopy_accountMap_eq h; simpa using hm
  · have hm := executionEnvOp_accountMap_eq h; simpa using hm
  · have hm := executionEnvOp_accountMap_eq h; simpa using hm
  · have hm := ternaryCopyOp_accountMap_eq codeCopy_accountMap_eq h; simpa using hm
  · have hm := unaryStateOp_accountMap_eq
      (f := Ethereum.State.extCodeSize)
      (by intro s v; simp [Ethereum.State.extCodeSize, Ethereum.State.addAccessedAccount])
      h
    simpa using hm
  · have hm := quaternaryCopyOp_accountMap_eq extCodeCopy'_accountMap_eq h; simpa using hm
  · have hm := machineStateOp_accountMap_eq h; simpa using hm
  · split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
  · have hm := unaryStateOp_accountMap_eq
      (f := Ethereum.State.extCodeHash)
      (by
        intro s v
        simp [Ethereum.State.extCodeHash, Ethereum.State.addAccessedAccount,
          Ethereum.State.lookupAccount]
        split <;> simp)
      h
    simpa using hm

private lemma step_push_accountMap_eq
    {op : Operation.POp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.Push op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op with
  | PUSH0 =>
      simp [step, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
      rw [← h]
  | PUSH1 | PUSH2 | PUSH3 | PUSH4 | PUSH5 | PUSH6 | PUSH7 | PUSH8 | PUSH9 | PUSH10
  | PUSH11 | PUSH12 | PUSH13 | PUSH14 | PUSH15 | PUSH16 | PUSH17 | PUSH18 | PUSH19 | PUSH20
  | PUSH21 | PUSH22 | PUSH23 | PUSH24 | PUSH25 | PUSH26 | PUSH27 | PUSH28 | PUSH29 | PUSH30
  | PUSH31 | PUSH32 =>
      simp [step, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
      split at h <;> try contradiction
      injection h with hstate
      rw [← hstate]

private lemma step_dup_accountMap_eq
    {op : Operation.DOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.Dup op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op <;> simp [step] at h
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm
  · have hm := dup_accountMap_eq h; simpa using hm

private lemma step_exchange_accountMap_eq
    {op : Operation.ExOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.Exchange op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op <;> simp [step] at h
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm
  · have hm := swap_accountMap_eq h; simpa using hm

private lemma step_block_accountMap_eq
    {op : Operation.BOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.Block op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op <;> simp [step] at h
  · have hm := unaryStateOp_sameState_accountMap_eq h; simpa using hm
  · have hm := stateOp_accountMap_eq h; simpa using hm
  · have hm := stateOp_accountMap_eq h; simpa using hm
  · have hm := stateOp_accountMap_eq h; simpa using hm
  · have hm := executionEnvOp_accountMap_eq h; simpa using hm
  · have hm := stateOp_accountMap_eq h; simpa using hm
  · have hm := stateOp_accountMap_eq h; simpa using hm
  · have hm := stateOp_accountMap_eq h; simpa using hm
  · have hm := executionEnvOp_accountMap_eq h; simpa using hm
  · have hm := unaryExecutionEnvOp_accountMap_eq h; simpa using hm
  · have hm := executionEnvOp_accountMap_eq h; simpa using hm

private lemma step_log_accountMap_eq
    {op : Operation.LOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.Log op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op <;>
    simp [step, log0Op, log1Op, log2Op, log3Op, log4Op, evmLogOp,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    simp [logOp]

private lemma step_stackmemflow_consistent_except_owner
    {op : Operation.SMSFOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State} {acc : AccountAddress}
    (hacc : acc ≠ state.executionEnv.codeOwner)
    (h : step gasCost (.StackMemFlow op, arg) state = .ok state') :
    account_changes_consistent acc state.accountMap state'.accountMap := by
  cases op <;> simp [step] at h
  · split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    exact account_changes_consistent_rfl acc
  · split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    exact account_changes_consistent_rfl acc
  · have hm := binaryMachineStateOp_accountMap_eq h
    exact account_changes_consistent_of_accountMap_eq acc (by simpa using hm)
  · have hm := unaryStateOp_accountMap_eq
      (f := Ethereum.State.sload)
      (by
        intro s v
        simp [Ethereum.State.sload, Ethereum.State.addAccessedStorageKey,
          Ethereum.State.lookupAccount])
      h
    exact account_changes_consistent_of_accountMap_eq acc (by simpa using hm)
  · have hloc := binaryStateOp_account_changes_consistent
      (op := Ethereum.State.sstore) (acc := acc)
      (hop := fun a b => sstore_account_changes_consistent_ne a b (by simpa using hacc))
      h
    simpa using hloc
  · have hm := binaryMachineStateOp_accountMap_eq h
    exact account_changes_consistent_of_accountMap_eq acc (by simpa using hm)
  · split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    exact account_changes_consistent_rfl acc
  · split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    exact account_changes_consistent_rfl acc
  · rw [← h]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    exact account_changes_consistent_rfl acc
  · have hm := machineStateOp_accountMap_eq h
    exact account_changes_consistent_of_accountMap_eq acc (by simpa using hm)
  · have hm := machineStateOp_accountMap_eq h
    exact account_changes_consistent_of_accountMap_eq acc (by simpa using hm)
  · rw [← h]
    simp [Ethereum.State.incrPC]
    exact account_changes_consistent_rfl acc
  · have hm := unaryStateOp_accountMap_eq
      (f := Ethereum.State.tload)
      (by intro s v; simp [Ethereum.State.tload])
      h
    exact account_changes_consistent_of_accountMap_eq acc (by simpa using hm)
  · have hloc := binaryStateOp_account_changes_consistent
      (op := Ethereum.State.tstore) (acc := acc)
      (hop := fun a b => tstore_account_changes_consistent_ne a b (by simpa using hacc))
      h
    simpa using hloc
  · have hm := ternaryMachineStateOp_accountMap_eq h
    exact account_changes_consistent_of_accountMap_eq acc (by simpa using hm)

private lemma step_system_consistent_except_owner_max_depth
    {op : Operation.SOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State} {acc : AccountAddress}
    (hdepth : state.executionEnv.depth = 1024)
    (hacc : acc ≠ state.executionEnv.codeOwner)
    (h : step gasCost (.System op, arg) state = .ok state') :
    account_changes_consistent acc state.accountMap state'.accountMap := by
  cases op
  · simp [step, hdepth, bind, Except.bind] at h
    repeat split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    exact account_changes_consistent_rfl acc
  · simp [step, call, hdepth, bind, Except.bind] at h
    repeat split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    exact account_changes_consistent_rfl acc
  · simp [step, call, hdepth, bind, Except.bind] at h
    repeat split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    exact account_changes_consistent_rfl acc
  · simp [step] at h
    have hm := binaryMachineStateOp_accountMap_eq h
    exact account_changes_consistent_of_accountMap_eq acc (by simpa using hm)
  · simp [step, call, hdepth, bind, Except.bind] at h
    repeat split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    exact account_changes_consistent_rfl acc
  · simp [step, hdepth, bind, Except.bind] at h
    repeat split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    exact account_changes_consistent_rfl acc
  · simp [step, call, hdepth, bind, Except.bind] at h
    repeat split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    exact account_changes_consistent_rfl acc
  · simp [step] at h
    have hm := binaryMachineStateOp_accountMap_eq h
    exact account_changes_consistent_of_accountMap_eq acc (by simpa using hm)
  · simp [step] at h
  · simp [step, Ethereum.State.lookupAccount] at h
    cases hpop : state.machineState.stack.pop with
    | none =>
        simp [hpop] at h
    | some popped =>
        rcases popped with ⟨stack, targetWord⟩
        let target : AccountAddress := AccountAddress.ofUInt256 targetWord
        by_cases hcreated : state.executionEnv.codeOwner ∈ state.createdAccounts
        · cases howner : state.accountMap.find? state.executionEnv.codeOwner with
          | none =>
              simp [hpop, hcreated, howner] at h
              rw [← h]
              simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
              exact account_changes_consistent_rfl acc
          | some ownerAcc =>
              cases htarget : state.accountMap.find? target with
              | none =>
                  by_cases hzero : (ownerAcc.balance == { val := 0 }) = true
                  · simp [hpop, hcreated, howner, hzero] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, htarget]
                    exact account_changes_consistent_rfl acc
                  · simp [hpop, hcreated, howner, hzero] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, htarget]
                    exact account_changes_consistent_insert_fresh_then_insert_ne
                      acc target state.executionEnv.codeOwner state.accountMap
                      ({(default : Account) with balance := ownerAcc.balance})
                      ({ownerAcc with balance := UInt256.ofNat 0})
                      htarget hacc
              | some targetAcc =>
                  by_cases hsame : target = state.executionEnv.codeOwner
                  · simp [hpop, hcreated, howner] at h
                    rw [← h]
                    have htargetAcc : ownerAcc = targetAcc := by
                      simpa [hsame, howner] using htarget
                    subst targetAcc
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, howner, hsame]
                    have h₁ := account_changes_consistent_insert_ne
                      acc state.executionEnv.codeOwner state.accountMap
                      ({ownerAcc with balance := UInt256.ofNat 0}) hacc
                    have h₂ := account_changes_consistent_insert_ne
                      acc state.executionEnv.codeOwner
                      (state.accountMap.insert state.executionEnv.codeOwner
                        {ownerAcc with balance := UInt256.ofNat 0})
                      ({ownerAcc with balance := UInt256.ofNat 0}) hacc
                    exact account_changes_consistent_trans h₁ h₂
                  · simp [hpop, hcreated, howner] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, htarget, hsame]
                    have hpre := account_changes_consistent_sendEth_prelude
                      acc target state.executionEnv.codeOwner ownerAcc.balance true state.accountMap
                    rw [sendEth_true_find?_some_find?_some_ne
                      target state.executionEnv.codeOwner ownerAcc.balance state.accountMap
                      targetAcc ownerAcc htarget howner hsame] at hpre
                    simpa using hpre
        · cases howner : state.accountMap.find? state.executionEnv.codeOwner with
          | none =>
              simp [hpop, hcreated, howner] at h
              rw [← h]
              simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
              exact account_changes_consistent_rfl acc
          | some ownerAcc =>
              cases htarget : state.accountMap.find? target with
              | none =>
                  by_cases hzero : (ownerAcc.balance == { val := 0 }) = true
                  · simp [hpop, hcreated, howner, hzero] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, htarget]
                    exact account_changes_consistent_rfl acc
                  · simp [hpop, hcreated, howner, hzero] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, htarget]
                    exact account_changes_consistent_insert_fresh_then_insert_ne
                      acc target state.executionEnv.codeOwner state.accountMap
                      ({(default : Account) with balance := ownerAcc.balance})
                      ({ownerAcc with balance := UInt256.ofNat 0})
                      htarget hacc
              | some targetAcc =>
                  by_cases hsame : target = state.executionEnv.codeOwner
                  · simp [hpop, hcreated, howner] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, howner, hsame]
                    exact account_changes_consistent_rfl acc
                  · simp [hpop, hcreated, howner] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, htarget, hsame]
                    have hpre := account_changes_consistent_sendEth_prelude
                      acc target state.executionEnv.codeOwner ownerAcc.balance true state.accountMap
                    rw [sendEth_true_find?_some_find?_some_ne
                      target state.executionEnv.codeOwner ownerAcc.balance state.accountMap
                      targetAcc ownerAcc htarget howner hsame] at hpre
                    simpa using hpre

set_option maxHeartbeats 1000000 in
private lemma step_system_consistent_except_owner_succ_depth
    {op : Operation.SOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State} {acc : AccountAddress}
    (hdepth : 1024 - state.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H w
        createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H w =
            (createdAccounts', σ', g', A', z, o') →
          acc ≠ r →
          account_changes_consistent acc σ σ')
    (ihLambda : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o g p v i ζ H w
        a createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o g p v i e ζ H w =
            (a, createdAccounts', σ', g', A', z, o') →
          account_changes_consistent acc σ σ')
    (hacc : acc ≠ state.executionEnv.codeOwner)
    (h : step gasCost (.System op, arg) state = .ok state') :
    account_changes_consistent acc state.accountMap state'.accountMap := by
  cases op
  · simp [step] at h
    cases hpop : state.machineState.stack.pop3 with
    | none =>
        simp [hpop] at h
    | some popped =>
        rcases popped with ⟨stack, μ₀, μ₁, μ₂⟩
        let owner : Account :=
          (state.accountMap.find? state.executionEnv.codeOwner).getD default
        let σStar : AccountMap :=
          state.accountMap.insert state.executionEnv.codeOwner
            {owner with nonce := owner.nonce + ⟨1⟩}
        by_cases hnonce :
            ((state.accountMap.find? state.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1
        · simp [hpop] at h
          repeat split at h <;> try contradiction
          all_goals
            injection h with hstate
            rw [← hstate]
            simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
            exact account_changes_consistent_rfl acc
        · by_cases hDepth :
              μ₀ ≤ (state.accountMap.find? state.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
                state.executionEnv.depth < 1024 ∧
                (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152
          · simp [hpop, hDepth] at h
            repeat split at h <;> try contradiction
            all_goals
              injection h with hstate
              rw [← hstate]
              simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
            all_goals
              first
              |
                have hpre :
                    account_changes_consistent acc state.accountMap σStar :=
                  account_changes_consistent_insert_ne acc state.executionEnv.codeOwner
                    state.accountMap {owner with nonce := owner.nonce + ⟨1⟩} hacc
                have hmeasure :
                    1024 -
                        (⟨state.executionEnv.depth.val + 1,
                          Nat.succ_lt_succ hDepth.2.1⟩ : Fin 1025).val = n := by
                  simp
                  omega
                have hrec :
                    account_changes_consistent acc σStar
                      (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                        state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                        state.executionEnv.codeOwner state.executionEnv.sender
                        (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                        (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                        (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                        ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                        none state.executionEnv.header state.executionEnv.perm).2.2.1 := by
                  exact ihLambda
                    state.executionEnv.blobVersionedHashes state.genesisBlockHeader state.blocks
                    state.createdAccounts
                    ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                    σStar state.σ₀ state.substate
                    state.executionEnv.codeOwner state.executionEnv.sender
                    (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                    (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                    (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                    none state.executionEnv.header state.executionEnv.perm
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      none state.executionEnv.header state.executionEnv.perm).1
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      none state.executionEnv.header state.executionEnv.perm).2.1
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      none state.executionEnv.header state.executionEnv.perm).2.2.1
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      none state.executionEnv.header state.executionEnv.perm).2.2.2.1
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      none state.executionEnv.header state.executionEnv.perm).2.2.2.2.1
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      none state.executionEnv.header state.executionEnv.perm).2.2.2.2.2.1
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      none state.executionEnv.header state.executionEnv.perm).2.2.2.2.2.2
                    hmeasure
                    rfl
                exact account_changes_consistent_trans hpre hrec
          · simp [hpop, hDepth] at h
            repeat split at h <;> try contradiction
            all_goals
              injection h with hstate
              rw [← hstate]
              simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
              exact account_changes_consistent_rfl acc
  · simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at h <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    by_cases hrecipient : acc = AccountAddress.ofUInt256 μ₁
    · exact account_changes_consistent_of_call_recipient_own_code_succ_depth
        (recipient := μ₁)
        (t := μ₁)
        (evmState := {state with
          machineState := {state.machineState with execLength := state.machineState.execLength + 1}})
        rfl hrecipient hcall
    · exact account_changes_consistent_of_call_except_recipient_succ_depth
        (n := n)
        (recipient := μ₁)
        (evmState := {state with
          machineState := {state.machineState with execLength := state.machineState.execLength + 1}})
        hdepth ihTheta hrecipient hcall
  · simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at h <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    exact account_changes_consistent_of_call_except_recipient_succ_depth
      (n := n)
      (recipient := UInt256.ofNat ↑state.executionEnv.codeOwner)
      (evmState := {state with
        machineState := {state.machineState with execLength := state.machineState.execLength + 1}})
      hdepth ihTheta
      (by simpa [accountAddress_ofUInt256_ofNat] using hacc)
      hcall
  · simp [step] at h
    have hm := binaryMachineStateOp_accountMap_eq h
    exact account_changes_consistent_of_accountMap_eq acc (by simpa using hm)
  · simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at h <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    exact account_changes_consistent_of_call_except_recipient_succ_depth
      (n := n)
      (recipient := UInt256.ofNat ↑state.executionEnv.codeOwner)
      (evmState := {state with
        machineState := {state.machineState with execLength := state.machineState.execLength + 1}})
      hdepth ihTheta
      (by simpa [accountAddress_ofUInt256_ofNat] using hacc)
      hcall
  · simp [step] at h
    cases hpop : state.machineState.stack.pop4 with
    | none =>
        simp [hpop] at h
    | some popped =>
        rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃⟩
        let owner : Account :=
          (state.accountMap.find? state.executionEnv.codeOwner).getD default
        let σStar : AccountMap :=
          state.accountMap.insert state.executionEnv.codeOwner
            {owner with nonce := owner.nonce + ⟨1⟩}
        by_cases hnonce :
            ((state.accountMap.find? state.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1
        · simp [hpop] at h
          repeat split at h <;> try contradiction
          all_goals
            injection h with hstate
            rw [← hstate]
            simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
            exact account_changes_consistent_rfl acc
        · by_cases hDepth :
              μ₀ ≤ (state.accountMap.find? state.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
                state.executionEnv.depth < 1024 ∧
                (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152
          · simp [hpop, hDepth] at h
            repeat split at h <;> try contradiction
            all_goals
              injection h with hstate
              rw [← hstate]
              simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
            all_goals
              first
              |
                have hpre :
                    account_changes_consistent acc state.accountMap σStar :=
                  account_changes_consistent_insert_ne acc state.executionEnv.codeOwner
                    state.accountMap {owner with nonce := owner.nonce + ⟨1⟩} hacc
                have hmeasure :
                    1024 -
                        (⟨state.executionEnv.depth.val + 1,
                          Nat.succ_lt_succ hDepth.2.1⟩ : Fin 1025).val = n := by
                  simp
                  omega
                have hrec :
                    account_changes_consistent acc σStar
                      (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                        state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                        state.executionEnv.codeOwner state.executionEnv.sender
                        (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                        (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                        (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                        ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                        (some (UInt256.toByteArray μ₃)) state.executionEnv.header
                        state.executionEnv.perm).2.2.1 := by
                  exact ihLambda
                    state.executionEnv.blobVersionedHashes state.genesisBlockHeader state.blocks
                    state.createdAccounts
                    ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                    σStar state.σ₀ state.substate
                    state.executionEnv.codeOwner state.executionEnv.sender
                    (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                    (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                    (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                    (some (UInt256.toByteArray μ₃)) state.executionEnv.header state.executionEnv.perm
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      (some (UInt256.toByteArray μ₃)) state.executionEnv.header
                      state.executionEnv.perm).1
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      (some (UInt256.toByteArray μ₃)) state.executionEnv.header
                      state.executionEnv.perm).2.1
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      (some (UInt256.toByteArray μ₃)) state.executionEnv.header
                      state.executionEnv.perm).2.2.1
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      (some (UInt256.toByteArray μ₃)) state.executionEnv.header
                      state.executionEnv.perm).2.2.2.1
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      (some (UInt256.toByteArray μ₃)) state.executionEnv.header
                      state.executionEnv.perm).2.2.2.2.1
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      (some (UInt256.toByteArray μ₃)) state.executionEnv.header
                      state.executionEnv.perm).2.2.2.2.2.1
                    (Lambda state.executionEnv.blobVersionedHashes state.createdAccounts
                      state.genesisBlockHeader state.blocks σStar state.σ₀ state.substate
                      state.executionEnv.codeOwner state.executionEnv.sender
                      (UInt256.ofNat (L (state.machineState.gasAvailable.toNat - gasCost)))
                      (UInt256.ofNat state.executionEnv.gasPrice) μ₀
                      (state.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat)
                      ⟨state.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
                      (some (UInt256.toByteArray μ₃)) state.executionEnv.header
                      state.executionEnv.perm).2.2.2.2.2.2
                    hmeasure
                    rfl
                exact account_changes_consistent_trans hpre hrec
          · simp [hpop, hDepth] at h
            repeat split at h <;> try contradiction
            all_goals
              injection h with hstate
              rw [← hstate]
              simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
              exact account_changes_consistent_rfl acc
  · simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at h <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    by_cases hrecipient : acc = AccountAddress.ofUInt256 μ₁
    · exact account_changes_consistent_of_call_recipient_own_code_succ_depth
        (recipient := μ₁)
        (t := μ₁)
        (evmState := {state with
          machineState := {state.machineState with execLength := state.machineState.execLength + 1}})
        rfl hrecipient hcall
    · exact account_changes_consistent_of_call_except_recipient_succ_depth
        (n := n)
        (recipient := μ₁)
        (evmState := {state with
          machineState := {state.machineState with execLength := state.machineState.execLength + 1}})
        hdepth ihTheta hrecipient hcall
  · simp [step] at h
    have hm := binaryMachineStateOp_accountMap_eq h
    exact account_changes_consistent_of_accountMap_eq acc (by simpa using hm)
  · simp [step] at h
  · simp [step, Ethereum.State.lookupAccount] at h
    cases hpop : state.machineState.stack.pop with
    | none =>
        simp [hpop] at h
    | some popped =>
        rcases popped with ⟨stack, targetWord⟩
        let target : AccountAddress := AccountAddress.ofUInt256 targetWord
        by_cases hcreated : state.executionEnv.codeOwner ∈ state.createdAccounts
        · cases howner : state.accountMap.find? state.executionEnv.codeOwner with
          | none =>
              simp [hpop, hcreated, howner] at h
              rw [← h]
              simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
              exact account_changes_consistent_rfl acc
          | some ownerAcc =>
              cases htarget : state.accountMap.find? target with
              | none =>
                  by_cases hzero : (ownerAcc.balance == { val := 0 }) = true
                  · simp [hpop, hcreated, howner, hzero] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, htarget]
                    exact account_changes_consistent_rfl acc
                  · simp [hpop, hcreated, howner, hzero] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, htarget]
                    exact account_changes_consistent_insert_fresh_then_insert_ne
                      acc target state.executionEnv.codeOwner state.accountMap
                      ({(default : Account) with balance := ownerAcc.balance})
                      ({ownerAcc with balance := UInt256.ofNat 0})
                      htarget hacc
              | some targetAcc =>
                  by_cases hsame : target = state.executionEnv.codeOwner
                  · simp [hpop, hcreated, howner] at h
                    rw [← h]
                    have htargetAcc : ownerAcc = targetAcc := by
                      simpa [hsame, howner] using htarget
                    subst targetAcc
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, howner, hsame]
                    have h₁ := account_changes_consistent_insert_ne
                      acc state.executionEnv.codeOwner state.accountMap
                      ({ownerAcc with balance := UInt256.ofNat 0}) hacc
                    have h₂ := account_changes_consistent_insert_ne
                      acc state.executionEnv.codeOwner
                      (state.accountMap.insert state.executionEnv.codeOwner
                        {ownerAcc with balance := UInt256.ofNat 0})
                      ({ownerAcc with balance := UInt256.ofNat 0}) hacc
                    exact account_changes_consistent_trans h₁ h₂
                  · simp [hpop, hcreated, howner] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, htarget, hsame]
                    have hpre := account_changes_consistent_sendEth_prelude
                      acc target state.executionEnv.codeOwner ownerAcc.balance true state.accountMap
                    rw [sendEth_true_find?_some_find?_some_ne
                      target state.executionEnv.codeOwner ownerAcc.balance state.accountMap
                      targetAcc ownerAcc htarget howner hsame] at hpre
                    simpa using hpre
        · cases howner : state.accountMap.find? state.executionEnv.codeOwner with
          | none =>
              simp [hpop, hcreated, howner] at h
              rw [← h]
              simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
              exact account_changes_consistent_rfl acc
          | some ownerAcc =>
              cases htarget : state.accountMap.find? target with
              | none =>
                  by_cases hzero : (ownerAcc.balance == { val := 0 }) = true
                  · simp [hpop, hcreated, howner, hzero] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, htarget]
                    exact account_changes_consistent_rfl acc
                  · simp [hpop, hcreated, howner, hzero] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, htarget]
                    exact account_changes_consistent_insert_fresh_then_insert_ne
                      acc target state.executionEnv.codeOwner state.accountMap
                      ({(default : Account) with balance := ownerAcc.balance})
                      ({ownerAcc with balance := UInt256.ofNat 0})
                      htarget hacc
              | some targetAcc =>
                  by_cases hsame : target = state.executionEnv.codeOwner
                  · simp [hpop, hcreated, howner] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, howner, hsame]
                    exact account_changes_consistent_rfl acc
                  · simp [hpop, hcreated, howner] at h
                    rw [← h]
                    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
                      target, htarget, hsame]
                    have hpre := account_changes_consistent_sendEth_prelude
                      acc target state.executionEnv.codeOwner ownerAcc.balance true state.accountMap
                    rw [sendEth_true_find?_some_find?_some_ne
                      target state.executionEnv.codeOwner ownerAcc.balance state.accountMap
                      targetAcc ownerAcc htarget howner hsame] at hpre
                    simpa using hpre

theorem account_changes_consistent_of_Z
    {op : Operation}
    {stateZ : State} {cost : Nat}
    (hZ : Z validJumps op state = .ok (stateZ, cost)) :
    account_changes_consistent acc state.accountMap stateZ.accountMap := by
  unfold Z at hZ
  by_cases hδ : δ op = none
  · rw [if_pos hδ] at hZ
    contradiction
  rw [if_neg hδ] at hZ
  by_cases hstack : state.machineState.stack.length < (δ op).getD 0
  · rw [if_pos hstack] at hZ
    contradiction
  rw [if_neg hstack] at hZ
  by_cases hcost₁ : state.machineState.gasAvailable.toNat < memoryExpansionCost state op
  · rw [if_pos hcost₁] at hZ
    contradiction
  rw [if_neg hcost₁] at hZ
  set state₁ : State :=
    { state with machineState.gasAvailable :=
        state.machineState.gasAvailable.natSub (memoryExpansionCost state op) } with hstate₁
  by_cases hcost₂ : state₁.machineState.gasAvailable.toNat < C' state₁ op
  · rw [if_pos (by simpa [state₁] using hcost₂)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hcost₂)] at hZ
  by_cases hjump :
      op = Operation.JUMP ∧
        Z.notIn state₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [state₁] using hjump)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hjump)] at hZ
  by_cases hjumpi :
      op = Operation.JUMPI ∧
        state₁.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
        Z.notIn state₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [state₁] using hjumpi)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hjumpi)] at hZ
  by_cases hreturndata :
      op = Operation.RETURNDATACOPY ∧
        (state₁.machineState.stack.getD 1 ⟨0⟩).toNat
          + (state₁.machineState.stack.getD 2 ⟨0⟩).toNat
            > state₁.machineState.returnData.size
  · rw [if_pos (by simpa [state₁] using hreturndata)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hreturndata)] at hZ
  by_cases hstackover :
      state₁.machineState.stack.length - (δ op).getD 0 + (α op).getD 0 > 1024
  · rw [if_pos (by simpa [state₁] using hstackover)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hstackover)] at hZ
  by_cases hstatic :
      (¬ state₁.executionEnv.perm) ∧
        (op ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
          (op = .CALL ∧ state₁.machineState.stack[2]? ≠ some ⟨0⟩))
  · rw [if_pos (by simpa [state₁] using hstatic)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hstatic)] at hZ
  by_cases hsstore :
      (op = .SSTORE) ∧ state₁.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos (by simpa [state₁] using hsstore)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hsstore)] at hZ
  by_cases hcreate :
      op.isCreate ∧ state₁.machineState.stack.getD 2 ⟨0⟩ > ⟨49152⟩
  · rw [if_pos (by simpa [state₁] using hcreate)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hcreate)] at hZ
  simp at hZ
  rcases hZ with ⟨hstate, _hcost⟩
  rw [← hstate]
  simp [state₁]
  exact account_changes_consistent_rfl acc

theorem Z_executionEnv_eq
    {op : Operation}
    {stateZ : State} {cost : Nat}
    (hZ : Z validJumps op state = .ok (stateZ, cost)) :
    stateZ.executionEnv = state.executionEnv := by
  unfold Z at hZ
  by_cases hδ : δ op = none
  · rw [if_pos hδ] at hZ
    contradiction
  rw [if_neg hδ] at hZ
  by_cases hstack : state.machineState.stack.length < (δ op).getD 0
  · rw [if_pos hstack] at hZ
    contradiction
  rw [if_neg hstack] at hZ
  by_cases hcost₁ : state.machineState.gasAvailable.toNat < memoryExpansionCost state op
  · rw [if_pos hcost₁] at hZ
    contradiction
  rw [if_neg hcost₁] at hZ
  set state₁ : State :=
    { state with machineState.gasAvailable :=
        state.machineState.gasAvailable.natSub (memoryExpansionCost state op) } with hstate₁
  by_cases hcost₂ : state₁.machineState.gasAvailable.toNat < C' state₁ op
  · rw [if_pos (by simpa [state₁] using hcost₂)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hcost₂)] at hZ
  by_cases hjump :
      op = Operation.JUMP ∧
        Z.notIn state₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [state₁] using hjump)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hjump)] at hZ
  by_cases hjumpi :
      op = Operation.JUMPI ∧
        state₁.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
        Z.notIn state₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [state₁] using hjumpi)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hjumpi)] at hZ
  by_cases hreturndata :
      op = Operation.RETURNDATACOPY ∧
        (state₁.machineState.stack.getD 1 ⟨0⟩).toNat
          + (state₁.machineState.stack.getD 2 ⟨0⟩).toNat
            > state₁.machineState.returnData.size
  · rw [if_pos (by simpa [state₁] using hreturndata)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hreturndata)] at hZ
  by_cases hstackover :
      state₁.machineState.stack.length - (δ op).getD 0 + (α op).getD 0 > 1024
  · rw [if_pos (by simpa [state₁] using hstackover)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hstackover)] at hZ
  by_cases hstatic :
      (¬ state₁.executionEnv.perm) ∧
        (op ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
          (op = .CALL ∧ state₁.machineState.stack[2]? ≠ some ⟨0⟩))
  · rw [if_pos (by simpa [state₁] using hstatic)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hstatic)] at hZ
  by_cases hsstore :
      (op = .SSTORE) ∧ state₁.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos (by simpa [state₁] using hsstore)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hsstore)] at hZ
  by_cases hcreate :
      op.isCreate ∧ state₁.machineState.stack.getD 2 ⟨0⟩ > ⟨49152⟩
  · rw [if_pos (by simpa [state₁] using hcreate)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hcreate)] at hZ
  simp at hZ
  rcases hZ with ⟨hstate, _hcost⟩
  rw [← hstate]

private lemma Xstep_executionEnv_eq
    {state state' : State} {ret : Option (HaltCause × ByteArray)}
    (hstep : Xstep validJumps state = .ok (state', ret)) :
    state'.executionEnv = state.executionEnv := by
  have h := hstep
  simp [Xstep] at h
  split at h
  · contradiction
  · split at h
    · simp [bind, Except.bind] at h
      split at h
      · contradiction
      · split at h <;>
          (simp at h
           simpa using congrArg (fun st : State => st.executionEnv) (And.left h).symm)
    · simp [bind, Except.bind] at h
      split at h
      · contradiction
      · split at h
        · simp at h
          simpa using congrArg (fun st : State => st.executionEnv) (And.left h).symm
        · split at h <;>
            (simp at h
             simpa using congrArg (fun st : State => st.executionEnv) (And.left h).symm)

theorem account_changes_consistent_except_owner_of_step_max_depth :
    ∀ gasCost instr state state',
    state.executionEnv.depth = 1024 →
    step gasCost instr state = .ok state' →
    ∀ acc, acc ≠ state.executionEnv.codeOwner →
      account_changes_consistent acc state.accountMap state'.accountMap
    := by
  intros gasCost instr state state' hdepth hstep acc hacc
  rcases instr with ⟨op, arg⟩
  cases op with
  | StopArith op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_stoparith_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | CompBit op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_compbit_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | Keccak op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_keccak_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | Env op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_env_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | Block op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_block_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | StackMemFlow op =>
      exact step_stackmemflow_consistent_except_owner
        (op := op) (gasCost := gasCost) (arg := arg) hacc hstep
  | Push op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_push_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | Dup op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_dup_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | Exchange op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_exchange_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | Log op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_log_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | System op =>
      exact step_system_consistent_except_owner_max_depth
        (op := op) (gasCost := gasCost) (arg := arg) hdepth hacc hstep

theorem account_changes_consistent_except_owner_of_step_succ_depth :
    ∀ gasCost instr state state' acc,
    (1024 - state.executionEnv.depth.val) = n + 1 →
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H w
        createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H w =
            (createdAccounts', σ', g', A', z, o') →
          acc ≠ r →
          account_changes_consistent acc σ σ') →
    (ihLambda : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o g p v i ζ H w
        a createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o g p v i e ζ H w =
            (a, createdAccounts', σ', g', A', z, o') →
          account_changes_consistent acc σ σ') →
    step gasCost instr state = .ok state' →
    acc ≠ state.executionEnv.codeOwner →
    account_changes_consistent acc state.accountMap state'.accountMap
    := by
  intros gasCost instr state state' acc hdepth ihTheta ihLambda hstep hacc
  rcases instr with ⟨op, arg⟩
  cases op with
  | StopArith op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_stoparith_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | CompBit op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_compbit_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | Keccak op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_keccak_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | Env op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_env_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | Block op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_block_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | StackMemFlow op =>
      exact step_stackmemflow_consistent_except_owner
        (op := op) (gasCost := gasCost) (arg := arg) hacc hstep
  | Push op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_push_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | Dup op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_dup_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | Exchange op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_exchange_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | Log op =>
      exact account_changes_consistent_of_accountMap_eq acc
        (step_log_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
  | System op =>
      exact step_system_consistent_except_owner_succ_depth
        (op := op) (gasCost := gasCost) (arg := arg)
        hdepth ihTheta ihLambda hacc hstep

theorem account_changes_consistent_except_owner_of_Xstep_max_depth :
    ∀ state state' ret,
    state.executionEnv.depth = 1024 →
    Xstep validJumps state = .ok (state', ret) →
    ∀ acc, acc ≠ state.executionEnv.codeOwner →
      account_changes_consistent acc state.accountMap state'.accountMap
    := by
  intros state state' ret hdepth hXstep acc hacc
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  simp [Xstep, ← hinstr] at hXstep
  split at hXstep
  · contradiction
  · rename_i stateZ cost hZ
    simp [bind, Except.bind] at hXstep
    split at hXstep
    · contradiction
    · rename_i stepped hStep
      have hZ' : Z validJumps op state = .ok (stateZ, cost) := by
        simpa [← hinstr] using hZ
      have hStep' :
          step cost (op, arg)
            { stateZ with executionEnv.depth := state.executionEnv.depth } = .ok stepped := by
        simpa [← hinstr] using hStep
      have hZLoc :
          account_changes_consistent acc state.accountMap stateZ.accountMap :=
        account_changes_consistent_of_Z (validJumps := validJumps)
          (state := state) (op := op) hZ'
      have hZEnv : stateZ.executionEnv = state.executionEnv :=
        Z_executionEnv_eq (validJumps := validJumps) (state := state) (op := op) hZ'
      have hStepLoc :
          account_changes_consistent acc
            ({ stateZ with executionEnv.depth := state.executionEnv.depth }).accountMap
            stepped.accountMap :=
        account_changes_consistent_except_owner_of_step_max_depth
          cost (op, arg) { stateZ with executionEnv.depth := state.executionEnv.depth } stepped
          (by simp [hdepth])
          hStep' acc
          (by simpa [hZEnv] using hacc)
      have hprefix :
          account_changes_consistent acc state.accountMap stepped.accountMap := by
        exact account_changes_consistent_trans hZLoc (by simpa using hStepLoc)
      repeat split at hXstep
      all_goals
        try contradiction
        try
          injection hXstep with hpair
          have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
            congrArg Prod.fst hpair
          rw [← hstateEq]
          simpa using hprefix
        try
          split at hXstep
          · injection hXstep with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            simpa using hprefix
          · injection hXstep with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            simpa using hprefix

theorem account_changes_consistent_except_owner_of_Xstep_succ_depth :
    ∀ state state' ret acc,
    (1024 - state.executionEnv.depth.val) = n + 1 →
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H w
        createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H w =
            (createdAccounts', σ', g', A', z, o') →
          acc ≠ r →
          account_changes_consistent acc σ σ') →
    (ihLambda : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o g p v i ζ H w
        a createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o g p v i e ζ H w =
            (a, createdAccounts', σ', g', A', z, o') →
          account_changes_consistent acc σ σ') →
    Xstep validJumps state = .ok (state', ret) →
    acc ≠ state.executionEnv.codeOwner →
    account_changes_consistent acc state.accountMap state'.accountMap
    := by
  intros state state' ret acc hdepth ihTheta ihLambda hXstep hacc
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  simp [Xstep, ← hinstr] at hXstep
  split at hXstep
  · contradiction
  · rename_i stateZ cost hZ
    simp [bind, Except.bind] at hXstep
    split at hXstep
    · contradiction
    · rename_i stepped hStep
      have hZ' : Z validJumps op state = .ok (stateZ, cost) := by
        simpa [← hinstr] using hZ
      have hStep' :
          step cost (op, arg)
            { stateZ with executionEnv.depth := state.executionEnv.depth } = .ok stepped := by
        simpa [← hinstr] using hStep
      have hZLoc :
          account_changes_consistent acc state.accountMap stateZ.accountMap :=
        account_changes_consistent_of_Z (validJumps := validJumps)
          (state := state) (op := op) hZ'
      have hZEnv : stateZ.executionEnv = state.executionEnv :=
        Z_executionEnv_eq (validJumps := validJumps) (state := state) (op := op) hZ'
      have hStepLoc :
          account_changes_consistent acc
            ({ stateZ with executionEnv.depth := state.executionEnv.depth }).accountMap
            stepped.accountMap :=
        account_changes_consistent_except_owner_of_step_succ_depth
          (n := n)
          cost (op, arg) { stateZ with executionEnv.depth := state.executionEnv.depth } stepped acc
          (by simp [hdepth])
          ihTheta
          ihLambda
          hStep'
          (by simpa [hZEnv] using hacc)
      have hprefix :
          account_changes_consistent acc state.accountMap stepped.accountMap := by
        exact account_changes_consistent_trans hZLoc (by simpa using hStepLoc)
      repeat split at hXstep
      all_goals
        try contradiction
        try
          injection hXstep with hpair
          have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
            congrArg Prod.fst hpair
          rw [← hstateEq]
          simpa using hprefix
        try
          split at hXstep
          · injection hXstep with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            simpa using hprefix
          · injection hXstep with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            simpa using hprefix

theorem account_changes_consistent_except_owner_of_X_max_depth :
    ∀ state state' o,
    state.executionEnv.depth = 1024 →
    X f validJumps state = .ok (.success state' o) →
    ∀ acc, acc ≠ state.executionEnv.codeOwner →
      account_changes_consistent acc state.accountMap state'.accountMap
    := by
  intros state state' o hdepth hX acc hacc
  induction f generalizing state state' o acc with
  | zero =>
      simp [X] at hX
  | succ f ih =>
      simp [X] at hX
      cases hstep : Xstep validJumps state with
      | error err =>
          rw [hstep] at hX
          change Except.error err = Except.ok (ExecutionResult.success state' o) at hX
          contradiction
      | ok stepRes =>
          rcases stepRes with ⟨state₁, ret⟩
          have hstepLoc := account_changes_consistent_except_owner_of_Xstep_max_depth
            (validJumps := validJumps) state state₁ ret hdepth hstep acc hacc
          rw [hstep] at hX
          cases ret with
          | none =>
              change
                X f validJumps
                    { state₁ with executionEnv.depth := state.executionEnv.depth } =
                  Except.ok (ExecutionResult.success state' o) at hX
              have henv := Xstep_executionEnv_eq (validJumps := validJumps) hstep
              have hdepth₁ :
                  ({ state₁ with executionEnv.depth := state.executionEnv.depth }).executionEnv.depth = 1024 := by
                simp [hdepth]
              have hacc₁ :
                  acc ≠ ({ state₁ with executionEnv.depth := state.executionEnv.depth }).executionEnv.codeOwner := by
                simpa [henv] using hacc
              have htail := ih
                ({ state₁ with executionEnv.depth := state.executionEnv.depth })
                state' o hdepth₁ hX acc hacc₁
              exact account_changes_consistent_trans hstepLoc (by simpa using htail)
          | some retVal =>
              rcases retVal with ⟨cause, out⟩
              cases cause with
              | success =>
                change
                  Except.ok (ExecutionResult.success state₁ out) =
                    Except.ok (ExecutionResult.success state' o) at hX
                injection hX with hres
                injection hres with hstate _hout
                simpa [hstate] using hstepLoc
              | revert =>
                change
                  Except.ok (ExecutionResult.revert state₁.machineState.gasAvailable.toUInt256 out) =
                    Except.ok (ExecutionResult.success state' o) at hX
                injection hX with hres
                cases hres

theorem account_changes_consistent_except_owner_of_X_succ_depth :
    ∀ state state' o acc,
    (1024 - state.executionEnv.depth.val) = n + 1 →
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H w
        createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H w =
            (createdAccounts', σ', g', A', z, o') →
          acc ≠ r →
          account_changes_consistent acc σ σ') →
    (ihLambda : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o g p v i ζ H w
        a createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o g p v i e ζ H w =
            (a, createdAccounts', σ', g', A', z, o') →
          account_changes_consistent acc σ σ') →
    X f validJumps state = .ok (.success state' o) →
    acc ≠ state.executionEnv.codeOwner →
    account_changes_consistent acc state.accountMap state'.accountMap
    := by
  intros state state' o acc hdepth ihTheta ihLambda hX hacc
  induction f generalizing state state' o acc with
  | zero =>
      simp [X] at hX
  | succ f ih =>
      simp [X] at hX
      cases hstep : Xstep validJumps state with
      | error err =>
          rw [hstep] at hX
          change Except.error err = Except.ok (ExecutionResult.success state' o) at hX
          contradiction
      | ok stepRes =>
          rcases stepRes with ⟨state₁, ret⟩
          have hstepLoc := account_changes_consistent_except_owner_of_Xstep_succ_depth
            (n := n)
            (validJumps := validJumps) state state₁ ret acc hdepth ihTheta ihLambda hstep hacc
          rw [hstep] at hX
          cases ret with
          | none =>
              change
                X f validJumps
                    { state₁ with executionEnv.depth := state.executionEnv.depth } =
                  Except.ok (ExecutionResult.success state' o) at hX
              have henv := Xstep_executionEnv_eq (validJumps := validJumps) hstep
              have hdepth₁ :
                  1024 - ({ state₁ with executionEnv.depth := state.executionEnv.depth }).executionEnv.depth.val =
                    n + 1 := by
                simp [hdepth]
              have hacc₁ :
                  acc ≠ ({ state₁ with executionEnv.depth := state.executionEnv.depth }).executionEnv.codeOwner := by
                simpa [henv] using hacc
              have htail := ih
                ({ state₁ with executionEnv.depth := state.executionEnv.depth })
                state' o acc hdepth₁
                ihTheta
                ihLambda
                hX hacc₁
              exact account_changes_consistent_trans hstepLoc (by simpa using htail)
          | some retVal =>
              rcases retVal with ⟨cause, out⟩
              cases cause with
              | success =>
                change
                  Except.ok (ExecutionResult.success state₁ out) =
                    Except.ok (ExecutionResult.success state' o) at hX
                injection hX with hres
                injection hres with hstate _hout
                simpa [hstate] using hstepLoc
              | revert =>
                change
                  Except.ok (ExecutionResult.revert state₁.machineState.gasAvailable.toUInt256 out) =
                    Except.ok (ExecutionResult.success state' o) at hX
                injection hX with hres
                cases hres

theorem account_changes_consistent_except_owner_of_Xi_max_depth :
    ∀ createdAccounts' σ' g' A' o,
    I.depth = 1024 →
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.success (createdAccounts', σ', g', A') o) →
    ∀ acc, acc ≠ I.codeOwner →
      account_changes_consistent acc σ σ'
    := by
  intros createdAccounts' σ' g' A' o hdepth hXi acc hacc
  simp [Ξ] at hXi
  set freshState : State :=
    { (default : State) with
      accountMap := σ,
      σ₀ := σ₀,
      executionEnv := I,
      substate := A,
      createdAccounts := createdAccounts,
      machineState := { (default : State).machineState with gasAvailable := Sat256.ofUInt256 g },
      blocks := blocks,
      genesisBlockHeader := genesisBlockHeader } with hfresh
  change Except.bind (X (g.toNat + 1) (D_J I.code 0) freshState)
      (fun result =>
        match result with
        | ExecutionResult.success evmState' o =>
            Except.ok (ExecutionResult.success
              (evmState'.createdAccounts, evmState'.accountMap,
                evmState'.machineState.gasAvailable.toUInt256, evmState'.substate) o)
        | ExecutionResult.revert g' o => Except.ok (ExecutionResult.revert g' o)) =
        Except.ok (ExecutionResult.success (createdAccounts', σ', g', A') o) at hXi
  cases hX : X (g.toNat + 1) (D_J I.code 0) freshState with
  | error err =>
      simp [hX, Except.bind] at hXi
  | ok res =>
      cases res with
      | revert gas out =>
          simp [hX, Except.bind] at hXi
      | success evmState' out =>
          simp [hX, Except.bind] at hXi
          rcases hXi with ⟨⟨hcreated, hσ, hg, hA⟩, ho⟩
          rw [← hσ]
          have hloc := account_changes_consistent_except_owner_of_X_max_depth
            (f := g.toNat + 1) (validJumps := D_J I.code 0)
            freshState evmState' out (by simpa [hfresh] using hdepth) hX acc
            (by simpa [hfresh] using hacc)
          simpa [hfresh, hcreated] using hloc

theorem account_changes_consistent_except_owner_of_Xi_succ_depth :
    ∀ createdAccounts' σ' g' A' o n acc,
    (1024 - I.depth.val) = n + 1 →
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H w
        createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H w =
            (createdAccounts', σ', g', A', z, o') →
          acc ≠ r →
          account_changes_consistent acc σ σ') →
    (ihLambda : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o g p v i ζ H w
        a createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o g p v i e ζ H w =
            (a, createdAccounts', σ', g', A', z, o') →
          account_changes_consistent acc σ σ') →
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.success (createdAccounts', σ', g', A') o) →
    acc ≠ I.codeOwner →
      account_changes_consistent acc σ σ'
    := by
  intros createdAccounts' σ' g' A' o n acc hdepth ihTheta ihLambda hXi hacc
  simp [Ξ] at hXi
  set freshState : State :=
    { (default : State) with
      accountMap := σ,
      σ₀ := σ₀,
      executionEnv := I,
      substate := A,
      createdAccounts := createdAccounts,
      machineState := { (default : State).machineState with gasAvailable := Sat256.ofUInt256 g },
      blocks := blocks,
      genesisBlockHeader := genesisBlockHeader } with hfresh
  change Except.bind (X (g.toNat + 1) (D_J I.code 0) freshState)
      (fun result =>
        match result with
        | ExecutionResult.success evmState' o =>
            Except.ok (ExecutionResult.success
              (evmState'.createdAccounts, evmState'.accountMap,
                evmState'.machineState.gasAvailable.toUInt256, evmState'.substate) o)
        | ExecutionResult.revert g' o => Except.ok (ExecutionResult.revert g' o)) =
        Except.ok (ExecutionResult.success (createdAccounts', σ', g', A') o) at hXi
  cases hX : X (g.toNat + 1) (D_J I.code 0) freshState with
  | error err =>
      simp [hX, Except.bind] at hXi
  | ok res =>
      cases res with
      | revert gas out =>
          simp [hX, Except.bind] at hXi
      | success evmState' out =>
          simp [hX, Except.bind] at hXi
          rcases hXi with ⟨⟨hcreated, hσ, hg, hA⟩, ho⟩
          rw [← hσ]
          have hloc := account_changes_consistent_except_owner_of_X_succ_depth
            (f := g.toNat + 1) (n := n) (validJumps := D_J I.code 0)
            (state := freshState) evmState' out acc
            (by simpa [hfresh] using hdepth)
            (by simpa [hfresh] using ihTheta)
            (by simpa [hfresh] using ihLambda)
            hX
            (by simpa [hfresh] using hacc)
          simpa [hfresh, hcreated] using hloc

private lemma account_changes_consistent_if_empty_or_sendEth_prelude
    (acc r s : AccountAddress) (v : UInt256) (σ τ : AccountMap)
    (hτ : τ = ∅ ∨ τ = sendEth r s v true σ) :
    account_changes_consistent acc σ (if τ == ∅ then σ else τ) := by
  rcases hτ with hτ | hτ
  · subst τ
    simp [rbMap_empty_beq_empty, account_changes_consistent_rfl]
  · subst τ
    by_cases hEmpty : (sendEth r s v true σ == (∅ : AccountMap)) = true
    · simp [hEmpty, account_changes_consistent_rfl]
    · simp [hEmpty]
      exact account_changes_consistent_sendEth_prelude acc r s v true σ

private lemma account_changes_consistent_nonempty_or_sendEth_prelude
    (acc r s : AccountAddress) (v : UInt256) (σ τ : AccountMap)
    (hnot_empty : ¬(τ == ∅) = true)
    (hτ : τ = ∅ ∨ τ = sendEth r s v true σ) :
    account_changes_consistent acc σ τ := by
  rcases hτ with hτ | hτ
  · subst τ
    exact False.elim (hnot_empty rbMap_empty_beq_empty)
  · subst τ
    exact account_changes_consistent_sendEth_prelude acc r s v true σ

private lemma precompile_ECREC_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_ECREC σ g A I).1 = ∅ ∨ (Ξ_ECREC σ g A I).1 = σ := by
  simp only [Ξ_ECREC]
  split <;> simp

private lemma precompile_SHA256_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_SHA256 σ g A I).1 = ∅ ∨ (Ξ_SHA256 σ g A I).1 = σ := by
  simp only [Ξ_SHA256]
  split <;> simp

private lemma precompile_RIP160_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_RIP160 σ g A I).1 = ∅ ∨ (Ξ_RIP160 σ g A I).1 = σ := by
  simp only [Ξ_RIP160]
  split <;> simp

private lemma precompile_ID_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_ID σ g A I).1 = ∅ ∨ (Ξ_ID σ g A I).1 = σ := by
  simp only [Ξ_ID]
  split <;> simp

private lemma precompile_EXPMOD_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_EXPMOD σ g A I).1 = ∅ ∨ (Ξ_EXPMOD σ g A I).1 = σ := by
  unfold Ξ_EXPMOD
  set data := I.calldata
  set base_length := nat_of_slice data 0 32
  set exp_length := nat_of_slice data 32 32
  set modulus_length := nat_of_slice data 64 32
  set exp := fun _ : Unit => nat_of_slice data (96 + base_length) exp_length
  set gᵣ :=
    (let multiplication_complexity := fun x y => ((max x y + 7) / 8) ^ 2
     let adjusted_exp_length :=
      if exp_length ≤ 32 && exp () == 0 then
        0
      else if exp_length ≤ 32 then
        Nat.log 2 (exp ())
      else
        let length_part := 8 * (exp_length - 32)
        let bits_part :=
          let exp_head := nat_of_slice data (96 + base_length) 32
          if 32 < exp_length ∧ exp_head != 0 then Nat.log 2 exp_head else 0
        length_part + bits_part
     let iterations := max adjusted_exp_length 1
     let G_quaddivisor := 3
     max 200 (multiplication_complexity base_length modulus_length * iterations / G_quaddivisor))
  simp only
  repeat' (first | split | simp)

private lemma precompile_BN_ADD_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BN_ADD σ g A I).1 = ∅ ∨ (Ξ_BN_ADD σ g A I).1 = σ := by
  simp only [Ξ_BN_ADD]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

private lemma precompile_BN_MUL_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BN_MUL σ g A I).1 = ∅ ∨ (Ξ_BN_MUL σ g A I).1 = σ := by
  simp only [Ξ_BN_MUL]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

private lemma precompile_SNARKV_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_SNARKV σ g A I).1 = ∅ ∨ (Ξ_SNARKV σ g A I).1 = σ := by
  simp only [Ξ_SNARKV]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

private lemma precompile_BLAKE2_F_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BLAKE2_F σ g A I).1 = ∅ ∨ (Ξ_BLAKE2_F σ g A I).1 = σ := by
  simp only [Ξ_BLAKE2_F]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

private lemma precompile_PointEval_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_PointEval σ g A I).1 = ∅ ∨ (Ξ_PointEval σ g A I).1 = σ := by
  simp only [Ξ_PointEval]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

private lemma precompiled_Theta_accountMap_eq
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader)
    (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap)
    (A : Substate)
    (s o r pc : AccountAddress)
    (g p v v' : UInt256)
    (d : ByteArray)
    (e : Fin 1025)
    (H : BlockHeader)
    (w : Bool) :
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Precompiled pc) g p v v' d e H w).2.1 =
      (let σ₁ := sendEth r s v true σ
       let I : ExecutionEnv :=
        { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d,
          code := default, gasPrice := p.toNat, header := H, depth := e, perm := w,
          blobVersionedHashes := blobVersionedHashes }
       let result : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
        match pc with
        | 1 => (∅, Ξ_ECREC σ₁ g A I)
        | 2 => (∅, Ξ_SHA256 σ₁ g A I)
        | 3 => (∅, Ξ_RIP160 σ₁ g A I)
        | 4 => (∅, Ξ_ID σ₁ g A I)
        | 5 => (∅, Ξ_EXPMOD σ₁ g A I)
        | 6 => (∅, Ξ_BN_ADD σ₁ g A I)
        | 7 => (∅, Ξ_BN_MUL σ₁ g A I)
        | 8 => (∅, Ξ_SNARKV σ₁ g A I)
        | 9 => (∅, Ξ_BLAKE2_F σ₁ g A I)
        | 10 => (∅, Ξ_PointEval σ₁ g A I)
        | _ => default
       if result.2.1 == ∅ then σ else result.2.1) := by
  unfold Θ sendEth
  simp
  rfl

private lemma precompiled_result_accountMap_empty_or_self
    (pc : AccountAddress) (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (let result : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
      match pc with
      | 1 => (∅, Ξ_ECREC σ g A I)
      | 2 => (∅, Ξ_SHA256 σ g A I)
      | 3 => (∅, Ξ_RIP160 σ g A I)
      | 4 => (∅, Ξ_ID σ g A I)
      | 5 => (∅, Ξ_EXPMOD σ g A I)
      | 6 => (∅, Ξ_BN_ADD σ g A I)
      | 7 => (∅, Ξ_BN_MUL σ g A I)
      | 8 => (∅, Ξ_SNARKV σ g A I)
      | 9 => (∅, Ξ_BLAKE2_F σ g A I)
      | 10 => (∅, Ξ_PointEval σ g A I)
      | _ => default
     result.2.1) = ∅ ∨
    (let result : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
      match pc with
      | 1 => (∅, Ξ_ECREC σ g A I)
      | 2 => (∅, Ξ_SHA256 σ g A I)
      | 3 => (∅, Ξ_RIP160 σ g A I)
      | 4 => (∅, Ξ_ID σ g A I)
      | 5 => (∅, Ξ_EXPMOD σ g A I)
      | 6 => (∅, Ξ_BN_ADD σ g A I)
      | 7 => (∅, Ξ_BN_MUL σ g A I)
      | 8 => (∅, Ξ_SNARKV σ g A I)
      | 9 => (∅, Ξ_BLAKE2_F σ g A I)
      | 10 => (∅, Ξ_PointEval σ g A I)
      | _ => default
     result.2.1) = σ := by
  repeat split
  all_goals
    first
    | exact precompile_ECREC_accountMap_empty_or_self σ g A I
    | exact precompile_SHA256_accountMap_empty_or_self σ g A I
    | exact precompile_RIP160_accountMap_empty_or_self σ g A I
    | exact precompile_ID_accountMap_empty_or_self σ g A I
    | exact precompile_EXPMOD_accountMap_empty_or_self σ g A I
    | exact precompile_BN_ADD_accountMap_empty_or_self σ g A I
    | exact precompile_BN_MUL_accountMap_empty_or_self σ g A I
    | exact precompile_SNARKV_accountMap_empty_or_self σ g A I
    | exact precompile_BLAKE2_F_accountMap_empty_or_self σ g A I
    | exact precompile_PointEval_accountMap_empty_or_self σ g A I
    | exact Or.inl rfl

theorem account_changes_consistent_of_precompiled_Theta :
    ∀ createdAccounts' σ' g' A' z o',
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (toExecute σ r) g p v v' d e H w =
      (createdAccounts', σ', g', A', z, o') →
    toExecute σ r = .Precompiled pc →
    ∀ acc, account_changes_consistent acc σ σ'
    := by
  intros createdAccounts' σ' g' A' z o' hTheta hPrecomp acc
  rw [hPrecomp] at hTheta
  have hσ_proj := congrArg (fun x => x.2.1) hTheta
  have hσ : (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
      (.Precompiled pc) g p v v' d e H w).2.1 = σ' := by
    simpa using hσ_proj
  rw [← hσ]
  rw [precompiled_Theta_accountMap_eq]
  exact account_changes_consistent_if_empty_or_sendEth_prelude acc r s v σ _
    (by
      let σ₁ := sendEth r s v true σ
      let I : ExecutionEnv :=
        { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d,
          code := default, gasPrice := p.toNat, header := H, depth := e, perm := w,
          blobVersionedHashes := blobVersionedHashes }
      simpa [σ₁, I] using precompiled_result_accountMap_empty_or_self pc σ₁ g A I)

theorem account_changes_consistent_except_owner_of_precompiled_Theta :
    ∀ createdAccounts' σ' g' A' z o',
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Precompiled pc) g p v v' d e H w =
      (createdAccounts', σ', g', A', z, o') →
    ∀ acc, acc ≠ r → account_changes_consistent acc σ σ'
    := by
  intros createdAccounts' σ' g' A' z o' hTheta acc hacc_ne_r
  have hσ_proj := congrArg (fun x => x.2.1) hTheta
  have hσ : (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
      (.Precompiled pc) g p v v' d e H w).2.1 = σ' := by
    simpa using hσ_proj
  rw [← hσ]
  rw [precompiled_Theta_accountMap_eq]
  exact account_changes_consistent_if_empty_or_sendEth_prelude acc r s v σ _
    (by
      let σ₁ := sendEth r s v true σ
      let I : ExecutionEnv :=
        { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d,
          code := default, gasPrice := p.toNat, header := H, depth := e, perm := w,
          blobVersionedHashes := blobVersionedHashes }
      simpa [σ₁, I] using precompiled_result_accountMap_empty_or_self pc σ₁ g A I)


theorem account_changes_consistent_except_owner_of_Theta_and_Lambda :
    ∀ a c createdAccounts' σ' g' A' z o' e,
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c
        g p v v' d e H w =
      (createdAccounts', σ', g', A', z, o') →
      ∀ acc, acc ≠ r →
        account_changes_consistent acc σ σ') ∧
    (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o g p v i e ζ H w =
      (a, createdAccounts', σ', g', A', z, o') →
      ∀ acc, account_changes_consistent acc σ σ')
    := by
  intros a c createdAccounts' σ' g' A' z o' e
  generalize hn : 1024 - e.val = n
  induction n generalizing blobVersionedHashes genesisBlockHeader blocks
      createdAccounts e σ σ₀ A s o r c g p v v' d i ζ H w
      createdAccounts' σ' A' g' z o' a with
  | zero =>
      constructor
      · intro hTheta acc hacc_ne_r
        have he_eq : e = 1024 := by omega
        subst e
        cases hc : c with
        | Precompiled pc =>
            exact account_changes_consistent_except_owner_of_precompiled_Theta
              (blobVersionedHashes := blobVersionedHashes) (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
              (σ := σ) (σ₀ := σ₀) (A := A) (s := s) (o := o) (r := r)
              (g := g) (p := p) (v := v) (v' := v') (d := d) (e := 1024) (H := H) (w := w)
              createdAccounts' σ' g' A' z o' (by simpa [hc] using hTheta) acc hacc_ne_r
        | Code code =>
            unfold Θ at hTheta
            simp [hc] at hTheta
            split at hTheta <;> rename_i hXi
            · simp at hTheta
              rcases hTheta with ⟨hcreated, hσ, hg, hA, hz, ho⟩
              rw [← hσ]
              exact account_changes_consistent_rfl acc
            · simp at hTheta
              rcases hTheta with ⟨hcreated, hσ, hg, hA, hz, ho⟩
              rw [← hσ]
              exact account_changes_consistent_rfl acc
            · rename_i createdAccountsXi σStarStar gStarStar AStarStar returnedData
              simp at hTheta
              rcases hTheta with ⟨hcreated, hσ, hg, hA, hz, ho⟩
              split_ifs at hσ with hempty
              · rw [← hσ]
                exact account_changes_consistent_rfl acc
              · rw [← hσ]
                have hXiAcc := by
                  apply account_changes_consistent_except_owner_of_Xi_max_depth at hXi
                  · exact hXi acc (by simpa using hacc_ne_r)
                  · simp
                apply account_changes_consistent_trans
                · exact account_changes_consistent_sendEth_prelude acc r s v true σ
                · simpa [sendEth] using hXiAcc
      · intro hLambda acc
        by_cases hacc_ne_a : acc ≠ a
        ·
          have he_eq : e = 1024 := by omega
          subst e
          unfold Lambda at hLambda
          simp at hLambda
          split at hLambda <;> rename_i hXi
          · simp at hLambda
            rcases hLambda with ⟨ha, hcreated, hσ, hg, hA, hz, ho⟩
            rw [← hσ]
            exact account_changes_consistent_rfl acc
          · simp at hLambda
            rcases hLambda with ⟨ha, hcreated, hσ, hg, hA, hz, ho⟩
            rw [← hσ]
            exact account_changes_consistent_rfl acc
          · rename_i _ createdAccountsXi σStarStar gStarStar AStarStar returnedData
            simp at hLambda
            rcases hLambda with ⟨ha, hcreated, hσ, hg, hA, hz, ho⟩
            split_ifs at hσ with hfinal
            · rw [← hσ]
              exact account_changes_consistent_rfl acc
            · rw [← hσ]
              have hXiAcc := by
                apply account_changes_consistent_except_owner_of_Xi_max_depth at hXi
                · exact hXi acc (by simpa [← ha] using hacc_ne_a)
                · simp
              apply account_changes_consistent_trans
              · exact account_changes_consistent_sendEthCreate_prelude acc a s v true σ
              · simp [sendEthCreate]
                split <;> rename_i hs
                · apply account_changes_consistent_trans
                  · simpa [hs, ← ha] using hXiAcc
                  · exact account_changes_consistent_insert_ne acc _ σStarStar _ (by simpa [← ha] using hacc_ne_a)
                · apply account_changes_consistent_trans
                  · simpa [hs, ← ha] using hXiAcc
                  · exact account_changes_consistent_insert_ne acc _ σStarStar _ (by simpa [← ha] using hacc_ne_a)
        · have hacc_eq_a : acc = a := by
            by_contra h
            exact hacc_ne_a h
          subst a
          by_cases hdead : account_dead σ acc
          · exact account_changes_consistent_init_dead hdead
          ·
            -- Non-dead create targets should return the original map. Closing
            -- this requires normalizing the EIP-7610 invalid-init-code branch.
            sorry
  | succ n' ih =>
      constructor
      · intro hTheta acc hacc_ne_r
        cases hc : c with
        | Precompiled pc =>
            exact account_changes_consistent_except_owner_of_precompiled_Theta
              (blobVersionedHashes := blobVersionedHashes) (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
              (σ := σ) (σ₀ := σ₀) (A := A) (s := s) (o := o) (r := r)
              (g := g) (p := p) (v := v) (v' := v') (d := d) (e := e) (H := H) (w := w)
              createdAccounts' σ' g' A' z o' (by simpa [hc] using hTheta) acc hacc_ne_r
        | Code code =>
            unfold Θ at hTheta
            simp [hc] at hTheta
            split at hTheta <;> rename_i hXi
            · simp at hTheta
              rcases hTheta with ⟨hcreated, hσ, hg, hA, hz, ho⟩
              rw [← hσ]
              exact account_changes_consistent_rfl acc
            · simp at hTheta
              rcases hTheta with ⟨hcreated, hσ, hg, hA, hz, ho⟩
              rw [← hσ]
              exact account_changes_consistent_rfl acc
            · rename_i createdAccountsXi σStarStar gStarStar AStarStar returnedData
              simp at hTheta
              rcases hTheta with ⟨hcreated, hσ, hg, hA, hz, ho⟩
              split_ifs at hσ with hempty
              · rw [← hσ]
                exact account_changes_consistent_rfl acc
              · rw [← hσ]
                have hXiAcc := by
                  apply (account_changes_consistent_except_owner_of_Xi_succ_depth
                      (n := n') (acc := acc)) at hXi
                  · exact hXi (by simpa using hacc_ne_r)
                  · simpa using hn
                  · intro blobVersionedHashesᵢ genesisBlockHeaderᵢ blocksᵢ
                      createdAccountsᵢ eᵢ σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ rᵢ cᵢ gᵢ pᵢ vᵢ v'ᵢ dᵢ Hᵢ wᵢ
                      createdAccounts'ᵢ σ'ᵢ g'ᵢ A'ᵢ zᵢ o'ᵢ heᵢ hThetaᵢ hacc_ne_rᵢ
                    exact (ih (blobVersionedHashes := blobVersionedHashesᵢ)
                      (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                      (createdAccounts := createdAccountsᵢ) (σ := σᵢ) (σ₀ := σ₀ᵢ)
                      (A := Aᵢ) (s := sᵢ) (o := oᵢ) (r := rᵢ) (g := gᵢ) (p := pᵢ)
                      (v := vᵢ) (v' := v'ᵢ) (d := dᵢ) (i := default) (ζ := none)
                      (H := Hᵢ) (w := wᵢ)
                      default cᵢ createdAccounts'ᵢ σ'ᵢ g'ᵢ A'ᵢ zᵢ o'ᵢ eᵢ heᵢ).1
                      hThetaᵢ acc hacc_ne_rᵢ
                  · intro blobVersionedHashesᵢ genesisBlockHeaderᵢ blocksᵢ
                      createdAccountsᵢ eᵢ σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ gᵢ pᵢ vᵢ iᵢ ζᵢ Hᵢ wᵢ
                      aᵢ createdAccounts'ᵢ σ'ᵢ g'ᵢ A'ᵢ zᵢ o'ᵢ heᵢ hLambdaᵢ
                    exact (ih (blobVersionedHashes := blobVersionedHashesᵢ)
                      (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                      (createdAccounts := createdAccountsᵢ) (σ := σᵢ) (σ₀ := σ₀ᵢ)
                      (A := Aᵢ) (s := sᵢ) (o := oᵢ) (r := default) (g := gᵢ) (p := pᵢ)
                      (v := vᵢ) (v' := default) (d := default) (i := iᵢ) (ζ := ζᵢ)
                      (H := Hᵢ) (w := wᵢ)
                      aᵢ (toExecute σᵢ default) createdAccounts'ᵢ σ'ᵢ g'ᵢ A'ᵢ zᵢ o'ᵢ eᵢ heᵢ).2
                      hLambdaᵢ acc
                apply account_changes_consistent_trans
                · exact account_changes_consistent_sendEth_prelude acc r s v true σ
                · simpa [sendEth] using hXiAcc
      · intro hLambda acc
        by_cases hacc_ne_a : acc ≠ a
        · unfold Lambda at hLambda
          simp at hLambda
          split at hLambda <;> rename_i hXi
          · simp at hLambda
            rcases hLambda with ⟨ha, hcreated, hσ, hg, hA, hz, ho⟩
            rw [← hσ]
            exact account_changes_consistent_rfl acc
          · simp at hLambda
            rcases hLambda with ⟨ha, hcreated, hσ, hg, hA, hz, ho⟩
            rw [← hσ]
            exact account_changes_consistent_rfl acc
          · rename_i _ createdAccountsXi σStarStar gStarStar AStarStar returnedData
            simp at hLambda
            rcases hLambda with ⟨ha, hcreated, hσ, hg, hA, hz, ho⟩
            split_ifs at hσ with hfinal
            · rw [← hσ]
              exact account_changes_consistent_rfl acc
            · rw [← hσ]
              have hXiAcc := by
                apply (account_changes_consistent_except_owner_of_Xi_succ_depth
                    (n := n') (acc := acc)) at hXi
                · exact hXi (by simpa [← ha] using hacc_ne_a)
                · simpa using hn
                · intro blobVersionedHashesᵢ genesisBlockHeaderᵢ blocksᵢ
                    createdAccountsᵢ eᵢ σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ rᵢ cᵢ gᵢ pᵢ vᵢ v'ᵢ dᵢ Hᵢ wᵢ
                    createdAccounts'ᵢ σ'ᵢ g'ᵢ A'ᵢ zᵢ o'ᵢ heᵢ hThetaᵢ hacc_ne_r
                  exact (ih (blobVersionedHashes := blobVersionedHashesᵢ)
                    (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                    (createdAccounts := createdAccountsᵢ) (σ := σᵢ) (σ₀ := σ₀ᵢ)
                    (A := Aᵢ) (s := sᵢ) (o := oᵢ) (r := rᵢ) (g := gᵢ) (p := pᵢ)
                    (v := vᵢ) (v' := v'ᵢ) (d := dᵢ) (i := default) (ζ := none)
                    (H := Hᵢ) (w := wᵢ)
                    default cᵢ createdAccounts'ᵢ σ'ᵢ g'ᵢ A'ᵢ zᵢ o'ᵢ eᵢ heᵢ).1
                    hThetaᵢ acc hacc_ne_r
                · intro blobVersionedHashesᵢ genesisBlockHeaderᵢ blocksᵢ
                    createdAccountsᵢ eᵢ σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ gᵢ pᵢ vᵢ iᵢ ζᵢ Hᵢ wᵢ
                    aᵢ createdAccounts'ᵢ σ'ᵢ g'ᵢ A'ᵢ zᵢ o'ᵢ heᵢ hLambdaᵢ
                  exact (ih (blobVersionedHashes := blobVersionedHashesᵢ)
                    (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                    (createdAccounts := createdAccountsᵢ) (σ := σᵢ) (σ₀ := σ₀ᵢ)
                    (A := Aᵢ) (s := sᵢ) (o := oᵢ) (r := default) (g := gᵢ) (p := pᵢ)
                    (v := vᵢ) (v' := default) (d := default) (i := iᵢ) (ζ := ζᵢ)
                    (H := Hᵢ) (w := wᵢ)
                    aᵢ (toExecute σᵢ default) createdAccounts'ᵢ σ'ᵢ g'ᵢ A'ᵢ zᵢ o'ᵢ eᵢ heᵢ).2
                    hLambdaᵢ acc
              apply account_changes_consistent_trans
              · exact account_changes_consistent_sendEthCreate_prelude acc a s v true σ
              · simp [sendEthCreate]
                split <;> rename_i hs
                · apply account_changes_consistent_trans
                  · simpa [hs, ← ha] using hXiAcc
                  · exact account_changes_consistent_insert_ne acc _ σStarStar _ (by simpa [← ha] using hacc_ne_a)
                · apply account_changes_consistent_trans
                  · simpa [hs, ← ha] using hXiAcc
                  · exact account_changes_consistent_insert_ne acc _ σStarStar _ (by simpa [← ha] using hacc_ne_a)
        · have hacc_eq_a : acc = a := by
            by_contra h
            exact hacc_ne_a h
          subst a
          by_cases hdead : account_dead σ acc
          · exact account_changes_consistent_init_dead hdead
          ·
            -- Non-dead create targets should return the original map. Closing
            -- this requires normalizing the EIP-7610 invalid-init-code branch.
            sorry

theorem account_changes_consistent_of_Theta :
    ∀ createdAccounts' σ' g' A' z o' e,
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (toExecute σ r) g p v v' d e H w =
      (createdAccounts', σ', g', A', z, o') →
    ∀ acc, account_changes_consistent acc σ σ'
    := by
  intros createdAccounts' σ' g' A' z o' e hTheta acc
  by_cases hacc : acc = r
  · subst acc
    simp [account_changes_consistent]
    apply Relation.ReflTransGen.single
    exact account_change_consistent.by_own_code_from_start hTheta
  · exact (account_changes_consistent_except_owner_of_Theta_and_Lambda
      (blobVersionedHashes := blobVersionedHashes) (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
      (σ := σ) (σ₀ := σ₀) (A := A) (s := s) (o := o) (r := r)
      (g := g) (p := p) (v := v) (v' := v') (d := d) (i := default) (ζ := none)
      (H := H) (w := w)
      default (toExecute σ r) createdAccounts' σ' g' A' z o' e).1 hTheta acc hacc

theorem account_changes_consistent_weak_of_Theta :
    ∀ c createdAccounts' σ' g' A' z o' e,
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c
        g p v v' d e H w =
      (createdAccounts', σ', g', A', z, o') →
    ∀ acc, acc ≠ r →
      account_changes_consistent acc σ σ'
    := by
  intros c createdAccounts' σ' g' A' z o' e hTheta acc hacc_ne_r
  exact (account_changes_consistent_except_owner_of_Theta_and_Lambda
    (blobVersionedHashes := blobVersionedHashes) (createdAccounts := createdAccounts)
    (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
    (σ := σ) (σ₀ := σ₀) (A := A) (s := s) (o := o) (r := r)
    (g := g) (p := p) (v := v) (v' := v') (d := d) (i := default) (ζ := none)
    (H := H) (w := w)
    default c createdAccounts' σ' g' A' z o' e).1 hTheta acc hacc_ne_r

theorem account_changes_consistent_weak_of_Lambda :
    ∀ a createdAccounts' σ' g' A' z o' e,
    Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o g p v i e ζ H w =
      (a, createdAccounts', σ', g', A', z, o') →
    ∀ acc, account_changes_consistent acc σ σ'
    := by
  intros a createdAccounts' σ' g' A' z o' e hLambda acc
  exact (account_changes_consistent_except_owner_of_Theta_and_Lambda
    (blobVersionedHashes := blobVersionedHashes) (createdAccounts := createdAccounts)
    (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
    (σ := σ) (σ₀ := σ₀) (A := A) (s := s) (o := o) (r := default)
    (g := g) (p := p) (v := v) (v' := default) (d := default) (i := i) (ζ := ζ)
    (H := H) (w := w)
    a (toExecute σ default) createdAccounts' σ' g' A' z o' e).2 hLambda acc

theorem account_changes_consistent_weak_of_Theta_and_Lambda :
    ∀ a c createdAccounts' σ' g' A' z o' e,
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c
        g p v v' d e H w =
      (createdAccounts', σ', g', A', z, o') →
      ∀ acc, acc ≠ r →
        account_changes_consistent acc σ σ') ∧
    (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o g p v i e ζ H w =
      (a, createdAccounts', σ', g', A', z, o') →
      ∀ acc, account_changes_consistent acc σ σ')
    := by
  intros a c createdAccounts' σ' g' A' z o' e
  constructor
  · intro hTheta acc hacc_ne_r
    exact account_changes_consistent_weak_of_Theta c createdAccounts' σ' g' A' z o' e
      hTheta acc hacc_ne_r
  · intro hLambda acc
    exact account_changes_consistent_weak_of_Lambda a createdAccounts' σ' g' A' z o' e
      hLambda acc
