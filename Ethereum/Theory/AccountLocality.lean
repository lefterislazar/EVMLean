import Ethereum.Semantics
import Ethereum.Wheels
import Batteries.Data.RBMap.Lemmas

namespace Ethereum
namespace EVM

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

def sendEthCreate (a s : AccountAddress) (v : UInt256) (F : Bool) (σ : AccountMap) : AccountMap :=
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


inductive account_change_consistent (acc : AccountAddress) : AccountMap → AccountMap → Prop where
  | unchanged {σ σ'}:
    unchanged acc σ σ'
    → account_change_consistent acc σ σ'

  | by_own_code :
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀  A s o acc (toExecute σ acc) g p v v' d e H w = (createdAccounts', σ', g', A', z, o')
    → account_change_consistent acc (sendEth r s v z σ) σ'

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

/-
lemma account_changes_consistent_sendEth :
    ∀ acc, account_changes_consistent acc (sendEth r s l z σ) σ := by
  intro
  simp [account_changes_consistent]
  apply Relation.ReflTransGen.single
  apply account_change_consistent.unchanged
  apply unchanged_rfl
  -/

theorem account_changes_consistent_of_X_max_depth :
    ∀ state state' o,
    state.executionEnv.depth = 1024 →
    X f validJumps state = .ok (.success state' o) →
    ∀ acc, account_changes_consistent acc state.accountMap state'.accountMap
    := by
intros state' o hdepth hX acc
sorry

theorem account_changes_consistent_of_X_succ_depth :
    ∀ state' o,
    (1024 - state.executionEnv.depth.val) = n + 1 →
    (ih : ∀ (e : Fin 1025) σ σ₀ A s o r g p v v' d H w createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r (toExecute σ r) g p v v' d e H w =
              (createdAccounts', σ', g', A', z, o') →
      account_changes_consistent acc (sendEth r s v z σ) σ') →
    X f validJumps state = .ok (.success state' o) →
    ∀ acc, account_changes_consistent acc σ σ'
    := by
intros state' o hdepth hX acc
sorry

theorem account_changes_consistent_of_Xi_max_depth :
    ∀ createdAccounts' σ' g' A' o,
    I.depth = 1024 →
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ A g I = .ok (.success (createdAccounts', σ', g', A') o) →
    ∀ acc, acc ≠ I.codeOwner → account_changes_consistent acc σ σ'
    := by
intros createdAccounts' σ' g' A' o hdepth hXi acc
sorry

theorem account_changes_consistent_of_Xi_succ_depth :
    ∀ createdAccounts' σ' g' A' o n,
    (1024 - I.depth.val) = n + 1 →
    (ih : ∀ (e : Fin 1025) σ σ₀ A s o r g p v v' d H w createdAccounts' σ' g' A' z o',
        1024 - e.val = n →
          Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r (toExecute σ r) g p v v' d e H w =
              (createdAccounts', σ', g', A', z, o') →
      account_changes_consistent acc (sendEth r s v z σ) σ') →
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ A g I = .ok (.success (createdAccounts', σ', g', A') o) →
    ∀ acc, acc ≠ I.codeOwner → account_changes_consistent acc σ σ'
    := by
intros createdAccounts' σ' g' A' o hdepth hXi acc
sorry

theorem account_changes_consistent_of_precompiled_Theta :
    ∀ createdAccounts' σ' g' A' z o',
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀  A s o r (toExecute σ r) g p v v' d e H w = (createdAccounts', σ', g', A', z, o') →
    toExecute σ r = .Precompiled pc →
    ∀ acc, account_changes_consistent acc (sendEth r s v z σ) σ'
    := by
intros createdAccounts' σ' g' A' z o' hTheta hPrecomp acc
· by_cases hacc_eq_r : (acc = r)
  · simp [account_changes_consistent]
    apply Relation.ReflTransGen.single
    subst acc
    exact account_change_consistent.by_own_code hTheta
  · unfold Θ at hTheta
    simp [hPrecomp] at hTheta
    split at hTheta <;> rename_i hsplit0
    · sorry -- PRECOMPILES
    · sorry -- PRECOMPILES
    · sorry -- PRECOMPILES
    · sorry -- PRECOMPILES
    · sorry -- PRECOMPILES
    · sorry -- PRECOMPILES
    · sorry -- PRECOMPILES
    · sorry -- PRECOMPILES
    · sorry -- PRECOMPILES
    · sorry -- PRECOMPILES

    · simp [default] at hTheta
      simp [hTheta.right.left]
      rw [hTheta.right.right.right.right.left]
      apply account_changes_consistent_rfl

-- set_option maxRecDepth 10000000000
theorem account_changes_consistent_of_Theta_max_depth :
    ∀ createdAccounts' σ' g' A' z o',
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀  A s o r (toExecute σ r) g p v v' d (.ofNat 1025 1024) H w = (createdAccounts', σ', g', A', z, o') →
    ∀ acc, account_changes_consistent acc (sendEth r s v z σ) σ'
    := by
intros createdAccounts' σ' g' A' z o' hTheta acc
generalize hσ_eth : sendEth r s v z σ = σ_eth 
cases hprecomp : (toExecute σ r)
· by_cases hacc_eq_r : (acc = r)
  · simp [account_changes_consistent]
    apply Relation.ReflTransGen.single
    subst acc σ_eth
    exact account_change_consistent.by_own_code hTheta
  · unfold Θ at hTheta
    simp [hprecomp] at hTheta
    split at hTheta <;> rename_i hsplit0
    · split at hTheta <;> rename_i hsplit1
      · rw [← hTheta.right.left]
        subst σ_eth; simp at hTheta
        simp [hTheta.right.right.right.right.left]
        apply account_changes_consistent_rfl
      · simp at hsplit1
    · split at hTheta <;> rename_i hsplit1
      · rw [← hTheta.right.left]
        simp [hsplit1] at hTheta;
        subst σ_eth; simp [hTheta.right.right.right.right.left]
        apply account_changes_consistent_rfl
      · rw [← hTheta.right.left]
        simp at hsplit1
    · split at hTheta <;> rename_i h_empty
      · rw [← hTheta.right.left]
        simp at h_empty
        simp [h_empty] at hTheta
        subst σ_eth;
        simp [hTheta.right.right.right.right.left]
        apply account_changes_consistent_rfl
      · simp [← hTheta.right.left]
        simp at h_empty; simp [h_empty] at hTheta
        rename_i code' _ _ σStarStar _ _ _
        split at hsplit0 <;> rename_i heq0
        · split at hsplit0 <;> rename_i heq1
          · split at hsplit0 <;> rename_i heq2
            · generalize hσᵢ : Batteries.RBMap.insert σ r { nonce := (default: Account).nonce, balance := v, storage := (default : Account).storage, code := (default : Account).code, tstorage := (default : Account).tstorage } = σᵢ
              rw [hσᵢ] at hsplit0
              generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := 1024, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
              rw [henvᵢ] at hsplit0
              have : σ_eth = σᵢ := by
                subst σ_eth σᵢ
                simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                grind
              rw [this]
              apply account_changes_consistent_of_Xi_max_depth at hsplit0
              · apply hsplit0 acc; simp [← henvᵢ]; assumption
              · simp [← henvᵢ]
            · generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := 1024, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
              rw [henvᵢ] at hsplit0
              have : σ_eth = σ := by
                subst σ_eth
                simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                grind
              rw [this]
              apply account_changes_consistent_of_Xi_max_depth at hsplit0
              apply hsplit0 acc
              · simp [← henvᵢ]; assumption
              simp [← henvᵢ]
          · rename_i σ_r
            generalize hσᵢ : Batteries.RBMap.insert σ r { nonce := σ_r.nonce, balance := σ_r.balance + v, storage := σ_r.storage, code := σ_r.code, tstorage := σ_r.tstorage } = σᵢ
            rw [hσᵢ] at hsplit0
            generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := 1024, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
            rw [henvᵢ] at hsplit0
            have : σ_eth = σᵢ := by
              subst σ_eth σᵢ
              simp [sendEth, hTheta.right.right.right.right.left, heq1]
              grind
            rw [this]
            apply account_changes_consistent_of_Xi_max_depth at hsplit0
            apply hsplit0 acc
            · simp [← henvᵢ]; assumption
            simp [← henvᵢ]
        · rename_i σ_r
          split at hsplit0 <;> rename_i heq1
          · split at hsplit0 <;> rename_i heq2
            · generalize hσᵢ : ((Batteries.RBMap.insert σ r
                    { nonce := (default : Account).nonce, balance := v, storage := (default : Account).storage, code := (default : Account).code,
                      tstorage := (default : Account).tstorage }).insert
                s
                { nonce := σ_r.nonce, balance := σ_r.balance - v, storage := σ_r.storage, code := σ_r.code,
                  tstorage := σ_r.tstorage }) = σᵢ
              rw [hσᵢ] at hsplit0
              generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := 1024, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
              rw [henvᵢ] at hsplit0
              have : σ_eth = σᵢ := by
                subst σ_eth σᵢ
                simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                grind
              rw [this]
              apply account_changes_consistent_of_Xi_max_depth at hsplit0
              apply hsplit0 acc
              · simp [← henvᵢ]; assumption
              simp [← henvᵢ]
            · generalize hσᵢ : (Batteries.RBMap.insert σ s
                { nonce := σ_r.nonce, balance := σ_r.balance - v, storage := σ_r.storage, code := σ_r.code,
                  tstorage := σ_r.tstorage }) = σᵢ
              rw [hσᵢ] at hsplit0
              generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := 1024, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
              rw [henvᵢ] at hsplit0
              have : σ_eth = σᵢ := by
                subst σ_eth σᵢ
                simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                grind
              rw [this]
              apply account_changes_consistent_of_Xi_max_depth at hsplit0
              apply hsplit0 acc
              · simp [← henvᵢ]; assumption
              simp [← henvᵢ]
          · rename_i σ_r'
            generalize hσᵢ : ((Batteries.RBMap.insert σ r
                  { nonce := σ_r'.nonce, balance := σ_r'.balance + v, storage := σ_r'.storage, code := σ_r'.code,
                    tstorage := σ_r'.tstorage }).insert
              s
              { nonce := σ_r.nonce, balance := σ_r.balance - v, storage := σ_r.storage, code := σ_r.code,
                tstorage := σ_r.tstorage }) = σᵢ
            rw [hσᵢ] at hsplit0
            generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := 1024, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
            rw [henvᵢ] at hsplit0
            have : σ_eth = σᵢ := by
              subst σ_eth σᵢ
              simp [sendEth, hTheta.right.right.right.right.left, heq1]
              grind
            rw [this]
            apply account_changes_consistent_of_Xi_max_depth at hsplit0
            apply hsplit0 acc
            · simp [← henvᵢ]; assumption
            simp [← henvᵢ]
· subst σ_eth; apply account_changes_consistent_of_precompiled_Theta
  · exact hTheta
  · exact hprecomp

theorem account_changes_consistent_of_Lambda_max_depth :
    ∀ a createdAccounts' σ' g' A' z o',
    Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o  g p v i (.ofNat 1025 1024) ζ H w = (a, createdAccounts', σ', g', A', z, o') →
    ∀ acc, account_changes_consistent acc (sendEthCreate a s v z σ) σ'
    := by
intros a createdAccounts' σ' g' A' z o' hLambda acc
generalize hσ_eth : sendEthCreate a s v z σ = σ_eth 
· subst σ_eth
  unfold Lambda at hLambda
  -- cases h_r_in : (Batteries.RBMap.find? σ r)
  -- · simp at hLambda
  --   rw [h_r_in] at hLambda
  -- · _
  split at hLambda <;> rename_i h_s_in
  · simp [h_s_in] at hLambda
    split at hLambda <;> rename_i hXi
    · split at hLambda <;> rename_i hfinds
      · simp at hLambda
        simp [hLambda]
        apply account_changes_consistent_rfl
      · simp at hLambda
        simp [hLambda]
        apply account_changes_consistent_rfl
    · split at hLambda <;> rename_i hfinds
      · simp at hLambda
        simp [hLambda]
        apply account_changes_consistent_rfl
      · simp at hLambda
        simp [hLambda]
        apply account_changes_consistent_rfl
    · split at hLambda <;> rename_i ac h_addr_exist
      · simp at hLambda
        split at hLambda <;> rename_i h_fail
        · rw [← hLambda.right.right.left]
          rw [← hLambda.right.right.right.right.right.left]
          cases h_fail
          · rename_i h_fail'
            cases h_fail'
            · rename_i h_fail'; apply decide_eq_false at h_fail'
              simp [h_fail'] 
              apply account_changes_consistent_rfl
            · rename_i h_fail'; apply decide_eq_false at h_fail'
              simp [h_fail'] 
              apply account_changes_consistent_rfl
          · rename_i h_fail'
            cases h_fail'
            · rename_i h_fail'; simp [h_fail'] 
              apply account_changes_consistent_rfl
            · rename_i h_fail';
              cases h_fail'
              · rename_i h_fail'; simp [h_fail'] 
                apply account_changes_consistent_rfl
              · rename_i h_fail'; simp [h_fail'] 
                apply account_changes_consistent_rfl
        · simp [← hLambda]
          simp at h_fail
          simp [h_fail]
          obtain ⟨⟨hf1,hf2⟩, hf3, hf4, hf5⟩ := h_fail
          let hf1' := decide_eq_true hf1
          let hf3' := decide_eq_false (Nat.le_lt_asymm hf3)
          simp [hf3']
          let hf4' := decide_eq_false (Nat.le_lt_asymm hf4)
          simp [hf4']

          simp [account_changes_consistent]
          apply Relation.ReflTransGen.single
          apply account_change_consistent.unchanged
          by_cases h_acc_in : (acc = ((fromByteArrayBigEndian
          ((ffi.KEC (Lambda.L_A s (Option.option { val := 0 } (fun x => (x : Account).nonce) none - { val := 1 }) ζ i)).extract 12 32))))
          · apply unchanged.empty
            · simp [sendEth]
              split <;> rename_i h
              · split <;> rename_i h'
                · split <;> rename_i h''
                  · rw [Batteries.RBMap.find?_insert_of_eq]
                    · rw [← h_acc_in]; simp
                  · simp [h'] at h_addr_exist
                · rw [Batteries.RBMap.find?_insert_of_eq]
                  · rw [h_addr_exist] at h'; simp at h'
                    rw [← h']
                    simp
                    apply And.intro
                    · apply And.intro
                      · simp [hf2, default, instInhabitedAccount.default, instInhabitedPersistentAccountState.default, UInt256.ofNat, Id.run]
                      · _
                    · _
                  · simp; simp [← h_acc_in]
              · _ 

          cases h_fail
          · rename_i h_fail'1 h_fail'2
            cases h_fail'2
            · rename_i h_fail'2 h_fail'3;
              simp [h_fail'1, h_fail'2, h_fail'3]
              apply account_changes_consistent_rfl
            · rename_i h_fail'; apply decide_eq_false at h_fail'
              simp [h_fail'] 
              apply account_changes_consistent_rfl
          · rename_i h_fail'
            cases h_fail'
            · rename_i h_fail'; simp [h_fail'] 
              apply account_changes_consistent_rfl
            · rename_i h_fail';
              cases h_fail'
              · rename_i h_fail'; simp [h_fail'] 
                apply account_changes_consistent_rfl
              · rename_i h_fail'; simp [h_fail'] 
                apply account_changes_consistent_rfl
          split at hLambda <;> rename_i hfoo
        apply account_changes_consistent_rfl
      · simp [← hTheta.right.left]
        simp at h_empty; simp [h_empty] at hTheta
        rename_i code' _ _ σStarStar _ _ _
        split at hsplit0 <;> rename_i heq0
        · split at hsplit0 <;> rename_i heq1
          · split at hsplit0 <;> rename_i heq2
            · generalize hσᵢ : Batteries.RBMap.insert σ r { nonce := (default: Account).nonce, balance := v, storage := (default : Account).storage, code := (default : Account).code, tstorage := (default : Account).tstorage } = σᵢ
              rw [hσᵢ] at hsplit0
              generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := 1024, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
              rw [henvᵢ] at hsplit0
              have : σ_eth = σᵢ := by
                subst σ_eth σᵢ
                simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                grind
              rw [this]
              apply account_changes_consistent_of_Xi_max_depth at hsplit0
              · apply hsplit0 acc; simp [← henvᵢ]; assumption
              · simp [← henvᵢ]
            · generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := 1024, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
              rw [henvᵢ] at hsplit0
              have : σ_eth = σ := by
                subst σ_eth
                simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                grind
              rw [this]
              apply account_changes_consistent_of_Xi_max_depth at hsplit0
              apply hsplit0 acc
              · simp [← henvᵢ]; assumption
              simp [← henvᵢ]
          · rename_i σ_r
            generalize hσᵢ : Batteries.RBMap.insert σ r { nonce := σ_r.nonce, balance := σ_r.balance + v, storage := σ_r.storage, code := σ_r.code, tstorage := σ_r.tstorage } = σᵢ
            rw [hσᵢ] at hsplit0
            generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := 1024, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
            rw [henvᵢ] at hsplit0
            have : σ_eth = σᵢ := by
              subst σ_eth σᵢ
              simp [sendEth, hTheta.right.right.right.right.left, heq1]
              grind
            rw [this]
            apply account_changes_consistent_of_Xi_max_depth at hsplit0
            apply hsplit0 acc
            · simp [← henvᵢ]; assumption
            simp [← henvᵢ]
        · rename_i σ_r
          split at hsplit0 <;> rename_i heq1
          · split at hsplit0 <;> rename_i heq2
            · generalize hσᵢ : ((Batteries.RBMap.insert σ r
                    { nonce := (default : Account).nonce, balance := v, storage := (default : Account).storage, code := (default : Account).code,
                      tstorage := (default : Account).tstorage }).insert
                s
                { nonce := σ_r.nonce, balance := σ_r.balance - v, storage := σ_r.storage, code := σ_r.code,
                  tstorage := σ_r.tstorage }) = σᵢ
              rw [hσᵢ] at hsplit0
              generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := 1024, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
              rw [henvᵢ] at hsplit0
              have : σ_eth = σᵢ := by
                subst σ_eth σᵢ
                simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                grind
              rw [this]
              apply account_changes_consistent_of_Xi_max_depth at hsplit0
              apply hsplit0 acc
              · simp [← henvᵢ]; assumption
              simp [← henvᵢ]
            · generalize hσᵢ : (Batteries.RBMap.insert σ s
                { nonce := σ_r.nonce, balance := σ_r.balance - v, storage := σ_r.storage, code := σ_r.code,
                  tstorage := σ_r.tstorage }) = σᵢ
              rw [hσᵢ] at hsplit0
              generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := 1024, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
              rw [henvᵢ] at hsplit0
              have : σ_eth = σᵢ := by
                subst σ_eth σᵢ
                simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                grind
              rw [this]
              apply account_changes_consistent_of_Xi_max_depth at hsplit0
              apply hsplit0 acc
              · simp [← henvᵢ]; assumption
              simp [← henvᵢ]
          · rename_i σ_r'
            generalize hσᵢ : ((Batteries.RBMap.insert σ r
                  { nonce := σ_r'.nonce, balance := σ_r'.balance + v, storage := σ_r'.storage, code := σ_r'.code,
                    tstorage := σ_r'.tstorage }).insert
              s
              { nonce := σ_r.nonce, balance := σ_r.balance - v, storage := σ_r.storage, code := σ_r.code,
                tstorage := σ_r.tstorage }) = σᵢ
            rw [hσᵢ] at hsplit0
            generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := 1024, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
            rw [henvᵢ] at hsplit0
            have : σ_eth = σᵢ := by
              subst σ_eth σᵢ
              simp [sendEth, hTheta.right.right.right.right.left, heq1]
              grind
            rw [this]
            apply account_changes_consistent_of_Xi_max_depth at hsplit0
            apply hsplit0 acc
            · simp [← henvᵢ]; assumption
            simp [← henvᵢ]
· subst σ_eth; apply account_changes_consistent_of_precompiled_Theta
  · exact hTheta
  · exact hprecomp


theorem account_changes_consistent_of_Theta :
    ∀ createdAccounts' σ' g' A' z o' e,
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀  A s o r (toExecute σ r) g p v v' d e H w = (createdAccounts', σ', g', A', z, o') →
    ∀ acc, account_changes_consistent acc (sendEth r s v z σ) σ'
    := by
intros createdAccounts' σ' g' A' z o' e hTheta acc
generalize hn : 1024 - e.val = n
revert hTheta
revert e σ σ₀ A s o r g p v v' d H w createdAccounts' σ' A' g' z o'
induction n with
| zero =>
  intros σ σ₀ A s o r g p v v' d H w createdAccounts' σ' A' g' z o' e he hTheta
  have he_eq : e = 1024 := by omega
  subst e
  apply account_changes_consistent_of_Theta_max_depth; exact hTheta
| succ n' ih =>
  intros σ σ₀ A s o r g p v v' d H w createdAccounts' σ' A' g' z o' e he hTheta
  by_cases hacc_eq_r : (acc = r)
  · simp [account_changes_consistent]
    apply Relation.ReflTransGen.single
    subst acc
    exact account_change_consistent.by_own_code hTheta
  · have he_lt : e < 1024 := by omega
    set e' := e + 1 with he'
    cases hprecomp : (toExecute σ r)
    · by_cases hacc_eq_r : (acc = r)
      · simp [account_changes_consistent]
        apply Relation.ReflTransGen.single
        subst acc
        exact account_change_consistent.by_own_code hTheta
      · unfold Θ at hTheta
        simp [hprecomp] at hTheta
        split at hTheta <;> rename_i hsplit0
        · split at hTheta <;> rename_i hsplit1
          · rw [← hTheta.right.left]
            simp at hTheta
            simp [hTheta.right.right.right.right.left]
            apply account_changes_consistent_rfl
          · simp at hsplit1
        · split at hTheta <;> rename_i hsplit1
          · rw [← hTheta.right.left]
            simp [hsplit1] at hTheta;
            simp [hTheta.right.right.right.right.left]
            apply account_changes_consistent_rfl
          · rw [← hTheta.right.left]
            simp at hsplit1
        · split at hTheta <;> rename_i h_empty
          · rw [← hTheta.right.left]
            simp at h_empty
            simp [h_empty] at hTheta
            simp [hTheta.right.right.right.right.left]
            apply account_changes_consistent_rfl
          · simp [← hTheta.right.left]
            simp at h_empty; simp [h_empty] at hTheta
            rename_i code' _ _ σStarStar _ _ _
            split at hsplit0 <;> rename_i heq0
            · split at hsplit0 <;> rename_i heq1
              · split at hsplit0 <;> rename_i heq2
                · generalize hσᵢ : Batteries.RBMap.insert σ r { nonce := (default: Account).nonce, balance := v, storage := (default : Account).storage, code := (default : Account).code, tstorage := (default : Account).tstorage } = σᵢ
                  rw [hσᵢ] at hsplit0
                  generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := e, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
                  rw [henvᵢ] at hsplit0
                  have : (sendEth r s v z σ) = σᵢ := by
                    subst σᵢ
                    simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                    grind
                  rw [this]
                  apply account_changes_consistent_of_Xi_succ_depth at hsplit0
                  · apply hsplit0 acc; simp [← henvᵢ]; assumption
                  · exact blobVersionedHashes
                  · exact acc
                  · exact n'
                  · simp [← henvᵢ]; exact he
                  · intros
                    rename_i he_i hTheta'
                    apply ih
                    · exact he_i
                    · subst e'
                      omega
                · generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := e, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
                  rw [henvᵢ] at hsplit0
                  have : (sendEth r s v z σ) = σ := by
                    simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                    grind
                  rw [this]
                  apply account_changes_consistent_of_Xi_succ_depth at hsplit0
                  · apply hsplit0 acc; simp [← henvᵢ]; assumption
                  · exact blobVersionedHashes
                  · exact acc
                  · exact n'
                  · simp [← henvᵢ]; exact he
                  · intros
                    rename_i he_i hTheta'
                    apply ih
                    · exact he_i
                    · subst e'
                      omega
              · rename_i σ_r
                generalize hσᵢ : Batteries.RBMap.insert σ r { nonce := σ_r.nonce, balance := σ_r.balance + v, storage := σ_r.storage, code := σ_r.code, tstorage := σ_r.tstorage } = σᵢ
                rw [hσᵢ] at hsplit0
                generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := e, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
                rw [henvᵢ] at hsplit0
                have : (sendEth r s v z σ) = σᵢ := by
                  subst σᵢ
                  simp [sendEth, hTheta.right.right.right.right.left, heq1]
                  grind
                rw [this]
                apply account_changes_consistent_of_Xi_succ_depth at hsplit0
                · apply hsplit0 acc; simp [← henvᵢ]; assumption
                · exact blobVersionedHashes
                · exact acc
                · exact n'
                · simp [← henvᵢ]; exact he
                · intros
                  rename_i he_i hTheta'
                  apply ih
                  · exact he_i
                  · subst e'
                    omega
            · rename_i σ_r
              split at hsplit0 <;> rename_i heq1
              · split at hsplit0 <;> rename_i heq2
                · generalize hσᵢ : ((Batteries.RBMap.insert σ r
                        { nonce := (default : Account).nonce, balance := v, storage := (default : Account).storage, code := (default : Account).code,
                          tstorage := (default : Account).tstorage }).insert
                    s
                    { nonce := σ_r.nonce, balance := σ_r.balance - v, storage := σ_r.storage, code := σ_r.code,
                      tstorage := σ_r.tstorage }) = σᵢ
                  rw [hσᵢ] at hsplit0
                  generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := e, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
                  rw [henvᵢ] at hsplit0
                  have : (sendEth r s v z σ) = σᵢ := by
                    subst σᵢ
                    simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                    grind
                  rw [this]
                  apply account_changes_consistent_of_Xi_succ_depth at hsplit0
                  · apply hsplit0 acc; simp [← henvᵢ]; assumption
                  · exact blobVersionedHashes
                  · exact acc
                  · exact n'
                  · simp [← henvᵢ]; exact he
                  · intros
                    rename_i he_i hTheta'
                    apply ih
                    · exact he_i
                    · subst e'
                      omega
                · generalize hσᵢ : (Batteries.RBMap.insert σ s
                    { nonce := σ_r.nonce, balance := σ_r.balance - v, storage := σ_r.storage, code := σ_r.code,
                      tstorage := σ_r.tstorage }) = σᵢ
                  rw [hσᵢ] at hsplit0
                  generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := e, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
                  rw [henvᵢ] at hsplit0
                  have : (sendEth r s v z σ) = σᵢ := by
                    subst σᵢ
                    simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                    grind
                  rw [this]
                  apply account_changes_consistent_of_Xi_succ_depth at hsplit0
                  · apply hsplit0 acc; simp [← henvᵢ]; assumption
                  · exact blobVersionedHashes
                  · exact acc
                  · exact n'
                  · simp [← henvᵢ]; exact he
                  · intros
                    rename_i he_i hTheta'
                    apply ih
                    · exact he_i
                    · subst e'
                      omega
              · rename_i σ_r'
                generalize hσᵢ : ((Batteries.RBMap.insert σ r
                      { nonce := σ_r'.nonce, balance := σ_r'.balance + v, storage := σ_r'.storage, code := σ_r'.code,
                        tstorage := σ_r'.tstorage }).insert
                  s
                  { nonce := σ_r.nonce, balance := σ_r.balance - v, storage := σ_r.storage, code := σ_r.code,
                    tstorage := σ_r.tstorage }) = σᵢ
                rw [hσᵢ] at hsplit0
                generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := e, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
                rw [henvᵢ] at hsplit0
                have : (sendEth r s v z σ) = σᵢ := by
                  subst σᵢ
                  simp [sendEth, hTheta.right.right.right.right.left, heq1]
                  grind
                rw [this]
                apply account_changes_consistent_of_Xi_succ_depth at hsplit0
                · apply hsplit0 acc; simp [← henvᵢ]; assumption
                · exact blobVersionedHashes
                · exact acc
                · exact n'
                · simp [← henvᵢ]; exact he
                · intros
                  rename_i he_i hTheta'
                  apply ih
                  · exact he_i
                  · subst e'
                    omega

    · apply account_changes_consistent_of_precompiled_Theta
      · exact hTheta
      · exact hprecomp

theorem account_changes_consistent_of_Theta_and_Lambda :
    ∀ a createdAccounts' σ' g' A' z o' e,
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀  A s o r (toExecute σ r) g p v v' d e H w = (createdAccounts', σ', g', A', z, o') →
      ∀ acc, account_changes_consistent acc (sendEth r s v z σ) σ') ∧
    (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀  A s o  g p v i (.ofNat 1025 1024) ζ H w = (a, createdAccounts', σ', g', A', z, o') →
      ∀ acc, account_changes_consistent acc (sendEth r s v z σ) σ')
    := by
intros a createdAccounts' σ' g' A' z o' e
generalize hn : 1024 - e.val = n
revert e σ σ₀ A s o r g p v v' d H w createdAccounts' σ' A' g' z o'
induction n with
| zero =>
  intros σ σ₀ A s o r g p v v' d H w createdAccounts' σ' A' g' z o' e he
  have he_eq : e = 1024 := by omega
  subst e
  apply And.intro
  · intro hTheta; apply account_changes_consistent_of_Theta_max_depth; exact hTheta
  · intro hLambda; _
| succ n' ih =>
  intros σ σ₀ A s o r g p v v' d H w createdAccounts' σ' A' g' z o' e he hTheta
  by_cases hacc_eq_r : (acc = r)
  · simp [account_changes_consistent]
    apply Relation.ReflTransGen.single
    subst acc
    exact account_change_consistent.by_own_code hTheta
  · have he_lt : e < 1024 := by omega
    set e' := e + 1 with he'
    cases hprecomp : (toExecute σ r)
    · by_cases hacc_eq_r : (acc = r)
      · simp [account_changes_consistent]
        apply Relation.ReflTransGen.single
        subst acc
        exact account_change_consistent.by_own_code hTheta
      · unfold Θ at hTheta
        simp [hprecomp] at hTheta
        split at hTheta <;> rename_i hsplit0
        · split at hTheta <;> rename_i hsplit1
          · rw [← hTheta.right.left]
            simp at hTheta
            simp [hTheta.right.right.right.right.left]
            apply account_changes_consistent_rfl
          · simp at hsplit1
        · split at hTheta <;> rename_i hsplit1
          · rw [← hTheta.right.left]
            simp [hsplit1] at hTheta;
            simp [hTheta.right.right.right.right.left]
            apply account_changes_consistent_rfl
          · rw [← hTheta.right.left]
            simp at hsplit1
        · split at hTheta <;> rename_i h_empty
          · rw [← hTheta.right.left]
            simp at h_empty
            simp [h_empty] at hTheta
            simp [hTheta.right.right.right.right.left]
            apply account_changes_consistent_rfl
          · simp [← hTheta.right.left]
            simp at h_empty; simp [h_empty] at hTheta
            rename_i code' _ _ σStarStar _ _ _
            split at hsplit0 <;> rename_i heq0
            · split at hsplit0 <;> rename_i heq1
              · split at hsplit0 <;> rename_i heq2
                · generalize hσᵢ : Batteries.RBMap.insert σ r { nonce := (default: Account).nonce, balance := v, storage := (default : Account).storage, code := (default : Account).code, tstorage := (default : Account).tstorage } = σᵢ
                  rw [hσᵢ] at hsplit0
                  generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := e, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
                  rw [henvᵢ] at hsplit0
                  have : (sendEth r s v z σ) = σᵢ := by
                    subst σᵢ
                    simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                    grind
                  rw [this]
                  apply account_changes_consistent_of_Xi_succ_depth at hsplit0
                  · apply hsplit0 acc; simp [← henvᵢ]; assumption
                  · exact blobVersionedHashes
                  · exact acc
                  · exact n'
                  · simp [← henvᵢ]; exact he
                  · intros
                    rename_i he_i hTheta'
                    apply ih
                    · exact he_i
                    · subst e'
                      omega
                · generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := e, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
                  rw [henvᵢ] at hsplit0
                  have : (sendEth r s v z σ) = σ := by
                    simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                    grind
                  rw [this]
                  apply account_changes_consistent_of_Xi_succ_depth at hsplit0
                  · apply hsplit0 acc; simp [← henvᵢ]; assumption
                  · exact blobVersionedHashes
                  · exact acc
                  · exact n'
                  · simp [← henvᵢ]; exact he
                  · intros
                    rename_i he_i hTheta'
                    apply ih
                    · exact he_i
                    · subst e'
                      omega
              · rename_i σ_r
                generalize hσᵢ : Batteries.RBMap.insert σ r { nonce := σ_r.nonce, balance := σ_r.balance + v, storage := σ_r.storage, code := σ_r.code, tstorage := σ_r.tstorage } = σᵢ
                rw [hσᵢ] at hsplit0
                generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := e, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
                rw [henvᵢ] at hsplit0
                have : (sendEth r s v z σ) = σᵢ := by
                  subst σᵢ
                  simp [sendEth, hTheta.right.right.right.right.left, heq1]
                  grind
                rw [this]
                apply account_changes_consistent_of_Xi_succ_depth at hsplit0
                · apply hsplit0 acc; simp [← henvᵢ]; assumption
                · exact blobVersionedHashes
                · exact acc
                · exact n'
                · simp [← henvᵢ]; exact he
                · intros
                  rename_i he_i hTheta'
                  apply ih
                  · exact he_i
                  · subst e'
                    omega
            · rename_i σ_r
              split at hsplit0 <;> rename_i heq1
              · split at hsplit0 <;> rename_i heq2
                · generalize hσᵢ : ((Batteries.RBMap.insert σ r
                        { nonce := (default : Account).nonce, balance := v, storage := (default : Account).storage, code := (default : Account).code,
                          tstorage := (default : Account).tstorage }).insert
                    s
                    { nonce := σ_r.nonce, balance := σ_r.balance - v, storage := σ_r.storage, code := σ_r.code,
                      tstorage := σ_r.tstorage }) = σᵢ
                  rw [hσᵢ] at hsplit0
                  generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := e, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
                  rw [henvᵢ] at hsplit0
                  have : (sendEth r s v z σ) = σᵢ := by
                    subst σᵢ
                    simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                    grind
                  rw [this]
                  apply account_changes_consistent_of_Xi_succ_depth at hsplit0
                  · apply hsplit0 acc; simp [← henvᵢ]; assumption
                  · exact blobVersionedHashes
                  · exact acc
                  · exact n'
                  · simp [← henvᵢ]; exact he
                  · intros
                    rename_i he_i hTheta'
                    apply ih
                    · exact he_i
                    · subst e'
                      omega
                · generalize hσᵢ : (Batteries.RBMap.insert σ s
                    { nonce := σ_r.nonce, balance := σ_r.balance - v, storage := σ_r.storage, code := σ_r.code,
                      tstorage := σ_r.tstorage }) = σᵢ
                  rw [hσᵢ] at hsplit0
                  generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := e, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
                  rw [henvᵢ] at hsplit0
                  have : (sendEth r s v z σ) = σᵢ := by
                    subst σᵢ
                    simp [sendEth, hTheta.right.right.right.right.left, heq1, heq2]
                    grind
                  rw [this]
                  apply account_changes_consistent_of_Xi_succ_depth at hsplit0
                  · apply hsplit0 acc; simp [← henvᵢ]; assumption
                  · exact blobVersionedHashes
                  · exact acc
                  · exact n'
                  · simp [← henvᵢ]; exact he
                  · intros
                    rename_i he_i hTheta'
                    apply ih
                    · exact he_i
                    · subst e'
                      omega
              · rename_i σ_r'
                generalize hσᵢ : ((Batteries.RBMap.insert σ r
                      { nonce := σ_r'.nonce, balance := σ_r'.balance + v, storage := σ_r'.storage, code := σ_r'.code,
                        tstorage := σ_r'.tstorage }).insert
                  s
                  { nonce := σ_r.nonce, balance := σ_r.balance - v, storage := σ_r.storage, code := σ_r.code,
                    tstorage := σ_r.tstorage }) = σᵢ
                rw [hσᵢ] at hsplit0
                generalize henvᵢ : { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d, code := code', gasPrice := p.toNat, header := H, depth := e, perm := w, blobVersionedHashes := blobVersionedHashes : ExecutionEnv} = envᵢ
                rw [henvᵢ] at hsplit0
                have : (sendEth r s v z σ) = σᵢ := by
                  subst σᵢ
                  simp [sendEth, hTheta.right.right.right.right.left, heq1]
                  grind
                rw [this]
                apply account_changes_consistent_of_Xi_succ_depth at hsplit0
                · apply hsplit0 acc; simp [← henvᵢ]; assumption
                · exact blobVersionedHashes
                · exact acc
                · exact n'
                · simp [← henvᵢ]; exact he
                · intros
                  rename_i he_i hTheta'
                  apply ih
                  · exact he_i
                  · subst e'
                    omega

    · apply account_changes_consistent_of_precompiled_Theta
      · exact hTheta
      · exact hprecomp

