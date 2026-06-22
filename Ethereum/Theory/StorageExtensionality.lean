import Ethereum.Semantics
import Batteries.Data.RBMap.Lemmas

namespace Ethereum
namespace EVM

/-!
This file proves a conservative account-map extensionality theorem for the
top-level message-call and contract-creation functions.

The storage component is compared extensionally: for every slot, both storages
either do not contain the slot or contain the same value.
-/

instance : Std.TransCmp (compare : UInt256 → UInt256 → Ordering) where
  eq_swap := by
    intro a b
    cases a
    cases b
    simpa [compare, Ethereum.instOrdUInt256.ord] using
      (Std.OrientedCmp.eq_swap
        (cmp := (compare : Fin UInt256.size → Fin UInt256.size → Ordering)))
  isLE_trans := by
    intro a b c hab hbc
    cases a with
    | mk av =>
    cases b with
    | mk bv =>
    cases c with
    | mk cv =>
    have hab' : (compare av bv).isLE = true := by
      simpa [compare, Ethereum.instOrdUInt256.ord] using hab
    have hbc' : (compare bv cv).isLE = true := by
      simpa [compare, Ethereum.instOrdUInt256.ord] using hbc
    have hac' : (compare av cv).isLE = true :=
      Std.TransCmp.isLE_trans
        (cmp := (compare : Fin UInt256.size → Fin UInt256.size → Ordering)) hab' hbc'
    simpa [compare, Ethereum.instOrdUInt256.ord] using hac'

private def rbNodeAll₂TestM {α β} (R : α → β → Bool)
    (t : Batteries.RBNode α) :
    StateT (Batteries.RBNode.Stream β) Option PUnit :=
  t.forM fun a s => do
    let (b, s) ← s.next?
    bif R a b then pure (PUnit.unit, s) else none

private theorem rbNodeAll₂_run_testM_nil {α β} (R : α → β → Bool) :
    ∀ t : Batteries.RBNode α,
      StateT.run (rbNodeAll₂TestM R t)
          (Batteries.RBNode.Stream.nil : Batteries.RBNode.Stream β) =
        match t with
        | .nil => some (PUnit.unit, Batteries.RBNode.Stream.nil)
        | .node .. => none
  | .nil => by rfl
  | .node c l v r => by
      change Option.bind
          (StateT.run (rbNodeAll₂TestM R l)
            (Batteries.RBNode.Stream.nil : Batteries.RBNode.Stream β))
          (fun x => Option.bind
            (((fun a s => do
                let (b, s) ← Batteries.RBNode.Stream.next? s
                bif R a b then pure (PUnit.unit, s) else none) v) x.2)
            (fun y => StateT.run (rbNodeAll₂TestM R r) y.2)) = none
      rw [rbNodeAll₂_run_testM_nil R l]
      cases l <;> simp [rbNodeAll₂TestM, Batteries.RBNode.Stream.next?]

private theorem rbNode_all₂_nil_right {α β} (R : α → β → Bool) :
    ∀ t : Batteries.RBNode α,
      Batteries.RBNode.all₂ R t (.nil : Batteries.RBNode β) =
        match t with
        | .nil => true
        | .node .. => false
  | .nil => by rfl
  | .node c l v r => by
      unfold Batteries.RBNode.all₂
      rw [show (Batteries.RBNode.nil : Batteries.RBNode β).toStream =
          (Batteries.RBNode.Stream.nil : Batteries.RBNode.Stream β) from rfl]
      change
        (match StateT.run (rbNodeAll₂TestM R (Batteries.RBNode.node c l v r))
            (Batteries.RBNode.Stream.nil : Batteries.RBNode.Stream β) with
         | some (_, Batteries.RBNode.Stream.nil) => true
         | _ => false) = false
      rw [rbNodeAll₂_run_testM_nil R (Batteries.RBNode.node c l v r)]

private theorem rbMap_beq_empty_iff_toList_eq_nil {α β}
    {cmp : α → α → Ordering} [BEq α] [BEq β]
    (m : Batteries.RBMap α β cmp) :
    (m == (∅ : Batteries.RBMap α β cmp)) = true ↔
      m.toList = [] := by
  cases m with
  | mk val wf =>
      cases val with
      | nil =>
          constructor
          · intro _; rfl
          · intro _
            change Batteries.RBMap.instBEq._aux_1
              ⟨Batteries.RBNode.nil, wf⟩
              (∅ : Batteries.RBMap α β cmp) = true
            rfl
      | node c l v r =>
          constructor
          · intro h
            change Batteries.RBNode.all₂
              (fun x₁ x₂ : α × β => x₁ == x₂)
              (Batteries.RBNode.node c l v r)
              Batteries.RBNode.nil = true at h
            rw [rbNode_all₂_nil_right] at h
            simp at h
          · intro h
            simp [Batteries.RBMap.toList, Batteries.RBSet.toList] at h

private theorem rbMap_beq_empty_iff_forall_find?_none {α β}
    {cmp : α → α → Ordering} [BEq α] [BEq β] [Std.TransCmp cmp] [Std.ReflCmp cmp]
    (m : Batteries.RBMap α β cmp) :
    (m == (∅ : Batteries.RBMap α β cmp)) = true ↔
      ∀ key, m.find? key = none := by
  constructor
  · intro hempty key
    have hlist := (rbMap_beq_empty_iff_toList_eq_nil m).1 hempty
    cases hfind : m.find? key with
    | none => rfl
    | some value =>
        obtain ⟨foundKey, hmem, _hcmp⟩ :=
          Batteries.RBMap.find?_some_mem_toList hfind
        simp [hlist] at hmem
  · intro hfinds
    apply (rbMap_beq_empty_iff_toList_eq_nil m).2
    cases hlist : m.toList with
    | nil => rfl
    | cons entry entries =>
        rcases entry with ⟨key, value⟩
        have hmem : (key, value) ∈ m.toList := by
          simp [hlist]
        have hfind : m.find? key = some value := by
          rw [Batteries.RBMap.find?_some]
          exact ⟨key, hmem, Std.ReflCmp.compare_self⟩
        rw [hfinds key] at hfind
        contradiction

def storageExtensionalEq (st₁ st₂ : Storage) : Prop :=
  ∀ slot,
    (st₁.find? slot = none ∧ st₂.find? slot = none) ∨
    ∃ value, st₁.find? slot = some value ∧ st₂.find? slot = some value

def accountExtensionalEq (acc₁ acc₂ : Account) : Prop :=
  acc₁.nonce = acc₂.nonce ∧
  acc₁.balance = acc₂.balance ∧
  acc₁.code = acc₂.code ∧
  storageExtensionalEq acc₁.storage acc₂.storage ∧
  storageExtensionalEq acc₁.tstorage acc₂.tstorage

def accountMapExtensionalEq (σ₁ σ₂ : AccountMap) : Prop :=
  ∀ addr,
    match σ₁.find? addr, σ₂.find? addr with
    | none, none => True
    | some acc₁, some acc₂ => accountExtensionalEq acc₁ acc₂
    | _, _ => False

theorem storageExtensionalEq_refl (st : Storage) :
    storageExtensionalEq st st := by
  intro slot
  cases h : st.find? slot with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some value => exact Or.inr ⟨value, rfl, rfl⟩

theorem accountExtensionalEq_refl (acc : Account) :
    accountExtensionalEq acc acc := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> exact storageExtensionalEq_refl _

theorem accountMapExtensionalEq_refl (σ : AccountMap) :
    accountMapExtensionalEq σ σ := by
  intro addr
  cases σ.find? addr <;> simp [accountExtensionalEq_refl]

theorem storageExtensionalEq_symm {st₁ st₂ : Storage}
    (h : storageExtensionalEq st₁ st₂) :
    storageExtensionalEq st₂ st₁ := by
  intro slot
  rcases h slot with ⟨h₁, h₂⟩ | ⟨value, h₁, h₂⟩
  · exact Or.inl ⟨h₂, h₁⟩
  · exact Or.inr ⟨value, h₂, h₁⟩

theorem storageExtensionalEq_findD {st₁ st₂ : Storage}
    (h : storageExtensionalEq st₁ st₂) (slot defaultValue : UInt256) :
    st₁.findD slot defaultValue = st₂.findD slot defaultValue := by
  rcases h slot with ⟨h₁, h₂⟩ | ⟨value, h₁, h₂⟩
  · simp [Batteries.RBMap.findD, h₁, h₂]
  · simp [Batteries.RBMap.findD, h₁, h₂]

theorem storageExtensionalEq_beq_empty {st₁ st₂ : Storage}
    (h : storageExtensionalEq st₁ st₂) :
    (st₁ == (∅ : Storage)) = (st₂ == (∅ : Storage)) := by
  cases h₁ : (st₁ == (∅ : Storage)) <;> cases h₂ : (st₂ == (∅ : Storage))
  · rfl
  · have hnone₂ : ∀ slot, st₂.find? slot = none :=
      (rbMap_beq_empty_iff_forall_find?_none st₂).1 h₂
    have hnone₁ : ∀ slot, st₁.find? slot = none := by
      intro slot
      rcases h slot with ⟨hslot₁, _hslot₂⟩ | ⟨value, _hslot₁, hslot₂⟩
      · exact hslot₁
      · rw [hnone₂ slot] at hslot₂
        contradiction
    have h₁true : (st₁ == (∅ : Storage)) = true :=
      (rbMap_beq_empty_iff_forall_find?_none st₁).2 hnone₁
    simp [h₁] at h₁true
  · have hnone₁ : ∀ slot, st₁.find? slot = none :=
      (rbMap_beq_empty_iff_forall_find?_none st₁).1 h₁
    have hnone₂ : ∀ slot, st₂.find? slot = none := by
      intro slot
      rcases h slot with ⟨_hslot₁, hslot₂⟩ | ⟨value, hslot₁, _hslot₂⟩
      · exact hslot₂
      · rw [hnone₁ slot] at hslot₁
        contradiction
    have h₂true : (st₂ == (∅ : Storage)) = true :=
      (rbMap_beq_empty_iff_forall_find?_none st₂).2 hnone₂
    simp [h₂] at h₂true
  · rfl

theorem storageExtensionalEq_insert_same {st₁ st₂ : Storage}
    (h : storageExtensionalEq st₁ st₂) (slot value : UInt256) :
    storageExtensionalEq (st₁.insert slot value) (st₂.insert slot value) := by
  intro query
  rw [Batteries.RBMap.find?_insert, Batteries.RBMap.find?_insert]
  by_cases hcmp : compare query slot = .eq
  · simp [hcmp]
  · simp [hcmp]
    exact h query

private theorem rbNode_suffix_eq {α} {b' c' b c d : List α} {z y : α}
    (ih : b' ++ z :: c' = b ++ c) :
    b' ++ z :: (c' ++ y :: d) = b ++ (c ++ y :: d) := by
  calc
    b' ++ z :: (c' ++ y :: d) = (b' ++ z :: c') ++ y :: d := by
      simp [List.append_assoc]
    _ = (b ++ c) ++ y :: d := by rw [ih]
    _ = b ++ (c ++ y :: d) := by simp [List.append_assoc]

private theorem rbNode_append_toList {α} : ∀ (l r : Batteries.RBNode α),
    (l.append r).toList = l.toList ++ r.toList
  | .nil, r => by simp [Batteries.RBNode.append]
  | .node c a x b, .nil => by cases c <;> simp [Batteries.RBNode.append]
  | .node .red a x b, .node .black c y d => by
      simp only [Batteries.RBNode.append, Batteries.RBNode.toList_node]
      rw [rbNode_append_toList]
      simp [List.append_assoc]
  | .node .black a x b, .node .red c y d => by
      simp only [Batteries.RBNode.append, Batteries.RBNode.toList_node]
      rw [rbNode_append_toList]
      simp [List.append_assoc]
  | .node .red a x b, .node .red c y d => by
      simp only [Batteries.RBNode.append]
      cases h : Batteries.RBNode.append b c with
      | nil =>
          have hih := rbNode_append_toList b c
          rw [h] at hih
          simp at hih
          simp [hih, List.append_assoc]
      | node col b' z c' =>
          have ih : b'.toList ++ z :: c'.toList = b.toList ++ c.toList := by
            have hih := rbNode_append_toList b c
            rw [h] at hih
            simpa using hih
          cases col <;> simp only [Batteries.RBNode.toList_node]
          · have hs := rbNode_suffix_eq (y := y) (d := d.toList) ih
            simpa [List.append_assoc] using congrArg (fun t => a.toList ++ x :: t) hs
          · simp [rbNode_suffix_eq (y := y) (d := d.toList) ih, List.append_assoc]
  | .node .black a x b, .node .black c y d => by
      simp only [Batteries.RBNode.append]
      cases h : Batteries.RBNode.append b c with
      | nil =>
          have hih := rbNode_append_toList b c
          rw [h] at hih
          simp at hih
          simp [hih, List.append_assoc]
      | node col b' z c' =>
          have ih : b'.toList ++ z :: c'.toList = b.toList ++ c.toList := by
            have hih := rbNode_append_toList b c
            rw [h] at hih
            simpa using hih
          cases col <;> simp only [Batteries.RBNode.toList_node]
          · have hs := rbNode_suffix_eq (y := y) (d := d.toList) ih
            simpa [List.append_assoc] using congrArg (fun t => a.toList ++ x :: t) hs
          · rw [Batteries.RBNode.balLeft_toList]
            simp [rbNode_suffix_eq (y := y) (d := d.toList) ih, List.append_assoc]
termination_by l r => l.size + r.size

private theorem rbNode_filter_all_bool {α} {t : Batteries.RBNode α} {p : α → Bool}
    (h : ∀ x, x ∈ t → p x = true) : t.toList.filter p = t.toList := by
  apply List.filter_eq_self.2
  intro x hx
  exact h x (by simpa using hx)

private theorem rbNode_del_toList_filter {α} {cmp : α → α → Ordering} {cut : α → Ordering}
    [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut] :
    ∀ (t : Batteries.RBNode α), Batteries.RBNode.Ordered cmp t →
      (t.del cut).toList = t.toList.filter (fun x => cut x != .eq)
  | .nil, _ => by simp [Batteries.RBNode.del]
  | .node _ a y b, ht => by
      rcases ht with ⟨hay, hyb, ha, hb⟩
      unfold Batteries.RBNode.del
      cases hy : cut y
      · have hbfilter : b.toList.filter (fun x => cut x != .eq) = b.toList := by
          apply rbNode_filter_all_bool
          intro z hz
          have hzlt : cut z = .lt :=
            Batteries.RBNode.IsCut.lt_trans (Batteries.RBNode.All_def.1 hyb z hz).1 hy
          simp [hzlt]
        cases a.isBlack <;>
          simp [hy, rbNode_del_toList_filter a ha, Batteries.RBNode.balLeft_toList,
            hbfilter]
      · have hafilter : a.toList.filter (fun x => cut x != .eq) = a.toList := by
          apply rbNode_filter_all_bool
          intro z hz
          have hzy : cmp z y = .lt := (Batteries.RBNode.All_def.1 hay z hz).1
          have hyz : cmp y z = .gt := Std.OrientedCmp.gt_iff_lt.2 hzy
          have hcut : cut z = .gt := by
            have htmp : cmp y z = cut z :=
              Batteries.RBNode.IsStrictCut.exact (cmp := cmp) (cut := cut) hy
            simpa [hyz] using htmp.symm
          simp [hcut]
        have hbfilter : b.toList.filter (fun x => cut x != .eq) = b.toList := by
          apply rbNode_filter_all_bool
          intro z hz
          have hyz : cmp y z = .lt := (Batteries.RBNode.All_def.1 hyb z hz).1
          have hcut : cut z = .lt := by
            have htmp : cmp y z = cut z :=
              Batteries.RBNode.IsStrictCut.exact (cmp := cmp) (cut := cut) hy
            simpa [hyz] using htmp.symm
          simp [hcut]
        simp [hy, rbNode_append_toList, hafilter, hbfilter]
      · have hafilter : a.toList.filter (fun x => cut x != .eq) = a.toList := by
          apply rbNode_filter_all_bool
          intro z hz
          have hzgt : cut z = .gt :=
            Batteries.RBNode.IsCut.gt_trans (Batteries.RBNode.All_def.1 hay z hz).1 hy
          simp [hzgt]
        cases b.isBlack <;>
          simp [hy, rbNode_del_toList_filter b hb, Batteries.RBNode.balRight_toList,
            hafilter]
termination_by t => t.size

private theorem rbNode_erase_toList_filter {α} {cmp : α → α → Ordering}
    {cut : α → Ordering} [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut]
    (t : Batteries.RBNode α) (ht : Batteries.RBNode.Ordered cmp t) :
    (t.erase cut).toList = t.toList.filter (fun x => cut x != .eq) := by
  simp [Batteries.RBNode.erase, rbNode_del_toList_filter t ht]

private theorem storage_erase_toList_filter (st : Storage) (slot : UInt256) :
    (st.erase slot).toList = st.toList.filter (fun entry => compare slot entry.1 != .eq) := by
  cases st with
  | mk val wf =>
      exact rbNode_erase_toList_filter val wf.out.1

private theorem storage_find?_erase_eq (st : Storage) (slot query : UInt256)
    (hquery : compare query slot = .eq) :
    (st.erase slot).find? query = none := by
  cases hfind : (st.erase slot).find? query with
  | none => rfl
  | some value =>
      obtain ⟨key, hmem, hcmp⟩ := Batteries.RBMap.find?_some_mem_toList hfind
      rw [storage_erase_toList_filter st slot] at hmem
      simp at hmem
      rcases hmem with ⟨_horig, hnot⟩
      have hslotkey : compare slot key = .eq := by
        have hqkey : compare query key = .eq := hcmp
        rw [Std.TransCmp.congr_left hquery] at hqkey
        exact hqkey
      simp [hslotkey] at hnot

private theorem storage_find?_erase_ne (st : Storage) (slot query : UInt256)
    (hquery : compare query slot ≠ .eq) :
    (st.erase slot).find? query = st.find? query := by
  cases h₁ : (st.erase slot).find? query with
  | none =>
      cases h₂ : st.find? query with
      | none => rfl
      | some value =>
          exfalso
          obtain ⟨key, hmem, hcmp⟩ := Batteries.RBMap.find?_some_mem_toList h₂
          have hslotkey_ne : (compare slot key != .eq) = true := by
            by_contra hfalse
            simp at hfalse
            have hqslot : compare query slot = .eq := by
              have hslotkey : compare slot key = .eq := by simpa using hfalse
              have hkeyslot : compare key slot = .eq := by
                have hswap :=
                  (Std.OrientedCmp.eq_swap (cmp := compare) (a := slot) (b := key))
                rw [hslotkey] at hswap
                simpa using hswap.symm
              have hqkey : compare query key = .eq := hcmp
              rw [Std.TransCmp.congr_right hkeyslot] at hqkey
              exact hqkey
            exact hquery hqslot
          have hmemErase : (key, value) ∈ (st.erase slot).toList := by
            rw [storage_erase_toList_filter st slot]
            simp [hmem, hslotkey_ne]
          have hfindErase : (st.erase slot).find? query = some value := by
            rw [Batteries.RBMap.find?_some]
            exact ⟨key, hmemErase, hcmp⟩
          rw [h₁] at hfindErase
          contradiction
  | some value =>
      obtain ⟨key, hmem, hcmp⟩ := Batteries.RBMap.find?_some_mem_toList h₁
      rw [storage_erase_toList_filter st slot] at hmem
      simp at hmem
      rcases hmem with ⟨hmemOrig, _hnot⟩
      have hfindOrig : st.find? query = some value := by
        rw [Batteries.RBMap.find?_some]
        exact ⟨key, hmemOrig, hcmp⟩
      rw [hfindOrig]

private theorem storage_find?_erase (st : Storage) (slot query : UInt256) :
    (st.erase slot).find? query =
      if compare query slot = .eq then none else st.find? query := by
  by_cases h : compare query slot = .eq
  · simp [h, storage_find?_erase_eq st slot query h]
  · simp [h, storage_find?_erase_ne st slot query h]

theorem storageExtensionalEq_erase_same {st₁ st₂ : Storage}
    (h : storageExtensionalEq st₁ st₂) (slot : UInt256) :
    storageExtensionalEq (st₁.erase slot) (st₂.erase slot) := by
  intro query
  rw [storage_find?_erase, storage_find?_erase]
  by_cases hcmp : compare query slot = .eq
  · simp [hcmp]
  · simp [hcmp]
    exact h query

theorem accountExtensionalEq_symm {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) :
    accountExtensionalEq acc₂ acc₁ := by
  rcases h with ⟨hnonce, hbalance, hcode, hstorage, htstorage⟩
  exact ⟨hnonce.symm, hbalance.symm, hcode.symm,
    storageExtensionalEq_symm hstorage, storageExtensionalEq_symm htstorage⟩

theorem accountExtensionalEq_storage_findD {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) (slot defaultValue : UInt256) :
    acc₁.storage.findD slot defaultValue = acc₂.storage.findD slot defaultValue :=
  storageExtensionalEq_findD h.2.2.2.1 slot defaultValue

theorem accountExtensionalEq_tstorage_findD {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) (slot defaultValue : UInt256) :
    acc₁.tstorage.findD slot defaultValue = acc₂.tstorage.findD slot defaultValue :=
  storageExtensionalEq_findD h.2.2.2.2 slot defaultValue

theorem accountExtensionalEq_with_nonce {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) (nonce : UInt256) :
    accountExtensionalEq ({ acc₁ with nonce := nonce } : Account)
      ({ acc₂ with nonce := nonce } : Account) := by
  rcases h with ⟨_hnonce, hbalance, hcode, hstorage, htstorage⟩
  exact ⟨rfl, hbalance, hcode, hstorage, htstorage⟩

theorem accountExtensionalEq_inc_nonce {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) :
    accountExtensionalEq ({ acc₁ with nonce := acc₁.nonce + ⟨1⟩ } : Account)
      ({ acc₂ with nonce := acc₂.nonce + ⟨1⟩ } : Account) := by
  rcases h with ⟨hnonce, hbalance, hcode, hstorage, htstorage⟩
  exact ⟨by simp [hnonce], hbalance, hcode, hstorage, htstorage⟩

theorem accountExtensionalEq_with_balance {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) (balance : UInt256) :
    accountExtensionalEq ({ acc₁ with balance := balance } : Account)
      ({ acc₂ with balance := balance } : Account) := by
  rcases h with ⟨hnonce, _hbalance, hcode, hstorage, htstorage⟩
  exact ⟨hnonce, rfl, hcode, hstorage, htstorage⟩

theorem accountExtensionalEq_add_balance {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) (amount : UInt256) :
    accountExtensionalEq ({ acc₁ with balance := acc₁.balance + amount } : Account)
      ({ acc₂ with balance := acc₂.balance + amount } : Account) := by
  rcases h with ⟨hnonce, hbalance, hcode, hstorage, htstorage⟩
  exact ⟨hnonce, by simp [hbalance], hcode, hstorage, htstorage⟩

theorem accountExtensionalEq_sub_balance {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) (amount : UInt256) :
    accountExtensionalEq ({ acc₁ with balance := acc₁.balance - amount } : Account)
      ({ acc₂ with balance := acc₂.balance - amount } : Account) := by
  rcases h with ⟨hnonce, hbalance, hcode, hstorage, htstorage⟩
  exact ⟨hnonce, by simp [hbalance], hcode, hstorage, htstorage⟩

theorem accountExtensionalEq_with_code {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) (code : ByteArray) :
    accountExtensionalEq ({ acc₁ with code := code } : Account)
      ({ acc₂ with code := code } : Account) := by
  rcases h with ⟨hnonce, hbalance, _hcode, hstorage, htstorage⟩
  exact ⟨hnonce, hbalance, rfl, hstorage, htstorage⟩

theorem accountExtensionalEq_with_storage {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) {storage₁ storage₂ : Storage}
    (hstorage : storageExtensionalEq storage₁ storage₂) :
    accountExtensionalEq ({ acc₁ with storage := storage₁ } : Account)
      ({ acc₂ with storage := storage₂ } : Account) := by
  rcases h with ⟨hnonce, hbalance, hcode, _hstorage, htstorage⟩
  exact ⟨hnonce, hbalance, hcode, hstorage, htstorage⟩

theorem accountExtensionalEq_with_tstorage {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) {tstorage₁ tstorage₂ : Storage}
    (htstorage : storageExtensionalEq tstorage₁ tstorage₂) :
    accountExtensionalEq ({ acc₁ with tstorage := tstorage₁ } : Account)
      ({ acc₂ with tstorage := tstorage₂ } : Account) := by
  rcases h with ⟨hnonce, hbalance, hcode, hstorage, _htstorage⟩
  exact ⟨hnonce, hbalance, hcode, hstorage, htstorage⟩

theorem accountExtensionalEq_storage_beq_empty {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) :
    (acc₁.storage == (∅ : Storage)) = (acc₂.storage == (∅ : Storage)) :=
  storageExtensionalEq_beq_empty h.2.2.2.1

theorem accountExtensionalEq_updateStorage_insert {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) (slot value : UInt256)
    (hvalue : ¬ value == default) :
    accountExtensionalEq (acc₁.updateStorage slot value) (acc₂.updateStorage slot value) := by
  simp [Account.updateStorage, hvalue]
  exact accountExtensionalEq_with_storage h
    (storageExtensionalEq_insert_same h.2.2.2.1 slot value)

theorem accountExtensionalEq_updateTransientStorage_insert {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) (slot value : UInt256)
    (hvalue : ¬ value == default) :
    accountExtensionalEq
      (acc₁.updateTransientStorage slot value)
      (acc₂.updateTransientStorage slot value) := by
  simp [Account.updateTransientStorage, hvalue]
  exact accountExtensionalEq_with_tstorage h
    (storageExtensionalEq_insert_same h.2.2.2.2 slot value)

theorem accountExtensionalEq_updateStorage {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) (slot value : UInt256) :
    accountExtensionalEq (acc₁.updateStorage slot value) (acc₂.updateStorage slot value) := by
  by_cases hvalue : value == default
  · simp [Account.updateStorage, hvalue]
    exact accountExtensionalEq_with_storage h
      (storageExtensionalEq_erase_same h.2.2.2.1 slot)
  · exact accountExtensionalEq_updateStorage_insert h slot value hvalue

theorem accountExtensionalEq_updateTransientStorage {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) (slot value : UInt256) :
    accountExtensionalEq
      (acc₁.updateTransientStorage slot value)
      (acc₂.updateTransientStorage slot value) := by
  by_cases hvalue : value == default
  · simp [Account.updateTransientStorage, hvalue]
    exact accountExtensionalEq_with_tstorage h
      (storageExtensionalEq_erase_same h.2.2.2.2 slot)
  · exact accountExtensionalEq_updateTransientStorage_insert h slot value hvalue

theorem accountMapExtensionalEq_symm {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) :
    accountMapExtensionalEq σ₂ σ₁ := by
  intro addr
  specialize h addr
  cases h₁ : σ₁.find? addr <;> cases h₂ : σ₂.find? addr <;>
    simp [h₁, h₂] at h ⊢
  exact accountExtensionalEq_symm h

theorem accountMapExtensionalEq_find?_none_left {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) {addr : AccountAddress}
    (hfind : σ₁.find? addr = none) :
    σ₂.find? addr = none := by
  specialize h addr
  rw [hfind] at h
  cases h₂ : σ₂.find? addr <;> simp [h₂] at h ⊢

theorem accountMapExtensionalEq_find?_none_right {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) {addr : AccountAddress}
    (hfind : σ₂.find? addr = none) :
    σ₁.find? addr = none :=
  accountMapExtensionalEq_find?_none_left (accountMapExtensionalEq_symm h) hfind

theorem accountMapExtensionalEq_find?_some_left {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) {addr : AccountAddress} {acc₁ : Account}
    (hfind : σ₁.find? addr = some acc₁) :
    ∃ acc₂, σ₂.find? addr = some acc₂ ∧ accountExtensionalEq acc₁ acc₂ := by
  specialize h addr
  rw [hfind] at h
  cases h₂ : σ₂.find? addr with
  | none => simp [h₂] at h
  | some acc₂ =>
      have hacc : accountExtensionalEq acc₁ acc₂ := by
        simpa [h₂] using h
      exact ⟨acc₂, rfl, hacc⟩

theorem accountMapExtensionalEq_find?_some_right {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) {addr : AccountAddress} {acc₂ : Account}
    (hfind : σ₂.find? addr = some acc₂) :
    ∃ acc₁, σ₁.find? addr = some acc₁ ∧ accountExtensionalEq acc₁ acc₂ := by
  obtain ⟨acc₁, hfind₁, hacc⟩ :=
    accountMapExtensionalEq_find?_some_left (accountMapExtensionalEq_symm h) hfind
  exact ⟨acc₁, hfind₁, accountExtensionalEq_symm hacc⟩

theorem accountMapExtensionalEq_findD {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr : AccountAddress) :
    accountExtensionalEq (σ₁.findD addr default) (σ₂.findD addr default) := by
  specialize h addr
  cases h₁ : σ₁.find? addr <;> cases h₂ : σ₂.find? addr <;>
    simp [Batteries.RBMap.findD, h₁, h₂] at h ⊢
  · exact accountExtensionalEq_refl default
  · exact h

theorem accountMapExtensionalEq_insert_same {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) {addr : AccountAddress}
    {acc₁ acc₂ : Account} (hacc : accountExtensionalEq acc₁ acc₂) :
    accountMapExtensionalEq (σ₁.insert addr acc₁) (σ₂.insert addr acc₂) := by
  intro query
  rw [Batteries.RBMap.find?_insert, Batteries.RBMap.find?_insert]
  by_cases hcmp : compare query addr = .eq
  · simp [hcmp, hacc]
  · simp [hcmp]
    exact h query

theorem accountMapExtensionalEq_debit_if_present {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr : AccountAddress) (value : UInt256) :
    accountMapExtensionalEq
      (match σ₁.find? addr with
        | none => σ₁
        | some acc => σ₁.insert addr { acc with balance := acc.balance - value })
      (match σ₂.find? addr with
        | none => σ₂
        | some acc => σ₂.insert addr { acc with balance := acc.balance - value }) := by
  have hmap := h
  specialize h addr
  cases h₁ : σ₁.find? addr with
  | none =>
      cases h₂ : σ₂.find? addr with
      | none =>
          exact hmap
      | some acc₂ =>
          simp [h₁, h₂] at h
  | some acc₁ =>
      cases h₂ : σ₂.find? addr with
      | none =>
          simp [h₁, h₂] at h
      | some acc₂ =>
          simp [h₁, h₂] at h ⊢
          exact accountMapExtensionalEq_insert_same
            hmap
            (accountExtensionalEq_sub_balance h value)

theorem accountMapExtensionalEq_credit {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr : AccountAddress) (value : UInt256) :
    accountMapExtensionalEq
      (match σ₁.find? addr with
        | none =>
          if value != UInt256.ofNat 0 then
            σ₁.insert addr { (default : Account) with balance := value }
          else
            σ₁
        | some acc =>
          σ₁.insert addr { acc with balance := acc.balance + value })
      (match σ₂.find? addr with
        | none =>
          if value != UInt256.ofNat 0 then
            σ₂.insert addr { (default : Account) with balance := value }
          else
            σ₂
        | some acc =>
          σ₂.insert addr { acc with balance := acc.balance + value }) := by
  have haddr := h addr
  cases h₁ : σ₁.find? addr with
  | none =>
      cases h₂ : σ₂.find? addr with
      | none =>
          simp [h₁, h₂] at haddr ⊢
          by_cases hv : value != UInt256.ofNat 0
          · have hvne : value ≠ UInt256.ofNat 0 := by
              simpa [bne] using hv
            simp [hvne]
            exact accountMapExtensionalEq_insert_same h
              (accountExtensionalEq_with_balance (accountExtensionalEq_refl default) value)
          · have hveq : value = UInt256.ofNat 0 := by
              simpa [bne] using hv
            simp [hveq]
            exact h
      | some acc₂ =>
          simp [h₁, h₂] at haddr
  | some acc₁ =>
      cases h₂ : σ₂.find? addr with
      | none =>
          simp [h₁, h₂] at haddr
      | some acc₂ =>
          simp [h₁, h₂] at haddr ⊢
          exact accountMapExtensionalEq_insert_same h
            (accountExtensionalEq_add_balance haddr value)

theorem accountMapExtensionalEq_call_prelude {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (recipient sender : AccountAddress)
    (value : UInt256) :
    accountMapExtensionalEq
      (let σ' :=
        match σ₁.find? recipient with
        | none =>
          if value != UInt256.ofNat 0 then
            σ₁.insert recipient { (default : Account) with balance := value }
          else
            σ₁
        | some acc =>
          σ₁.insert recipient { acc with balance := acc.balance + value }
       match σ'.find? sender with
       | none => σ'
       | some acc => σ'.insert sender { acc with balance := acc.balance - value })
      (let σ' :=
        match σ₂.find? recipient with
        | none =>
          if value != UInt256.ofNat 0 then
            σ₂.insert recipient { (default : Account) with balance := value }
          else
            σ₂
        | some acc =>
          σ₂.insert recipient { acc with balance := acc.balance + value }
       match σ'.find? sender with
       | none => σ'
       | some acc => σ'.insert sender { acc with balance := acc.balance - value }) := by
  exact accountMapExtensionalEq_debit_if_present
    (accountMapExtensionalEq_credit h recipient value) sender value

theorem accountMapExtensionalEq_create_prelude {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (created sender : AccountAddress)
    (value : UInt256) :
    accountMapExtensionalEq
      (match σ₁.find? sender with
        | none => σ₁
        | some acc =>
          σ₁.insert sender { acc with balance := acc.balance - value }
            |>.insert created
              { (σ₁.findD created default) with
                nonce := (σ₁.findD created default).nonce + ⟨1⟩
                balance := value + (σ₁.findD created default).balance })
      (match σ₂.find? sender with
        | none => σ₂
        | some acc =>
          σ₂.insert sender { acc with balance := acc.balance - value }
            |>.insert created
              { (σ₂.findD created default) with
                nonce := (σ₂.findD created default).nonce + ⟨1⟩
                balance := value + (σ₂.findD created default).balance }) := by
  have hsender := h sender
  cases h₁ : σ₁.find? sender with
  | none =>
      cases h₂ : σ₂.find? sender with
      | none =>
          exact h
      | some acc₂ =>
          simp [h₁, h₂] at hsender
  | some acc₁ =>
      cases h₂ : σ₂.find? sender with
      | none =>
          simp [h₁, h₂] at hsender
      | some acc₂ =>
          simp [h₁, h₂] at hsender ⊢
          have hdebited : accountMapExtensionalEq
              (σ₁.insert sender { acc₁ with balance := acc₁.balance - value })
              (σ₂.insert sender { acc₂ with balance := acc₂.balance - value }) :=
            accountMapExtensionalEq_insert_same h
              (accountExtensionalEq_sub_balance hsender value)
          have hcreated :
              accountExtensionalEq
                { (σ₁.findD created default) with
                  nonce := (σ₁.findD created default).nonce + ⟨1⟩
                  balance := value + (σ₁.findD created default).balance }
                { (σ₂.findD created default) with
                  nonce := (σ₂.findD created default).nonce + ⟨1⟩
                  balance := value + (σ₂.findD created default).balance } := by
            have hbase := accountMapExtensionalEq_findD h created
            rcases hbase with ⟨hnonce, hbalance, hcode, hstorage, htstorage⟩
            exact ⟨by simp [hnonce], by simp [hbalance], hcode, hstorage, htstorage⟩
          exact accountMapExtensionalEq_insert_same hdebited hcreated

theorem accountExtensionalEq_emptyAccount {acc₁ acc₂ : Account}
    (h : accountExtensionalEq acc₁ acc₂) :
    Account.emptyAccount acc₁ = Account.emptyAccount acc₂ := by
  rcases h with ⟨hnonce, hbalance, hcode, _hstorage, _htstorage⟩
  simp [Account.emptyAccount, hnonce, hbalance, hcode]

theorem accountMapExtensionalEq_accountExists {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr : AccountAddress) :
    (σ₁.find? addr).isSome = (σ₂.find? addr).isSome := by
  specialize h addr
  cases h₁ : σ₁.find? addr <;> cases h₂ : σ₂.find? addr <;>
    simp [h₁, h₂] at h ⊢

theorem accountMapExtensionalEq_beq_empty {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) :
    (σ₁ == (∅ : AccountMap)) = (σ₂ == (∅ : AccountMap)) := by
  cases h₁ : (σ₁ == (∅ : AccountMap)) <;> cases h₂ : (σ₂ == (∅ : AccountMap))
  · rfl
  · have hnone₂ : ∀ addr, σ₂.find? addr = none :=
      (rbMap_beq_empty_iff_forall_find?_none σ₂).1 h₂
    have hnone₁ : ∀ addr, σ₁.find? addr = none := by
      intro addr
      exact accountMapExtensionalEq_find?_none_right h (hnone₂ addr)
    have h₁true : (σ₁ == (∅ : AccountMap)) = true :=
      (rbMap_beq_empty_iff_forall_find?_none σ₁).2 hnone₁
    simp [h₁] at h₁true
  · have hnone₁ : ∀ addr, σ₁.find? addr = none :=
      (rbMap_beq_empty_iff_forall_find?_none σ₁).1 h₁
    have hnone₂ : ∀ addr, σ₂.find? addr = none := by
      intro addr
      exact accountMapExtensionalEq_find?_none_left h (hnone₁ addr)
    have h₂true : (σ₂ == (∅ : AccountMap)) = true :=
      (rbMap_beq_empty_iff_forall_find?_none σ₂).2 hnone₂
    simp [h₂] at h₂true
  · rfl

theorem accountMapExtensionalEq_dead {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr : AccountAddress) :
    Ethereum.State.dead σ₁ addr = Ethereum.State.dead σ₂ addr := by
  unfold Ethereum.State.dead
  specialize h addr
  cases h₁ : σ₁.find? addr <;> cases h₂ : σ₂.find? addr <;>
    simp [h₁, h₂] at h ⊢
  exact accountExtensionalEq_emptyAccount h

theorem accountMapExtensionalEq_Cnew {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (target : AccountAddress) (value : UInt256) :
    Cnew target value σ₁ = Cnew target value σ₂ := by
  simp [Cnew, accountMapExtensionalEq_dead h target]

theorem accountMapExtensionalEq_Cextra {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (target recipient : AccountAddress)
    (value : UInt256) (substate : Substate) :
    Cextra target recipient value σ₁ substate =
      Cextra target recipient value σ₂ substate := by
  simp [Cextra, accountMapExtensionalEq_Cnew h recipient value]

theorem accountMapExtensionalEq_Cgascap {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (target recipient : AccountAddress)
    (value gas : UInt256) (machine : MachineState) (substate : Substate) :
    Cgascap target recipient value gas σ₁ machine substate =
      Cgascap target recipient value gas σ₂ machine substate := by
  simp [Cgascap, accountMapExtensionalEq_Cextra h target recipient value substate]

theorem accountMapExtensionalEq_Ccallgas {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (target recipient : AccountAddress)
    (value gas : UInt256) (machine : MachineState) (substate : Substate) :
    Ccallgas target recipient value gas σ₁ machine substate =
      Ccallgas target recipient value gas σ₂ machine substate := by
  have hcap := accountMapExtensionalEq_Cgascap h target recipient value gas machine substate
  unfold Ccallgas
  split <;> simp [hcap]

theorem accountMapExtensionalEq_Ccall {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (target recipient : AccountAddress)
    (value gas : UInt256) (machine : MachineState) (substate : Substate) :
    Ccall target recipient value gas σ₁ machine substate =
      Ccall target recipient value gas σ₂ machine substate := by
  simp [Ccall, accountMapExtensionalEq_Cgascap h target recipient value gas machine substate,
    accountMapExtensionalEq_Cextra h target recipient value substate]

theorem accountMapExtensionalEq_toExecute {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr : AccountAddress) :
    toExecute σ₁ addr = toExecute σ₂ addr := by
  unfold toExecute
  by_cases hpre : addr ∈ π
  · simp [hpre]
  · simp [hpre]
    specialize h addr
    cases h₁ : σ₁.find? addr <;> cases h₂ : σ₂.find? addr <;>
      simp [h₁, h₂] at h ⊢
    exact congrArg ToExecute.Code h.2.2.1

theorem accountMapExtensionalEq_balanceOf {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr : AccountAddress) :
    (σ₁.find? addr |>.elim ⟨0⟩ (·.balance)) =
      (σ₂.find? addr |>.elim ⟨0⟩ (·.balance)) := by
  specialize h addr
  cases h₁ : σ₁.find? addr <;> cases h₂ : σ₂.find? addr <;>
    simp [h₁, h₂] at h ⊢
  exact h.2.1

theorem accountMapExtensionalEq_balanceOf_option {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr : AccountAddress) :
    (σ₁.find? addr |>.option ⟨0⟩ (·.balance)) =
      (σ₂.find? addr |>.option ⟨0⟩ (·.balance)) := by
  specialize h addr
  cases h₁ : σ₁.find? addr <;> cases h₂ : σ₂.find? addr <;>
    simp [h₁, h₂] at h ⊢
  exact h.2.1

theorem accountMapExtensionalEq_nonceOf {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr : AccountAddress) :
    (σ₁.find? addr |>.option ⟨0⟩ (·.nonce)) =
      (σ₂.find? addr |>.option ⟨0⟩ (·.nonce)) := by
  specialize h addr
  cases h₁ : σ₁.find? addr <;> cases h₂ : σ₂.find? addr <;>
    simp [h₁, h₂] at h ⊢
  exact h.1

theorem accountMapExtensionalEq_findD_storage_beq_empty {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr : AccountAddress) :
    ((σ₁.findD addr default).storage == (∅ : Storage)) =
      ((σ₂.findD addr default).storage == (∅ : Storage)) :=
  accountExtensionalEq_storage_beq_empty (accountMapExtensionalEq_findD h addr)

theorem accountMapExtensionalEq_create_collision_check {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr : AccountAddress) :
    let existent₁ := σ₁.findD addr default
    let existent₂ := σ₂.findD addr default
    (existent₁.nonce ≠ ⟨0⟩ || existent₁.code.size ≠ 0 ||
      existent₁.storage != default) =
    (existent₂.nonce ≠ ⟨0⟩ || existent₂.code.size ≠ 0 ||
      existent₂.storage != default) := by
  intro existent₁ existent₂
  have hacc := accountMapExtensionalEq_findD h addr
  have hstorage := accountExtensionalEq_storage_beq_empty hacc
  rcases hacc with ⟨hnonce, _hbalance, hcode, _hstorageExt, _htstorageExt⟩
  change
    ((σ₁.findD addr default).nonce ≠ ⟨0⟩ ||
        (σ₁.findD addr default).code.size ≠ 0 ||
        (σ₁.findD addr default).storage != default) =
      ((σ₂.findD addr default).nonce ≠ ⟨0⟩ ||
        (σ₂.findD addr default).code.size ≠ 0 ||
        (σ₂.findD addr default).storage != default)
  simp [hnonce, hcode, bne, hstorage]

theorem accountMapExtensionalEq_storage_findD_of_findD {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr slot defaultValue : UInt256) :
    (σ₁.findD (AccountAddress.ofUInt256 addr) default).storage.findD slot defaultValue =
      (σ₂.findD (AccountAddress.ofUInt256 addr) default).storage.findD slot defaultValue := by
  specialize h (AccountAddress.ofUInt256 addr)
  cases h₁ : σ₁.find? (AccountAddress.ofUInt256 addr) <;>
    cases h₂ : σ₂.find? (AccountAddress.ofUInt256 addr) <;>
    simp [Batteries.RBMap.findD, h₁, h₂] at h ⊢
  exact accountExtensionalEq_storage_findD h slot defaultValue

theorem accountMapExtensionalEq_find!_storage_findD {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (addr : AccountAddress)
    (slot defaultValue : UInt256) :
    (σ₁.find! addr).storage.findD slot defaultValue =
      (σ₂.find! addr).storage.findD slot defaultValue := by
  specialize h addr
  cases h₁ : σ₁.find? addr <;> cases h₂ : σ₂.find? addr <;>
    simp [Batteries.RBMap.find!, h₁, h₂] at h ⊢
  exact accountExtensionalEq_storage_findD h slot defaultValue

theorem accountMapExtensionalEq_if_empty_fallback {σ₁ σ₂ τ₁ τ₂ : AccountMap}
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (hτ : accountMapExtensionalEq τ₁ τ₂)
    (hflag : (τ₁ == (∅ : AccountMap)) = (τ₂ == (∅ : AccountMap))) :
    accountMapExtensionalEq
      (if τ₁ == (∅ : AccountMap) then σ₁ else τ₁)
      (if τ₂ == (∅ : AccountMap) then σ₂ else τ₂) := by
  cases h₁ : (τ₁ == (∅ : AccountMap)) <;>
    cases h₂ : (τ₂ == (∅ : AccountMap)) <;>
    simp [h₁, h₂] at hflag ⊢
  · exact hτ
  · exact hσ

theorem accountMapExtensionalEq_if_empty_fallback_of_extensional {σ₁ σ₂ τ₁ τ₂ : AccountMap}
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (hτ : accountMapExtensionalEq τ₁ τ₂) :
    accountMapExtensionalEq
      (if τ₁ == (∅ : AccountMap) then σ₁ else τ₁)
      (if τ₂ == (∅ : AccountMap) then σ₂ else τ₂) :=
  accountMapExtensionalEq_if_empty_fallback hσ hτ
    (accountMapExtensionalEq_beq_empty hτ)

def stateExtensionalEq (state₁ state₂ : State) : Prop :=
  accountMapExtensionalEq state₁.accountMap state₂.accountMap ∧
  state₁.σ₀ = state₂.σ₀ ∧
  state₁.totalGasUsedInBlock = state₂.totalGasUsedInBlock ∧
  state₁.transactionReceipts = state₂.transactionReceipts ∧
  state₁.substate = state₂.substate ∧
  state₁.executionEnv = state₂.executionEnv ∧
  state₁.machineState = state₂.machineState ∧
  state₁.blocks = state₂.blocks ∧
  state₁.genesisBlockHeader = state₂.genesisBlockHeader ∧
  state₁.createdAccounts = state₂.createdAccounts

theorem stateExtensionalEq_refl (state : State) :
    stateExtensionalEq state state := by
  exact ⟨accountMapExtensionalEq_refl state.accountMap,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem stateExtensionalEq_addAccessedAccount {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (addr : AccountAddress) :
    stateExtensionalEq
      (Ethereum.State.addAccessedAccount state₁ addr)
      (Ethereum.State.addAccessedAccount state₂ addr) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [stateExtensionalEq, Ethereum.State.addAccessedAccount, hσ, hσ₀, hgas,
    hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated]

theorem stateExtensionalEq_addAccessedStorageKey {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (sk : AccountAddress × UInt256) :
    stateExtensionalEq
      (Ethereum.State.addAccessedStorageKey state₁ sk)
      (Ethereum.State.addAccessedStorageKey state₂ sk) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [stateExtensionalEq, Ethereum.State.addAccessedStorageKey, hσ, hσ₀, hgas,
    hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated]

theorem stateExtensionalEq_balance {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (k : UInt256) :
    let r₁ := Ethereum.State.balance state₁ k
    let r₂ := Ethereum.State.balance state₂ k
    stateExtensionalEq r₁.1 r₂.1 ∧ r₁.2 = r₂.2 := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [Ethereum.State.balance]
  constructor
  · exact stateExtensionalEq_addAccessedAccount
      ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
      (AccountAddress.ofUInt256 k)
  · exact accountMapExtensionalEq_balanceOf hσ (AccountAddress.ofUInt256 k)

theorem stateExtensionalEq_selfbalance {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    Ethereum.State.selfbalance state₁ = Ethereum.State.selfbalance state₂ := by
  rcases h with ⟨hσ, _hσ₀, _hgas, _hreceipts, _hsub, henv, _hmachine, _hblocks,
    _hheader, _hcreated⟩
  simp [Ethereum.State.selfbalance]
  rw [← henv]
  exact accountMapExtensionalEq_balanceOf hσ state₁.executionEnv.codeOwner

theorem stateExtensionalEq_extCodeSize {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (addrWord : UInt256) :
    let r₁ := Ethereum.State.extCodeSize state₁ addrWord
    let r₂ := Ethereum.State.extCodeSize state₂ addrWord
    stateExtensionalEq r₁.1 r₂.1 ∧ r₁.2 = r₂.2 := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [Ethereum.State.extCodeSize, Ethereum.State.lookupAccount]
  constructor
  · exact stateExtensionalEq_addAccessedAccount
      ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
      (AccountAddress.ofUInt256 addrWord)
  · specialize hσ (AccountAddress.ofUInt256 addrWord)
    cases h₁ : state₁.accountMap.find? (AccountAddress.ofUInt256 addrWord) <;>
      cases h₂ : state₂.accountMap.find? (AccountAddress.ofUInt256 addrWord) <;>
      simp [h₁, h₂] at hσ ⊢
    exact congrArg (fun code : ByteArray => UInt256.ofNat code.size) hσ.2.2.1

theorem stateExtensionalEq_extCodeHash {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (addrWord : UInt256) :
    let r₁ := Ethereum.State.extCodeHash state₁ addrWord
    let r₂ := Ethereum.State.extCodeHash state₂ addrWord
    stateExtensionalEq r₁.1 r₂.1 ∧ r₁.2 = r₂.2 := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  let addr := AccountAddress.ofUInt256 addrWord
  have hdead := accountMapExtensionalEq_dead hσ addr
  simp [Ethereum.State.extCodeHash, Ethereum.State.lookupAccount]
  constructor
  · by_cases hd₁ : Ethereum.State.dead state₁.accountMap addr
    · have hd₂ : Ethereum.State.dead state₂.accountMap addr = true := by
        simpa [hd₁] using hdead
      simp [addr, hd₁, hd₂]
      exact stateExtensionalEq_addAccessedAccount
        ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
        addr
    · have hd₂ : Ethereum.State.dead state₂.accountMap addr = false := by
        cases hd₂' : Ethereum.State.dead state₂.accountMap addr
        · rfl
        · have : Ethereum.State.dead state₁.accountMap addr = true := by
            simpa [hd₂'] using hdead
          simp [this] at hd₁
      simp [addr, hd₁, hd₂]
      exact stateExtensionalEq_addAccessedAccount
        ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
        addr
  · by_cases hd₁ : Ethereum.State.dead state₁.accountMap addr
    · have hd₂ : Ethereum.State.dead state₂.accountMap addr = true := by
        simpa [hd₁] using hdead
      simp [addr, hd₁, hd₂]
    · have hd₂ : Ethereum.State.dead state₂.accountMap addr = false := by
        cases hd₂' : Ethereum.State.dead state₂.accountMap addr
        · rfl
        · have : Ethereum.State.dead state₁.accountMap addr = true := by
            simpa [hd₂'] using hdead
          simp [this] at hd₁
      simp [addr, hd₁, hd₂]
      specialize hσ addr
      have hd₁' : Ethereum.State.dead state₁.accountMap addr = false := by
        simpa using hd₁
      cases h₁ : state₁.accountMap.find? addr <;>
        cases h₂ : state₂.accountMap.find? addr <;>
        simp [Ethereum.State.dead, h₁, h₂] at hσ hd₁' hd₂ ⊢
      unfold Account.codeHash PersistentAccountState.codeHash
      exact congrArg (fun code : ByteArray =>
        UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC code))) hσ.2.2.1

theorem stateExtensionalEq_blockHash {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (blockNumber : UInt256) :
    Ethereum.State.blockHash state₁ blockNumber =
      Ethereum.State.blockHash state₂ blockNumber := by
  rcases h with ⟨_hσ, _hσ₀, _hgas, _hreceipts, _hsub, henv, _hmachine,
    hblocks, _hheader, _hcreated⟩
  simp [Ethereum.State.blockHash, Ethereum.State.blockHashes, henv, hblocks]

theorem stateExtensionalEq_calldatacopy {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (mstart datastart size : UInt256) :
    stateExtensionalEq
      (calldatacopy state₁ mstart datastart size)
      (calldatacopy state₂ mstart datastart size) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [calldatacopy, stateExtensionalEq, hσ, hσ₀, hgas, hreceipts, hsub,
    henv, hmachine, hblocks, hheader, hcreated]

theorem stateExtensionalEq_codeCopy {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (mstart cstart size : UInt256) :
    stateExtensionalEq
      (codeCopy state₁ mstart cstart size)
      (codeCopy state₂ mstart cstart size) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [codeCopy, stateExtensionalEq, hσ, hσ₀, hgas, hreceipts, hsub, henv,
    hmachine, hblocks, hheader, hcreated]

theorem stateExtensionalEq_extCodeCopy' {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂)
    (acc mstart cstart size : UInt256) :
    stateExtensionalEq
      (extCodeCopy' state₁ acc mstart cstart size)
      (extCodeCopy' state₂ acc mstart cstart size) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let addr := AccountAddress.ofUInt256 acc
  have hcode :
      (σ₁.find? addr).option ByteArray.empty (fun account => account.code) =
        (σ₂.find? addr).option ByteArray.empty (fun account => account.code) := by
    specialize hσ addr
    cases h₁ : σ₁.find? addr <;> cases h₂ : σ₂.find? addr <;>
      simp [h₁, h₂] at hσ ⊢
    exact hσ.2.2.1
  simp [extCodeCopy', Ethereum.State.lookupAccount, addr, stateExtensionalEq,
    hσ, hcode]

theorem stateExtensionalEq_sload {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (slot : UInt256) :
    let r₁ := Ethereum.State.sload state₁ slot
    let r₂ := Ethereum.State.sload state₂ slot
    stateExtensionalEq r₁.1 r₂.1 ∧ r₁.2 = r₂.2 := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  simp [Ethereum.State.sload, Ethereum.State.lookupAccount]
  constructor
  · simp [stateExtensionalEq, Ethereum.State.addAccessedStorageKey, hσ]
  · specialize hσ env₁.codeOwner
    cases h₁ : σ₁.find? env₁.codeOwner <;>
      cases h₂ : σ₂.find? env₁.codeOwner <;>
      simp [h₁, h₂] at hσ ⊢
    exact accountExtensionalEq_storage_findD hσ slot ⟨0⟩

theorem stateExtensionalEq_tload {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (slot : UInt256) :
    let r₁ := Ethereum.State.tload state₁ slot
    let r₂ := Ethereum.State.tload state₂ slot
    stateExtensionalEq r₁.1 r₂.1 ∧ r₁.2 = r₂.2 := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  simp [Ethereum.State.tload, Ethereum.State.lookupAccount]
  constructor
  · exact ⟨hσ, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · specialize hσ env₁.codeOwner
    cases h₁ : σ₁.find? env₁.codeOwner <;>
      cases h₂ : σ₂.find? env₁.codeOwner <;>
      simp [h₁, h₂] at hσ ⊢
    exact accountExtensionalEq_tstorage_findD hσ slot ⟨0⟩

theorem stateExtensionalEq_setAccount {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) {addr : AccountAddress}
    {acc₁ acc₂ : Account} (hacc : accountExtensionalEq acc₁ acc₂) :
    stateExtensionalEq
      (Ethereum.State.setAccount state₁ addr acc₁)
      (Ethereum.State.setAccount state₂ addr acc₂) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [stateExtensionalEq, Ethereum.State.setAccount,
    accountMapExtensionalEq_insert_same hσ hacc, hσ₀, hgas, hreceipts, hsub,
    henv, hmachine, hblocks, hheader, hcreated]

theorem stateExtensionalEq_updateAccount {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) {addr : AccountAddress}
    {acc₁ acc₂ : Account} (hacc : accountExtensionalEq acc₁ acc₂) :
    stateExtensionalEq
      (Ethereum.State.updateAccount addr acc₁ state₁)
      (Ethereum.State.updateAccount addr acc₂ state₂) := by
  simpa [Ethereum.State.updateAccount, Ethereum.State.setAccount]
    using stateExtensionalEq_setAccount h hacc

theorem stateExtensionalEq_with_refundBalance {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (refundBalance : UInt256) :
    stateExtensionalEq
      ({ state₁ with substate.refundBalance := refundBalance } : State)
      ({ state₂ with substate.refundBalance := refundBalance } : State) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [stateExtensionalEq, hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine,
    hblocks, hheader, hcreated]

theorem stateExtensionalEq_tstore_insert {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (slot value : UInt256)
    (hvalue : ¬ value == default) :
    stateExtensionalEq
      (Ethereum.State.tstore state₁ slot value)
      (Ethereum.State.tstore state₂ slot value) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  simp [Ethereum.State.tstore, Ethereum.State.lookupAccount]
  have hσmap : accountMapExtensionalEq σ₁ σ₂ := hσ
  specialize hσ env₁.codeOwner
  cases h₁ : σ₁.find? env₁.codeOwner with
  | none =>
      cases h₂ : σ₂.find? env₁.codeOwner with
      | none =>
          exact ⟨hσmap, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | some acc₂ =>
          simp [h₁, h₂] at hσ
  | some acc₁ =>
      cases h₂ : σ₂.find? env₁.codeOwner with
      | none =>
          simp [h₁, h₂] at hσ
      | some acc₂ =>
          have hacc : accountExtensionalEq acc₁ acc₂ := by
            simpa [h₁, h₂] using hσ
          simp [Ethereum.State.updateAccount, Account.updateTransientStorage, hvalue,
            stateExtensionalEq, Option.option]
          exact accountMapExtensionalEq_insert_same hσmap
            (accountExtensionalEq_with_tstorage hacc
              (storageExtensionalEq_insert_same hacc.2.2.2.2 slot value))

theorem stateExtensionalEq_tstore {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (slot value : UInt256) :
    stateExtensionalEq
      (Ethereum.State.tstore state₁ slot value)
      (Ethereum.State.tstore state₂ slot value) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  simp [Ethereum.State.tstore, Ethereum.State.lookupAccount]
  have hσmap : accountMapExtensionalEq σ₁ σ₂ := hσ
  specialize hσ env₁.codeOwner
  cases h₁ : σ₁.find? env₁.codeOwner with
  | none =>
      cases h₂ : σ₂.find? env₁.codeOwner with
      | none =>
          exact ⟨hσmap, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | some acc₂ =>
          simp [h₁, h₂] at hσ
  | some acc₁ =>
      cases h₂ : σ₂.find? env₁.codeOwner with
      | none =>
          simp [h₁, h₂] at hσ
      | some acc₂ =>
          have hacc : accountExtensionalEq acc₁ acc₂ := by
            simpa [h₁, h₂] using hσ
          simp [Ethereum.State.updateAccount, stateExtensionalEq, Option.option]
          exact accountMapExtensionalEq_insert_same hσmap
            (accountExtensionalEq_updateTransientStorage hacc slot value)

theorem stateExtensionalEq_sstore {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (slot value : UInt256) :
    stateExtensionalEq
      (Ethereum.State.sstore state₁ slot value)
      (Ethereum.State.sstore state₂ slot value) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  have hσmap : accountMapExtensionalEq σ₁ σ₂ := hσ
  have hstate : stateExtensionalEq
      ({ accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
         transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
         machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
         createdAccounts := created₁ } : State)
      ({ accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
         transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
         machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
         createdAccounts := created₁ } : State) := by
    exact ⟨hσmap, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hv : (σ₁.find! env₁.codeOwner).storage.findD slot ⟨0⟩ =
      (σ₂.find! env₁.codeOwner).storage.findD slot ⟨0⟩ :=
    accountMapExtensionalEq_find!_storage_findD hσmap env₁.codeOwner slot ⟨0⟩
  simp [Ethereum.State.sstore, Ethereum.State.lookupAccount]
  specialize hσ env₁.codeOwner
  cases h₁ : σ₁.find? env₁.codeOwner with
  | none =>
      cases h₂ : σ₂.find? env₁.codeOwner with
      | none =>
          simp [Batteries.RBMap.find!, h₁, h₂]
          exact hstate
      | some acc₂ =>
          simp [h₁, h₂] at hσ
  | some acc₁ =>
      cases h₂ : σ₂.find? env₁.codeOwner with
      | none =>
          simp [h₁, h₂] at hσ
      | some acc₂ =>
          have hacc : accountExtensionalEq acc₁ acc₂ := by
            simpa [h₁, h₂] using hσ
          simp [Batteries.RBMap.find!, h₁, h₂] at hv
          simp [Batteries.RBMap.find!, h₁, h₂, hv]
          let base₁ : State :=
            ({ accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
               transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
               machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
               createdAccounts := created₁ } : State)
          let base₂ : State :=
            ({ accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
               transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
               machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
               createdAccounts := created₁ } : State)
          have hbase : stateExtensionalEq
              (Ethereum.State.setAccount base₁ env₁.codeOwner (acc₁.updateStorage slot value)
                |>.addAccessedStorageKey (env₁.codeOwner, slot))
              (Ethereum.State.setAccount base₂ env₁.codeOwner (acc₂.updateStorage slot value)
                |>.addAccessedStorageKey (env₁.codeOwner, slot)) := by
            exact stateExtensionalEq_addAccessedStorageKey
              (stateExtensionalEq_setAccount hstate
                (accountExtensionalEq_updateStorage hacc slot value))
              (env₁.codeOwner, slot)
          exact stateExtensionalEq_with_refundBalance hbase _

theorem stateExtensionalEq_Csstore {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    Csstore state₁ = Csstore state₂ := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  have hv := accountMapExtensionalEq_find!_storage_findD hσ env₁.codeOwner
    (machine₁.stack[0]?.getD default) ⟨0⟩
  simp [Csstore]
  simp [hv]

theorem stateExtensionalEq_Cselfdestruct {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    Cselfdestruct state₁ = Cselfdestruct state₂ := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  simp [Cselfdestruct, accountMapExtensionalEq_dead hσ]
  specialize hσ env₁.codeOwner
  cases h₁ : σ₁.find? env₁.codeOwner <;>
    cases h₂ : σ₂.find? env₁.codeOwner <;>
    simp [h₁, h₂] at hσ ⊢
  simp [Option.option]
  simp [hσ.2.1]

set_option maxHeartbeats 400000 in
theorem stateExtensionalEq_C' {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (instr : Operation) :
    C' state₁ instr = C' state₂ instr := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases instr with
  | StopArith op =>
      cases op <;> simp [C']
  | CompBit op =>
      cases op <;> simp [C']
  | Keccak op =>
      cases op ; simp [C']
  | Env op =>
      cases op <;> simp [C']
  | Block op =>
      cases op <;> simp [C']
  | StackMemFlow op =>
      cases op <;> simp [C']
      exact stateExtensionalEq_Csstore
        (state₁ :=
          { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
            transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
            machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
            createdAccounts := created₁ })
        (state₂ :=
          { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
            transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
            machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
            createdAccounts := created₁ })
        ⟨hσ, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | Push op =>
      cases op <;> simp [C']
  | Dup op =>
      cases op <;> simp [C']
  | Exchange op =>
      cases op <;> simp [C']
  | Log op =>
      cases op <;> simp [C']
  | System op =>
      cases op <;> simp [C', accountMapExtensionalEq_Ccall hσ]
      exact stateExtensionalEq_Cselfdestruct
        (state₁ :=
          { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
            transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
            machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
            createdAccounts := created₁ })
        (state₂ :=
          { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
            transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
            machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
            createdAccounts := created₁ })
        ⟨hσ, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem stateExtensionalEq_memoryExpansionCost {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (instr : Operation) :
    memoryExpansionCost state₁ instr = memoryExpansionCost state₂ instr := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨_hσ, _hσ₀, _hgas, _hreceipts, _hsub, _henv, hmachine,
    _hblocks, _hheader, _hcreated⟩
  subst machine₂
  cases instr <;> simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

theorem stateExtensionalEq_subtract_memoryExpansionCost {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (instr : Operation) :
    stateExtensionalEq
      ({ state₁ with machineState.gasAvailable :=
          state₁.machineState.gasAvailable.subNat (memoryExpansionCost state₁ instr) } : State)
      ({ state₂ with machineState.gasAvailable :=
          state₂.machineState.gasAvailable.subNat (memoryExpansionCost state₂ instr) } : State) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  have hmem := stateExtensionalEq_memoryExpansionCost
    ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
    instr
  simp [stateExtensionalEq, hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine,
    hblocks, hheader, hcreated, hmem]

theorem stateExtensionalEq_Z_charged_cost {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (instr : Operation) :
    let charged₁ : State :=
      { state₁ with machineState.gasAvailable :=
          state₁.machineState.gasAvailable.subNat (memoryExpansionCost state₁ instr) }
    let charged₂ : State :=
      { state₂ with machineState.gasAvailable :=
          state₂.machineState.gasAvailable.subNat (memoryExpansionCost state₂ instr) }
    stateExtensionalEq charged₁ charged₂ ∧ C' charged₁ instr = C' charged₂ instr := by
  intro charged₁ charged₂
  have hcharged := stateExtensionalEq_subtract_memoryExpansionCost h instr
  exact ⟨hcharged, stateExtensionalEq_C' hcharged instr⟩

theorem stateExtensionalEq_with_machineState {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) {machine : MachineState} :
    stateExtensionalEq
      ({ state₁ with machineState := machine } : State)
      ({ state₂ with machineState := machine } : State) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, _hmachine, hblocks,
    hheader, hcreated⟩
  simp [stateExtensionalEq, hσ, hσ₀, hgas, hreceipts, hsub, henv, hblocks,
    hheader, hcreated]

theorem stateExtensionalEq_step_charged {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat) :
    stateExtensionalEq
      ({ ({ state₁ with
          machineState.execLength := state₁.machineState.execLength + 1 } : State) with
          machineState.gasAvailable :=
            ({ state₁ with
              machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat
              gasCost } : State)
      ({ ({ state₂ with
          machineState.execLength := state₂.machineState.execLength + 1 } : State) with
          machineState.gasAvailable :=
            ({ state₂ with
              machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat
              gasCost } : State) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [stateExtensionalEq, hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine,
    hblocks, hheader, hcreated]

theorem stateExtensionalEq_setReturnData {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (r : ByteArray) :
    stateExtensionalEq
      ({ state₁ with machineState := state₁.machineState.setReturnData r } : State)
      ({ state₂ with machineState := state₂.machineState.setReturnData r } : State) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [stateExtensionalEq, MachineState.setReturnData, hσ, hσ₀, hgas, hreceipts,
    hsub, henv, hmachine, hblocks, hheader, hcreated]

theorem stateExtensionalEq_with_executionEnv {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) {env : ExecutionEnv} :
    stateExtensionalEq
      ({ state₁ with executionEnv := env } : State)
      ({ state₂ with executionEnv := env } : State) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, _henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [stateExtensionalEq, hσ, hσ₀, hgas, hreceipts, hsub, hmachine, hblocks,
    hheader, hcreated]

theorem stateExtensionalEq_with_executionEnv_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) {depth : Fin 1025} :
    stateExtensionalEq
      ({ state₁ with executionEnv.depth := depth } : State)
      ({ state₂ with executionEnv.depth := depth } : State) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [stateExtensionalEq, hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine,
    hblocks, hheader, hcreated]

theorem stateExtensionalEq_incrPC {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (pcΔ : Nat := 1) :
    stateExtensionalEq
      (Ethereum.State.incrPC state₁ pcΔ)
      (Ethereum.State.incrPC state₂ pcΔ) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [stateExtensionalEq, Ethereum.State.incrPC, hσ, hσ₀, hgas, hreceipts,
    hsub, henv, hmachine, hblocks, hheader, hcreated]

theorem stateExtensionalEq_replaceStackAndIncrPC {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (stack : Stack UInt256) (pcΔ : Nat := 1) :
    stateExtensionalEq
      (Ethereum.State.replaceStackAndIncrPC state₁ stack pcΔ)
      (Ethereum.State.replaceStackAndIncrPC state₂ stack pcΔ) := by
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
    stateExtensionalEq, hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated]

def exceptStateExtensionalEq
    (r₁ r₂ : Except EVM.ExecutionException State) : Prop :=
  match r₁, r₂ with
  | .ok state₁, .ok state₂ => stateExtensionalEq state₁ state₂
  | .error e₁, .error e₂ => e₁ = e₂
  | _, _ => False

def exceptStateCostExtensionalEq
    (r₁ r₂ : Except EVM.ExecutionException (State × ℕ)) : Prop :=
  match r₁, r₂ with
  | .ok (state₁, cost₁), .ok (state₂, cost₂) =>
      stateExtensionalEq state₁ state₂ ∧ cost₁ = cost₂
  | .error e₁, .error e₂ => e₁ = e₂
  | _, _ => False

def exceptUIntStateExtensionalEq
    (r₁ r₂ : Except EVM.ExecutionException (UInt256 × State)) : Prop :=
  match r₁, r₂ with
  | .ok (value₁, state₁), .ok (value₂, state₂) =>
      value₁ = value₂ ∧ stateExtensionalEq state₁ state₂
  | .error e₁, .error e₂ => e₁ = e₂
  | _, _ => False

def exceptStateRetExtensionalEq
    (r₁ r₂ : Except EVM.ExecutionException (State × Option (HaltCause × ByteArray))) : Prop :=
  match r₁, r₂ with
  | .ok (state₁, ret₁), .ok (state₂, ret₂) =>
      stateExtensionalEq state₁ state₂ ∧ ret₁ = ret₂
  | .error e₁, .error e₂ => e₁ = e₂
  | _, _ => False

def executionResultStateExtensionalEq
    (r₁ r₂ : ExecutionResult State) : Prop :=
  match r₁, r₂ with
  | .success state₁ out₁, .success state₂ out₂ =>
      stateExtensionalEq state₁ state₂ ∧ out₁ = out₂
  | .revert gas₁ out₁, .revert gas₂ out₂ =>
      gas₁ = gas₂ ∧ out₁ = out₂
  | _, _ => False

def exceptExecutionResultStateExtensionalEq
    (r₁ r₂ : Except EVM.ExecutionException (ExecutionResult State)) : Prop :=
  match r₁, r₂ with
  | .ok result₁, .ok result₂ => executionResultStateExtensionalEq result₁ result₂
  | .error e₁, .error e₂ => e₁ = e₂
  | _, _ => False

def executionResultXiExtensionalEq
    (r₁ r₂ :
      ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate)) :
    Prop :=
  match r₁, r₂ with
  | .success (created₁, σ₁, gas₁, substate₁) out₁,
    .success (created₂, σ₂, gas₂, substate₂) out₂ =>
      created₁ = created₂ ∧ accountMapExtensionalEq σ₁ σ₂ ∧ gas₁ = gas₂ ∧
        substate₁ = substate₂ ∧ out₁ = out₂
  | .revert gas₁ out₁, .revert gas₂ out₂ =>
      gas₁ = gas₂ ∧ out₁ = out₂
  | _, _ => False

def exceptExecutionResultXiExtensionalEq
    (r₁ r₂ :
      Except EVM.ExecutionException
        (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))) :
    Prop :=
  match r₁, r₂ with
  | .ok result₁, .ok result₂ => executionResultXiExtensionalEq result₁ result₂
  | .error e₁, .error e₂ => e₁ = e₂
  | _, _ => False

theorem Z_ok_eq_charged_cost {validJumps : Array UInt256} {instr : Operation}
    {state stateZ : State} {cost : ℕ}
    (hZ : Z validJumps instr state = .ok (stateZ, cost)) :
    let charged : State :=
      { state with machineState.gasAvailable :=
          state.machineState.gasAvailable.subNat (memoryExpansionCost state instr) }
    stateZ = charged ∧ cost = C' charged instr := by
  intro charged
  unfold Z at hZ
  by_cases hδ : δ instr = none
  · rw [if_pos hδ] at hZ
    contradiction
  rw [if_neg hδ] at hZ
  by_cases hstack : state.machineState.stack.length < (δ instr).getD 0
  · rw [if_pos hstack] at hZ
    contradiction
  rw [if_neg hstack] at hZ
  by_cases hcost₁ : state.machineState.gasAvailable.toNat < memoryExpansionCost state instr
  · rw [if_pos hcost₁] at hZ
    contradiction
  rw [if_neg hcost₁] at hZ
  by_cases hcost₂ : charged.machineState.gasAvailable.toNat < C' charged instr
  · rw [if_pos (by simpa [charged] using hcost₂)] at hZ
    contradiction
  rw [if_neg (by simpa [charged] using hcost₂)] at hZ
  by_cases hjump :
      instr = Operation.JUMP ∧ Z.notIn charged.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [charged] using hjump)] at hZ
    contradiction
  rw [if_neg (by simpa [charged] using hjump)] at hZ
  by_cases hjumpi :
      instr = Operation.JUMPI ∧ charged.machineState.stack[1]? ≠ some ⟨0⟩ ∧
        Z.notIn charged.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [charged] using hjumpi)] at hZ
    contradiction
  rw [if_neg (by simpa [charged] using hjumpi)] at hZ
  by_cases hreturndata :
      instr = Operation.RETURNDATACOPY ∧
        (charged.machineState.stack.getD 1 ⟨0⟩).toNat +
          (charged.machineState.stack.getD 2 ⟨0⟩).toNat >
            charged.machineState.returnData.size
  · rw [if_pos (by simpa [charged] using hreturndata)] at hZ
    contradiction
  rw [if_neg (by simpa [charged] using hreturndata)] at hZ
  by_cases hstackover :
      charged.machineState.stack.length - (δ instr).getD 0 + (α instr).getD 0 > 1024
  · rw [if_pos (by simpa [charged] using hstackover)] at hZ
    contradiction
  rw [if_neg (by simpa [charged] using hstackover)] at hZ
  by_cases hstatic :
      (¬ charged.executionEnv.perm) ∧
        (instr ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2,
          .LOG3, .LOG4, .TSTORE] ∨
          (instr = .CALL ∧ charged.machineState.stack[2]? ≠ some ⟨0⟩))
  · rw [if_pos (by simpa [charged] using hstatic)] at hZ
    contradiction
  rw [if_neg (by simpa [charged] using hstatic)] at hZ
  by_cases hsstore :
      (instr = .SSTORE) ∧ charged.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos (by simpa [charged] using hsstore)] at hZ
    contradiction
  rw [if_neg (by simpa [charged] using hsstore)] at hZ
  by_cases hcreate :
      instr.isCreate ∧ charged.machineState.stack.getD 2 ⟨0⟩ > ⟨49152⟩
  · rw [if_pos (by simpa [charged] using hcreate)] at hZ
    contradiction
  rw [if_neg (by simpa [charged] using hcreate)] at hZ
  simp at hZ
  exact ⟨hZ.1.symm, hZ.2.symm⟩

theorem stateExtensionalEq_of_Z_ok_ok {state₁ state₂ stateZ₁ stateZ₂ : State}
    {validJumps : Array UInt256} {instr : Operation} {cost₁ cost₂ : ℕ}
    (h : stateExtensionalEq state₁ state₂)
    (hZ₁ : Z validJumps instr state₁ = .ok (stateZ₁, cost₁))
    (hZ₂ : Z validJumps instr state₂ = .ok (stateZ₂, cost₂)) :
    stateExtensionalEq stateZ₁ stateZ₂ ∧ cost₁ = cost₂ := by
  let charged₁ : State :=
    { state₁ with machineState.gasAvailable :=
        state₁.machineState.gasAvailable.subNat (memoryExpansionCost state₁ instr) }
  let charged₂ : State :=
    { state₂ with machineState.gasAvailable :=
        state₂.machineState.gasAvailable.subNat (memoryExpansionCost state₂ instr) }
  have hcharged_cost := stateExtensionalEq_Z_charged_cost h instr
  change stateExtensionalEq charged₁ charged₂ ∧ C' charged₁ instr = C' charged₂ instr
    at hcharged_cost
  have hz₁ := Z_ok_eq_charged_cost (validJumps := validJumps) hZ₁
  have hz₂ := Z_ok_eq_charged_cost (validJumps := validJumps) hZ₂
  change stateZ₁ = charged₁ ∧ cost₁ = C' charged₁ instr at hz₁
  change stateZ₂ = charged₂ ∧ cost₂ = C' charged₂ instr at hz₂
  rw [hz₁.1, hz₂.1, hz₁.2, hz₂.2]
  exact hcharged_cost

theorem Z_extensional {state₁ state₂ : State} {validJumps : Array UInt256} {instr : Operation}
    (h : stateExtensionalEq state₁ state₂) :
    exceptStateCostExtensionalEq (Z validJumps instr state₁) (Z validJumps instr state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let s₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
      createdAccounts := created₁ }
  let s₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
      createdAccounts := created₁ }
  have hs : stateExtensionalEq s₁ s₂ := by
    simp [s₁, s₂, stateExtensionalEq, hσ]
  have hmem := stateExtensionalEq_memoryExpansionCost hs instr
  have hcharged := stateExtensionalEq_Z_charged_cost hs instr
  change
    (let charged₁ : State :=
      { s₁ with machineState.gasAvailable :=
          s₁.machineState.gasAvailable.subNat (memoryExpansionCost s₁ instr) }
     let charged₂ : State :=
      { s₂ with machineState.gasAvailable :=
          s₂.machineState.gasAvailable.subNat (memoryExpansionCost s₂ instr) }
     stateExtensionalEq charged₁ charged₂ ∧ C' charged₁ instr = C' charged₂ instr)
      at hcharged
  change exceptStateCostExtensionalEq (Z validJumps instr s₁) (Z validJumps instr s₂)
  unfold Z
  by_cases hδ : δ instr = none
  · simp [hδ, exceptStateCostExtensionalEq]
  simp [hδ]
  by_cases hstack : machine₁.stack.length < (δ instr).getD 0
  · simp [s₁, s₂, hstack, exceptStateCostExtensionalEq]
  simp [s₁, s₂, hstack]
  by_cases hcost₁ : machine₁.gasAvailable.toNat < memoryExpansionCost s₁ instr
  · have hcost₂ : machine₁.gasAvailable.toNat < memoryExpansionCost s₂ instr := by
      simpa [hmem] using hcost₁
    simp [s₁, s₂, hcost₁, hcost₂, exceptStateCostExtensionalEq]
  have hcost₂ : ¬machine₁.gasAvailable.toNat < memoryExpansionCost s₂ instr := by
    simpa [hmem] using hcost₁
  simp [s₁, s₂, hcost₁, hcost₂]
  let charged₁ : State :=
    { s₁ with machineState.gasAvailable :=
        s₁.machineState.gasAvailable.subNat (memoryExpansionCost s₁ instr) }
  let charged₂ : State :=
    { s₂ with machineState.gasAvailable :=
        s₂.machineState.gasAvailable.subNat (memoryExpansionCost s₂ instr) }
  have hcharged' : stateExtensionalEq charged₁ charged₂ ∧ C' charged₁ instr = C' charged₂ instr := by
    simpa [charged₁, charged₂] using hcharged
  rcases hcharged'.1 with ⟨_hσc, _hσ0c, _hgasc, _hreceiptc, _hsubc, _henv,
    hmachine, _hblocksc, _hheaderc, _hcreatedc⟩
  by_cases hcostc₁ : charged₁.machineState.gasAvailable.toNat < C' charged₁ instr
  · have hcostc₂ : charged₂.machineState.gasAvailable.toNat < C' charged₂ instr := by
      simpa [hmachine, hcharged'.2] using hcostc₁
    have hcostc₁n :
        machine₁.gasAvailable.toNat - memoryExpansionCost s₁ instr < C' charged₁ instr := by
      simpa [charged₁, s₁] using hcostc₁
    have hcostc₂n :
        machine₁.gasAvailable.toNat - memoryExpansionCost s₂ instr < C' charged₂ instr := by
      simpa [charged₂, s₂] using hcostc₂
    rw [if_pos hcostc₁n, if_pos hcostc₂n]
    rfl
  have hcostc₂ : ¬charged₂.machineState.gasAvailable.toNat < C' charged₂ instr := by
    simpa [hmachine, hcharged'.2] using hcostc₁
  have hcostc₁n :
      ¬machine₁.gasAvailable.toNat - memoryExpansionCost s₁ instr < C' charged₁ instr := by
    simpa [charged₁, s₁] using hcostc₁
  have hcostc₂n :
      ¬machine₁.gasAvailable.toNat - memoryExpansionCost s₂ instr < C' charged₂ instr := by
    simpa [charged₂, s₂] using hcostc₂
  rw [if_neg hcostc₁n, if_neg hcostc₂n]
  by_cases hjump : instr = Operation.JUMP ∧ Z.notIn machine₁.stack[0]? validJumps = true
  · rw [if_pos hjump, if_pos hjump]
    rfl
  rw [if_neg hjump, if_neg hjump]
  by_cases hjumpi :
      instr = Operation.JUMPI ∧
        machine₁.stack[1]? ≠ some ⟨0⟩ ∧ Z.notIn machine₁.stack[0]? validJumps = true
  · rw [if_pos hjumpi, if_pos hjumpi]
    rfl
  rw [if_neg hjumpi, if_neg hjumpi]
  by_cases hret :
      instr = Operation.RETURNDATACOPY ∧
        machine₁.returnData.size <
          (machine₁.stack[1]?.getD (⟨0⟩ : UInt256)).toNat +
            (machine₁.stack[2]?.getD (⟨0⟩ : UInt256)).toNat
  · rw [if_pos hret, if_pos hret]
    rfl
  rw [if_neg hret, if_neg hret]
  by_cases hover : machine₁.stack.length - (δ instr).getD 0 + (α instr).getD 0 > 1024
  · rw [if_pos hover, if_pos hover]
    rfl
  rw [if_neg hover, if_neg hover]
  by_cases hstatic :
      env₁.perm = false ∧
        ((instr = Operation.CREATE ∨
            instr = Operation.CREATE2 ∨
              instr = Operation.SSTORE ∨
                instr = Operation.SELFDESTRUCT ∨
                  instr = Operation.LOG0 ∨
                    instr = Operation.LOG1 ∨
                      instr = Operation.LOG2 ∨
                        instr = Operation.LOG3 ∨ instr = Operation.LOG4 ∨ instr = Operation.TSTORE) ∨
          instr = Operation.CALL ∧ machine₁.stack[2]? ≠ some ⟨0⟩)
  · rw [if_pos hstatic, if_pos hstatic]
    rfl
  rw [if_neg hstatic, if_neg hstatic]
  by_cases hsstore₁ :
      instr = Operation.SSTORE ∧
        machine₁.gasAvailable.toNat ≤ GasConstants.Gcallstipend + memoryExpansionCost s₁ instr
  · have hsstore₂ :
        instr = Operation.SSTORE ∧
          machine₁.gasAvailable.toNat ≤ GasConstants.Gcallstipend + memoryExpansionCost s₂ instr := by
      simpa [hmem] using hsstore₁
    rw [if_pos hsstore₁, if_pos hsstore₂]
    rfl
  have hsstore₂ :
      ¬(instr = Operation.SSTORE ∧
        machine₁.gasAvailable.toNat ≤ GasConstants.Gcallstipend + memoryExpansionCost s₂ instr) := by
    simpa [hmem] using hsstore₁
  rw [if_neg hsstore₁, if_neg hsstore₂]
  by_cases hcreate :
      instr.isCreate = true ∧ (⟨49152⟩ : UInt256) <
        machine₁.stack[2]?.getD (⟨0⟩ : UInt256)
  · rw [if_pos hcreate, if_pos hcreate]
    rfl
  rw [if_neg hcreate, if_neg hcreate]
  exact hcharged'

theorem Xstep_extensional_of_step {state₁ state₂ : State} {validJumps : Array UInt256}
    (h : stateExtensionalEq state₁ state₂)
    (hstep : ∀ (cost : Nat) (instr : Operation × Option (UInt256 × Nat))
        (stateZ₁ stateZ₂ : State),
        stateExtensionalEq stateZ₁ stateZ₂ →
          exceptStateExtensionalEq
            (step cost instr {stateZ₁ with executionEnv.depth := state₁.executionEnv.depth})
            (step cost instr {stateZ₂ with executionEnv.depth := state₂.executionEnv.depth})) :
    exceptStateRetExtensionalEq (Xstep validJumps state₁) (Xstep validJumps state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let s₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
      createdAccounts := created₁ }
  let s₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
      createdAccounts := created₁ }
  have hs : stateExtensionalEq s₁ s₂ := by
    simp [s₁, s₂, stateExtensionalEq, hσ]
  set instr : Operation × Option (UInt256 × Nat) :=
    decode env₁.code machine₁.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  have hZ := Z_extensional (state₁ := s₁) (state₂ := s₂)
    (validJumps := validJumps) (instr := op) hs
  simp [Xstep, ← hinstr]
  cases hZ₁ : Z validJumps op s₁ with
  | error e₁ =>
      cases hZ₂ : Z validJumps op s₂ with
      | error e₂ =>
          have he : e₁ = e₂ := by
            simpa [hZ₁, hZ₂, exceptStateCostExtensionalEq] using hZ
          simp [exceptStateRetExtensionalEq, he]
      | ok ok₂ =>
          have hfalse : False := by
            have hz := hZ
            simp [hZ₁, hZ₂, exceptStateCostExtensionalEq] at hz
          exact False.elim hfalse
  | ok ok₁ =>
      cases hZ₂ : Z validJumps op s₂ with
      | error e₂ =>
          have hfalse : False := by
            have hz := hZ
            simp [hZ₁, hZ₂, exceptStateCostExtensionalEq] at hz
          exact False.elim hfalse
      | ok ok₂ =>
          rcases ok₁ with ⟨stateZ₁, cost₁⟩
          rcases ok₂ with ⟨stateZ₂, cost₂⟩
          have hZok : stateExtensionalEq stateZ₁ stateZ₂ ∧ cost₁ = cost₂ := by
            simpa [hZ₁, hZ₂, exceptStateCostExtensionalEq] using hZ
          have hcost : cost₂ = cost₁ := hZok.2.symm
          subst cost₂
          have hstepRel := hstep cost₁ (op, arg) stateZ₁ stateZ₂ hZok.1
          simp [bind, Except.bind]
          cases hs₁ :
              step cost₁ (op, arg) { stateZ₁ with executionEnv.depth := env₁.depth } with
          | error e₁ =>
              cases hs₂ :
                  step cost₁ (op, arg) { stateZ₂ with executionEnv.depth := env₁.depth } with
              | error e₂ =>
                  have he : e₁ = e₂ := by
                    simpa [hs₁, hs₂, exceptStateExtensionalEq] using hstepRel
                  simp [exceptStateRetExtensionalEq, he]
              | ok stepped₂ =>
                  have hfalse : False := by
                    have hsrel := hstepRel
                    simp [hs₁, hs₂, exceptStateExtensionalEq] at hsrel
                  exact False.elim hfalse
          | ok stepped₁ =>
              cases hs₂ :
                  step cost₁ (op, arg) { stateZ₂ with executionEnv.depth := env₁.depth } with
              | error e₂ =>
                  have hfalse : False := by
                    have hsrel := hstepRel
                    simp [hs₁, hs₂, exceptStateExtensionalEq] at hsrel
                  exact False.elim hfalse
              | ok stepped₂ =>
                  have hstepped : stateExtensionalEq stepped₁ stepped₂ := by
                    simpa [hs₁, hs₂, exceptStateExtensionalEq] using hstepRel
                  have hfinal :
                      stateExtensionalEq
                        ({stepped₁ with executionEnv := env₁} : State)
                        ({stepped₂ with executionEnv := env₁} : State) :=
                    stateExtensionalEq_with_executionEnv hstepped
                  have hstepped_copy := hstepped
                  rcases hstepped_copy with ⟨_hσf, _hσ0f, _hgasf, _hreceiptsf,
                    _hsubf, _henvf, hmachinef, _hblocksf, _hheaderf, _hcreatedf⟩
                  have hH :
                      (if op = Operation.RETURN ∨ op = Operation.REVERT then
                          some stepped₁.machineState.H_return
                       else if op = Operation.STOP ∨ op = Operation.SELFDESTRUCT then
                          some ByteArray.empty
                       else none) =
                        (if op = Operation.RETURN ∨ op = Operation.REVERT then
                          some stepped₂.machineState.H_return
                       else if op = Operation.STOP ∨ op = Operation.SELFDESTRUCT then
                          some ByteArray.empty
                       else none) := by
                    simp [hmachinef]
                  simp
                  rw [hH]
                  cases
                    (if op = Operation.RETURN ∨ op = Operation.REVERT then
                        some stepped₂.machineState.H_return
                     else if op = Operation.STOP ∨ op = Operation.SELFDESTRUCT then
                        some ByteArray.empty
                     else none) with
                  | none =>
                      simp [exceptStateRetExtensionalEq, hfinal]
                  | some out =>
                      by_cases hrevert : op = Operation.REVERT
                      · simp [hrevert, exceptStateRetExtensionalEq, hfinal]
                      · simp [hrevert, exceptStateRetExtensionalEq, hfinal]

theorem X_extensional_of_Xstep {state₁ state₂ : State} {validJumps : Array UInt256}
    (fuel : Nat)
    (h : stateExtensionalEq state₁ state₂)
    (hxstep : ∀ state₁ state₂ : State,
      stateExtensionalEq state₁ state₂ →
        exceptStateRetExtensionalEq (Xstep validJumps state₁) (Xstep validJumps state₂)) :
    exceptExecutionResultStateExtensionalEq
      (X fuel validJumps state₁) (X fuel validJumps state₂) := by
  induction fuel generalizing state₁ state₂ with
  | zero =>
      simp [X, exceptExecutionResultStateExtensionalEq]
  | succ fuel ih =>
      simp [X]
      have hstepRel := hxstep state₁ state₂ h
      cases hstep₁ : Xstep validJumps state₁ with
      | error e₁ =>
          cases hstep₂ : Xstep validJumps state₂ with
          | error e₂ =>
              have he : e₁ = e₂ := by
                simpa [hstep₁, hstep₂, exceptStateRetExtensionalEq] using hstepRel
              subst e₁
              rfl
          | ok step₂ =>
              have hfalse : False := by
                have hs := hstepRel
                simp [hstep₁, hstep₂, exceptStateRetExtensionalEq] at hs
              exact False.elim hfalse
      | ok step₁ =>
          cases hstep₂ : Xstep validJumps state₂ with
          | error e₂ =>
              have hfalse : False := by
                have hs := hstepRel
                simp [hstep₁, hstep₂, exceptStateRetExtensionalEq] at hs
              exact False.elim hfalse
          | ok step₂ =>
              rcases step₁ with ⟨next₁, ret₁⟩
              rcases step₂ with ⟨next₂, ret₂⟩
              have hnext_ret : stateExtensionalEq next₁ next₂ ∧ ret₁ = ret₂ := by
                simpa [hstep₁, hstep₂, exceptStateRetExtensionalEq] using hstepRel
              have hret : ret₂ = ret₁ := hnext_ret.2.symm
              subst ret₂
              simp [bind, Except.bind]
              cases ret₁ with
              | none =>
                  have hdepth : state₁.executionEnv.depth = state₂.executionEnv.depth := by
                    exact congrArg ExecutionEnv.depth h.2.2.2.2.2.1
                  have htail :
                      stateExtensionalEq
                        ({next₁ with executionEnv.depth := state₁.executionEnv.depth} : State)
                        ({next₂ with executionEnv.depth := state₂.executionEnv.depth} : State) := by
                    rw [← hdepth]
                    exact stateExtensionalEq_with_executionEnv_depth hnext_ret.1
                  exact ih htail
              | some ret =>
                  rcases ret with ⟨cause, out⟩
                  cases cause with
                  | revert =>
                      have hmachine : next₁.machineState = next₂.machineState := by
                        exact hnext_ret.1.2.2.2.2.2.2.1
                      simp [exceptExecutionResultStateExtensionalEq, executionResultStateExtensionalEq,
                        hmachine]
                  | success =>
                      simp [exceptExecutionResultStateExtensionalEq, executionResultStateExtensionalEq,
                        hnext_ret.1]

theorem Xi_extensional_of_Xstep
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ₁ σ₂ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (hxstep : ∀ state₁ state₂ : State,
      stateExtensionalEq state₁ state₂ →
        exceptStateRetExtensionalEq (Xstep (D_J I.code 0) state₁) (Xstep (D_J I.code 0) state₂)) :
    exceptExecutionResultXiExtensionalEq
      (Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I)
      (Ξ createdAccounts genesisBlockHeader blocks σ₂ σ₀ g A I) := by
  let fresh₁ : State :=
    { (default : State) with
      accountMap := σ₁
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := .ofUInt256 g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }
  let fresh₂ : State :=
    { (default : State) with
      accountMap := σ₂
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := .ofUInt256 g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }
  have hfresh : stateExtensionalEq fresh₁ fresh₂ := by
    simp [fresh₁, fresh₂, stateExtensionalEq, hσ]
  have hX := X_extensional_of_Xstep (state₁ := fresh₁) (state₂ := fresh₂)
    (validJumps := D_J I.code 0) (fuel := UInt256.toNat g + 1) hfresh hxstep
  simp [Ξ]
  cases hX₁ : X (UInt256.toNat g + 1) (D_J I.code 0) fresh₁ with
  | error e₁ =>
      cases hX₂ : X (UInt256.toNat g + 1) (D_J I.code 0) fresh₂ with
      | error e₂ =>
          have he : e₁ = e₂ := by
            simpa [hX₁, hX₂, exceptExecutionResultStateExtensionalEq] using hX
          subst e₁
          rfl
      | ok result₂ =>
          have hfalse : False := by
            have hx := hX
            simp [hX₁, hX₂, exceptExecutionResultStateExtensionalEq] at hx
          exact False.elim hfalse
  | ok result₁ =>
      cases hX₂ : X (UInt256.toNat g + 1) (D_J I.code 0) fresh₂ with
      | error e₂ =>
          have hfalse : False := by
            have hx := hX
            simp [hX₁, hX₂, exceptExecutionResultStateExtensionalEq] at hx
          exact False.elim hfalse
      | ok result₂ =>
          have hres : executionResultStateExtensionalEq result₁ result₂ := by
            simpa [hX₁, hX₂, exceptExecutionResultStateExtensionalEq] using hX
          cases result₁ with
          | revert gas₁ out₁ =>
              cases result₂ with
              | revert gas₂ out₂ =>
                  have hrev : gas₁ = gas₂ ∧ out₁ = out₂ := by
                    simpa [executionResultStateExtensionalEq] using hres
                  rw [hrev.1, hrev.2]
                  simp [bind, Except.bind, exceptExecutionResultXiExtensionalEq,
                    executionResultXiExtensionalEq]
              | success state₂ out₂ =>
                  have hfalse : False := by
                    have hr := hres
                    simp [executionResultStateExtensionalEq] at hr
                  exact False.elim hfalse
          | success state₁ out₁ =>
              cases result₂ with
              | revert gas₂ out₂ =>
                  have hfalse : False := by
                    have hr := hres
                    simp [executionResultStateExtensionalEq] at hr
                  exact False.elim hfalse
              | success state₂ out₂ =>
                  have hsucc : stateExtensionalEq state₁ state₂ ∧ out₁ = out₂ := by
                    simpa [executionResultStateExtensionalEq] using hres
                  rcases hsucc.1 with ⟨hmap, _hσ0, _htotal, _hreceipts, hsub,
                    _henv, hmachine, _hblocks, _hheader, hcreated⟩
                  rw [hsucc.2]
                  simp [bind, Except.bind, exceptExecutionResultXiExtensionalEq,
                    executionResultXiExtensionalEq]
                  exact ⟨hcreated, hmap,
                    congrArg (fun machine : MachineState => machine.gasAvailable.toUInt256) hmachine,
                    hsub⟩

theorem Xstep_extensional_of_step_at_depth {state₁ state₂ : State} {validJumps : Array UInt256}
    (h : stateExtensionalEq state₁ state₂) {n : Nat}
    (hdepth : 1024 - state₁.executionEnv.depth.val = n + 1)
    (hstep : ∀ (cost : Nat) (instr : Operation × Option (UInt256 × Nat))
        (stateZ₁ stateZ₂ : State),
        stateExtensionalEq stateZ₁ stateZ₂ →
        1024 - ({stateZ₁ with executionEnv.depth := state₁.executionEnv.depth} : State).executionEnv.depth.val = n + 1 →
          exceptStateExtensionalEq
            (step cost instr {stateZ₁ with executionEnv.depth := state₁.executionEnv.depth})
            (step cost instr {stateZ₂ with executionEnv.depth := state₂.executionEnv.depth})) :
    exceptStateRetExtensionalEq (Xstep validJumps state₁) (Xstep validJumps state₂) := by
  apply Xstep_extensional_of_step h
  intro cost instr stateZ₁ stateZ₂ hZ
  exact hstep cost instr stateZ₁ stateZ₂ hZ (by simpa using hdepth)

theorem X_extensional_of_Xstep_at_depth {state₁ state₂ : State} {validJumps : Array UInt256}
    (fuel : Nat)
    (h : stateExtensionalEq state₁ state₂) {n : Nat}
    (hdepth : 1024 - state₁.executionEnv.depth.val = n + 1)
    (hxstep : ∀ state₁ state₂ : State,
      stateExtensionalEq state₁ state₂ →
      1024 - state₁.executionEnv.depth.val = n + 1 →
        exceptStateRetExtensionalEq (Xstep validJumps state₁) (Xstep validJumps state₂)) :
    exceptExecutionResultStateExtensionalEq
      (X fuel validJumps state₁) (X fuel validJumps state₂) := by
  induction fuel generalizing state₁ state₂ with
  | zero =>
      simp [X, exceptExecutionResultStateExtensionalEq]
  | succ fuel ih =>
      simp [X]
      have hstepRel := hxstep state₁ state₂ h hdepth
      cases hstep₁ : Xstep validJumps state₁ with
      | error e₁ =>
          cases hstep₂ : Xstep validJumps state₂ with
          | error e₂ =>
              have he : e₁ = e₂ := by
                simpa [hstep₁, hstep₂, exceptStateRetExtensionalEq] using hstepRel
              subst e₁
              rfl
          | ok step₂ =>
              have hfalse : False := by
                have hs := hstepRel
                simp [hstep₁, hstep₂, exceptStateRetExtensionalEq] at hs
              exact False.elim hfalse
      | ok step₁ =>
          cases hstep₂ : Xstep validJumps state₂ with
          | error e₂ =>
              have hfalse : False := by
                have hs := hstepRel
                simp [hstep₁, hstep₂, exceptStateRetExtensionalEq] at hs
              exact False.elim hfalse
          | ok step₂ =>
              rcases step₁ with ⟨next₁, ret₁⟩
              rcases step₂ with ⟨next₂, ret₂⟩
              have hnext_ret : stateExtensionalEq next₁ next₂ ∧ ret₁ = ret₂ := by
                simpa [hstep₁, hstep₂, exceptStateRetExtensionalEq] using hstepRel
              have hret : ret₂ = ret₁ := hnext_ret.2.symm
              subst ret₂
              simp [bind, Except.bind]
              cases ret₁ with
              | none =>
                  have hdepthEq : state₁.executionEnv.depth = state₂.executionEnv.depth := by
                    exact congrArg ExecutionEnv.depth h.2.2.2.2.2.1
                  have htail :
                      stateExtensionalEq
                        ({next₁ with executionEnv.depth := state₁.executionEnv.depth} : State)
                        ({next₂ with executionEnv.depth := state₂.executionEnv.depth} : State) := by
                    rw [← hdepthEq]
                    exact stateExtensionalEq_with_executionEnv_depth hnext_ret.1
                  have htailDepth : 1024 - ({next₁ with executionEnv.depth := state₁.executionEnv.depth} : State).executionEnv.depth.val = n + 1 := by
                    simpa using hdepth
                  exact ih htail htailDepth
              | some ret =>
                  rcases ret with ⟨cause, out⟩
                  cases cause with
                  | revert =>
                      have hmachine : next₁.machineState = next₂.machineState := by
                        exact hnext_ret.1.2.2.2.2.2.2.1
                      simp [exceptExecutionResultStateExtensionalEq, executionResultStateExtensionalEq,
                        hmachine]
                  | success =>
                      simp [exceptExecutionResultStateExtensionalEq, executionResultStateExtensionalEq,
                        hnext_ret.1]

theorem Xi_extensional_of_Xstep_at_depth
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ₁ σ₂ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (hσ : accountMapExtensionalEq σ₁ σ₂) {n : Nat}
    (hdepth : 1024 - I.depth.val = n + 1)
    (hxstep : ∀ state₁ state₂ : State,
      stateExtensionalEq state₁ state₂ →
      1024 - state₁.executionEnv.depth.val = n + 1 →
        exceptStateRetExtensionalEq (Xstep (D_J I.code 0) state₁) (Xstep (D_J I.code 0) state₂)) :
    exceptExecutionResultXiExtensionalEq
      (Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I)
      (Ξ createdAccounts genesisBlockHeader blocks σ₂ σ₀ g A I) := by
  let fresh₁ : State :=
    { (default : State) with
      accountMap := σ₁
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := .ofUInt256 g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }
  let fresh₂ : State :=
    { (default : State) with
      accountMap := σ₂
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := .ofUInt256 g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }
  have hfresh : stateExtensionalEq fresh₁ fresh₂ := by
    simp [fresh₁, fresh₂, stateExtensionalEq, hσ]
  have hfreshDepth : 1024 - fresh₁.executionEnv.depth.val = n + 1 := by
    simpa [fresh₁] using hdepth
  have hX := X_extensional_of_Xstep_at_depth (state₁ := fresh₁) (state₂ := fresh₂)
    (validJumps := D_J I.code 0) (fuel := UInt256.toNat g + 1) hfresh hfreshDepth hxstep
  simp [Ξ]
  cases hX₁ : X (UInt256.toNat g + 1) (D_J I.code 0) fresh₁ with
  | error e₁ =>
      cases hX₂ : X (UInt256.toNat g + 1) (D_J I.code 0) fresh₂ with
      | error e₂ =>
          have he : e₁ = e₂ := by
            simpa [hX₁, hX₂, exceptExecutionResultStateExtensionalEq] using hX
          subst e₁
          rfl
      | ok result₂ =>
          have hfalse : False := by
            have hx := hX
            simp [hX₁, hX₂, exceptExecutionResultStateExtensionalEq] at hx
          exact False.elim hfalse
  | ok result₁ =>
      cases hX₂ : X (UInt256.toNat g + 1) (D_J I.code 0) fresh₂ with
      | error e₂ =>
          have hfalse : False := by
            have hx := hX
            simp [hX₁, hX₂, exceptExecutionResultStateExtensionalEq] at hx
          exact False.elim hfalse
      | ok result₂ =>
          have hres : executionResultStateExtensionalEq result₁ result₂ := by
            simpa [hX₁, hX₂, exceptExecutionResultStateExtensionalEq] using hX
          cases result₁ with
          | revert gas₁ out₁ =>
              cases result₂ with
              | revert gas₂ out₂ =>
                  have hrev : gas₁ = gas₂ ∧ out₁ = out₂ := by
                    simpa [executionResultStateExtensionalEq] using hres
                  rw [hrev.1, hrev.2]
                  simp [bind, Except.bind, exceptExecutionResultXiExtensionalEq,
                    executionResultXiExtensionalEq]
              | success state₂ out₂ =>
                  have hfalse : False := by
                    have hr := hres
                    simp [executionResultStateExtensionalEq] at hr
                  exact False.elim hfalse
          | success state₁ out₁ =>
              cases result₂ with
              | revert gas₂ out₂ =>
                  have hfalse : False := by
                    have hr := hres
                    simp [executionResultStateExtensionalEq] at hr
                  exact False.elim hfalse
              | success state₂ out₂ =>
                  have hsucc : stateExtensionalEq state₁ state₂ ∧ out₁ = out₂ := by
                    simpa [executionResultStateExtensionalEq] using hres
                  rcases hsucc.1 with ⟨hmap, _hσ0, _htotal, _hreceipts, hsub,
                    _henv, hmachine, _hblocks, _hheader, hcreated⟩
                  rw [hsucc.2]
                  simp [bind, Except.bind, exceptExecutionResultXiExtensionalEq,
                    executionResultXiExtensionalEq]
                  exact ⟨hcreated, hmap,
                    congrArg (fun machine : MachineState => machine.gasAvailable.toUInt256) hmachine,
                    hsub⟩

theorem exceptStateExtensionalEq_refl (r : Except EVM.ExecutionException State) :
    exceptStateExtensionalEq r r := by
  cases r with
  | ok state => exact stateExtensionalEq_refl state
  | error e => rfl

theorem exceptUIntStateExtensionalEq_replaceStackAndIncrPC
    {r₁ r₂ : Except EVM.ExecutionException (UInt256 × State)}
    (h : exceptUIntStateExtensionalEq r₁ r₂) (stack : Stack UInt256) :
    exceptStateExtensionalEq
      (r₁.bind fun (x, state) => .ok (state.replaceStackAndIncrPC (stack.push x)))
      (r₂.bind fun (x, state) => .ok (state.replaceStackAndIncrPC (stack.push x))) := by
  cases r₁ with
  | error e₁ =>
      cases r₂ with
      | error e₂ =>
          have he : e₁ = e₂ := by
            simpa [exceptUIntStateExtensionalEq] using h
          subst e₂
          rfl
      | ok ok₂ =>
          have hfalse : False := by
            simpa [exceptUIntStateExtensionalEq] using h
          exact False.elim hfalse
  | ok ok₁ =>
      rcases ok₁ with ⟨x₁, state₁⟩
      cases r₂ with
      | error e₂ =>
          have hfalse : False := by
            simpa [exceptUIntStateExtensionalEq] using h
          exact False.elim hfalse
      | ok ok₂ =>
          rcases ok₂ with ⟨x₂, state₂⟩
          have hrel : x₁ = x₂ ∧ stateExtensionalEq state₁ state₂ := by
            simpa [exceptUIntStateExtensionalEq] using h
          rw [← hrel.1]
          exact stateExtensionalEq_replaceStackAndIncrPC hrel.2 (stack.push x₁)

theorem execUnOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (f : Primop.Unary) :
    exceptStateExtensionalEq (execUnOp f state₁) (execUnOp f state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop with
  | none =>
      simp [execUnOp, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀⟩
      simp [execUnOp, hpop, exceptStateExtensionalEq]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
        stateExtensionalEq, hσ]

theorem execBinOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (f : Primop.Binary) :
    exceptStateExtensionalEq (execBinOp f state₁) (execBinOp f state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop2 with
  | none =>
      simp [execBinOp, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁⟩
      simp [execBinOp, hpop, exceptStateExtensionalEq]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
        stateExtensionalEq, hσ]

theorem execTriOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (f : Primop.Ternary) :
    exceptStateExtensionalEq (execTriOp f state₁) (execTriOp f state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop3 with
  | none =>
      simp [execTriOp, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂⟩
      simp [execTriOp, hpop, exceptStateExtensionalEq]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
        stateExtensionalEq, hσ]

theorem executionEnvOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (op : ExecutionEnv → UInt256) :
    exceptStateExtensionalEq (executionEnvOp op state₁) (executionEnvOp op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  simp [executionEnvOp, exceptStateExtensionalEq]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
    stateExtensionalEq, hσ]

theorem step_stoparith_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (op : Operation.SAOp) (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.StopArith op, arg) state₁)
      (step gasCost (.StopArith op, arg) state₂) := by
  let charged₁ : State :=
    { ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  let charged₂ : State :=
    { ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  have hc : stateExtensionalEq charged₁ charged₂ := by
    simpa [charged₁, charged₂] using stateExtensionalEq_step_charged h gasCost
  cases op <;> simp [step]
  · exact stateExtensionalEq_setReturnData hc .empty
  · exact execBinOp_extensional hc UInt256.add
  · exact execBinOp_extensional hc UInt256.mul
  · exact execBinOp_extensional hc UInt256.sub
  · exact execBinOp_extensional hc UInt256.div
  · exact execBinOp_extensional hc UInt256.sdiv
  · exact execBinOp_extensional hc UInt256.mod
  · exact execBinOp_extensional hc UInt256.smod
  · exact execTriOp_extensional hc UInt256.addMod
  · exact execTriOp_extensional hc UInt256.mulMod
  · exact execBinOp_extensional hc UInt256.exp
  · exact execBinOp_extensional hc UInt256.signextend

theorem step_compbit_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (op : Operation.CBLOp) (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.CompBit op, arg) state₁)
      (step gasCost (.CompBit op, arg) state₂) := by
  let charged₁ : State :=
    { ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  let charged₂ : State :=
    { ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  have hc : stateExtensionalEq charged₁ charged₂ := by
    simpa [charged₁, charged₂] using stateExtensionalEq_step_charged h gasCost
  cases op <;> simp [step]
  · exact execBinOp_extensional hc UInt256.lt
  · exact execBinOp_extensional hc UInt256.gt
  · exact execBinOp_extensional hc UInt256.slt
  · exact execBinOp_extensional hc UInt256.sgt
  · exact execBinOp_extensional hc UInt256.eq
  · exact execUnOp_extensional hc UInt256.isZero
  · exact execBinOp_extensional hc UInt256.land
  · exact execBinOp_extensional hc UInt256.lor
  · exact execBinOp_extensional hc UInt256.xor
  · exact execUnOp_extensional hc UInt256.lnot
  · exact execBinOp_extensional hc UInt256.byteAt
  · exact execBinOp_extensional hc (flip UInt256.shiftLeft)
  · exact execBinOp_extensional hc (flip UInt256.shiftRight)
  · exact execBinOp_extensional hc UInt256.sar

theorem machineStateOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (op : MachineState → UInt256) :
    exceptStateExtensionalEq (machineStateOp op state₁) (machineStateOp op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  simp [machineStateOp, exceptStateExtensionalEq]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
    stateExtensionalEq, hσ]

theorem unaryExecutionEnvOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂)
    (op : ExecutionEnv → UInt256 → UInt256) :
    exceptStateExtensionalEq
      (unaryExecutionEnvOp op state₁) (unaryExecutionEnvOp op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop with
  | none =>
      simp [unaryExecutionEnvOp, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀⟩
      simp [unaryExecutionEnvOp, hpop, exceptStateExtensionalEq]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
        stateExtensionalEq, hσ]

theorem stateOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (op : State → UInt256)
    (hop : op state₁ = op state₂) :
    exceptStateExtensionalEq (stateOp op state₁) (stateOp op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  simp [stateOp, exceptStateExtensionalEq] at hop ⊢
  simp [hop, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
    stateExtensionalEq, hσ]

theorem unaryStateOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂)
    (op : State → UInt256 → State × UInt256)
    (hop : ∀ value,
      let r₁ := op state₁ value
      let r₂ := op state₂ value
      stateExtensionalEq r₁.1 r₂.1 ∧ r₁.2 = r₂.2) :
    exceptStateExtensionalEq (unaryStateOp op state₁) (unaryStateOp op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop with
  | none =>
      simp [unaryStateOp, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀⟩
      have hopμ := hop μ₀
      simp [unaryStateOp, hpop, exceptStateExtensionalEq]
      rw [hopμ.2]
      let state₂' : State :=
        { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := gas₁,
          transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
          machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
          createdAccounts := created₁ }
      exact stateExtensionalEq_replaceStackAndIncrPC hopμ.1
        (stack.push (op state₂' μ₀).2)

theorem binaryStateOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂)
    (op : State → UInt256 → UInt256 → State)
    (hop : ∀ value₁ value₂,
      stateExtensionalEq (op state₁ value₁ value₂) (op state₂ value₁ value₂)) :
    exceptStateExtensionalEq (binaryStateOp op state₁) (binaryStateOp op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop2 with
  | none =>
      simp [binaryStateOp, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁⟩
      have hopμ := hop μ₀ μ₁
      simp [binaryStateOp, hpop, exceptStateExtensionalEq]
      exact stateExtensionalEq_replaceStackAndIncrPC hopμ stack

theorem binaryMachineStateOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂)
    (op : MachineState → UInt256 → UInt256 → MachineState) :
    exceptStateExtensionalEq
      (binaryMachineStateOp op state₁) (binaryMachineStateOp op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop2 with
  | none =>
      simp [binaryMachineStateOp, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁⟩
      simp [binaryMachineStateOp, hpop, exceptStateExtensionalEq]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
        stateExtensionalEq, hσ]

theorem binaryMachineStateOp'_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂)
    (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) :
    exceptStateExtensionalEq
      (binaryMachineStateOp' op state₁) (binaryMachineStateOp' op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop2 with
  | none =>
      simp [binaryMachineStateOp', hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁⟩
      simp [binaryMachineStateOp', hpop, exceptStateExtensionalEq]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
        stateExtensionalEq, hσ]

theorem step_keccak_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (op : Operation.KOp) (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.Keccak op, arg) state₁)
      (step gasCost (.Keccak op, arg) state₂) := by
  let charged₁ : State :=
    { ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  let charged₂ : State :=
    { ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  have hc : stateExtensionalEq charged₁ charged₂ := by
    simpa [charged₁, charged₂] using stateExtensionalEq_step_charged h gasCost
  cases op
  simp [step]
  exact binaryMachineStateOp'_extensional hc MachineState.keccak256

theorem ternaryMachineStateOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂)
    (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) :
    exceptStateExtensionalEq
      (ternaryMachineStateOp op state₁) (ternaryMachineStateOp op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop3 with
  | none =>
      simp [ternaryMachineStateOp, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂⟩
      simp [ternaryMachineStateOp, hpop, exceptStateExtensionalEq]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
        stateExtensionalEq, hσ]

theorem ternaryCopyOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂)
    (op : State → UInt256 → UInt256 → UInt256 → State)
    (hop : ∀ value₁ value₂ value₃,
      stateExtensionalEq (op state₁ value₁ value₂ value₃)
        (op state₂ value₁ value₂ value₃)) :
    exceptStateExtensionalEq (ternaryCopyOp op state₁) (ternaryCopyOp op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop3 with
  | none =>
      simp [ternaryCopyOp, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂⟩
      have hopμ := hop μ₀ μ₁ μ₂
      simp [ternaryCopyOp, hpop, exceptStateExtensionalEq]
      exact stateExtensionalEq_replaceStackAndIncrPC hopμ stack

theorem quaternaryCopyOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂)
    (op : State → UInt256 → UInt256 → UInt256 → UInt256 → State)
    (hop : ∀ value₁ value₂ value₃ value₄,
      stateExtensionalEq (op state₁ value₁ value₂ value₃ value₄)
        (op state₂ value₁ value₂ value₃ value₄)) :
    exceptStateExtensionalEq
      (quaternaryCopyOp op state₁) (quaternaryCopyOp op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop4 with
  | none =>
      simp [quaternaryCopyOp, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃⟩
      have hopμ := hop μ₀ μ₁ μ₂ μ₃
      simp [quaternaryCopyOp, hpop, exceptStateExtensionalEq]
      exact stateExtensionalEq_replaceStackAndIncrPC hopμ stack

theorem evmLogOp_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (μ₀ μ₁ : UInt256) (t : Array UInt256) :
    stateExtensionalEq (evmLogOp state₁ μ₀ μ₁ t) (evmLogOp state₂ μ₀ μ₁ t) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  simp [evmLogOp, logOp, stateExtensionalEq, hσ]

theorem log0Op_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    exceptStateExtensionalEq (log0Op state₁) (log0Op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop2 with
  | none =>
      simp [log0Op, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁⟩
      simp [log0Op, hpop, exceptStateExtensionalEq]
      exact stateExtensionalEq_replaceStackAndIncrPC
        (evmLogOp_extensional (h := by simp [stateExtensionalEq, hσ]) μ₀ μ₁ #[])
        stack

theorem log1Op_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    exceptStateExtensionalEq (log1Op state₁) (log1Op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop3 with
  | none =>
      simp [log1Op, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂⟩
      simp [log1Op, hpop, exceptStateExtensionalEq]
      exact stateExtensionalEq_replaceStackAndIncrPC
        (evmLogOp_extensional (h := by simp [stateExtensionalEq, hσ]) μ₀ μ₁ #[μ₂])
        stack

theorem log2Op_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    exceptStateExtensionalEq (log2Op state₁) (log2Op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop4 with
  | none =>
      simp [log2Op, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃⟩
      simp [log2Op, hpop, exceptStateExtensionalEq]
      exact stateExtensionalEq_replaceStackAndIncrPC
        (evmLogOp_extensional (h := by simp [stateExtensionalEq, hσ])
          μ₀ μ₁ #[μ₂, μ₃])
        stack

theorem log3Op_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    exceptStateExtensionalEq (log3Op state₁) (log3Op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop5 with
  | none =>
      simp [log3Op, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄⟩
      simp [log3Op, hpop, exceptStateExtensionalEq]
      exact stateExtensionalEq_replaceStackAndIncrPC
        (evmLogOp_extensional (h := by simp [stateExtensionalEq, hσ])
          μ₀ μ₁ #[μ₂, μ₃, μ₄])
        stack

theorem log4Op_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    exceptStateExtensionalEq (log4Op state₁) (log4Op state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop6 with
  | none =>
      simp [log4Op, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅⟩
      simp [log4Op, hpop, exceptStateExtensionalEq]
      exact stateExtensionalEq_replaceStackAndIncrPC
        (evmLogOp_extensional (h := by simp [stateExtensionalEq, hσ])
          μ₀ μ₁ #[μ₂, μ₃, μ₄, μ₅])
        stack

theorem dup_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (n : ℕ) :
    exceptStateExtensionalEq (dup n state₁) (dup n state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  by_cases hlen : n ≤ machine₁.stack.length
  · simp [dup, hlen, exceptStateExtensionalEq]
    exact stateExtensionalEq_replaceStackAndIncrPC
      (by simp [stateExtensionalEq, hσ]) _
  · simp [dup, hlen, exceptStateExtensionalEq]

theorem swap_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (n : ℕ) :
    exceptStateExtensionalEq (swap n state₁) (swap n state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  by_cases hlen : n + 1 ≤ machine₁.stack.length
  · simp [swap, hlen, exceptStateExtensionalEq]
    exact stateExtensionalEq_replaceStackAndIncrPC
      (by simp [stateExtensionalEq, hσ]) _
  · simp [swap, hlen, exceptStateExtensionalEq]

theorem mload_step_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    exceptStateExtensionalEq
      (match state₁.machineState.stack.pop with
        | some ⟨s, μ₀⟩ =>
            let (v, mState') := state₁.machineState.mload μ₀
            let evmState' := {state₁ with machineState := mState'}
            .ok <| evmState'.replaceStackAndIncrPC (s.push v)
        | _ => .error .StackUnderflow)
      (match state₂.machineState.stack.pop with
        | some ⟨s, μ₀⟩ =>
            let (v, mState') := state₂.machineState.mload μ₀
            let evmState' := {state₂ with machineState := mState'}
            .ok <| evmState'.replaceStackAndIncrPC (s.push v)
        | _ => .error .StackUnderflow) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop with
  | none =>
      simp [exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀⟩
      simp [exceptStateExtensionalEq]
      simp [MachineState.mload, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC, stateExtensionalEq, hσ]

theorem returndatacopy_step_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    exceptStateExtensionalEq
      (match state₁.machineState.stack.pop3 with
        | some ⟨stack', μ₀, μ₁, μ₂⟩ =>
            let mState' := state₁.machineState.returndatacopy μ₀ μ₁ μ₂
            let evmState' := {state₁ with machineState := mState'}
            .ok <| evmState'.replaceStackAndIncrPC stack'
        | _ => .error .StackUnderflow)
      (match state₂.machineState.stack.pop3 with
        | some ⟨stack', μ₀, μ₁, μ₂⟩ =>
            let mState' := state₂.machineState.returndatacopy μ₀ μ₁ μ₂
            let evmState' := {state₂ with machineState := mState'}
            .ok <| evmState'.replaceStackAndIncrPC stack'
        | _ => .error .StackUnderflow) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop3 with
  | none =>
      simp [exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂⟩
      simp [exceptStateExtensionalEq]
      simp [MachineState.returndatacopy, Ethereum.State.replaceStackAndIncrPC,
        Ethereum.State.incrPC, stateExtensionalEq, hσ]

theorem step_env_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (op : Operation.EOp) (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.Env op, arg) state₁)
      (step gasCost (.Env op, arg) state₂) := by
  let charged₁ : State :=
    { ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  let charged₂ : State :=
    { ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  have hc : stateExtensionalEq charged₁ charged₂ := by
    simpa [charged₁, charged₂] using stateExtensionalEq_step_charged h gasCost
  cases op <;> simp [step]
  · exact executionEnvOp_extensional hc (.ofNat ∘ Fin.val ∘ ExecutionEnv.codeOwner)
  · exact unaryStateOp_extensional hc Ethereum.State.balance (by
      intro value
      exact stateExtensionalEq_balance hc value)
  · exact executionEnvOp_extensional hc (.ofNat ∘ Fin.val ∘ ExecutionEnv.sender)
  · exact executionEnvOp_extensional hc (.ofNat ∘ Fin.val ∘ ExecutionEnv.source)
  · exact executionEnvOp_extensional hc ExecutionEnv.weiValue
  · exact unaryStateOp_extensional hc (fun s v => (s, Ethereum.State.calldataload s v)) (by
      intro value
      rcases hc with ⟨hσ, hσ0, hgas, hreceipts, hsub, henv, hmachine, hblocks,
        hheader, hcreated⟩
      constructor
      · exact ⟨hσ, hσ0, hgas, hreceipts, hsub, henv, hmachine, hblocks, hheader,
          hcreated⟩
      · simp [Ethereum.State.calldataload, henv])
  · exact executionEnvOp_extensional hc (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.calldata)
  · exact ternaryCopyOp_extensional hc calldatacopy (by
      intro v₁ v₂ v₃
      exact stateExtensionalEq_calldatacopy hc v₁ v₂ v₃)
  · exact executionEnvOp_extensional hc (.ofNat ∘ ExecutionEnv.gasPrice)
  · exact executionEnvOp_extensional hc (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code)
  · exact ternaryCopyOp_extensional hc codeCopy (by
      intro v₁ v₂ v₃
      exact stateExtensionalEq_codeCopy hc v₁ v₂ v₃)
  · exact unaryStateOp_extensional hc Ethereum.State.extCodeSize (by
      intro value
      exact stateExtensionalEq_extCodeSize hc value)
  · exact quaternaryCopyOp_extensional hc Ethereum.extCodeCopy' (by
      intro v₁ v₂ v₃ v₄
      exact stateExtensionalEq_extCodeCopy' hc v₁ v₂ v₃ v₄)
  · exact machineStateOp_extensional hc Ethereum.MachineState.returndatasize
  · exact returndatacopy_step_extensional hc
  · exact unaryStateOp_extensional hc Ethereum.State.extCodeHash (by
      intro value
      exact stateExtensionalEq_extCodeHash hc value)

theorem step_block_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (op : Operation.BOp) (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.Block op, arg) state₁)
      (step gasCost (.Block op, arg) state₂) := by
  let charged₁ : State :=
    { ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  let charged₂ : State :=
    { ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  have hc : stateExtensionalEq charged₁ charged₂ := by
    simpa [charged₁, charged₂] using stateExtensionalEq_step_charged h gasCost
  cases op <;> simp [step]
  · exact unaryStateOp_extensional hc (fun s v => (s, Ethereum.State.blockHash s v)) (by
      intro value
      exact ⟨hc, stateExtensionalEq_blockHash hc value⟩)
  · exact stateOp_extensional hc (.ofNat ∘ Fin.val ∘ Ethereum.State.coinBase) (by
      rcases hc with ⟨_hσ, _hσ0, _hgas, _hreceipts, _hsub, henv, _hmachine, _hblocks,
        _hheader, _hcreated⟩
      simp [Ethereum.State.coinBase, henv])
  · exact stateOp_extensional hc Ethereum.State.timeStamp (by
      rcases hc with ⟨_hσ, _hσ0, _hgas, _hreceipts, _hsub, henv, _hmachine, _hblocks,
        _hheader, _hcreated⟩
      simp [Ethereum.State.timeStamp, henv])
  · exact stateOp_extensional hc Ethereum.State.number (by
      rcases hc with ⟨_hσ, _hσ0, _hgas, _hreceipts, _hsub, henv, _hmachine, _hblocks,
        _hheader, _hcreated⟩
      simp [Ethereum.State.number, henv])
  · exact executionEnvOp_extensional hc Ethereum.prevRandao
  · exact stateOp_extensional hc Ethereum.State.gasLimit (by
      rcases hc with ⟨_hσ, _hσ0, _hgas, _hreceipts, _hsub, henv, _hmachine, _hblocks,
        _hheader, _hcreated⟩
      simp [Ethereum.State.gasLimit, henv])
  · exact stateOp_extensional hc Ethereum.State.chainId (by
      simp [Ethereum.State.chainId])
  · exact stateOp_extensional hc Ethereum.State.selfbalance (stateExtensionalEq_selfbalance hc)
  · exact executionEnvOp_extensional hc Ethereum.basefee
  · exact unaryExecutionEnvOp_extensional hc blobhash
  · exact executionEnvOp_extensional hc Ethereum.ExecutionEnv.getBlobGasprice

theorem pop_step_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    exceptStateExtensionalEq
      (match state₁.machineState.stack.pop with
        | some ⟨s, _⟩ => .ok <| state₁.replaceStackAndIncrPC s
        | _ => .error .StackUnderflow)
      (match state₂.machineState.stack.pop with
        | some ⟨s, _⟩ => .ok <| state₂.replaceStackAndIncrPC s
        | _ => .error .StackUnderflow) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop with
  | none =>
      simp [exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀⟩
      simp [exceptStateExtensionalEq]
      exact stateExtensionalEq_replaceStackAndIncrPC
        (by simp [stateExtensionalEq, hσ]) stack

theorem jump_step_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    exceptStateExtensionalEq
      (match state₁.machineState.stack.pop with
        | some ⟨stack, μ₀⟩ =>
            let newPc := μ₀
            .ok <| {state₁ with machineState.pc := newPc, machineState.stack := stack}
        | _ => .error .StackUnderflow)
      (match state₂.machineState.stack.pop with
        | some ⟨stack, μ₀⟩ =>
            let newPc := μ₀
            .ok <| {state₂ with machineState.pc := newPc, machineState.stack := stack}
        | _ => .error .StackUnderflow) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop with
  | none =>
      simp [exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀⟩
      simp [exceptStateExtensionalEq, stateExtensionalEq, hσ]

theorem jumpi_step_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) :
    exceptStateExtensionalEq
      (match state₁.machineState.stack.pop2 with
        | some ⟨stack, μ₀, μ₁⟩ =>
            let newPc := if μ₁ != ⟨0⟩ then μ₀ else state₁.machineState.pc + ⟨1⟩
            .ok <| {state₁ with machineState.pc := newPc, machineState.stack := stack}
        | _ => .error .StackUnderflow)
      (match state₂.machineState.stack.pop2 with
        | some ⟨stack, μ₀, μ₁⟩ =>
            let newPc := if μ₁ != ⟨0⟩ then μ₀ else state₂.machineState.pc + ⟨1⟩
            .ok <| {state₂ with machineState.pc := newPc, machineState.stack := stack}
        | _ => .error .StackUnderflow) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks,
    hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop2 with
  | none =>
      simp [exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁⟩
      simp [exceptStateExtensionalEq, stateExtensionalEq, hσ]

theorem step_stackmemflow_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (op : Operation.SMSFOp) (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.StackMemFlow op, arg) state₁)
      (step gasCost (.StackMemFlow op, arg) state₂) := by
  let charged₁ : State :=
    { ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  let charged₂ : State :=
    { ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  have hc : stateExtensionalEq charged₁ charged₂ := by
    simpa [charged₁, charged₂] using stateExtensionalEq_step_charged h gasCost
  cases op <;> simp [step]
  · exact pop_step_extensional hc
  · exact mload_step_extensional hc
  · exact binaryMachineStateOp_extensional hc MachineState.mstore
  · exact unaryStateOp_extensional hc Ethereum.State.sload (by
      intro value
      exact stateExtensionalEq_sload hc value)
  · exact binaryStateOp_extensional hc Ethereum.State.sstore (by
      intro value₁ value₂
      exact stateExtensionalEq_sstore hc value₁ value₂)
  · exact binaryMachineStateOp_extensional hc MachineState.mstore8
  · exact jump_step_extensional hc
  · simpa [bne] using jumpi_step_extensional hc
  · simp [exceptStateExtensionalEq]
    rcases h with ⟨hσ, hσ0, hgas, hreceipts, hsub, henv, hmachine, hblocks, hheader,
      hcreated⟩
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      stateExtensionalEq, hσ, hσ0, hgas, hreceipts, hsub, henv, hmachine, hblocks,
      hheader, hcreated]
  · exact machineStateOp_extensional hc MachineState.msize
  · exact machineStateOp_extensional hc MachineState.gas
  · simp [exceptStateExtensionalEq]
    exact stateExtensionalEq_incrPC hc
  · exact unaryStateOp_extensional hc Ethereum.State.tload (by
      intro value
      exact stateExtensionalEq_tload hc value)
  · exact binaryStateOp_extensional hc Ethereum.State.tstore (by
      intro value₁ value₂
      exact stateExtensionalEq_tstore hc value₁ value₂)
  · exact ternaryMachineStateOp_extensional hc MachineState.mcopy

theorem step_push_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (op : Operation.POp) (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.Push op, arg) state₁)
      (step gasCost (.Push op, arg) state₂) := by
  let charged₁ : State :=
    { ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  let charged₂ : State :=
    { ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  have hc : stateExtensionalEq charged₁ charged₂ := by
    simpa [charged₁, charged₂] using stateExtensionalEq_step_charged h gasCost
  cases op <;> simp [step]
  · simp [exceptStateExtensionalEq]
    rcases h with ⟨hσ, hσ0, hgas, hreceipts, hsub, henv, hmachine, hblocks, hheader,
      hcreated⟩
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      stateExtensionalEq, hσ, hσ0, hgas, hreceipts, hsub, henv, hmachine, hblocks,
      hheader, hcreated]
  all_goals
    cases arg with
    | none =>
        simp [exceptStateExtensionalEq]
    | some a =>
        rcases a with ⟨argWord, argWidth⟩
        simp [exceptStateExtensionalEq]
        rcases h with ⟨hσ, hσ0, hgas, hreceipts, hsub, henv, hmachine, hblocks,
          hheader, hcreated⟩
        simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
          stateExtensionalEq, hσ, hσ0, hgas, hreceipts, hsub, henv, hmachine,
          hblocks, hheader, hcreated]

theorem step_dup_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (op : Operation.DOp) (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.Dup op, arg) state₁)
      (step gasCost (.Dup op, arg) state₂) := by
  let charged₁ : State :=
    { ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  let charged₂ : State :=
    { ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  have hc : stateExtensionalEq charged₁ charged₂ := by
    simpa [charged₁, charged₂] using stateExtensionalEq_step_charged h gasCost
  cases op <;> simp [step] <;> exact dup_extensional hc _

theorem step_exchange_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (op : Operation.ExOp) (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.Exchange op, arg) state₁)
      (step gasCost (.Exchange op, arg) state₂) := by
  let charged₁ : State :=
    { ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  let charged₂ : State :=
    { ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  have hc : stateExtensionalEq charged₁ charged₂ := by
    simpa [charged₁, charged₂] using stateExtensionalEq_step_charged h gasCost
  cases op <;> simp [step] <;> exact swap_extensional hc _

theorem step_log_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (op : Operation.LOp) (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.Log op, arg) state₁)
      (step gasCost (.Log op, arg) state₂) := by
  let charged₁ : State :=
    { ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  let charged₂ : State :=
    { ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  have hc : stateExtensionalEq charged₁ charged₂ := by
    simpa [charged₁, charged₂] using stateExtensionalEq_step_charged h gasCost
  cases op <;> simp [step]
  · exact log0Op_extensional hc
  · exact log1Op_extensional hc
  · exact log2Op_extensional hc
  · exact log3Op_extensional hc
  · exact log4Op_extensional hc

theorem step_return_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.RETURN, arg) state₁)
      (step gasCost (.RETURN, arg) state₂) := by
  let charged₁ : State :=
    { ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  let charged₂ : State :=
    { ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  have hc : stateExtensionalEq charged₁ charged₂ := by
    simpa [charged₁, charged₂] using stateExtensionalEq_step_charged h gasCost
  simp [step]
  exact binaryMachineStateOp_extensional hc MachineState.evmReturn

theorem step_revert_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.REVERT, arg) state₁)
      (step gasCost (.REVERT, arg) state₂) := by
  let charged₁ : State :=
    { ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₁ with machineState.execLength := state₁.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  let charged₂ : State :=
    { ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State) with
      machineState.gasAvailable :=
        ({ state₂ with machineState.execLength := state₂.machineState.execLength + 1 } : State).machineState.gasAvailable.subNat gasCost }
  have hc : stateExtensionalEq charged₁ charged₂ := by
    simpa [charged₁, charged₂] using stateExtensionalEq_step_charged h gasCost
  simp [step]
  exact binaryMachineStateOp_extensional hc MachineState.evmRevert

theorem step_invalid_extensional {state₁ state₂ : State}
    (gasCost : Nat) (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.INVALID, arg) state₁)
      (step gasCost (.INVALID, arg) state₂) := by
  simp [step, exceptStateExtensionalEq]

theorem step_extensional_of_system_cases {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (op : Operation) (arg : Option (UInt256 × Nat))
    (hcreate :
      exceptStateExtensionalEq
        (step gasCost (.CREATE, arg) state₁)
        (step gasCost (.CREATE, arg) state₂))
    (hcall :
      exceptStateExtensionalEq
        (step gasCost (.CALL, arg) state₁)
        (step gasCost (.CALL, arg) state₂))
    (hcallcode :
      exceptStateExtensionalEq
        (step gasCost (.CALLCODE, arg) state₁)
        (step gasCost (.CALLCODE, arg) state₂))
    (hdelegatecall :
      exceptStateExtensionalEq
        (step gasCost (.DELEGATECALL, arg) state₁)
        (step gasCost (.DELEGATECALL, arg) state₂))
    (hcreate2 :
      exceptStateExtensionalEq
        (step gasCost (.CREATE2, arg) state₁)
        (step gasCost (.CREATE2, arg) state₂))
    (hstaticcall :
      exceptStateExtensionalEq
        (step gasCost (.STATICCALL, arg) state₁)
        (step gasCost (.STATICCALL, arg) state₂))
    (hselfdestruct :
      exceptStateExtensionalEq
        (step gasCost (.SELFDESTRUCT, arg) state₁)
        (step gasCost (.SELFDESTRUCT, arg) state₂)) :
    exceptStateExtensionalEq
      (step gasCost (op, arg) state₁)
      (step gasCost (op, arg) state₂) := by
  cases op with
  | StopArith op =>
      exact step_stoparith_extensional h gasCost op arg
  | CompBit op =>
      exact step_compbit_extensional h gasCost op arg
  | Keccak op =>
      exact step_keccak_extensional h gasCost op arg
  | Env op =>
      exact step_env_extensional h gasCost op arg
  | Block op =>
      exact step_block_extensional h gasCost op arg
  | StackMemFlow op =>
      exact step_stackmemflow_extensional h gasCost op arg
  | Push op =>
      exact step_push_extensional h gasCost op arg
  | Dup op =>
      exact step_dup_extensional h gasCost op arg
  | Exchange op =>
      exact step_exchange_extensional h gasCost op arg
  | Log op =>
      exact step_log_extensional h gasCost op arg
  | System op =>
      cases op with
      | CREATE => exact hcreate
      | CALL => exact hcall
      | CALLCODE => exact hcallcode
      | RETURN => exact step_return_extensional h gasCost arg
      | DELEGATECALL => exact hdelegatecall
      | CREATE2 => exact hcreate2
      | STATICCALL => exact hstaticcall
      | REVERT => exact step_revert_extensional h gasCost arg
      | INVALID => exact step_invalid_extensional gasCost arg
      | SELFDESTRUCT => exact hselfdestruct

private theorem selfdestruct_transfer_created_extensional {σ₁ σ₂ : AccountMap}
    (hσ : accountMapExtensionalEq σ₁ σ₂) (owner target : AccountAddress) :
    accountMapExtensionalEq
      (match σ₁.find? owner with
        | none => σ₁
        | some σ_Iₐ =>
            match σ₁.find? target with
            | none =>
                if σ_Iₐ.balance = ⟨0⟩ then
                  σ₁
                else
                  σ₁.insert target {(default : Account) with balance := σ_Iₐ.balance}
                    |>.insert owner {σ_Iₐ with balance := ⟨0⟩}
            | some σ_r =>
                if target = owner then
                  σ₁.insert target {σ_r with balance := ⟨0⟩}
                    |>.insert owner {σ_Iₐ with balance := ⟨0⟩}
                else
                  σ₁.insert target {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                    |>.insert owner {σ_Iₐ with balance := ⟨0⟩})
      (match σ₂.find? owner with
        | none => σ₂
        | some σ_Iₐ =>
            match σ₂.find? target with
            | none =>
                if σ_Iₐ.balance = ⟨0⟩ then
                  σ₂
                else
                  σ₂.insert target {(default : Account) with balance := σ_Iₐ.balance}
                    |>.insert owner {σ_Iₐ with balance := ⟨0⟩}
            | some σ_r =>
                if target = owner then
                  σ₂.insert target {σ_r with balance := ⟨0⟩}
                    |>.insert owner {σ_Iₐ with balance := ⟨0⟩}
                else
                  σ₂.insert target {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                    |>.insert owner {σ_Iₐ with balance := ⟨0⟩}) := by
  cases howner₁ : σ₁.find? owner with
  | none =>
      have howner₂ := accountMapExtensionalEq_find?_none_left hσ howner₁
      simp [howner₂, hσ]
  | some owner₁ =>
      obtain ⟨owner₂, howner₂, hownerExt⟩ :=
        accountMapExtensionalEq_find?_some_left hσ howner₁
      simp [howner₂]
      cases htarget₁ : σ₁.find? target with
      | none =>
          have htarget₂ := accountMapExtensionalEq_find?_none_left hσ htarget₁
          have hbal : owner₁.balance = owner₂.balance := hownerExt.2.1
          simp [htarget₂]
          by_cases hz : owner₁.balance = ⟨0⟩
          · have hz₂ : owner₂.balance = ⟨0⟩ := by simpa [← hbal] using hz
            simp [hz, hz₂, hσ]
          · have hz₂ : ¬ owner₂.balance = ⟨0⟩ := by
              intro hzero
              exact hz (by simpa [hbal] using hzero)
            simp [hz, hz₂]
            rw [hbal]
            exact accountMapExtensionalEq_insert_same
              (accountMapExtensionalEq_insert_same hσ
                (accountExtensionalEq_with_balance (accountExtensionalEq_refl default) owner₂.balance))
              (accountExtensionalEq_with_balance hownerExt ⟨0⟩)
      | some target₁ =>
          obtain ⟨target₂, htarget₂, htargetExt⟩ :=
            accountMapExtensionalEq_find?_some_left hσ htarget₁
          simp [htarget₂]
          by_cases heq : target = owner
          · simp [heq]
            exact accountMapExtensionalEq_insert_same
              (accountMapExtensionalEq_insert_same hσ
                (accountExtensionalEq_with_balance htargetExt ⟨0⟩))
              (accountExtensionalEq_with_balance hownerExt ⟨0⟩)
          · simp [heq]
            rw [hownerExt.2.1]
            exact accountMapExtensionalEq_insert_same
              (accountMapExtensionalEq_insert_same hσ
                (accountExtensionalEq_add_balance htargetExt owner₂.balance))
              (accountExtensionalEq_with_balance hownerExt ⟨0⟩)

private theorem selfdestruct_transfer_extensional {σ₁ σ₂ : AccountMap}
    (hσ : accountMapExtensionalEq σ₁ σ₂) (owner target : AccountAddress) :
    accountMapExtensionalEq
      (match σ₁.find? owner with
        | none => σ₁
        | some σ_Iₐ =>
            match σ₁.find? target with
            | none =>
                if σ_Iₐ.balance = ⟨0⟩ then
                  σ₁
                else
                  σ₁.insert target {(default : Account) with balance := σ_Iₐ.balance}
                    |>.insert owner {σ_Iₐ with balance := ⟨0⟩}
            | some σ_r =>
                if target = owner then
                  σ₁
                else
                  σ₁.insert target {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                    |>.insert owner {σ_Iₐ with balance := ⟨0⟩})
      (match σ₂.find? owner with
        | none => σ₂
        | some σ_Iₐ =>
            match σ₂.find? target with
            | none =>
                if σ_Iₐ.balance = ⟨0⟩ then
                  σ₂
                else
                  σ₂.insert target {(default : Account) with balance := σ_Iₐ.balance}
                    |>.insert owner {σ_Iₐ with balance := ⟨0⟩}
            | some σ_r =>
                if target = owner then
                  σ₂
                else
                  σ₂.insert target {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                    |>.insert owner {σ_Iₐ with balance := ⟨0⟩}) := by
  cases howner₁ : σ₁.find? owner with
  | none =>
      have howner₂ := accountMapExtensionalEq_find?_none_left hσ howner₁
      simp [howner₂, hσ]
  | some owner₁ =>
      obtain ⟨owner₂, howner₂, hownerExt⟩ :=
        accountMapExtensionalEq_find?_some_left hσ howner₁
      simp [howner₂]
      cases htarget₁ : σ₁.find? target with
      | none =>
          have htarget₂ := accountMapExtensionalEq_find?_none_left hσ htarget₁
          have hbal : owner₁.balance = owner₂.balance := hownerExt.2.1
          simp [htarget₂]
          by_cases hz : owner₁.balance = ⟨0⟩
          · have hz₂ : owner₂.balance = ⟨0⟩ := by simpa [← hbal] using hz
            simp [hz, hz₂, hσ]
          · have hz₂ : ¬ owner₂.balance = ⟨0⟩ := by
              intro hzero
              exact hz (by simpa [hbal] using hzero)
            simp [hz, hz₂]
            rw [hbal]
            exact accountMapExtensionalEq_insert_same
              (accountMapExtensionalEq_insert_same hσ
                (accountExtensionalEq_with_balance (accountExtensionalEq_refl default) owner₂.balance))
              (accountExtensionalEq_with_balance hownerExt ⟨0⟩)
      | some target₁ =>
          obtain ⟨target₂, htarget₂, htargetExt⟩ :=
            accountMapExtensionalEq_find?_some_left hσ htarget₁
          simp [htarget₂]
          by_cases heq : target = owner
          · simp [heq, hσ]
          · simp [heq]
            rw [hownerExt.2.1]
            exact accountMapExtensionalEq_insert_same
              (accountMapExtensionalEq_insert_same hσ
                (accountExtensionalEq_add_balance htargetExt owner₂.balance))
              (accountExtensionalEq_with_balance hownerExt ⟨0⟩)

theorem step_selfdestruct_extensional {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.SELFDESTRUCT, arg) state₁)
      (step gasCost (.SELFDESTRUCT, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ gas₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ gas₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, hgas, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst gas₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop with
  | none =>
      simp [step, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₁⟩
      by_cases hcreatedOwner : created₁.contains env₁.codeOwner
      · simp [step, hpop, hcreatedOwner, Ethereum.State.lookupAccount]
        simpa [exceptStateExtensionalEq, stateExtensionalEq,
          Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
          selfdestruct_transfer_created_extensional hσ env₁.codeOwner
            (AccountAddress.ofUInt256 μ₁)
      · simp [step, hpop, hcreatedOwner, Ethereum.State.lookupAccount]
        simpa [exceptStateExtensionalEq, stateExtensionalEq,
          Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
          selfdestruct_transfer_extensional hσ env₁.codeOwner
            (AccountAddress.ofUInt256 μ₁)

@[simp] private theorem monadLift_option_some_local {α : Type} (a : α) :
    (monadLift (some a) : Except EVM.ExecutionException α) = .ok a := by
  rfl

@[simp] private theorem monadLift_option_none_local {α : Type} :
    (monadLift (none : Option α) : Except EVM.ExecutionException α) = .error .StackUnderflow := by
  rfl

theorem call_extensional_of_Theta {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (blobVersionedHashes : List ByteArray)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (permission : Bool)
    (hTheta : ∀ {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o r : AccountAddress} {c : ToExecute}
        {g p v v' : UInt256} {d : ByteArray} {e : Fin 1025}
        {H : BlockHeader} {w : Bool}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o r c
            g p v v' d e H w =
          (createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o r c
            g p v v' d e H w =
          (createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂') :
    exceptUIntStateExtensionalEq
      (call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission state₁)
      (call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
      createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
      createdAccounts := created₁ }
  let targetAddr : AccountAddress := AccountAddress.ofUInt256 t
  let recipientAddr : AccountAddress := AccountAddress.ofUInt256 recipient
  let sourceAddr : AccountAddress := AccountAddress.ofUInt256 source
  let Astar : Substate := (base₁.addAccessedAccount targetAddr).substate
  have hAstar₂ : (base₂.addAccessedAccount targetAddr).substate = Astar := by
    simp [Astar, base₁, base₂, Ethereum.State.addAccessedAccount]
  have hcallgas :
      Ccallgas targetAddr recipientAddr value gas σ₁ machine₁ sub₁ =
        Ccallgas targetAddr recipientAddr value gas σ₂ machine₁ sub₁ :=
    accountMapExtensionalEq_Ccallgas hσ targetAddr recipientAddr value gas machine₁ sub₁
  have hbalOpt :
      (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) =
        (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) :=
    accountMapExtensionalEq_balanceOf_option hσ env₁.codeOwner
  have hbalElim :
      (σ₁.find? env₁.codeOwner |>.elim ⟨0⟩ (·.balance)) =
        (σ₂.find? env₁.codeOwner |>.elim ⟨0⟩ (·.balance)) :=
    accountMapExtensionalEq_balanceOf hσ env₁.codeOwner
  have htoExec : toExecute σ₁ targetAddr = toExecute σ₂ targetAddr :=
    accountMapExtensionalEq_toExecute hσ targetAddr
  simp [call, base₂, targetAddr, recipientAddr,
    hcallgas, htoExec, ← hbalOpt, ← hbalElim, hAstar₂]
  by_cases hexec :
      value ≤ (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ env₁.depth < 1024
  · simp [hexec]
    cases hΘ₁ :
        Θ blobVersionedHashes created₁ header₁ blocks₁ σ₁ σ₀₁ Astar
          sourceAddr env₁.sender recipientAddr (toExecute σ₁ targetAddr)
          (UInt256.ofNat (Ccallgas targetAddr recipientAddr value gas σ₁ machine₁ sub₁))
          (UInt256.ofNat env₁.gasPrice) value value'
          (machine₁.memory.readWithPadding inOffset.toNat inSize.toNat) (env₁.depth + 1)
          env₁.header permission with
    | mk createdΘ₁ rest₁ =>
      rcases rest₁ with ⟨σΘ₁, gΘ₁, AΘ₁, zΘ₁, outΘ₁⟩
      cases hΘ₂ :
          Θ blobVersionedHashes created₁ header₁ blocks₁ σ₂ σ₀₁ Astar
            sourceAddr env₁.sender recipientAddr (toExecute σ₂ targetAddr)
            (UInt256.ofNat (Ccallgas targetAddr recipientAddr value gas σ₂ machine₁ sub₁))
            (UInt256.ofNat env₁.gasPrice) value value'
            (machine₁.memory.readWithPadding inOffset.toNat inSize.toNat) (env₁.depth + 1)
            env₁.header permission with
      | mk createdΘ₂ rest₂ =>
        rcases rest₂ with ⟨σΘ₂, gΘ₂, AΘ₂, zΘ₂, outΘ₂⟩
        have hΘ₂' :
            Θ blobVersionedHashes created₁ header₁ blocks₁ σ₂ σ₀₁ Astar
              sourceAddr env₁.sender recipientAddr (toExecute σ₁ targetAddr)
              (UInt256.ofNat (Ccallgas targetAddr recipientAddr value gas σ₁ machine₁ sub₁))
              (UInt256.ofNat env₁.gasPrice) value value'
              (machine₁.memory.readWithPadding inOffset.toNat inSize.toNat) (env₁.depth + 1)
              env₁.header permission =
            (createdΘ₂, σΘ₂, gΘ₂, AΘ₂, zΘ₂, outΘ₂) := by
          simpa [htoExec, hcallgas] using hΘ₂
        have hproj := hTheta hσ hΘ₁ hΘ₂'
        rcases hproj with ⟨hcreatedΘ, hgΘ, hAΘ, hzΘ, houtΘ, hσΘ⟩
        have hΘ₁norm :
            Θ blobVersionedHashes created₁ header₁ blocks₁ σ₁ σ₀₁
              Astar sourceAddr env₁.sender recipientAddr
              (toExecute σ₂ targetAddr)
              (UInt256.ofNat (Ccallgas targetAddr recipientAddr value gas σ₂ machine₁ sub₁))
              (UInt256.ofNat env₁.gasPrice) value value'
              (machine₁.memory.readWithPadding inOffset.toNat inSize.toNat) (env₁.depth + 1)
              env₁.header permission =
            (createdΘ₁, σΘ₁, gΘ₁, AΘ₁, zΘ₁, outΘ₁) := by
          simpa [htoExec, hcallgas] using hΘ₁
        subst createdΘ₂
        subst gΘ₂
        subst AΘ₂
        subst zΘ₂
        subst outΘ₂
        simp [Astar, base₁, targetAddr, recipientAddr, sourceAddr, hΘ₁norm,
          exceptUIntStateExtensionalEq, stateExtensionalEq, hσΘ]
  · have hAstar₁ : (base₁.addAccessedAccount targetAddr).substate = Astar := rfl
    simp [hexec, exceptUIntStateExtensionalEq, stateExtensionalEq, hσ,
      Astar, base₁, targetAddr, hAstar₁]

theorem call_extensional_of_Theta_at_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    {n : Nat} (hdepth : 1024 - state₁.executionEnv.depth.val = n + 1)
    (blobVersionedHashes : List ByteArray)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (permission : Bool)
    (hTheta : ∀ {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o r : AccountAddress} {c : ToExecute}
        {g p v v' : UInt256} {d : ByteArray} {e : Fin 1025}
        {H : BlockHeader} {w : Bool}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        1024 - e.val = n →
        Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o r c
            g p v v' d e H w =
          (createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o r c
            g p v v' d e H w =
          (createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂') :
    exceptUIntStateExtensionalEq
      (call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission state₁)
      (call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
      createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
      createdAccounts := created₁ }
  let targetAddr : AccountAddress := AccountAddress.ofUInt256 t
  let recipientAddr : AccountAddress := AccountAddress.ofUInt256 recipient
  let sourceAddr : AccountAddress := AccountAddress.ofUInt256 source
  let Astar : Substate := (base₁.addAccessedAccount targetAddr).substate
  have hAstar₂ : (base₂.addAccessedAccount targetAddr).substate = Astar := by
    simp [Astar, base₁, base₂, Ethereum.State.addAccessedAccount]
  have hcallgas :
      Ccallgas targetAddr recipientAddr value gas σ₁ machine₁ sub₁ =
        Ccallgas targetAddr recipientAddr value gas σ₂ machine₁ sub₁ :=
    accountMapExtensionalEq_Ccallgas hσ targetAddr recipientAddr value gas machine₁ sub₁
  have hbalOpt :
      (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) =
        (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) :=
    accountMapExtensionalEq_balanceOf_option hσ env₁.codeOwner
  have hbalElim :
      (σ₁.find? env₁.codeOwner |>.elim ⟨0⟩ (·.balance)) =
        (σ₂.find? env₁.codeOwner |>.elim ⟨0⟩ (·.balance)) :=
    accountMapExtensionalEq_balanceOf hσ env₁.codeOwner
  have htoExec : toExecute σ₁ targetAddr = toExecute σ₂ targetAddr :=
    accountMapExtensionalEq_toExecute hσ targetAddr
  simp [call, base₂, targetAddr, recipientAddr,
    hcallgas, htoExec, ← hbalOpt, ← hbalElim, hAstar₂]
  by_cases hexec :
      value ≤ (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ env₁.depth < 1024
  · simp [hexec]
    cases hΘ₁ :
        Θ blobVersionedHashes created₁ header₁ blocks₁ σ₁ σ₀₁ Astar
          sourceAddr env₁.sender recipientAddr (toExecute σ₁ targetAddr)
          (UInt256.ofNat (Ccallgas targetAddr recipientAddr value gas σ₁ machine₁ sub₁))
          (UInt256.ofNat env₁.gasPrice) value value'
          (machine₁.memory.readWithPadding inOffset.toNat inSize.toNat) (env₁.depth + 1)
          env₁.header permission with
    | mk createdΘ₁ rest₁ =>
      rcases rest₁ with ⟨σΘ₁, gΘ₁, AΘ₁, zΘ₁, outΘ₁⟩
      cases hΘ₂ :
          Θ blobVersionedHashes created₁ header₁ blocks₁ σ₂ σ₀₁ Astar
            sourceAddr env₁.sender recipientAddr (toExecute σ₂ targetAddr)
            (UInt256.ofNat (Ccallgas targetAddr recipientAddr value gas σ₂ machine₁ sub₁))
            (UInt256.ofNat env₁.gasPrice) value value'
            (machine₁.memory.readWithPadding inOffset.toNat inSize.toNat) (env₁.depth + 1)
            env₁.header permission with
      | mk createdΘ₂ rest₂ =>
        rcases rest₂ with ⟨σΘ₂, gΘ₂, AΘ₂, zΘ₂, outΘ₂⟩
        have hΘ₂' :
            Θ blobVersionedHashes created₁ header₁ blocks₁ σ₂ σ₀₁ Astar
              sourceAddr env₁.sender recipientAddr (toExecute σ₁ targetAddr)
              (UInt256.ofNat (Ccallgas targetAddr recipientAddr value gas σ₁ machine₁ sub₁))
              (UInt256.ofNat env₁.gasPrice) value value'
              (machine₁.memory.readWithPadding inOffset.toNat inSize.toNat) (env₁.depth + 1)
              env₁.header permission =
            (createdΘ₂, σΘ₂, gΘ₂, AΘ₂, zΘ₂, outΘ₂) := by
          simpa [htoExec, hcallgas] using hΘ₂
        have hdepth' : 1024 - env₁.depth.val = n + 1 := by
          simpa using hdepth
        have hrecDepth : 1024 - (env₁.depth + 1).val = n := by
          omega
        have hproj := hTheta hσ hrecDepth hΘ₁ hΘ₂'
        rcases hproj with ⟨hcreatedΘ, hgΘ, hAΘ, hzΘ, houtΘ, hσΘ⟩
        have hΘ₁norm :
            Θ blobVersionedHashes created₁ header₁ blocks₁ σ₁ σ₀₁
              Astar sourceAddr env₁.sender recipientAddr
              (toExecute σ₂ targetAddr)
              (UInt256.ofNat (Ccallgas targetAddr recipientAddr value gas σ₂ machine₁ sub₁))
              (UInt256.ofNat env₁.gasPrice) value value'
              (machine₁.memory.readWithPadding inOffset.toNat inSize.toNat) (env₁.depth + 1)
              env₁.header permission =
            (createdΘ₁, σΘ₁, gΘ₁, AΘ₁, zΘ₁, outΘ₁) := by
          simpa [htoExec, hcallgas] using hΘ₁
        subst createdΘ₂
        subst gΘ₂
        subst AΘ₂
        subst zΘ₂
        subst outΘ₂
        simp [Astar, base₁, targetAddr, recipientAddr, sourceAddr, hΘ₁norm,
          exceptUIntStateExtensionalEq, stateExtensionalEq, hσΘ]
  · have hAstar₁ : (base₁.addAccessedAccount targetAddr).substate = Astar := rfl
    simp [hexec, exceptUIntStateExtensionalEq, stateExtensionalEq, hσ,
      Astar, base₁, targetAddr, hAstar₁]

theorem call_extensional_max_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (hdepth : state₁.executionEnv.depth = 1024)
    (blobVersionedHashes : List ByteArray)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (permission : Bool) :
    exceptUIntStateExtensionalEq
      (call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission state₁)
      (call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
      createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := machine₁, blocks := blocks₁, genesisBlockHeader := header₁,
      createdAccounts := created₁ }
  let targetAddr : AccountAddress := AccountAddress.ofUInt256 t
  let recipientAddr : AccountAddress := AccountAddress.ofUInt256 recipient
  let Astar : Substate := (base₁.addAccessedAccount targetAddr).substate
  have hAstar₂ : (base₂.addAccessedAccount targetAddr).substate = Astar := by
    simp [Astar, base₁, base₂, Ethereum.State.addAccessedAccount]
  have hcallgas :
      Ccallgas targetAddr recipientAddr value gas σ₁ machine₁ sub₁ =
        Ccallgas targetAddr recipientAddr value gas σ₂ machine₁ sub₁ :=
    accountMapExtensionalEq_Ccallgas hσ targetAddr recipientAddr value gas machine₁ sub₁
  have hbalOpt :
      (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) =
        (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) :=
    accountMapExtensionalEq_balanceOf_option hσ env₁.codeOwner
  have hbalElim :
      (σ₁.find? env₁.codeOwner |>.elim ⟨0⟩ (·.balance)) =
        (σ₂.find? env₁.codeOwner |>.elim ⟨0⟩ (·.balance)) :=
    accountMapExtensionalEq_balanceOf hσ env₁.codeOwner
  have hdepthVal : env₁.depth.val = 1024 := by
    simpa using congrArg Fin.val hdepth
  have hexec :
      ¬ (value ≤ (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ env₁.depth < 1024) := by
    intro hcond
    have hlt : env₁.depth.val < 1024 := by exact hcond.2
    omega
  have hAstar₁ : (base₁.addAccessedAccount targetAddr).substate = Astar := rfl
  simp [call, base₂, targetAddr, recipientAddr, hcallgas, ← hbalOpt, ← hbalElim,
    hAstar₂, hexec, exceptUIntStateExtensionalEq, stateExtensionalEq, hσ,
    Astar, base₁, hAstar₁]

theorem step_CREATE_extensional_of_Lambda {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (arg : Option (UInt256 × Nat))
    (hLambda : ∀ {blobVersionedHashes : List ByteArray}
        {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o : AccountAddress} {g p v : UInt256} {i : ByteArray}
        {e : Fin 1025} {ζ : Option ByteArray} {H : BlockHeader} {w : Bool}
        {a₁ a₂ : AccountAddress}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₁ σ₀ A s o g p v i e ζ H w =
          (a₁, createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₂ σ₀ A s o g p v i e ζ H w =
          (a₂, createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        a₁ = a₂ ∧ g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂') :
    exceptStateExtensionalEq
      (step gasCost (.CREATE, arg) state₁)
      (step gasCost (.CREATE, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let charged₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState :=
        { machine₁ with
          execLength := machine₁.execLength + 1,
          gasAvailable := machine₁.gasAvailable.subNat gasCost },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let charged₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState :=
        { machine₁ with
          execLength := machine₁.execLength + 1,
          gasAvailable := machine₁.gasAvailable.subNat gasCost },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hcharged : stateExtensionalEq charged₁ charged₂ := by
    simp [charged₁, charged₂, stateExtensionalEq, hσ]
  cases hpop : machine₁.stack.pop3 with
  | none =>
      simp [step, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂⟩
      let owner₁ : Account := (σ₁.find? env₁.codeOwner).getD default
      let owner₂ : Account := (σ₂.find? env₁.codeOwner).getD default
      have howner : accountExtensionalEq owner₁ owner₂ := by
        simpa [owner₁, owner₂, Batteries.RBMap.findD] using
          accountMapExtensionalEq_findD hσ env₁.codeOwner
      let initcode : ByteArray := machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat
      let gasForCreate : UInt256 := UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))
      let σStar₁ : AccountMap :=
        σ₁.insert env₁.codeOwner { owner₁ with nonce := owner₁.nonce + ⟨1⟩ }
      let σStar₂ : AccountMap :=
        σ₂.insert env₁.codeOwner { owner₂ with nonce := owner₂.nonce + ⟨1⟩ }
      have hσStar : accountMapExtensionalEq σStar₁ σStar₂ := by
        exact accountMapExtensionalEq_insert_same hσ
          (accountExtensionalEq_inc_nonce howner)
      have hbalance :
          (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) =
            (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) :=
        accountMapExtensionalEq_balanceOf_option hσ env₁.codeOwner
      simp [step, hpop]
      by_cases hlimit₁ :
          18446744073709551615 ≤ ((σ₁.find? env₁.codeOwner).getD default).nonce.toNat
      · have hlimit₂ :
            18446744073709551615 ≤ ((σ₂.find? env₁.codeOwner).getD default).nonce.toNat := by
          simpa [owner₁, owner₂, howner.1] using hlimit₁
        by_cases hog :
            machine₁.gasAvailable.toNat - gasCost +
                (UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))).toNat <
              L (machine₁.gasAvailable.toNat - gasCost)
        · simp [hlimit₁, hlimit₂, hog, bind, Except.bind, exceptStateExtensionalEq,
            Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            stateExtensionalEq, hσ]
        · simp [hlimit₁, hlimit₂, hog, exceptStateExtensionalEq,
            Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            stateExtensionalEq, hσ]
      · have hlimit₂ :
            ¬18446744073709551615 ≤ ((σ₂.find? env₁.codeOwner).getD default).nonce.toNat := by
          intro hlim
          exact hlimit₁ (by simpa [owner₁, owner₂, howner.1] using hlim)
        simp [hlimit₁, hlimit₂]
        by_cases hcond₁ :
            μ₀ ≤ (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
              env₁.depth < 1024 ∧
              (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152
        · have hcond₂ :
              μ₀ ≤ (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
                env₁.depth < 1024 ∧
                (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152 := by
            simpa [← hbalance] using hcond₁
          simp [hcond₁, hcond₂]
          cases hΛ₁ :
              Lambda env₁.blobVersionedHashes created₁ header₁ blocks₁ σStar₁ σ₀₁ sub₁
                env₁.codeOwner env₁.sender gasForCreate (UInt256.ofNat env₁.gasPrice)
                μ₀ initcode ⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₁.2.1⟩
                none env₁.header env₁.perm with
          | mk a₁ rest₁ =>
            rcases rest₁ with ⟨createdΛ₁, σΛ₁, gΛ₁, AΛ₁, zΛ₁, outΛ₁⟩
            cases hΛ₂ :
                Lambda env₁.blobVersionedHashes created₁ header₁ blocks₁ σStar₂ σ₀₁ sub₁
                  env₁.codeOwner env₁.sender gasForCreate (UInt256.ofNat env₁.gasPrice)
                  μ₀ initcode ⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₂.2.1⟩
                  none env₁.header env₁.perm with
            | mk a₂ rest₂ =>
              rcases rest₂ with ⟨createdΛ₂, σΛ₂, gΛ₂, AΛ₂, zΛ₂, outΛ₂⟩
              have hΛ₂' :
                  Lambda env₁.blobVersionedHashes created₁ header₁ blocks₁ σStar₂ σ₀₁ sub₁
                    env₁.codeOwner env₁.sender gasForCreate (UInt256.ofNat env₁.gasPrice)
                    μ₀ initcode ⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₁.2.1⟩
                    none env₁.header env₁.perm =
                  (a₂, createdΛ₂, σΛ₂, gΛ₂, AΛ₂, zΛ₂, outΛ₂) := by
                -- The two depth proofs are proof-irrelevant.
                simpa using hΛ₂
              have hproj := hLambda hσStar hΛ₁ hΛ₂'
              rcases hproj with ⟨hcreatedΛ, haΛ, hgΛ, hAΛ, hzΛ, houtΛ, hσΛ⟩
              subst createdΛ₂
              subst a₂
              subst gΛ₂
              subst AΛ₂
              subst zΛ₂
              subst outΛ₂
              by_cases hog :
                  machine₁.gasAvailable.toNat - gasCost + gΛ₁.toNat <
                    L (machine₁.gasAvailable.toNat - gasCost)
              · simp [hog, hbalance, hΛ₁, hΛ₂, bind, Except.bind,
                  exceptStateExtensionalEq, stateExtensionalEq,
                  Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hσΛ]
              · simp [hog, hbalance, hΛ₁, hΛ₂, exceptStateExtensionalEq, stateExtensionalEq,
                  Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hσΛ]
        · have hcond₂ :
              ¬(μ₀ ≤ (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
                env₁.depth < 1024 ∧
                (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152) := by
            intro hcond
            exact hcond₁ (by simpa [hbalance] using hcond)
          by_cases hog :
              machine₁.gasAvailable.toNat - gasCost +
                  (UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))).toNat <
                L (machine₁.gasAvailable.toNat - gasCost)
          · simp [hcond₁, hcond₂, hog, bind, Except.bind, exceptStateExtensionalEq,
              Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              stateExtensionalEq, hσ]
          · simp [hcond₁, hcond₂, hog, exceptStateExtensionalEq,
              Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              stateExtensionalEq, hσ]

theorem step_CREATE_extensional_max_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (hdepth : state₁.executionEnv.depth = 1024)
    (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.CREATE, arg) state₁)
      (step gasCost (.CREATE, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop3 with
  | none =>
      simp [step, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂⟩
      let owner₁ : Account := (σ₁.find? env₁.codeOwner).getD default
      let owner₂ : Account := (σ₂.find? env₁.codeOwner).getD default
      have howner : accountExtensionalEq owner₁ owner₂ := by
        simpa [owner₁, owner₂, Batteries.RBMap.findD] using
          accountMapExtensionalEq_findD hσ env₁.codeOwner
      have hbalance :
          (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) =
            (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) :=
        accountMapExtensionalEq_balanceOf_option hσ env₁.codeOwner
      simp [step, hpop]
      by_cases hlimit₁ :
          18446744073709551615 ≤ ((σ₁.find? env₁.codeOwner).getD default).nonce.toNat
      · have hlimit₂ :
            18446744073709551615 ≤ ((σ₂.find? env₁.codeOwner).getD default).nonce.toNat := by
          simpa [owner₁, owner₂, howner.1] using hlimit₁
        by_cases hog :
            machine₁.gasAvailable.toNat - gasCost +
                (UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))).toNat <
              L (machine₁.gasAvailable.toNat - gasCost)
        · simp [hlimit₁, hlimit₂, hog, bind, Except.bind, exceptStateExtensionalEq,
            Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            stateExtensionalEq, hσ]
        · simp [hlimit₁, hlimit₂, hog, exceptStateExtensionalEq,
            Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            stateExtensionalEq, hσ]
      · have hlimit₂ :
            ¬18446744073709551615 ≤ ((σ₂.find? env₁.codeOwner).getD default).nonce.toNat := by
          intro hlim
          exact hlimit₁ (by simpa [owner₁, owner₂, howner.1] using hlim)
        simp [hlimit₁, hlimit₂]
        by_cases hcond₁ :
            μ₀ ≤ (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
              env₁.depth < 1024 ∧
              (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152
        · have hfalse : False := by
            have hval : env₁.depth.val = 1024 := by
              simpa using congrArg Fin.val hdepth
            have hlt : env₁.depth.val < 1024 := by
              exact hcond₁.2.1
            omega
          exact False.elim hfalse
        · have hcond₂ :
              ¬(μ₀ ≤ (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
                env₁.depth < 1024 ∧
                (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152) := by
            intro hcond
            exact hcond₁ (by simpa [hbalance] using hcond)
          by_cases hog :
              machine₁.gasAvailable.toNat - gasCost +
                  (UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))).toNat <
                L (machine₁.gasAvailable.toNat - gasCost)
          · simp [hcond₁, hcond₂, hog, bind, Except.bind, exceptStateExtensionalEq,
              Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              stateExtensionalEq, hσ]
          · simp [hcond₁, hcond₂, hog, exceptStateExtensionalEq,
              Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              stateExtensionalEq, hσ]

theorem step_CREATE_extensional_of_Lambda_at_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    {n : Nat} (hdepth : 1024 - state₁.executionEnv.depth.val = n + 1)
    (arg : Option (UInt256 × Nat))
    (hLambda : ∀ {blobVersionedHashes : List ByteArray}
        {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o : AccountAddress} {g p v : UInt256} {i : ByteArray}
        {e : Fin 1025} {ζ : Option ByteArray} {H : BlockHeader} {w : Bool}
        {a₁ a₂ : AccountAddress}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        1024 - e.val = n →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₁ σ₀ A s o g p v i e ζ H w =
          (a₁, createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₂ σ₀ A s o g p v i e ζ H w =
          (a₂, createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        a₁ = a₂ ∧ g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂') :
    exceptStateExtensionalEq
      (step gasCost (.CREATE, arg) state₁)
      (step gasCost (.CREATE, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let charged₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState :=
        { machine₁ with
          execLength := machine₁.execLength + 1,
          gasAvailable := machine₁.gasAvailable.subNat gasCost },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let charged₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState :=
        { machine₁ with
          execLength := machine₁.execLength + 1,
          gasAvailable := machine₁.gasAvailable.subNat gasCost },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hcharged : stateExtensionalEq charged₁ charged₂ := by
    simp [charged₁, charged₂, stateExtensionalEq, hσ]
  cases hpop : machine₁.stack.pop3 with
  | none =>
      simp [step, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂⟩
      let owner₁ : Account := (σ₁.find? env₁.codeOwner).getD default
      let owner₂ : Account := (σ₂.find? env₁.codeOwner).getD default
      have howner : accountExtensionalEq owner₁ owner₂ := by
        simpa [owner₁, owner₂, Batteries.RBMap.findD] using
          accountMapExtensionalEq_findD hσ env₁.codeOwner
      let initcode : ByteArray := machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat
      let gasForCreate : UInt256 := UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))
      let σStar₁ : AccountMap :=
        σ₁.insert env₁.codeOwner { owner₁ with nonce := owner₁.nonce + ⟨1⟩ }
      let σStar₂ : AccountMap :=
        σ₂.insert env₁.codeOwner { owner₂ with nonce := owner₂.nonce + ⟨1⟩ }
      have hσStar : accountMapExtensionalEq σStar₁ σStar₂ := by
        exact accountMapExtensionalEq_insert_same hσ
          (accountExtensionalEq_inc_nonce howner)
      have hbalance :
          (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) =
            (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) :=
        accountMapExtensionalEq_balanceOf_option hσ env₁.codeOwner
      simp [step, hpop]
      by_cases hlimit₁ :
          18446744073709551615 ≤ ((σ₁.find? env₁.codeOwner).getD default).nonce.toNat
      · have hlimit₂ :
            18446744073709551615 ≤ ((σ₂.find? env₁.codeOwner).getD default).nonce.toNat := by
          simpa [owner₁, owner₂, howner.1] using hlimit₁
        by_cases hog :
            machine₁.gasAvailable.toNat - gasCost +
                (UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))).toNat <
              L (machine₁.gasAvailable.toNat - gasCost)
        · simp [hlimit₁, hlimit₂, hog, bind, Except.bind, exceptStateExtensionalEq,
            Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            stateExtensionalEq, hσ]
        · simp [hlimit₁, hlimit₂, hog, exceptStateExtensionalEq,
            Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            stateExtensionalEq, hσ]
      · have hlimit₂ :
            ¬18446744073709551615 ≤ ((σ₂.find? env₁.codeOwner).getD default).nonce.toNat := by
          intro hlim
          exact hlimit₁ (by simpa [owner₁, owner₂, howner.1] using hlim)
        simp [hlimit₁, hlimit₂]
        by_cases hcond₁ :
            μ₀ ≤ (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
              env₁.depth < 1024 ∧
              (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152
        · have hcond₂ :
              μ₀ ≤ (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
                env₁.depth < 1024 ∧
                (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152 := by
            simpa [← hbalance] using hcond₁
          simp [hcond₁, hcond₂]
          cases hΛ₁ :
              Lambda env₁.blobVersionedHashes created₁ header₁ blocks₁ σStar₁ σ₀₁ sub₁
                env₁.codeOwner env₁.sender gasForCreate (UInt256.ofNat env₁.gasPrice)
                μ₀ initcode ⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₁.2.1⟩
                none env₁.header env₁.perm with
          | mk a₁ rest₁ =>
            rcases rest₁ with ⟨createdΛ₁, σΛ₁, gΛ₁, AΛ₁, zΛ₁, outΛ₁⟩
            cases hΛ₂ :
                Lambda env₁.blobVersionedHashes created₁ header₁ blocks₁ σStar₂ σ₀₁ sub₁
                  env₁.codeOwner env₁.sender gasForCreate (UInt256.ofNat env₁.gasPrice)
                  μ₀ initcode ⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₂.2.1⟩
                  none env₁.header env₁.perm with
            | mk a₂ rest₂ =>
              rcases rest₂ with ⟨createdΛ₂, σΛ₂, gΛ₂, AΛ₂, zΛ₂, outΛ₂⟩
              have hΛ₂' :
                  Lambda env₁.blobVersionedHashes created₁ header₁ blocks₁ σStar₂ σ₀₁ sub₁
                    env₁.codeOwner env₁.sender gasForCreate (UInt256.ofNat env₁.gasPrice)
                    μ₀ initcode ⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₁.2.1⟩
                    none env₁.header env₁.perm =
                  (a₂, createdΛ₂, σΛ₂, gΛ₂, AΛ₂, zΛ₂, outΛ₂) := by
                -- The two depth proofs are proof-irrelevant.
                simpa using hΛ₂
              have hdepth' : 1024 - env₁.depth.val = n + 1 := by
                simpa using hdepth
              have hrecDepth : 1024 - (⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₁.2.1⟩ : Fin 1025).val = n := by
                change 1024 - (env₁.depth.val + 1) = n
                omega
              have hproj := hLambda hσStar hrecDepth hΛ₁ hΛ₂'
              rcases hproj with ⟨hcreatedΛ, haΛ, hgΛ, hAΛ, hzΛ, houtΛ, hσΛ⟩
              subst createdΛ₂
              subst a₂
              subst gΛ₂
              subst AΛ₂
              subst zΛ₂
              subst outΛ₂
              by_cases hog :
                  machine₁.gasAvailable.toNat - gasCost + gΛ₁.toNat <
                    L (machine₁.gasAvailable.toNat - gasCost)
              · simp [hog, hbalance, hΛ₁, hΛ₂, bind, Except.bind,
                  exceptStateExtensionalEq, stateExtensionalEq,
                  Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hσΛ]
              · simp [hog, hbalance, hΛ₁, hΛ₂, exceptStateExtensionalEq, stateExtensionalEq,
                  Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hσΛ]
        · have hcond₂ :
              ¬(μ₀ ≤ (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
                env₁.depth < 1024 ∧
                (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152) := by
            intro hcond
            exact hcond₁ (by simpa [hbalance] using hcond)
          by_cases hog :
              machine₁.gasAvailable.toNat - gasCost +
                  (UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))).toNat <
                L (machine₁.gasAvailable.toNat - gasCost)
          · simp [hcond₁, hcond₂, hog, bind, Except.bind, exceptStateExtensionalEq,
              Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              stateExtensionalEq, hσ]
          · simp [hcond₁, hcond₂, hog, exceptStateExtensionalEq,
              Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              stateExtensionalEq, hσ]

theorem step_CREATE2_extensional_of_Lambda {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (arg : Option (UInt256 × Nat))
    (hLambda : ∀ {blobVersionedHashes : List ByteArray}
        {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o : AccountAddress} {g p v : UInt256} {i : ByteArray}
        {e : Fin 1025} {ζ : Option ByteArray} {H : BlockHeader} {w : Bool}
        {a₁ a₂ : AccountAddress}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₁ σ₀ A s o g p v i e ζ H w =
          (a₁, createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₂ σ₀ A s o g p v i e ζ H w =
          (a₂, createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        a₁ = a₂ ∧ g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂') :
    exceptStateExtensionalEq
      (step gasCost (.CREATE2, arg) state₁)
      (step gasCost (.CREATE2, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let charged₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState :=
        { machine₁ with
          execLength := machine₁.execLength + 1,
          gasAvailable := machine₁.gasAvailable.subNat gasCost },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let charged₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState :=
        { machine₁ with
          execLength := machine₁.execLength + 1,
          gasAvailable := machine₁.gasAvailable.subNat gasCost },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hcharged : stateExtensionalEq charged₁ charged₂ := by
    simp [charged₁, charged₂, stateExtensionalEq, hσ]
  cases hpop : machine₁.stack.pop4 with
  | none =>
      simp [step, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃⟩
      let owner₁ : Account := (σ₁.find? env₁.codeOwner).getD default
      let owner₂ : Account := (σ₂.find? env₁.codeOwner).getD default
      have howner : accountExtensionalEq owner₁ owner₂ := by
        simpa [owner₁, owner₂, Batteries.RBMap.findD] using
          accountMapExtensionalEq_findD hσ env₁.codeOwner
      let initcode : ByteArray := machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat
      let gasForCreate : UInt256 := UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))
      let σStar₁ : AccountMap :=
        σ₁.insert env₁.codeOwner { owner₁ with nonce := owner₁.nonce + ⟨1⟩ }
      let σStar₂ : AccountMap :=
        σ₂.insert env₁.codeOwner { owner₂ with nonce := owner₂.nonce + ⟨1⟩ }
      have hσStar : accountMapExtensionalEq σStar₁ σStar₂ := by
        exact accountMapExtensionalEq_insert_same hσ
          (accountExtensionalEq_inc_nonce howner)
      have hbalance :
          (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) =
            (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) :=
        accountMapExtensionalEq_balanceOf_option hσ env₁.codeOwner
      simp [step, hpop]
      by_cases hlimit₁ :
          18446744073709551615 ≤ ((σ₁.find? env₁.codeOwner).getD default).nonce.toNat
      · have hlimit₂ :
            18446744073709551615 ≤ ((σ₂.find? env₁.codeOwner).getD default).nonce.toNat := by
          simpa [owner₁, owner₂, howner.1] using hlimit₁
        by_cases hog :
            machine₁.gasAvailable.toNat - gasCost +
                (UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))).toNat <
              L (machine₁.gasAvailable.toNat - gasCost)
        · simp [hlimit₁, hlimit₂, hog, bind, Except.bind, exceptStateExtensionalEq,
            Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            stateExtensionalEq, hσ]
        · simp [hlimit₁, hlimit₂, hog, exceptStateExtensionalEq,
            Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            stateExtensionalEq, hσ]
      · have hlimit₂ :
            ¬18446744073709551615 ≤ ((σ₂.find? env₁.codeOwner).getD default).nonce.toNat := by
          intro hlim
          exact hlimit₁ (by simpa [owner₁, owner₂, howner.1] using hlim)
        simp [hlimit₁, hlimit₂]
        by_cases hcond₁ :
            μ₀ ≤ (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
              env₁.depth < 1024 ∧
              (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152
        · have hcond₂ :
              μ₀ ≤ (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
                env₁.depth < 1024 ∧
                (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152 := by
            simpa [← hbalance] using hcond₁
          simp [hcond₁, hcond₂]
          cases hΛ₁ :
              Lambda env₁.blobVersionedHashes created₁ header₁ blocks₁ σStar₁ σ₀₁ sub₁
                env₁.codeOwner env₁.sender gasForCreate (UInt256.ofNat env₁.gasPrice)
                μ₀ initcode ⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₁.2.1⟩
                (some (Ethereum.UInt256.toByteArray μ₃)) env₁.header env₁.perm with
          | mk a₁ rest₁ =>
            rcases rest₁ with ⟨createdΛ₁, σΛ₁, gΛ₁, AΛ₁, zΛ₁, outΛ₁⟩
            cases hΛ₂ :
                Lambda env₁.blobVersionedHashes created₁ header₁ blocks₁ σStar₂ σ₀₁ sub₁
                  env₁.codeOwner env₁.sender gasForCreate (UInt256.ofNat env₁.gasPrice)
                  μ₀ initcode ⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₂.2.1⟩
                  (some (Ethereum.UInt256.toByteArray μ₃)) env₁.header env₁.perm with
            | mk a₂ rest₂ =>
              rcases rest₂ with ⟨createdΛ₂, σΛ₂, gΛ₂, AΛ₂, zΛ₂, outΛ₂⟩
              have hΛ₂' :
                  Lambda env₁.blobVersionedHashes created₁ header₁ blocks₁ σStar₂ σ₀₁ sub₁
                    env₁.codeOwner env₁.sender gasForCreate (UInt256.ofNat env₁.gasPrice)
                    μ₀ initcode ⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₁.2.1⟩
                    (some (Ethereum.UInt256.toByteArray μ₃)) env₁.header env₁.perm =
                  (a₂, createdΛ₂, σΛ₂, gΛ₂, AΛ₂, zΛ₂, outΛ₂) := by
                -- The two depth proofs are proof-irrelevant.
                simpa using hΛ₂
              have hproj := hLambda hσStar hΛ₁ hΛ₂'
              rcases hproj with ⟨hcreatedΛ, haΛ, hgΛ, hAΛ, hzΛ, houtΛ, hσΛ⟩
              subst createdΛ₂
              subst a₂
              subst gΛ₂
              subst AΛ₂
              subst zΛ₂
              subst outΛ₂
              by_cases hog :
                  machine₁.gasAvailable.toNat - gasCost + gΛ₁.toNat <
                    L (machine₁.gasAvailable.toNat - gasCost)
              · simp [hog, hbalance, hΛ₁, hΛ₂, bind, Except.bind,
                  exceptStateExtensionalEq, stateExtensionalEq,
                  Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hσΛ]
              · simp [hog, hbalance, hΛ₁, hΛ₂, exceptStateExtensionalEq, stateExtensionalEq,
                  Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hσΛ]
        · have hcond₂ :
              ¬(μ₀ ≤ (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
                env₁.depth < 1024 ∧
                (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152) := by
            intro hcond
            exact hcond₁ (by simpa [hbalance] using hcond)
          by_cases hog :
              machine₁.gasAvailable.toNat - gasCost +
                  (UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))).toNat <
                L (machine₁.gasAvailable.toNat - gasCost)
          · simp [hcond₁, hcond₂, hog, bind, Except.bind, exceptStateExtensionalEq,
              Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              stateExtensionalEq, hσ]
          · simp [hcond₁, hcond₂, hog, exceptStateExtensionalEq,
              Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              stateExtensionalEq, hσ]

theorem step_CREATE2_extensional_max_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (hdepth : state₁.executionEnv.depth = 1024)
    (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (.CREATE2, arg) state₁)
      (step gasCost (.CREATE2, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  cases hpop : machine₁.stack.pop4 with
  | none =>
      simp [step, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃⟩
      let owner₁ : Account := (σ₁.find? env₁.codeOwner).getD default
      let owner₂ : Account := (σ₂.find? env₁.codeOwner).getD default
      have howner : accountExtensionalEq owner₁ owner₂ := by
        simpa [owner₁, owner₂, Batteries.RBMap.findD] using
          accountMapExtensionalEq_findD hσ env₁.codeOwner
      have hbalance :
          (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) =
            (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) :=
        accountMapExtensionalEq_balanceOf_option hσ env₁.codeOwner
      simp [step, hpop]
      by_cases hlimit₁ :
          18446744073709551615 ≤ ((σ₁.find? env₁.codeOwner).getD default).nonce.toNat
      · have hlimit₂ :
            18446744073709551615 ≤ ((σ₂.find? env₁.codeOwner).getD default).nonce.toNat := by
          simpa [owner₁, owner₂, howner.1] using hlimit₁
        by_cases hog :
            machine₁.gasAvailable.toNat - gasCost +
                (UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))).toNat <
              L (machine₁.gasAvailable.toNat - gasCost)
        · simp [hlimit₁, hlimit₂, hog, bind, Except.bind, exceptStateExtensionalEq,
            Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            stateExtensionalEq, hσ]
        · simp [hlimit₁, hlimit₂, hog, exceptStateExtensionalEq,
            Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            stateExtensionalEq, hσ]
      · have hlimit₂ :
            ¬18446744073709551615 ≤ ((σ₂.find? env₁.codeOwner).getD default).nonce.toNat := by
          intro hlim
          exact hlimit₁ (by simpa [owner₁, owner₂, howner.1] using hlim)
        simp [hlimit₁, hlimit₂]
        by_cases hcond₁ :
            μ₀ ≤ (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
              env₁.depth < 1024 ∧
              (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152
        · have hfalse : False := by
            have hval : env₁.depth.val = 1024 := by
              simpa using congrArg Fin.val hdepth
            have hlt : env₁.depth.val < 1024 := by
              exact hcond₁.2.1
            omega
          exact False.elim hfalse
        · have hcond₂ :
              ¬(μ₀ ≤ (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
                env₁.depth < 1024 ∧
                (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152) := by
            intro hcond
            exact hcond₁ (by simpa [hbalance] using hcond)
          by_cases hog :
              machine₁.gasAvailable.toNat - gasCost +
                  (UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))).toNat <
                L (machine₁.gasAvailable.toNat - gasCost)
          · simp [hcond₁, hcond₂, hog, bind, Except.bind, exceptStateExtensionalEq,
              Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              stateExtensionalEq, hσ]
          · simp [hcond₁, hcond₂, hog, exceptStateExtensionalEq,
              Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              stateExtensionalEq, hσ]

theorem step_CREATE2_extensional_of_Lambda_at_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    {n : Nat} (hdepth : 1024 - state₁.executionEnv.depth.val = n + 1)
    (arg : Option (UInt256 × Nat))
    (hLambda : ∀ {blobVersionedHashes : List ByteArray}
        {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o : AccountAddress} {g p v : UInt256} {i : ByteArray}
        {e : Fin 1025} {ζ : Option ByteArray} {H : BlockHeader} {w : Bool}
        {a₁ a₂ : AccountAddress}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        1024 - e.val = n →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₁ σ₀ A s o g p v i e ζ H w =
          (a₁, createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₂ σ₀ A s o g p v i e ζ H w =
          (a₂, createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        a₁ = a₂ ∧ g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂') :
    exceptStateExtensionalEq
      (step gasCost (.CREATE2, arg) state₁)
      (step gasCost (.CREATE2, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let charged₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState :=
        { machine₁ with
          execLength := machine₁.execLength + 1,
          gasAvailable := machine₁.gasAvailable.subNat gasCost },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let charged₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState :=
        { machine₁ with
          execLength := machine₁.execLength + 1,
          gasAvailable := machine₁.gasAvailable.subNat gasCost },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hcharged : stateExtensionalEq charged₁ charged₂ := by
    simp [charged₁, charged₂, stateExtensionalEq, hσ]
  cases hpop : machine₁.stack.pop4 with
  | none =>
      simp [step, hpop, exceptStateExtensionalEq]
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃⟩
      let owner₁ : Account := (σ₁.find? env₁.codeOwner).getD default
      let owner₂ : Account := (σ₂.find? env₁.codeOwner).getD default
      have howner : accountExtensionalEq owner₁ owner₂ := by
        simpa [owner₁, owner₂, Batteries.RBMap.findD] using
          accountMapExtensionalEq_findD hσ env₁.codeOwner
      let initcode : ByteArray := machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat
      let gasForCreate : UInt256 := UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))
      let σStar₁ : AccountMap :=
        σ₁.insert env₁.codeOwner { owner₁ with nonce := owner₁.nonce + ⟨1⟩ }
      let σStar₂ : AccountMap :=
        σ₂.insert env₁.codeOwner { owner₂ with nonce := owner₂.nonce + ⟨1⟩ }
      have hσStar : accountMapExtensionalEq σStar₁ σStar₂ := by
        exact accountMapExtensionalEq_insert_same hσ
          (accountExtensionalEq_inc_nonce howner)
      have hbalance :
          (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) =
            (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) :=
        accountMapExtensionalEq_balanceOf_option hσ env₁.codeOwner
      simp [step, hpop]
      by_cases hlimit₁ :
          18446744073709551615 ≤ ((σ₁.find? env₁.codeOwner).getD default).nonce.toNat
      · have hlimit₂ :
            18446744073709551615 ≤ ((σ₂.find? env₁.codeOwner).getD default).nonce.toNat := by
          simpa [owner₁, owner₂, howner.1] using hlimit₁
        by_cases hog :
            machine₁.gasAvailable.toNat - gasCost +
                (UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))).toNat <
              L (machine₁.gasAvailable.toNat - gasCost)
        · simp [hlimit₁, hlimit₂, hog, bind, Except.bind, exceptStateExtensionalEq,
            Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            stateExtensionalEq, hσ]
        · simp [hlimit₁, hlimit₂, hog, exceptStateExtensionalEq,
            Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
            stateExtensionalEq, hσ]
      · have hlimit₂ :
            ¬18446744073709551615 ≤ ((σ₂.find? env₁.codeOwner).getD default).nonce.toNat := by
          intro hlim
          exact hlimit₁ (by simpa [owner₁, owner₂, howner.1] using hlim)
        simp [hlimit₁, hlimit₂]
        by_cases hcond₁ :
            μ₀ ≤ (σ₁.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
              env₁.depth < 1024 ∧
              (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152
        · have hcond₂ :
              μ₀ ≤ (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
                env₁.depth < 1024 ∧
                (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152 := by
            simpa [← hbalance] using hcond₁
          simp [hcond₁, hcond₂]
          cases hΛ₁ :
              Lambda env₁.blobVersionedHashes created₁ header₁ blocks₁ σStar₁ σ₀₁ sub₁
                env₁.codeOwner env₁.sender gasForCreate (UInt256.ofNat env₁.gasPrice)
                μ₀ initcode ⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₁.2.1⟩
                (some (Ethereum.UInt256.toByteArray μ₃)) env₁.header env₁.perm with
          | mk a₁ rest₁ =>
            rcases rest₁ with ⟨createdΛ₁, σΛ₁, gΛ₁, AΛ₁, zΛ₁, outΛ₁⟩
            cases hΛ₂ :
                Lambda env₁.blobVersionedHashes created₁ header₁ blocks₁ σStar₂ σ₀₁ sub₁
                  env₁.codeOwner env₁.sender gasForCreate (UInt256.ofNat env₁.gasPrice)
                  μ₀ initcode ⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₂.2.1⟩
                  (some (Ethereum.UInt256.toByteArray μ₃)) env₁.header env₁.perm with
            | mk a₂ rest₂ =>
              rcases rest₂ with ⟨createdΛ₂, σΛ₂, gΛ₂, AΛ₂, zΛ₂, outΛ₂⟩
              have hΛ₂' :
                  Lambda env₁.blobVersionedHashes created₁ header₁ blocks₁ σStar₂ σ₀₁ sub₁
                    env₁.codeOwner env₁.sender gasForCreate (UInt256.ofNat env₁.gasPrice)
                    μ₀ initcode ⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₁.2.1⟩
                    (some (Ethereum.UInt256.toByteArray μ₃)) env₁.header env₁.perm =
                  (a₂, createdΛ₂, σΛ₂, gΛ₂, AΛ₂, zΛ₂, outΛ₂) := by
                -- The two depth proofs are proof-irrelevant.
                simpa using hΛ₂
              have hdepth' : 1024 - env₁.depth.val = n + 1 := by
                simpa using hdepth
              have hrecDepth : 1024 - (⟨env₁.depth.val + 1, Nat.succ_lt_succ hcond₁.2.1⟩ : Fin 1025).val = n := by
                change 1024 - (env₁.depth.val + 1) = n
                omega
              have hproj := hLambda hσStar hrecDepth hΛ₁ hΛ₂'
              rcases hproj with ⟨hcreatedΛ, haΛ, hgΛ, hAΛ, hzΛ, houtΛ, hσΛ⟩
              subst createdΛ₂
              subst a₂
              subst gΛ₂
              subst AΛ₂
              subst zΛ₂
              subst outΛ₂
              by_cases hog :
                  machine₁.gasAvailable.toNat - gasCost + gΛ₁.toNat <
                    L (machine₁.gasAvailable.toNat - gasCost)
              · simp [hog, hbalance, hΛ₁, hΛ₂, bind, Except.bind,
                  exceptStateExtensionalEq, stateExtensionalEq,
                  Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hσΛ]
              · simp [hog, hbalance, hΛ₁, hΛ₂, exceptStateExtensionalEq, stateExtensionalEq,
                  Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hσΛ]
        · have hcond₂ :
              ¬(μ₀ ≤ (σ₂.find? env₁.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
                env₁.depth < 1024 ∧
                (machine₁.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152) := by
            intro hcond
            exact hcond₁ (by simpa [hbalance] using hcond)
          by_cases hog :
              machine₁.gasAvailable.toNat - gasCost +
                  (UInt256.ofNat (L (machine₁.gasAvailable.toNat - gasCost))).toNat <
                L (machine₁.gasAvailable.toNat - gasCost)
          · simp [hcond₁, hcond₂, hog, bind, Except.bind, exceptStateExtensionalEq,
              Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              stateExtensionalEq, hσ]
          · simp [hcond₁, hcond₂, hog, exceptStateExtensionalEq,
              Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
              stateExtensionalEq, hσ]

theorem step_CALL_extensional_of_call {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (arg : Option (UInt256 × Nat))
    (hcall : ∀ {base₁ base₂ : State}
        (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256),
        stateExtensionalEq base₁ base₂ →
        exceptUIntStateExtensionalEq
          (call gasCost base₁.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₁.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
            base₁.executionEnv.perm base₁)
          (call gasCost base₂.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₂.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
            base₂.executionEnv.perm base₂)) :
    exceptStateExtensionalEq
      (step gasCost (.CALL, arg) state₁)
      (step gasCost (.CALL, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hb : stateExtensionalEq base₁ base₂ := by
    simp [base₁, base₂, stateExtensionalEq, hσ]
  cases hpop : machine₁.stack.pop7 with
  | none =>
      simp [step, hpop]
      change EVM.ExecutionException.StackUnderflow = EVM.ExecutionException.StackUnderflow
      rfl
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
      have hrel := hcall (base₁ := base₁) (base₂ := base₂)
        μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ hb
      simp [step, hpop, bind, Except.bind]
      simpa [base₁, base₂] using
        exceptUIntStateExtensionalEq_replaceStackAndIncrPC hrel stack

theorem step_CALLCODE_extensional_of_call {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (arg : Option (UInt256 × Nat))
    (hcall : ∀ {base₁ base₂ : State}
        (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256),
        stateExtensionalEq base₁ base₂ →
        exceptUIntStateExtensionalEq
          (call gasCost base₁.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₁.executionEnv.codeOwner) (.ofNat base₁.executionEnv.codeOwner)
            μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ base₁.executionEnv.perm base₁)
          (call gasCost base₂.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₂.executionEnv.codeOwner) (.ofNat base₂.executionEnv.codeOwner)
            μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ base₂.executionEnv.perm base₂)) :
    exceptStateExtensionalEq
      (step gasCost (.CALLCODE, arg) state₁)
      (step gasCost (.CALLCODE, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hb : stateExtensionalEq base₁ base₂ := by
    simp [base₁, base₂, stateExtensionalEq, hσ]
  cases hpop : machine₁.stack.pop7 with
  | none =>
      simp [step, hpop]
      change EVM.ExecutionException.StackUnderflow = EVM.ExecutionException.StackUnderflow
      rfl
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
      have hrel := hcall (base₁ := base₁) (base₂ := base₂)
        μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ hb
      simp [step, hpop, bind, Except.bind]
      simpa [base₁, base₂] using
        exceptUIntStateExtensionalEq_replaceStackAndIncrPC hrel stack

theorem step_DELEGATECALL_extensional_of_call {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (arg : Option (UInt256 × Nat))
    (hcall : ∀ {base₁ base₂ : State}
        (μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ : UInt256),
        stateExtensionalEq base₁ base₂ →
        exceptUIntStateExtensionalEq
          (call gasCost base₁.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₁.executionEnv.source) (.ofNat base₁.executionEnv.codeOwner)
            μ₁ ⟨0⟩ base₁.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ base₁.executionEnv.perm base₁)
          (call gasCost base₂.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₂.executionEnv.source) (.ofNat base₂.executionEnv.codeOwner)
            μ₁ ⟨0⟩ base₂.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ base₂.executionEnv.perm base₂)) :
    exceptStateExtensionalEq
      (step gasCost (.DELEGATECALL, arg) state₁)
      (step gasCost (.DELEGATECALL, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hb : stateExtensionalEq base₁ base₂ := by
    simp [base₁, base₂, stateExtensionalEq, hσ]
  cases hpop : machine₁.stack.pop6 with
  | none =>
      simp [step, hpop]
      change EVM.ExecutionException.StackUnderflow = EVM.ExecutionException.StackUnderflow
      rfl
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
      have hrel := hcall (base₁ := base₁) (base₂ := base₂)
        μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ hb
      simp [step, hpop, bind, Except.bind]
      simpa [base₁, base₂] using
        exceptUIntStateExtensionalEq_replaceStackAndIncrPC hrel stack

theorem step_STATICCALL_extensional_of_call {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (arg : Option (UInt256 × Nat))
    (hcall : ∀ {base₁ base₂ : State}
        (μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ : UInt256),
        stateExtensionalEq base₁ base₂ →
        exceptUIntStateExtensionalEq
          (call gasCost base₁.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₁.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩
            μ₃ μ₄ μ₅ μ₆ false base₁)
          (call gasCost base₂.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₂.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩
            μ₃ μ₄ μ₅ μ₆ false base₂)) :
    exceptStateExtensionalEq
      (step gasCost (.STATICCALL, arg) state₁)
      (step gasCost (.STATICCALL, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hb : stateExtensionalEq base₁ base₂ := by
    simp [base₁, base₂, stateExtensionalEq, hσ]
  cases hpop : machine₁.stack.pop6 with
  | none =>
      simp [step, hpop]
      change EVM.ExecutionException.StackUnderflow = EVM.ExecutionException.StackUnderflow
      rfl
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
      have hrel := hcall (base₁ := base₁) (base₂ := base₂)
        μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ hb
      simp [step, hpop, bind, Except.bind]
      simpa [base₁, base₂] using
        exceptUIntStateExtensionalEq_replaceStackAndIncrPC hrel stack

theorem step_CALL_extensional_of_call_at_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    {n : Nat} (hdepth : 1024 - state₁.executionEnv.depth.val = n + 1)
    (arg : Option (UInt256 × Nat))
    (hcall : ∀ {base₁ base₂ : State}
        (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256),
        stateExtensionalEq base₁ base₂ →
        1024 - base₁.executionEnv.depth.val = n + 1 →
        exceptUIntStateExtensionalEq
          (call gasCost base₁.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₁.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
            base₁.executionEnv.perm base₁)
          (call gasCost base₂.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₂.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
            base₂.executionEnv.perm base₂)) :
    exceptStateExtensionalEq
      (step gasCost (.CALL, arg) state₁)
      (step gasCost (.CALL, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hb : stateExtensionalEq base₁ base₂ := by
    simp [base₁, base₂, stateExtensionalEq, hσ]
  have hbdepth : 1024 - base₁.executionEnv.depth.val = n + 1 := by
    simpa [base₁] using hdepth
  cases hpop : machine₁.stack.pop7 with
  | none =>
      simp [step, hpop]
      change EVM.ExecutionException.StackUnderflow = EVM.ExecutionException.StackUnderflow
      rfl
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
      have hrel := hcall (base₁ := base₁) (base₂ := base₂)
        μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      simp [step, hpop, bind, Except.bind]
      simpa [base₁, base₂] using
        exceptUIntStateExtensionalEq_replaceStackAndIncrPC hrel stack

theorem step_CALLCODE_extensional_of_call_at_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    {n : Nat} (hdepth : 1024 - state₁.executionEnv.depth.val = n + 1)
    (arg : Option (UInt256 × Nat))
    (hcall : ∀ {base₁ base₂ : State}
        (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256),
        stateExtensionalEq base₁ base₂ →
        1024 - base₁.executionEnv.depth.val = n + 1 →
        exceptUIntStateExtensionalEq
          (call gasCost base₁.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₁.executionEnv.codeOwner) (.ofNat base₁.executionEnv.codeOwner)
            μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ base₁.executionEnv.perm base₁)
          (call gasCost base₂.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₂.executionEnv.codeOwner) (.ofNat base₂.executionEnv.codeOwner)
            μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ base₂.executionEnv.perm base₂)) :
    exceptStateExtensionalEq
      (step gasCost (.CALLCODE, arg) state₁)
      (step gasCost (.CALLCODE, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hb : stateExtensionalEq base₁ base₂ := by
    simp [base₁, base₂, stateExtensionalEq, hσ]
  have hbdepth : 1024 - base₁.executionEnv.depth.val = n + 1 := by
    simpa [base₁] using hdepth
  cases hpop : machine₁.stack.pop7 with
  | none =>
      simp [step, hpop]
      change EVM.ExecutionException.StackUnderflow = EVM.ExecutionException.StackUnderflow
      rfl
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
      have hrel := hcall (base₁ := base₁) (base₂ := base₂)
        μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      simp [step, hpop, bind, Except.bind]
      simpa [base₁, base₂] using
        exceptUIntStateExtensionalEq_replaceStackAndIncrPC hrel stack

theorem step_DELEGATECALL_extensional_of_call_at_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    {n : Nat} (hdepth : 1024 - state₁.executionEnv.depth.val = n + 1)
    (arg : Option (UInt256 × Nat))
    (hcall : ∀ {base₁ base₂ : State}
        (μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ : UInt256),
        stateExtensionalEq base₁ base₂ →
        1024 - base₁.executionEnv.depth.val = n + 1 →
        exceptUIntStateExtensionalEq
          (call gasCost base₁.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₁.executionEnv.source) (.ofNat base₁.executionEnv.codeOwner)
            μ₁ ⟨0⟩ base₁.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ base₁.executionEnv.perm base₁)
          (call gasCost base₂.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₂.executionEnv.source) (.ofNat base₂.executionEnv.codeOwner)
            μ₁ ⟨0⟩ base₂.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ base₂.executionEnv.perm base₂)) :
    exceptStateExtensionalEq
      (step gasCost (.DELEGATECALL, arg) state₁)
      (step gasCost (.DELEGATECALL, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hb : stateExtensionalEq base₁ base₂ := by
    simp [base₁, base₂, stateExtensionalEq, hσ]
  have hbdepth : 1024 - base₁.executionEnv.depth.val = n + 1 := by
    simpa [base₁] using hdepth
  cases hpop : machine₁.stack.pop6 with
  | none =>
      simp [step, hpop]
      change EVM.ExecutionException.StackUnderflow = EVM.ExecutionException.StackUnderflow
      rfl
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
      have hrel := hcall (base₁ := base₁) (base₂ := base₂)
        μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      simp [step, hpop, bind, Except.bind]
      simpa [base₁, base₂] using
        exceptUIntStateExtensionalEq_replaceStackAndIncrPC hrel stack

theorem step_STATICCALL_extensional_of_call_at_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    {n : Nat} (hdepth : 1024 - state₁.executionEnv.depth.val = n + 1)
    (arg : Option (UInt256 × Nat))
    (hcall : ∀ {base₁ base₂ : State}
        (μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ : UInt256),
        stateExtensionalEq base₁ base₂ →
        1024 - base₁.executionEnv.depth.val = n + 1 →
        exceptUIntStateExtensionalEq
          (call gasCost base₁.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₁.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩
            μ₃ μ₄ μ₅ μ₆ false base₁)
          (call gasCost base₂.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₂.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩
            μ₃ μ₄ μ₅ μ₆ false base₂)) :
    exceptStateExtensionalEq
      (step gasCost (.STATICCALL, arg) state₁)
      (step gasCost (.STATICCALL, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hb : stateExtensionalEq base₁ base₂ := by
    simp [base₁, base₂, stateExtensionalEq, hσ]
  have hbdepth : 1024 - base₁.executionEnv.depth.val = n + 1 := by
    simpa [base₁] using hdepth
  cases hpop : machine₁.stack.pop6 with
  | none =>
      simp [step, hpop]
      change EVM.ExecutionException.StackUnderflow = EVM.ExecutionException.StackUnderflow
      rfl
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
      have hrel := hcall (base₁ := base₁) (base₂ := base₂)
        μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      simp [step, hpop, bind, Except.bind]
      simpa [base₁, base₂] using
        exceptUIntStateExtensionalEq_replaceStackAndIncrPC hrel stack

theorem step_CALL_extensional_of_call_max_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (hdepth : state₁.executionEnv.depth = 1024)
    (arg : Option (UInt256 × Nat))
    (hcall : ∀ {base₁ base₂ : State}
        (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256),
        stateExtensionalEq base₁ base₂ →
        base₁.executionEnv.depth = 1024 →
        exceptUIntStateExtensionalEq
          (call gasCost base₁.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₁.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
            base₁.executionEnv.perm base₁)
          (call gasCost base₂.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₂.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
            base₂.executionEnv.perm base₂)) :
    exceptStateExtensionalEq
      (step gasCost (.CALL, arg) state₁)
      (step gasCost (.CALL, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hb : stateExtensionalEq base₁ base₂ := by
    simp [base₁, base₂, stateExtensionalEq, hσ]
  have hbdepth : base₁.executionEnv.depth = 1024 := by
    simpa [base₁] using hdepth
  cases hpop : machine₁.stack.pop7 with
  | none =>
      simp [step, hpop]
      change EVM.ExecutionException.StackUnderflow = EVM.ExecutionException.StackUnderflow
      rfl
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
      have hrel := hcall (base₁ := base₁) (base₂ := base₂)
        μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      simp [step, hpop, bind, Except.bind]
      simpa [base₁, base₂] using
        exceptUIntStateExtensionalEq_replaceStackAndIncrPC hrel stack

theorem step_CALLCODE_extensional_of_call_max_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (hdepth : state₁.executionEnv.depth = 1024)
    (arg : Option (UInt256 × Nat))
    (hcall : ∀ {base₁ base₂ : State}
        (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256),
        stateExtensionalEq base₁ base₂ →
        base₁.executionEnv.depth = 1024 →
        exceptUIntStateExtensionalEq
          (call gasCost base₁.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₁.executionEnv.codeOwner) (.ofNat base₁.executionEnv.codeOwner)
            μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ base₁.executionEnv.perm base₁)
          (call gasCost base₂.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₂.executionEnv.codeOwner) (.ofNat base₂.executionEnv.codeOwner)
            μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ base₂.executionEnv.perm base₂)) :
    exceptStateExtensionalEq
      (step gasCost (.CALLCODE, arg) state₁)
      (step gasCost (.CALLCODE, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hb : stateExtensionalEq base₁ base₂ := by
    simp [base₁, base₂, stateExtensionalEq, hσ]
  have hbdepth : base₁.executionEnv.depth = 1024 := by
    simpa [base₁] using hdepth
  cases hpop : machine₁.stack.pop7 with
  | none =>
      simp [step, hpop]
      change EVM.ExecutionException.StackUnderflow = EVM.ExecutionException.StackUnderflow
      rfl
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
      have hrel := hcall (base₁ := base₁) (base₂ := base₂)
        μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      simp [step, hpop, bind, Except.bind]
      simpa [base₁, base₂] using
        exceptUIntStateExtensionalEq_replaceStackAndIncrPC hrel stack

theorem step_DELEGATECALL_extensional_of_call_max_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (hdepth : state₁.executionEnv.depth = 1024)
    (arg : Option (UInt256 × Nat))
    (hcall : ∀ {base₁ base₂ : State}
        (μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ : UInt256),
        stateExtensionalEq base₁ base₂ →
        base₁.executionEnv.depth = 1024 →
        exceptUIntStateExtensionalEq
          (call gasCost base₁.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₁.executionEnv.source) (.ofNat base₁.executionEnv.codeOwner)
            μ₁ ⟨0⟩ base₁.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ base₁.executionEnv.perm base₁)
          (call gasCost base₂.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₂.executionEnv.source) (.ofNat base₂.executionEnv.codeOwner)
            μ₁ ⟨0⟩ base₂.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ base₂.executionEnv.perm base₂)) :
    exceptStateExtensionalEq
      (step gasCost (.DELEGATECALL, arg) state₁)
      (step gasCost (.DELEGATECALL, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hb : stateExtensionalEq base₁ base₂ := by
    simp [base₁, base₂, stateExtensionalEq, hσ]
  have hbdepth : base₁.executionEnv.depth = 1024 := by
    simpa [base₁] using hdepth
  cases hpop : machine₁.stack.pop6 with
  | none =>
      simp [step, hpop]
      change EVM.ExecutionException.StackUnderflow = EVM.ExecutionException.StackUnderflow
      rfl
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
      have hrel := hcall (base₁ := base₁) (base₂ := base₂)
        μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      simp [step, hpop, bind, Except.bind]
      simpa [base₁, base₂] using
        exceptUIntStateExtensionalEq_replaceStackAndIncrPC hrel stack

theorem step_STATICCALL_extensional_of_call_max_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (hdepth : state₁.executionEnv.depth = 1024)
    (arg : Option (UInt256 × Nat))
    (hcall : ∀ {base₁ base₂ : State}
        (μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ : UInt256),
        stateExtensionalEq base₁ base₂ →
        base₁.executionEnv.depth = 1024 →
        exceptUIntStateExtensionalEq
          (call gasCost base₁.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₁.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩
            μ₃ μ₄ μ₅ μ₆ false base₁)
          (call gasCost base₂.executionEnv.blobVersionedHashes μ₀
            (.ofNat base₂.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩
            μ₃ μ₄ μ₅ μ₆ false base₂)) :
    exceptStateExtensionalEq
      (step gasCost (.STATICCALL, arg) state₁)
      (step gasCost (.STATICCALL, arg) state₂) := by
  cases state₁ with
  | mk σ₁ σ₀₁ total₁ receipts₁ sub₁ env₁ machine₁ blocks₁ header₁ created₁ =>
  cases state₂ with
  | mk σ₂ σ₀₂ total₂ receipts₂ sub₂ env₂ machine₂ blocks₂ header₂ created₂ =>
  simp [stateExtensionalEq] at h
  rcases h with ⟨hσ, hσ₀, htotal, hreceipts, hsub, henv, hmachine, hblocks, hheader, hcreated⟩
  subst σ₀₂
  subst total₂
  subst receipts₂
  subst sub₂
  subst env₂
  subst machine₂
  subst blocks₂
  subst header₂
  subst created₂
  let base₁ : State :=
    { accountMap := σ₁, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  let base₂ : State :=
    { accountMap := σ₂, σ₀ := σ₀₁, totalGasUsedInBlock := total₁,
      transactionReceipts := receipts₁, substate := sub₁, executionEnv := env₁,
      machineState := { machine₁ with execLength := machine₁.execLength + 1 },
      blocks := blocks₁, genesisBlockHeader := header₁, createdAccounts := created₁ }
  have hb : stateExtensionalEq base₁ base₂ := by
    simp [base₁, base₂, stateExtensionalEq, hσ]
  have hbdepth : base₁.executionEnv.depth = 1024 := by
    simpa [base₁] using hdepth
  cases hpop : machine₁.stack.pop6 with
  | none =>
      simp [step, hpop]
      change EVM.ExecutionException.StackUnderflow = EVM.ExecutionException.StackUnderflow
      rfl
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
      have hrel := hcall (base₁ := base₁) (base₂ := base₂)
        μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      simp [step, hpop, bind, Except.bind]
      simpa [base₁, base₂] using
        exceptUIntStateExtensionalEq_replaceStackAndIncrPC hrel stack

theorem step_extensional_of_Theta_Lambda {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (op : Operation) (arg : Option (UInt256 × Nat))
    (hTheta : ∀ {blobVersionedHashes : List ByteArray}
        {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o r : AccountAddress} {c : ToExecute}
        {g p v v' : UInt256} {d : ByteArray} {e : Fin 1025}
        {H : BlockHeader} {w : Bool}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o r c
            g p v v' d e H w =
          (createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o r c
            g p v v' d e H w =
          (createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂')
    (hLambda : ∀ {blobVersionedHashes : List ByteArray}
        {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o : AccountAddress} {g p v : UInt256} {i : ByteArray}
        {e : Fin 1025} {ζ : Option ByteArray} {H : BlockHeader} {w : Bool}
        {a₁ a₂ : AccountAddress}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₁ σ₀ A s o g p v i e ζ H w =
          (a₁, createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₂ σ₀ A s o g p v i e ζ H w =
          (a₂, createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        a₁ = a₂ ∧ g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂') :
    exceptStateExtensionalEq
      (step gasCost (op, arg) state₁)
      (step gasCost (op, arg) state₂) := by
  apply step_extensional_of_system_cases h gasCost op arg
  · exact step_CREATE_extensional_of_Lambda h gasCost arg hLambda
  · exact step_CALL_extensional_of_call h gasCost arg (by
      intro base₁ base₂ μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ hb
      have henv : base₁.executionEnv = base₂.executionEnv := hb.2.2.2.2.2.1
      rw [← henv]
      exact call_extensional_of_Theta hb gasCost base₁.executionEnv.blobVersionedHashes
        μ₀ (.ofNat base₁.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
        base₁.executionEnv.perm hTheta)
  · exact step_CALLCODE_extensional_of_call h gasCost arg (by
      intro base₁ base₂ μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ hb
      have henv : base₁.executionEnv = base₂.executionEnv := hb.2.2.2.2.2.1
      rw [← henv]
      exact call_extensional_of_Theta hb gasCost base₁.executionEnv.blobVersionedHashes
        μ₀ (.ofNat base₁.executionEnv.codeOwner) (.ofNat base₁.executionEnv.codeOwner)
        μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ base₁.executionEnv.perm hTheta)
  · exact step_DELEGATECALL_extensional_of_call h gasCost arg (by
      intro base₁ base₂ μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ hb
      have henv : base₁.executionEnv = base₂.executionEnv := hb.2.2.2.2.2.1
      rw [← henv]
      exact call_extensional_of_Theta hb gasCost base₁.executionEnv.blobVersionedHashes
        μ₀ (.ofNat base₁.executionEnv.source) (.ofNat base₁.executionEnv.codeOwner)
        μ₁ ⟨0⟩ base₁.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ base₁.executionEnv.perm hTheta)
  · exact step_CREATE2_extensional_of_Lambda h gasCost arg hLambda
  · exact step_STATICCALL_extensional_of_call h gasCost arg (by
      intro base₁ base₂ μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ hb
      have henv : base₁.executionEnv = base₂.executionEnv := hb.2.2.2.2.2.1
      rw [← henv]
      exact call_extensional_of_Theta hb gasCost base₁.executionEnv.blobVersionedHashes
        μ₀ (.ofNat base₁.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩
        μ₃ μ₄ μ₅ μ₆ false hTheta)
  · exact step_selfdestruct_extensional h gasCost arg

theorem step_extensional_of_Theta_Lambda_at_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    {n : Nat} (hdepth : 1024 - state₁.executionEnv.depth.val = n + 1)
    (op : Operation) (arg : Option (UInt256 × Nat))
    (hTheta : ∀ {blobVersionedHashes : List ByteArray}
        {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o r : AccountAddress} {c : ToExecute}
        {g p v v' : UInt256} {d : ByteArray} {e : Fin 1025}
        {H : BlockHeader} {w : Bool}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        1024 - e.val = n →
        Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o r c
            g p v v' d e H w =
          (createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o r c
            g p v v' d e H w =
          (createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂')
    (hLambda : ∀ {blobVersionedHashes : List ByteArray}
        {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o : AccountAddress} {g p v : UInt256} {i : ByteArray}
        {e : Fin 1025} {ζ : Option ByteArray} {H : BlockHeader} {w : Bool}
        {a₁ a₂ : AccountAddress}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        1024 - e.val = n →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₁ σ₀ A s o g p v i e ζ H w =
          (a₁, createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₂ σ₀ A s o g p v i e ζ H w =
          (a₂, createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        a₁ = a₂ ∧ g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂') :
    exceptStateExtensionalEq
      (step gasCost (op, arg) state₁)
      (step gasCost (op, arg) state₂) := by
  apply step_extensional_of_system_cases h gasCost op arg
  · exact step_CREATE_extensional_of_Lambda_at_depth h gasCost hdepth arg hLambda
  · exact step_CALL_extensional_of_call_at_depth h gasCost hdepth arg (by
      intro base₁ base₂ μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      have henv : base₁.executionEnv = base₂.executionEnv := hb.2.2.2.2.2.1
      rw [← henv]
      exact call_extensional_of_Theta_at_depth hb gasCost hbdepth
        base₁.executionEnv.blobVersionedHashes
        μ₀ (.ofNat base₁.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
        base₁.executionEnv.perm hTheta)
  · exact step_CALLCODE_extensional_of_call_at_depth h gasCost hdepth arg (by
      intro base₁ base₂ μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      have henv : base₁.executionEnv = base₂.executionEnv := hb.2.2.2.2.2.1
      rw [← henv]
      exact call_extensional_of_Theta_at_depth hb gasCost hbdepth
        base₁.executionEnv.blobVersionedHashes
        μ₀ (.ofNat base₁.executionEnv.codeOwner) (.ofNat base₁.executionEnv.codeOwner)
        μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ base₁.executionEnv.perm hTheta)
  · exact step_DELEGATECALL_extensional_of_call_at_depth h gasCost hdepth arg (by
      intro base₁ base₂ μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      have henv : base₁.executionEnv = base₂.executionEnv := hb.2.2.2.2.2.1
      rw [← henv]
      exact call_extensional_of_Theta_at_depth hb gasCost hbdepth
        base₁.executionEnv.blobVersionedHashes
        μ₀ (.ofNat base₁.executionEnv.source) (.ofNat base₁.executionEnv.codeOwner)
        μ₁ ⟨0⟩ base₁.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ base₁.executionEnv.perm hTheta)
  · exact step_CREATE2_extensional_of_Lambda_at_depth h gasCost hdepth arg hLambda
  · exact step_STATICCALL_extensional_of_call_at_depth h gasCost hdepth arg (by
      intro base₁ base₂ μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      have henv : base₁.executionEnv = base₂.executionEnv := hb.2.2.2.2.2.1
      rw [← henv]
      exact call_extensional_of_Theta_at_depth hb gasCost hbdepth
        base₁.executionEnv.blobVersionedHashes
        μ₀ (.ofNat base₁.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩
        μ₃ μ₄ μ₅ μ₆ false hTheta)
  · exact step_selfdestruct_extensional h gasCost arg

theorem step_extensional_max_depth {state₁ state₂ : State}
    (h : stateExtensionalEq state₁ state₂) (gasCost : Nat)
    (hdepth : state₁.executionEnv.depth = 1024)
    (op : Operation) (arg : Option (UInt256 × Nat)) :
    exceptStateExtensionalEq
      (step gasCost (op, arg) state₁)
      (step gasCost (op, arg) state₂) := by
  apply step_extensional_of_system_cases h gasCost op arg
  · exact step_CREATE_extensional_max_depth h gasCost hdepth arg
  · exact step_CALL_extensional_of_call_max_depth h gasCost hdepth arg (by
      intro base₁ base₂ μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      have henv : base₁.executionEnv = base₂.executionEnv := hb.2.2.2.2.2.1
      rw [← henv]
      exact call_extensional_max_depth hb gasCost hbdepth
        base₁.executionEnv.blobVersionedHashes
        μ₀ (.ofNat base₁.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
        base₁.executionEnv.perm)
  · exact step_CALLCODE_extensional_of_call_max_depth h gasCost hdepth arg (by
      intro base₁ base₂ μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      have henv : base₁.executionEnv = base₂.executionEnv := hb.2.2.2.2.2.1
      rw [← henv]
      exact call_extensional_max_depth hb gasCost hbdepth
        base₁.executionEnv.blobVersionedHashes
        μ₀ (.ofNat base₁.executionEnv.codeOwner) (.ofNat base₁.executionEnv.codeOwner)
        μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ base₁.executionEnv.perm)
  · exact step_DELEGATECALL_extensional_of_call_max_depth h gasCost hdepth arg (by
      intro base₁ base₂ μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      have henv : base₁.executionEnv = base₂.executionEnv := hb.2.2.2.2.2.1
      rw [← henv]
      exact call_extensional_max_depth hb gasCost hbdepth
        base₁.executionEnv.blobVersionedHashes
        μ₀ (.ofNat base₁.executionEnv.source) (.ofNat base₁.executionEnv.codeOwner)
        μ₁ ⟨0⟩ base₁.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ base₁.executionEnv.perm)
  · exact step_CREATE2_extensional_max_depth h gasCost hdepth arg
  · exact step_STATICCALL_extensional_of_call_max_depth h gasCost hdepth arg (by
      intro base₁ base₂ μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ hb hbdepth
      have henv : base₁.executionEnv = base₂.executionEnv := hb.2.2.2.2.2.1
      rw [← henv]
      exact call_extensional_max_depth hb gasCost hbdepth
        base₁.executionEnv.blobVersionedHashes
        μ₀ (.ofNat base₁.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩
        μ₃ μ₄ μ₅ μ₆ false)
  · exact step_selfdestruct_extensional h gasCost arg

theorem Xstep_extensional_max_depth {state₁ state₂ : State} {validJumps : Array UInt256}
    (h : stateExtensionalEq state₁ state₂)
    (hdepth : state₁.executionEnv.depth = 1024) :
    exceptStateRetExtensionalEq (Xstep validJumps state₁) (Xstep validJumps state₂) := by
  apply Xstep_extensional_of_step h
  intro cost instr stateZ₁ stateZ₂ hZ
  rcases instr with ⟨op, arg⟩
  have hdepthEq : state₁.executionEnv.depth = state₂.executionEnv.depth :=
    h.2.2.2.2.2.1 ▸ rfl
  rw [← hdepthEq]
  exact step_extensional_max_depth
    (stateExtensionalEq_with_executionEnv_depth hZ) cost (by simpa using hdepth) op arg

theorem X_extensional_max_depth {state₁ state₂ : State} {validJumps : Array UInt256}
    (fuel : Nat)
    (h : stateExtensionalEq state₁ state₂)
    (hdepth : state₁.executionEnv.depth = 1024) :
    exceptExecutionResultStateExtensionalEq
      (X fuel validJumps state₁) (X fuel validJumps state₂) := by
  induction fuel generalizing state₁ state₂ with
  | zero =>
      simp [X, exceptExecutionResultStateExtensionalEq]
  | succ fuel ih =>
      simp [X]
      have hstepRel := Xstep_extensional_max_depth (validJumps := validJumps) h hdepth
      cases hstep₁ : Xstep validJumps state₁ with
      | error e₁ =>
          cases hstep₂ : Xstep validJumps state₂ with
          | error e₂ =>
              have he : e₁ = e₂ := by
                simpa [hstep₁, hstep₂, exceptStateRetExtensionalEq] using hstepRel
              subst e₁
              rfl
          | ok step₂ =>
              have hfalse : False := by
                have hs := hstepRel
                simp [hstep₁, hstep₂, exceptStateRetExtensionalEq] at hs
              exact False.elim hfalse
      | ok step₁ =>
          cases hstep₂ : Xstep validJumps state₂ with
          | error e₂ =>
              have hfalse : False := by
                have hs := hstepRel
                simp [hstep₁, hstep₂, exceptStateRetExtensionalEq] at hs
              exact False.elim hfalse
          | ok step₂ =>
              rcases step₁ with ⟨next₁, ret₁⟩
              rcases step₂ with ⟨next₂, ret₂⟩
              have hnext_ret : stateExtensionalEq next₁ next₂ ∧ ret₁ = ret₂ := by
                simpa [hstep₁, hstep₂, exceptStateRetExtensionalEq] using hstepRel
              have hret : ret₂ = ret₁ := hnext_ret.2.symm
              subst ret₂
              simp [bind, Except.bind]
              cases ret₁ with
              | none =>
                  have hdepthEq : state₁.executionEnv.depth = state₂.executionEnv.depth := by
                    exact congrArg ExecutionEnv.depth h.2.2.2.2.2.1
                  have htail :
                      stateExtensionalEq
                        ({next₁ with executionEnv.depth := state₁.executionEnv.depth} : State)
                        ({next₂ with executionEnv.depth := state₂.executionEnv.depth} : State) := by
                    rw [← hdepthEq]
                    exact stateExtensionalEq_with_executionEnv_depth hnext_ret.1
                  have htailDepth :
                      ({next₁ with executionEnv.depth := state₁.executionEnv.depth} : State).executionEnv.depth = 1024 := by
                    simpa using hdepth
                  exact ih htail htailDepth
              | some ret =>
                  rcases ret with ⟨cause, out⟩
                  cases cause with
                  | revert =>
                      have hmachine : next₁.machineState = next₂.machineState := by
                        exact hnext_ret.1.2.2.2.2.2.2.1
                      simp [exceptExecutionResultStateExtensionalEq, executionResultStateExtensionalEq,
                        hmachine]
                  | success =>
                      simp [exceptExecutionResultStateExtensionalEq, executionResultStateExtensionalEq,
                        hnext_ret.1]

theorem Xi_extensional_max_depth
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ₁ σ₂ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (hdepth : I.depth = 1024) :
    exceptExecutionResultXiExtensionalEq
      (Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I)
      (Ξ createdAccounts genesisBlockHeader blocks σ₂ σ₀ g A I) := by
  let fresh₁ : State :=
    { (default : State) with
      accountMap := σ₁
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := .ofUInt256 g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }
  let fresh₂ : State :=
    { (default : State) with
      accountMap := σ₂
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := .ofUInt256 g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }
  have hfresh : stateExtensionalEq fresh₁ fresh₂ := by
    simp [fresh₁, fresh₂, stateExtensionalEq, hσ]
  have hfreshDepth : fresh₁.executionEnv.depth = 1024 := by
    simpa [fresh₁] using hdepth
  have hX := X_extensional_max_depth (state₁ := fresh₁) (state₂ := fresh₂)
    (validJumps := D_J I.code 0) (fuel := UInt256.toNat g + 1) hfresh hfreshDepth
  simp [Ξ]
  cases hX₁ : X (UInt256.toNat g + 1) (D_J I.code 0) fresh₁ with
  | error e₁ =>
      cases hX₂ : X (UInt256.toNat g + 1) (D_J I.code 0) fresh₂ with
      | error e₂ =>
          have he : e₁ = e₂ := by
            simpa [hX₁, hX₂, exceptExecutionResultStateExtensionalEq] using hX
          subst e₁
          rfl
      | ok result₂ =>
          have hfalse : False := by
            have hx := hX
            simp [hX₁, hX₂, exceptExecutionResultStateExtensionalEq] at hx
          exact False.elim hfalse
  | ok result₁ =>
      cases hX₂ : X (UInt256.toNat g + 1) (D_J I.code 0) fresh₂ with
      | error e₂ =>
          have hfalse : False := by
            have hx := hX
            simp [hX₁, hX₂, exceptExecutionResultStateExtensionalEq] at hx
          exact False.elim hfalse
      | ok result₂ =>
          have hres : executionResultStateExtensionalEq result₁ result₂ := by
            simpa [hX₁, hX₂, exceptExecutionResultStateExtensionalEq] using hX
          cases result₁ with
          | revert gas₁ out₁ =>
              cases result₂ with
              | revert gas₂ out₂ =>
                  have hrev : gas₁ = gas₂ ∧ out₁ = out₂ := by
                    simpa [executionResultStateExtensionalEq] using hres
                  rw [hrev.1, hrev.2]
                  simp [bind, Except.bind, exceptExecutionResultXiExtensionalEq,
                    executionResultXiExtensionalEq]
              | success state₂ out₂ =>
                  have hfalse : False := by
                    have hr := hres
                    simp [executionResultStateExtensionalEq] at hr
                  exact False.elim hfalse
          | success state₁ out₁ =>
              cases result₂ with
              | revert gas₂ out₂ =>
                  have hfalse : False := by
                    have hr := hres
                    simp [executionResultStateExtensionalEq] at hr
                  exact False.elim hfalse
              | success state₂ out₂ =>
                  have hsucc : stateExtensionalEq state₁ state₂ ∧ out₁ = out₂ := by
                    simpa [executionResultStateExtensionalEq] using hres
                  rcases hsucc.1 with ⟨hmap, _hσ0, _htotal, _hreceipts, hsub,
                    _henv, hmachine, _hblocks, _hheader, hcreated⟩
                  rw [hsucc.2]
                  simp [bind, Except.bind, exceptExecutionResultXiExtensionalEq,
                    executionResultXiExtensionalEq]
                  exact ⟨hcreated, hmap,
                    congrArg (fun machine : MachineState => machine.gasAvailable.toUInt256) hmachine,
                    hsub⟩

theorem Xi_extensional_of_Theta_Lambda
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ₁ σ₂ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (hTheta : ∀ {blobVersionedHashes : List ByteArray}
        {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o r : AccountAddress} {c : ToExecute}
        {g p v v' : UInt256} {d : ByteArray} {e : Fin 1025}
        {H : BlockHeader} {w : Bool}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o r c
            g p v v' d e H w =
          (createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o r c
            g p v v' d e H w =
          (createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂')
    (hLambda : ∀ {blobVersionedHashes : List ByteArray}
        {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o : AccountAddress} {g p v : UInt256} {i : ByteArray}
        {e : Fin 1025} {ζ : Option ByteArray} {H : BlockHeader} {w : Bool}
        {a₁ a₂ : AccountAddress}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₁ σ₀ A s o g p v i e ζ H w =
          (a₁, createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₂ σ₀ A s o g p v i e ζ H w =
          (a₂, createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        a₁ = a₂ ∧ g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂') :
    exceptExecutionResultXiExtensionalEq
      (Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I)
      (Ξ createdAccounts genesisBlockHeader blocks σ₂ σ₀ g A I) := by
  apply Xi_extensional_of_Xstep hσ
  intro state₁ state₂ hstate
  apply Xstep_extensional_of_step hstate
  intro cost instr stateZ₁ stateZ₂ hZ
  rcases instr with ⟨op, arg⟩
  have hdepth : state₁.executionEnv.depth = state₂.executionEnv.depth := hstate.2.2.2.2.2.1 ▸ rfl
  rw [hdepth]
  exact step_extensional_of_Theta_Lambda
    (stateExtensionalEq_with_executionEnv_depth hZ) cost op arg hTheta hLambda

theorem Xi_extensional_of_Theta_Lambda_at_depth
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ₁ σ₂ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    {n : Nat} (hdepth : 1024 - I.depth.val = n + 1)
    (hTheta : ∀ {blobVersionedHashes : List ByteArray}
        {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o r : AccountAddress} {c : ToExecute}
        {g p v v' : UInt256} {d : ByteArray} {e : Fin 1025}
        {H : BlockHeader} {w : Bool}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        1024 - e.val = n →
        Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o r c
            g p v v' d e H w =
          (createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o r c
            g p v v' d e H w =
          (createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂')
    (hLambda : ∀ {blobVersionedHashes : List ByteArray}
        {createdAccounts : Batteries.RBSet AccountAddress compare}
        {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
        {σ₁ σ₂ σ₀ : AccountMap} {A : Substate}
        {s o : AccountAddress} {g p v : UInt256} {i : ByteArray}
        {e : Fin 1025} {ζ : Option ByteArray} {H : BlockHeader} {w : Bool}
        {a₁ a₂ : AccountAddress}
        {createdAccounts₁' createdAccounts₂' : Batteries.RBSet AccountAddress compare}
        {σ₁' σ₂' : AccountMap} {g₁' g₂' : UInt256}
        {A₁' A₂' : Substate} {z₁ z₂ : Bool} {o₁' o₂' : ByteArray},
        accountMapExtensionalEq σ₁ σ₂ →
        1024 - e.val = n →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₁ σ₀ A s o g p v i e ζ H w =
          (a₁, createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
        Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks
          σ₂ σ₀ A s o g p v i e ζ H w =
          (a₂, createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        a₁ = a₂ ∧ g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂') :
    exceptExecutionResultXiExtensionalEq
      (Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I)
      (Ξ createdAccounts genesisBlockHeader blocks σ₂ σ₀ g A I) := by
  apply Xi_extensional_of_Xstep_at_depth hσ hdepth
  intro state₁ state₂ hstate hstateDepth
  apply Xstep_extensional_of_step_at_depth hstate hstateDepth
  intro cost instr stateZ₁ stateZ₂ hZ hstepDepth
  rcases instr with ⟨op, arg⟩
  have hdepthEq : state₁.executionEnv.depth = state₂.executionEnv.depth :=
    hstate.2.2.2.2.2.1 ▸ rfl
  rw [← hdepthEq]
  exact step_extensional_of_Theta_Lambda_at_depth
    (stateExtensionalEq_with_executionEnv_depth hZ) cost hstepDepth op arg hTheta hLambda

theorem accountMapExtensionalEq_empty :
    accountMapExtensionalEq (∅ : AccountMap) (∅ : AccountMap) :=
  accountMapExtensionalEq_refl _

private def thetaResultExtensionalEq
    (result₁ result₂ :
      Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × Bool × ByteArray) :
    Prop :=
  result₁.1 = result₂.1 ∧
  result₁.2.2.1 = result₂.2.2.1 ∧
  result₁.2.2.2.1 = result₂.2.2.2.1 ∧
  result₁.2.2.2.2.1 = result₂.2.2.2.2.1 ∧
  result₁.2.2.2.2.2 = result₂.2.2.2.2.2 ∧
  accountMapExtensionalEq result₁.2.1 result₂.2.1

private def lambdaResultExtensionalEq
    (result₁ result₂ :
      AccountAddress × Batteries.RBSet AccountAddress compare × AccountMap ×
        UInt256 × Substate × Bool × ByteArray) :
    Prop :=
  result₁.2.1 = result₂.2.1 ∧
  result₁.1 = result₂.1 ∧
  result₁.2.2.2.1 = result₂.2.2.2.1 ∧
  result₁.2.2.2.2.1 = result₂.2.2.2.2.1 ∧
  result₁.2.2.2.2.2.1 = result₂.2.2.2.2.2.1 ∧
  result₁.2.2.2.2.2.2 = result₂.2.2.2.2.2.2 ∧
  accountMapExtensionalEq result₁.2.2.1 result₂.2.2.1

theorem xiThetaMatch_extensional
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {xi₁ xi₂ : Except EVM.ExecutionException
        (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))}
    {A : Substate}
    (hXi : exceptExecutionResultXiExtensionalEq xi₁ xi₂) :
    let result₁ : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
      match xi₁ with
      | .error _ => (createdAccounts, ∅, ⟨0⟩, A, .empty)
      | .ok (.revert g' o) => (createdAccounts, ∅, g', A, o)
      | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
          (createdAccounts', σStarStar, gStarStar, AStarStar, returnedData)
    let result₂ : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
      match xi₂ with
      | .error _ => (createdAccounts, ∅, ⟨0⟩, A, .empty)
      | .ok (.revert g' o) => (createdAccounts, ∅, g', A, o)
      | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
          (createdAccounts', σStarStar, gStarStar, AStarStar, returnedData)
    result₁.1 = result₂.1 ∧ accountMapExtensionalEq result₁.2.1 result₂.2.1 ∧
      result₁.2.2.1 = result₂.2.2.1 ∧ result₁.2.2.2.1 = result₂.2.2.2.1 ∧
      result₁.2.2.2.2 = result₂.2.2.2.2 := by
  dsimp
  cases xi₁ with
  | error e₁ =>
      cases xi₂ with
      | error e₂ => exact ⟨rfl, accountMapExtensionalEq_empty, rfl, rfl, rfl⟩
      | ok r₂ => simp [exceptExecutionResultXiExtensionalEq] at hXi
  | ok r₁ =>
      cases xi₂ with
      | error e₂ => simp [exceptExecutionResultXiExtensionalEq] at hXi
      | ok r₂ =>
          cases r₁ with
          | revert g₁ o₁ =>
              cases r₂ with
              | revert g₂ o₂ =>
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
                  exact ⟨rfl, accountMapExtensionalEq_empty, hXi.1, rfl, hXi.2⟩
              | success x₂ out₂ =>
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
          | success x₁ out₁ =>
              cases r₂ with
              | revert g₂ o₂ =>
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
              | success x₂ out₂ =>
                  rcases x₁ with ⟨created₁, σ₁, g₁, A₁⟩
                  rcases x₂ with ⟨created₂, σ₂, g₂, A₂⟩
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi ⊢
                  exact ⟨hXi.1, hXi.2.1, hXi.2.2.1, hXi.2.2.2.1, hXi.2.2.2.2⟩

theorem thetaFinalize_extensional {σ₁ σ₂ τ₁ τ₂ : AccountMap}
    {A A₁ A₂ : Substate} {created₁ created₂ : Batteries.RBSet AccountAddress compare}
    {g₁ g₂ : UInt256} {out₁ out₂ : ByteArray}
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (hcreated : created₁ = created₂) (hτ : accountMapExtensionalEq τ₁ τ₂)
    (hg : g₁ = g₂) (hA : A₁ = A₂) (hout : out₁ = out₂) :
    created₁ = created₂ ∧ g₁ = g₂ ∧
      (if τ₁ == (∅ : AccountMap) then A else A₁) =
        (if τ₂ == (∅ : AccountMap) then A else A₂) ∧
      (if τ₁ == (∅ : AccountMap) then false else true) =
        (if τ₂ == (∅ : AccountMap) then false else true) ∧
      out₁ = out₂ ∧
      accountMapExtensionalEq
        (if τ₁ == (∅ : AccountMap) then σ₁ else τ₁)
        (if τ₂ == (∅ : AccountMap) then σ₂ else τ₂) := by
  have hempty := accountMapExtensionalEq_beq_empty hτ
  cases h₁ : (τ₁ == (∅ : AccountMap)) <;> cases h₂ : (τ₂ == (∅ : AccountMap)) <;>
    simp [h₁, h₂] at hempty ⊢
  · exact ⟨hcreated, hg, hA, hout, hτ⟩
  · exact ⟨hcreated, hg, hout, hσ⟩

theorem thetaCodeResult_extensional_of_Xi {σ₁ σ₂ : AccountMap}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {xi₁ xi₂ : Except EVM.ExecutionException
        (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))}
    {A : Substate}
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (hXi : exceptExecutionResultXiExtensionalEq xi₁ xi₂) :
    thetaResultExtensionalEq
      (let result : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
        match xi₁ with
        | .error _ => (createdAccounts, ∅, ⟨0⟩, A, .empty)
        | .ok (.revert g' o) => (createdAccounts, ∅, g', A, o)
        | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
            (createdAccounts', σStarStar, gStarStar, AStarStar, returnedData)
       (result.1,
        if result.2.1 == (∅ : AccountMap) then σ₁ else result.2.1,
        result.2.2.1,
        if result.2.1 == (∅ : AccountMap) then A else result.2.2.2.1,
        if result.2.1 == (∅ : AccountMap) then false else true,
        result.2.2.2.2))
      (let result : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
        match xi₂ with
        | .error _ => (createdAccounts, ∅, ⟨0⟩, A, .empty)
        | .ok (.revert g' o) => (createdAccounts, ∅, g', A, o)
        | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
            (createdAccounts', σStarStar, gStarStar, AStarStar, returnedData)
       (result.1,
        if result.2.1 == (∅ : AccountMap) then σ₂ else result.2.1,
        result.2.2.1,
        if result.2.1 == (∅ : AccountMap) then A else result.2.2.2.1,
        if result.2.1 == (∅ : AccountMap) then false else true,
        result.2.2.2.2)) := by
  have hmatch := xiThetaMatch_extensional (createdAccounts := createdAccounts)
    (xi₁ := xi₁) (xi₂ := xi₂) (A := A) hXi
  dsimp at hmatch ⊢
  exact thetaFinalize_extensional hσ hmatch.1 hmatch.2.1 hmatch.2.2.1
    hmatch.2.2.2.1 hmatch.2.2.2.2

private def thetaXiResult
    (createdAccounts : Batteries.RBSet AccountAddress compare) (A : Substate)
    (xi : Except EVM.ExecutionException
      (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))) :
    Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
  match xi with
  | .error _ => (createdAccounts, ∅, ⟨0⟩, A, .empty)
  | .ok (.revert g' o) => (createdAccounts, ∅, g', A, o)
  | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
      (createdAccounts', σStarStar, gStarStar, AStarStar, returnedData)

theorem thetaCodeResult_extensional_of_Xi_expanded {σ₁ σ₂ : AccountMap}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {xi₁ xi₂ : Except EVM.ExecutionException
        (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))}
    {A : Substate}
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (hXi : exceptExecutionResultXiExtensionalEq xi₁ xi₂) :
    thetaResultExtensionalEq
      ((thetaXiResult createdAccounts A xi₁).1,
       if (thetaXiResult createdAccounts A xi₁).2.1 == (∅ : AccountMap) then σ₁ else
         (thetaXiResult createdAccounts A xi₁).2.1,
       (thetaXiResult createdAccounts A xi₁).2.2.1,
       if (thetaXiResult createdAccounts A xi₁).2.1 == (∅ : AccountMap) then A else
         (thetaXiResult createdAccounts A xi₁).2.2.2.1,
       if (thetaXiResult createdAccounts A xi₁).2.1 == (∅ : AccountMap) then false else true,
       (thetaXiResult createdAccounts A xi₁).2.2.2.2)
      ((thetaXiResult createdAccounts A xi₂).1,
       if (thetaXiResult createdAccounts A xi₂).2.1 == (∅ : AccountMap) then σ₂ else
         (thetaXiResult createdAccounts A xi₂).2.1,
       (thetaXiResult createdAccounts A xi₂).2.2.1,
       if (thetaXiResult createdAccounts A xi₂).2.1 == (∅ : AccountMap) then A else
         (thetaXiResult createdAccounts A xi₂).2.2.2.1,
       if (thetaXiResult createdAccounts A xi₂).2.1 == (∅ : AccountMap) then false else true,
       (thetaXiResult createdAccounts A xi₂).2.2.2.2) := by
  cases xi₁ with
  | error e₁ =>
      cases xi₂ with
      | error e₂ =>
          simp [thetaXiResult, thetaResultExtensionalEq]
          simpa using hσ
      | ok r₂ =>
          simp [exceptExecutionResultXiExtensionalEq] at hXi
  | ok r₁ =>
      cases xi₂ with
      | error e₂ =>
          simp [exceptExecutionResultXiExtensionalEq] at hXi
      | ok r₂ =>
          cases r₁ with
          | revert g₁ o₁ =>
              cases r₂ with
              | revert g₂ o₂ =>
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
                  simp [thetaXiResult, thetaResultExtensionalEq]
                  exact ⟨hXi.1, hXi.2, by simpa using hσ⟩
              | success x₂ out₂ =>
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
          | success x₁ out₁ =>
              cases r₂ with
              | revert g₂ o₂ =>
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
              | success x₂ out₂ =>
                  rcases x₁ with ⟨created₁, τ₁, g₁, A₁⟩
                  rcases x₂ with ⟨created₂, τ₂, g₂, A₂⟩
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
                  simpa [thetaXiResult, thetaResultExtensionalEq] using
                    (thetaFinalize_extensional hσ hXi.1 hXi.2.1 hXi.2.2.1
                      hXi.2.2.2.1 hXi.2.2.2.2)

theorem lambdaFinalize_extensional {σ₁ σ₂ τ₁ τ₂ : AccountMap}
    {AStar A₁ A₂ : Substate} {created₁ created₂ : Batteries.RBSet AccountAddress compare}
    {g₁ g₂ : UInt256} {a : AccountAddress} {returnedData : ByteArray}
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (hcreated : created₁ = created₂) (hτ : accountMapExtensionalEq τ₁ τ₂)
    (hg : g₁ = g₂) (hA : A₁ = A₂) :
    let c := GasConstants.Gcodedeposit * returnedData.size
    let F₁ : Bool := Id.run do
      let F₀ : Bool :=
        match σ₁.find? a with
        | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ ⟨0⟩
        | .none => false
      let F₂ : Bool := g₁.toNat < c
      let MAX_CODE_SIZE := 24576
      let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
      let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
      pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)
    let F₂ : Bool := Id.run do
      let F₀ : Bool :=
        match σ₂.find? a with
        | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ ⟨0⟩
        | .none => false
      let F₂ : Bool := g₂.toNat < c
      let MAX_CODE_SIZE := 24576
      let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
      let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
      pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)
    created₁ = created₂ ∧
      UInt256.ofNat (if F₁ then 0 else g₁.toNat - c) =
        UInt256.ofNat (if F₂ then 0 else g₂.toNat - c) ∧
      (if F₁ then AStar else A₁) = (if F₂ then AStar else A₂) ∧
      not F₁ = not F₂ ∧
      accountMapExtensionalEq
        (if F₁ then σ₁ else
          let newAccount' := τ₁.findD a default
          τ₁.insert a { newAccount' with code := returnedData })
        (if F₂ then σ₂ else
          let newAccount' := τ₂.findD a default
          τ₂.insert a { newAccount' with code := returnedData }) := by
  intro c F₁ F₂
  have hF₀ :
      (match σ₁.find? a with
        | .some ac => !decide (ac.code = ByteArray.empty) ||
            !decide (ac.nonce = (⟨0⟩ : UInt256))
        | .none => false) =
      (match σ₂.find? a with
        | .some ac => !decide (ac.code = ByteArray.empty) ||
            !decide (ac.nonce = (⟨0⟩ : UInt256))
        | .none => false) := by
    specialize hσ a
    cases h₁ : σ₁.find? a <;> cases h₂ : σ₂.find? a <;>
      simp [h₁, h₂] at hσ ⊢
    rcases hσ with ⟨hnonce, _hbalance, hcode, _hstorage, _htstorage⟩
    simp [hnonce, hcode]
  have hF : F₁ = F₂ := by
    simp [F₁, F₂, hF₀, hg]
  cases h₁ : F₁ <;> cases h₂ : F₂ <;> simp [h₁, h₂] at hF ⊢
  all_goals
    first
    | exact ⟨hcreated, hσ⟩
    | exact ⟨hcreated, by simp [hg], hA, accountMapExtensionalEq_insert_same hτ
        (accountExtensionalEq_with_code (accountMapExtensionalEq_findD hτ a) returnedData)⟩
    | contradiction

private theorem lambdaCollision_code_eq {σ₁ σ₂ : AccountMap}
    (hσ : accountMapExtensionalEq σ₁ σ₂) (a : AccountAddress) (i : ByteArray) :
    (if (σ₁.findD a default).nonce ≠ ⟨0⟩ ||
          (σ₁.findD a default).code ≠ ByteArray.empty ||
          (σ₁.findD a default).storage != default
      then ⟨#[0xfe]⟩ else i) =
    (if (σ₂.findD a default).nonce ≠ ⟨0⟩ ||
          (σ₂.findD a default).code ≠ ByteArray.empty ||
          (σ₂.findD a default).storage != default
      then ⟨#[0xfe]⟩ else i) := by
  have h := accountMapExtensionalEq_create_collision_check hσ a
  let b₁ : Bool :=
    decide ((σ₁.findD a default).nonce ≠ ⟨0⟩) ||
      decide ((σ₁.findD a default).code ≠ ByteArray.empty) ||
      ((σ₁.findD a default).storage != default)
  let b₂ : Bool :=
    decide ((σ₂.findD a default).nonce ≠ ⟨0⟩) ||
      decide ((σ₂.findD a default).code ≠ ByteArray.empty) ||
      ((σ₂.findD a default).storage != default)
  have hb : b₁ = b₂ := by
    simpa [b₁, b₂] using h
  change (if b₁ = true then ⟨#[0xfe]⟩ else i) =
    (if b₂ = true then ⟨#[0xfe]⟩ else i)
  rw [hb]

private theorem lambdaCollision_createdAccounts_eq {σ₁ σ₂ : AccountMap}
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (createdAccounts : Batteries.RBSet AccountAddress compare) (a : AccountAddress) :
    (if (σ₁.findD a default).nonce ≠ ⟨0⟩ ||
          (σ₁.findD a default).code ≠ ByteArray.empty ||
          (σ₁.findD a default).storage != default
      then createdAccounts else createdAccounts.insert a) =
    (if (σ₂.findD a default).nonce ≠ ⟨0⟩ ||
          (σ₂.findD a default).code ≠ ByteArray.empty ||
          (σ₂.findD a default).storage != default
      then createdAccounts else createdAccounts.insert a) := by
  have h := accountMapExtensionalEq_create_collision_check hσ a
  let b₁ : Bool :=
    decide ((σ₁.findD a default).nonce ≠ ⟨0⟩) ||
      decide ((σ₁.findD a default).code ≠ ByteArray.empty) ||
      ((σ₁.findD a default).storage != default)
  let b₂ : Bool :=
    decide ((σ₂.findD a default).nonce ≠ ⟨0⟩) ||
      decide ((σ₂.findD a default).code ≠ ByteArray.empty) ||
      ((σ₂.findD a default).storage != default)
  have hb : b₁ = b₂ := by
    simpa [b₁, b₂] using h
  change (if b₁ = true then createdAccounts else createdAccounts.insert a) =
    (if b₂ = true then createdAccounts else createdAccounts.insert a)
  rw [hb]

private def lambdaXiResult
    (a : AccountAddress) (createdAccounts : Batteries.RBSet AccountAddress compare)
    (σ : AccountMap) (AStar : Substate)
    (xi : Except EVM.ExecutionException
        (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))) :
    AccountAddress × Batteries.RBSet AccountAddress compare × AccountMap ×
      UInt256 × Substate × Bool × ByteArray :=
  match xi with
  | .error _ => (a, createdAccounts, σ, ⟨0⟩, AStar, false, .empty)
  | .ok (.revert g' o) => (a, createdAccounts, σ, g', AStar, false, o)
  | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
      let c := GasConstants.Gcodedeposit * returnedData.size
      let F : Bool := Id.run do
        let F₀ : Bool :=
          match σ.find? a with
          | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ ⟨0⟩
          | .none => false
        let F₂ : Bool := gStarStar.toNat < c
        let MAX_CODE_SIZE := 24576
        let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
        let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
        pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)
      let σ' : AccountMap :=
        if F then σ else
          let newAccount' := σStarStar.findD a default
          σStarStar.insert a { newAccount' with code := returnedData }
      let g' := if F then 0 else gStarStar.toNat - c
      let A' := if F then AStar else AStarStar
      let z := not F
      (a, createdAccounts', σ', .ofNat g', A', z, .empty)

private theorem lambdaResult_extensional_of_Xi {σ₁ σ₂ : AccountMap}
    {createdAccounts₁ createdAccounts₂ : Batteries.RBSet AccountAddress compare}
    {xi₁ xi₂ : Except EVM.ExecutionException
        (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))}
    {AStar : Substate} {a : AccountAddress}
    (hcreatedFallback : createdAccounts₁ = createdAccounts₂)
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (hXi : exceptExecutionResultXiExtensionalEq xi₁ xi₂) :
    lambdaResultExtensionalEq
      (match xi₁ with
      | .error _ => (a, createdAccounts₁, σ₁, ⟨0⟩, AStar, false, .empty)
      | .ok (.revert g' o) => (a, createdAccounts₁, σ₁, g', AStar, false, o)
      | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
          let c := GasConstants.Gcodedeposit * returnedData.size
          let F : Bool := Id.run do
            let F₀ : Bool :=
              match σ₁.find? a with
              | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ ⟨0⟩
              | .none => false
            let F₂ : Bool := gStarStar.toNat < c
            let MAX_CODE_SIZE := 24576
            let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
            let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
            pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)
          let σ' : AccountMap :=
            if F then σ₁ else
              let newAccount' := σStarStar.findD a default
              σStarStar.insert a { newAccount' with code := returnedData }
          let g' := if F then 0 else gStarStar.toNat - c
          let A' := if F then AStar else AStarStar
          let z := not F
          (a, createdAccounts', σ', .ofNat g', A', z, .empty))
      (match xi₂ with
      | .error _ => (a, createdAccounts₂, σ₂, ⟨0⟩, AStar, false, .empty)
      | .ok (.revert g' o) => (a, createdAccounts₂, σ₂, g', AStar, false, o)
      | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
          let c := GasConstants.Gcodedeposit * returnedData.size
          let F : Bool := Id.run do
            let F₀ : Bool :=
              match σ₂.find? a with
              | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ ⟨0⟩
              | .none => false
            let F₂ : Bool := gStarStar.toNat < c
            let MAX_CODE_SIZE := 24576
            let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
            let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
            pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)
          let σ' : AccountMap :=
            if F then σ₂ else
              let newAccount' := σStarStar.findD a default
              σStarStar.insert a { newAccount' with code := returnedData }
          let g' := if F then 0 else gStarStar.toNat - c
          let A' := if F then AStar else AStarStar
          let z := not F
          (a, createdAccounts', σ', .ofNat g', A', z, .empty)) := by
  cases xi₁ with
  | error e₁ =>
      cases xi₂ with
      | error e₂ => simp [lambdaResultExtensionalEq, hcreatedFallback, hσ]
      | ok r₂ => simp [exceptExecutionResultXiExtensionalEq] at hXi
  | ok r₁ =>
      cases xi₂ with
      | error e₂ => simp [exceptExecutionResultXiExtensionalEq] at hXi
      | ok r₂ =>
          cases r₁ with
          | revert g₁ o₁ =>
              cases r₂ with
              | revert g₂ o₂ =>
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq,
                    lambdaResultExtensionalEq] at hXi ⊢
                  exact ⟨hcreatedFallback, hXi.1, hXi.2, hσ⟩
              | success x₂ out₂ =>
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
          | success x₁ out₁ =>
              cases r₂ with
              | revert g₂ o₂ =>
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
              | success x₂ out₂ =>
                  rcases x₁ with ⟨created₁, τ₁, g₁, A₁⟩
                  rcases x₂ with ⟨created₂, τ₂, g₂, A₂⟩
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
                  have hout : out₁ = out₂ := hXi.2.2.2.2
                  subst out₂
                  have hfinal :=
                    lambdaFinalize_extensional (σ₁ := σ₁) (σ₂ := σ₂)
                      (τ₁ := τ₁) (τ₂ := τ₂) (AStar := AStar)
                      (A₁ := A₁) (A₂ := A₂) (created₁ := created₁)
                      (created₂ := created₂) (g₁ := g₁) (g₂ := g₂)
                      (a := a) (returnedData := out₁)
                      hσ hXi.1 hXi.2.1 hXi.2.2.1 hXi.2.2.2.1
                  rcases hfinal with ⟨hcreated, hg, hA, hz, hmap⟩
                  simp [lambdaResultExtensionalEq]
                  exact ⟨hcreated, by simpa using hg, by simpa using hA,
                    by simpa using hz, by simpa using hmap⟩

private theorem lambdaResult_extensional_of_Xi_named {σ₁ σ₂ : AccountMap}
    {createdAccounts₁ createdAccounts₂ : Batteries.RBSet AccountAddress compare}
    {xi₁ xi₂ : Except EVM.ExecutionException
        (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))}
    {AStar : Substate} {a : AccountAddress}
    (hcreatedFallback : createdAccounts₁ = createdAccounts₂)
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (hXi : exceptExecutionResultXiExtensionalEq xi₁ xi₂) :
    lambdaResultExtensionalEq
      (lambdaXiResult a createdAccounts₁ σ₁ AStar xi₁)
      (lambdaXiResult a createdAccounts₂ σ₂ AStar xi₂) := by
  unfold lambdaXiResult
  cases xi₁ with
  | error e₁ =>
      cases xi₂ with
      | error e₂ => simp [lambdaResultExtensionalEq, hcreatedFallback, hσ]
      | ok r₂ => simp [exceptExecutionResultXiExtensionalEq] at hXi
  | ok r₁ =>
      cases xi₂ with
      | error e₂ => simp [exceptExecutionResultXiExtensionalEq] at hXi
      | ok r₂ =>
          cases r₁ with
          | revert g₁ o₁ =>
              cases r₂ with
              | revert g₂ o₂ =>
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq,
                    lambdaResultExtensionalEq] at hXi ⊢
                  exact ⟨hcreatedFallback, hXi.1, hXi.2, hσ⟩
              | success x₂ out₂ =>
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
          | success x₁ out₁ =>
              cases r₂ with
              | revert g₂ o₂ =>
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
              | success x₂ out₂ =>
                  rcases x₁ with ⟨created₁, τ₁, g₁, A₁⟩
                  rcases x₂ with ⟨created₂, τ₂, g₂, A₂⟩
                  simp [exceptExecutionResultXiExtensionalEq, executionResultXiExtensionalEq] at hXi
                  have hout : out₁ = out₂ := hXi.2.2.2.2
                  subst out₂
                  have hfinal :=
                    lambdaFinalize_extensional (σ₁ := σ₁) (σ₂ := σ₂)
                      (τ₁ := τ₁) (τ₂ := τ₂) (AStar := AStar)
                      (A₁ := A₁) (A₂ := A₂) (created₁ := created₁)
                      (created₂ := created₂) (g₁ := g₁) (g₂ := g₂)
                      (a := a) (returnedData := out₁)
                      hσ hXi.1 hXi.2.1 hXi.2.2.1 hXi.2.2.2.1
                  rcases hfinal with ⟨hcreated, hg, hA, hz, hmap⟩
                  simp [lambdaResultExtensionalEq]
                  exact ⟨hcreated, by simpa using hg, by simpa using hA,
                    by simpa using hz, by simpa using hmap⟩

private theorem precompile_ECREC_accountMap_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    accountMapExtensionalEq (Ξ_ECREC σ₁ g A I).1 (Ξ_ECREC σ₂ g A I).1 := by
  by_cases hg : g.toNat < 3000
  · simp [Ξ_ECREC, hg, accountMapExtensionalEq_empty]
  · simp [Ξ_ECREC, hg, h]

private theorem precompile_SHA256_accountMap_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    accountMapExtensionalEq (Ξ_SHA256 σ₁ g A I).1 (Ξ_SHA256 σ₂ g A I).1 := by
  let gᵣ : Nat :=
    let l := I.calldata.size
    let ceil := (l + 31) / 32
    60 + 12 * ceil
  by_cases hg : g.toNat < gᵣ
  · simp [Ξ_SHA256, gᵣ, hg, accountMapExtensionalEq_empty]
  · simp [Ξ_SHA256, gᵣ, hg, h]

private theorem precompile_RIP160_accountMap_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    accountMapExtensionalEq (Ξ_RIP160 σ₁ g A I).1 (Ξ_RIP160 σ₂ g A I).1 := by
  let gᵣ : Nat :=
    let l := I.calldata.size
    let ceil := (l + 31) / 32
    600 + 120 * ceil
  by_cases hg : g.toNat < gᵣ
  · simp [Ξ_RIP160, gᵣ, hg, accountMapExtensionalEq_empty]
  · simp [Ξ_RIP160, gᵣ, hg, h]

private theorem precompile_ID_accountMap_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    accountMapExtensionalEq (Ξ_ID σ₁ g A I).1 (Ξ_ID σ₂ g A I).1 := by
  let gᵣ : Nat :=
    let l := I.calldata.size
    let ceil := (l + 31) / 32
    15 + 3 * ceil
  by_cases hg : g.toNat < gᵣ
  · simp [Ξ_ID, gᵣ, hg, accountMapExtensionalEq_empty]
  · simp [Ξ_ID, gᵣ, hg, h]

private theorem precompile_EXPMOD_accountMap_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    accountMapExtensionalEq (Ξ_EXPMOD σ₁ g A I).1 (Ξ_EXPMOD σ₂ g A I).1 := by
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
  repeat' (first | split | simp [accountMapExtensionalEq_empty, h])

private theorem precompile_BN_ADD_accountMap_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    accountMapExtensionalEq (Ξ_BN_ADD σ₁ g A I).1 (Ξ_BN_ADD σ₂ g A I).1 := by
  let gᵣ : Nat := 150
  by_cases hg : g.toNat < gᵣ
  · simp [Ξ_BN_ADD, gᵣ, hg, accountMapExtensionalEq_empty]
  · cases hres : BN_ADD (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
        (I.calldata.readBytes 64 32) (I.calldata.readBytes 96 32) <;>
      simp [Ξ_BN_ADD, gᵣ, hg, hres, dbgTrace, accountMapExtensionalEq_empty, h]

private theorem precompile_BN_MUL_accountMap_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    accountMapExtensionalEq (Ξ_BN_MUL σ₁ g A I).1 (Ξ_BN_MUL σ₂ g A I).1 := by
  let gᵣ : Nat := 6000
  by_cases hg : g.toNat < gᵣ
  · simp [Ξ_BN_MUL, gᵣ, hg, accountMapExtensionalEq_empty]
  · cases hres : BN_MUL (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
        (I.calldata.readBytes 64 32) <;>
      simp [Ξ_BN_MUL, gᵣ, hg, hres, dbgTrace, accountMapExtensionalEq_empty, h]

private theorem precompile_SNARKV_accountMap_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    accountMapExtensionalEq (Ξ_SNARKV σ₁ g A I).1 (Ξ_SNARKV σ₂ g A I).1 := by
  let d := I.calldata
  let k := d.size / 192
  let gᵣ : Nat := 34000 * k + 45000
  by_cases hg : g.toNat < gᵣ
  · simp [Ξ_SNARKV, d, k, gᵣ, hg, accountMapExtensionalEq_empty]
  · cases hres : SNARKV d <;>
      simp [Ξ_SNARKV, d, k, gᵣ, hg, hres, dbgTrace, accountMapExtensionalEq_empty, h]

private theorem precompile_BLAKE2_F_accountMap_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    accountMapExtensionalEq (Ξ_BLAKE2_F σ₁ g A I).1 (Ξ_BLAKE2_F σ₂ g A I).1 := by
  let d := I.calldata
  let gᵣ : Nat := fromByteArrayBigEndian (d.extract 0 4)
  by_cases hg : g.toNat < gᵣ
  · simp [Ξ_BLAKE2_F, d, gᵣ, hg, dbgTrace, accountMapExtensionalEq_empty]
  · cases hres : ffi.BLAKE2 d <;>
      simp [Ξ_BLAKE2_F, d, gᵣ, hg, hres, dbgTrace, accountMapExtensionalEq_empty, h]

private theorem precompile_PointEval_accountMap_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    accountMapExtensionalEq (Ξ_PointEval σ₁ g A I).1 (Ξ_PointEval σ₂ g A I).1 := by
  let d := I.calldata
  let gᵣ : Nat := 50000
  by_cases hg : g.toNat < gᵣ
  · simp [Ξ_PointEval, gᵣ, hg, accountMapExtensionalEq_empty]
  · cases hres : PointEval d <;>
      simp [Ξ_PointEval, d, gᵣ, hg, hres, dbgTrace, accountMapExtensionalEq_empty, h]

private def precompileResultExtensionalEq
    (result₁ result₂ : AccountMap × UInt256 × Substate × ByteArray) : Prop :=
  result₁.2.1 = result₂.2.1 ∧
  result₁.2.2.1 = result₂.2.2.1 ∧
  result₁.2.2.2 = result₂.2.2.2 ∧
  accountMapExtensionalEq result₁.1 result₂.1

private theorem precompile_ECREC_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    precompileResultExtensionalEq (Ξ_ECREC σ₁ g A I) (Ξ_ECREC σ₂ g A I) := by
  refine ⟨?_, ?_, ?_, precompile_ECREC_accountMap_extensional h g A I⟩
  · unfold Ξ_ECREC
    by_cases hg : g.toNat < 3000 <;> simp [hg]
  · unfold Ξ_ECREC
    by_cases hg : g.toNat < 3000 <;> simp [hg]
  · unfold Ξ_ECREC
    by_cases hg : g.toNat < 3000
    · simp [hg]
    · simp [hg]

private theorem precompile_SHA256_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    precompileResultExtensionalEq (Ξ_SHA256 σ₁ g A I) (Ξ_SHA256 σ₂ g A I) := by
  refine ⟨?_, ?_, ?_, precompile_SHA256_accountMap_extensional h g A I⟩ <;>
    (unfold Ξ_SHA256; repeat split <;> simp)

private theorem precompile_RIP160_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    precompileResultExtensionalEq (Ξ_RIP160 σ₁ g A I) (Ξ_RIP160 σ₂ g A I) := by
  refine ⟨?_, ?_, ?_, precompile_RIP160_accountMap_extensional h g A I⟩ <;>
    (unfold Ξ_RIP160; repeat split <;> simp)

private theorem precompile_ID_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    precompileResultExtensionalEq (Ξ_ID σ₁ g A I) (Ξ_ID σ₂ g A I) := by
  refine ⟨?_, ?_, ?_, precompile_ID_accountMap_extensional h g A I⟩
  all_goals
    unfold Ξ_ID
    let gᵣ : Nat :=
      let l := I.calldata.size
      let ceil := (l + 31) / 32
      15 + 3 * ceil
    by_cases hg : g.toNat < gᵣ <;> simp [gᵣ, hg]

private theorem precompile_EXPMOD_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    precompileResultExtensionalEq (Ξ_EXPMOD σ₁ g A I) (Ξ_EXPMOD σ₂ g A I) := by
  refine ⟨?_, ?_, ?_, precompile_EXPMOD_accountMap_extensional h g A I⟩ <;>
    (unfold Ξ_EXPMOD
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
     repeat' (first | split | simp))

private theorem precompile_BN_ADD_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    precompileResultExtensionalEq (Ξ_BN_ADD σ₁ g A I) (Ξ_BN_ADD σ₂ g A I) := by
  refine ⟨?_, ?_, ?_, precompile_BN_ADD_accountMap_extensional h g A I⟩
  all_goals
    unfold Ξ_BN_ADD
    by_cases hg : g.toNat < 150
    · simp [hg]
    · cases hres : BN_ADD (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
          (I.calldata.readBytes 64 32) (I.calldata.readBytes 96 32) <;>
        simp [hg, hres, dbgTrace]

private theorem precompile_BN_MUL_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    precompileResultExtensionalEq (Ξ_BN_MUL σ₁ g A I) (Ξ_BN_MUL σ₂ g A I) := by
  refine ⟨?_, ?_, ?_, precompile_BN_MUL_accountMap_extensional h g A I⟩
  all_goals
    unfold Ξ_BN_MUL
    by_cases hg : g.toNat < 6000
    · simp [hg]
    · cases hres : BN_MUL (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
          (I.calldata.readBytes 64 32) <;>
        simp [hg, hres, dbgTrace]

private theorem precompile_SNARKV_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    precompileResultExtensionalEq (Ξ_SNARKV σ₁ g A I) (Ξ_SNARKV σ₂ g A I) := by
  refine ⟨?_, ?_, ?_, precompile_SNARKV_accountMap_extensional h g A I⟩
  all_goals
    unfold Ξ_SNARKV
    let d := I.calldata
    let k := d.size / 192
    let gᵣ : Nat := 34000 * k + 45000
    by_cases hg : g.toNat < gᵣ
    · simp [d, k, gᵣ, hg]
    · cases hres : SNARKV d <;> simp [d, k, gᵣ, hg, hres, dbgTrace]

private theorem precompile_BLAKE2_F_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    precompileResultExtensionalEq (Ξ_BLAKE2_F σ₁ g A I) (Ξ_BLAKE2_F σ₂ g A I) := by
  refine ⟨?_, ?_, ?_, precompile_BLAKE2_F_accountMap_extensional h g A I⟩
  all_goals
    unfold Ξ_BLAKE2_F
    let d := I.calldata
    let gᵣ : Nat := fromByteArrayBigEndian (d.extract 0 4)
    by_cases hg : g.toNat < gᵣ
    · simp [d, gᵣ, hg, dbgTrace]
    · cases hres : ffi.BLAKE2 d <;> simp [d, gᵣ, hg, hres, dbgTrace]

private theorem precompile_PointEval_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    precompileResultExtensionalEq (Ξ_PointEval σ₁ g A I) (Ξ_PointEval σ₂ g A I) := by
  refine ⟨?_, ?_, ?_, precompile_PointEval_accountMap_extensional h g A I⟩
  all_goals
    unfold Ξ_PointEval
    let d := I.calldata
    by_cases hg : g.toNat < 50000
    · simp [d, hg]
    · cases hres : PointEval d <;> simp [d, hg, hres, dbgTrace]

private theorem precompile_dispatch_accountMap_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (pc : AccountAddress)
    (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    accountMapExtensionalEq
      (let result : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
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
       result.2.1)
      (let result : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
        match pc with
        | 1 => (∅, Ξ_ECREC σ₂ g A I)
        | 2 => (∅, Ξ_SHA256 σ₂ g A I)
        | 3 => (∅, Ξ_RIP160 σ₂ g A I)
        | 4 => (∅, Ξ_ID σ₂ g A I)
        | 5 => (∅, Ξ_EXPMOD σ₂ g A I)
        | 6 => (∅, Ξ_BN_ADD σ₂ g A I)
        | 7 => (∅, Ξ_BN_MUL σ₂ g A I)
        | 8 => (∅, Ξ_SNARKV σ₂ g A I)
        | 9 => (∅, Ξ_BLAKE2_F σ₂ g A I)
        | 10 => (∅, Ξ_PointEval σ₂ g A I)
        | _ => default
       result.2.1) := by
  repeat split
  all_goals
    first
    | exact precompile_ECREC_accountMap_extensional h g A I
    | exact precompile_SHA256_accountMap_extensional h g A I
    | exact precompile_RIP160_accountMap_extensional h g A I
    | exact precompile_ID_accountMap_extensional h g A I
    | exact precompile_EXPMOD_accountMap_extensional h g A I
    | exact precompile_BN_ADD_accountMap_extensional h g A I
    | exact precompile_BN_MUL_accountMap_extensional h g A I
    | exact precompile_SNARKV_accountMap_extensional h g A I
    | exact precompile_BLAKE2_F_accountMap_extensional h g A I
    | exact precompile_PointEval_accountMap_extensional h g A I
    | exact accountMapExtensionalEq_refl _

private def precompileDispatchExtensionalEq
    (result₁ result₂ :
      Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray) :
    Prop :=
  result₁.1 = result₂.1 ∧
  precompileResultExtensionalEq result₁.2 result₂.2

private theorem precompile_dispatch_extensional {σ₁ σ₂ : AccountMap}
    (h : accountMapExtensionalEq σ₁ σ₂) (pc : AccountAddress)
    (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    precompileDispatchExtensionalEq
      (match pc with
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
        | _ => default)
      (match pc with
        | 1 => (∅, Ξ_ECREC σ₂ g A I)
        | 2 => (∅, Ξ_SHA256 σ₂ g A I)
        | 3 => (∅, Ξ_RIP160 σ₂ g A I)
        | 4 => (∅, Ξ_ID σ₂ g A I)
        | 5 => (∅, Ξ_EXPMOD σ₂ g A I)
        | 6 => (∅, Ξ_BN_ADD σ₂ g A I)
        | 7 => (∅, Ξ_BN_MUL σ₂ g A I)
        | 8 => (∅, Ξ_SNARKV σ₂ g A I)
        | 9 => (∅, Ξ_BLAKE2_F σ₂ g A I)
        | 10 => (∅, Ξ_PointEval σ₂ g A I)
        | _ => default) := by
  repeat split
  all_goals
    first
    | exact ⟨rfl, precompile_ECREC_extensional h g A I⟩
    | exact ⟨rfl, precompile_SHA256_extensional h g A I⟩
    | exact ⟨rfl, precompile_RIP160_extensional h g A I⟩
    | exact ⟨rfl, precompile_ID_extensional h g A I⟩
    | exact ⟨rfl, precompile_EXPMOD_extensional h g A I⟩
    | exact ⟨rfl, precompile_BN_ADD_extensional h g A I⟩
    | exact ⟨rfl, precompile_BN_MUL_extensional h g A I⟩
    | exact ⟨rfl, precompile_SNARKV_extensional h g A I⟩
    | exact ⟨rfl, precompile_BLAKE2_F_extensional h g A I⟩
    | exact ⟨rfl, precompile_PointEval_extensional h g A I⟩
    | exact ⟨rfl, by simp [precompileResultExtensionalEq, accountMapExtensionalEq_refl]⟩

private theorem thetaPrecompiledResult_extensional_of_dispatch {σ₁ σ₂ : AccountMap}
    {result₁ result₂ :
      Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray}
    (A : Substate)
    (hσ : accountMapExtensionalEq σ₁ σ₂)
    (hdispatch : precompileDispatchExtensionalEq result₁ result₂) :
    thetaResultExtensionalEq
      (result₁.1,
       if result₁.2.1 == (∅ : AccountMap) then σ₁ else result₁.2.1,
       result₁.2.2.1,
       if result₁.2.1 == (∅ : AccountMap) then A else result₁.2.2.2.1,
       if result₁.2.1 == (∅ : AccountMap) then false else true,
       result₁.2.2.2.2)
      (result₂.1,
       if result₂.2.1 == (∅ : AccountMap) then σ₂ else result₂.2.1,
       result₂.2.2.1,
       if result₂.2.1 == (∅ : AccountMap) then A else result₂.2.2.2.1,
       if result₂.2.1 == (∅ : AccountMap) then false else true,
       result₂.2.2.2.2) := by
  rcases hdispatch with ⟨hcreated, hresult⟩
  exact thetaFinalize_extensional hσ hcreated hresult.2.2.2 hresult.1 hresult.2.1
    hresult.2.2.1

theorem accountMap_extensionality_of_Theta_and_Lambda
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ₁ σ₂ σ₀ : AccountMap}
    {A : Substate}
    {s o r : AccountAddress}
    {g p v v' : UInt256}
    {d i : ByteArray}
    {ζ : Option ByteArray}
    {H : BlockHeader}
    {w : Bool} :
    ∀ a₁ a₂ c createdAccounts₁' createdAccounts₂'
      σ₁' σ₂' g₁' g₂' A₁' A₂' z₁ z₂ o₁' o₂' e,
      accountMapExtensionalEq σ₁ σ₂ →
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o r c
          g p v v' d e H w =
        (createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
       Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o r c
          g p v v' d e H w =
        (createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂') ∧
      (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o
          g p v i e ζ H w =
        (a₁, createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') →
       Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o
          g p v i e ζ H w =
        (a₂, createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') →
        createdAccounts₁' = createdAccounts₂' ∧
        a₁ = a₂ ∧ g₁' = g₂' ∧ A₁' = A₂' ∧ z₁ = z₂ ∧ o₁' = o₂' ∧
        accountMapExtensionalEq σ₁' σ₂') := by
  intros a₁ a₂ c createdAccounts₁' createdAccounts₂'
    σ₁' σ₂' g₁' g₂' A₁' A₂' z₁ z₂ o₁' o₂' e hσ
  generalize hn : 1024 - e.val = n
  induction n generalizing blobVersionedHashes genesisBlockHeader blocks
      createdAccounts e σ₁ σ₂ σ₀ A s o r c g p v v' d i ζ H w
      a₁ a₂ createdAccounts₁' createdAccounts₂' σ₁' σ₂' A₁' A₂'
      g₁' g₂' z₁ z₂ o₁' o₂' with
  | zero =>
      have he_eq : e = 1024 := by omega
      subst e
      constructor
      · intro hTheta₁ hTheta₂
        cases hc : c with
        | Precompiled pc =>
            sorry
        | Code code =>
            have hpre := accountMapExtensionalEq_call_prelude hσ r s v
            have hXi :
                exceptExecutionResultXiExtensionalEq
                  (Ξ createdAccounts genesisBlockHeader blocks
                    (let σ' :=
                      match σ₁.find? r with
                      | none =>
                          if v != UInt256.ofNat 0 then
                            σ₁.insert r { (default : Account) with balance := v }
                          else
                            σ₁
                      | some acc =>
                          σ₁.insert r { acc with balance := acc.balance + v }
                     match σ'.find? s with
                     | none => σ'
                     | some acc => σ'.insert s { acc with balance := acc.balance - v })
                    σ₀ g A
                    { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
                      source := s, weiValue := v', depth := (1024 : Fin 1025), perm := w,
                      code := code, header := H, blobVersionedHashes := blobVersionedHashes })
                  (Ξ createdAccounts genesisBlockHeader blocks
                    (let σ' :=
                      match σ₂.find? r with
                      | none =>
                          if v != UInt256.ofNat 0 then
                            σ₂.insert r { (default : Account) with balance := v }
                          else
                            σ₂
                      | some acc =>
                          σ₂.insert r { acc with balance := acc.balance + v }
                     match σ'.find? s with
                     | none => σ'
                     | some acc => σ'.insert s { acc with balance := acc.balance - v })
                    σ₀ g A
                    { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
                      source := s, weiValue := v', depth := (1024 : Fin 1025), perm := w,
                      code := code, header := H, blobVersionedHashes := blobVersionedHashes }) :=
              Xi_extensional_max_depth hpre (by simp)
            have hrel :
                thetaResultExtensionalEq
                  (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o r
                    (ToExecute.Code code) g p v v' d (1024 : Fin 1025) H w)
                  (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o r
                    (ToExecute.Code code) g p v v' d (1024 : Fin 1025) H w) := by
              unfold Θ
              by_cases hv : v != UInt256.ofNat 0
              · have hvne : v ≠ UInt256.ofNat 0 := by
                  simpa [bne] using hv
                have hvb : (!v == UInt256.ofNat 0) = true := by
                  simpa [bne] using hv
                have hXi' := hXi
                simp [bne, hv, hvb, hvne] at hXi'
                simpa [bne, hv, hvb, hvne] using
                  (thetaCodeResult_extensional_of_Xi_expanded (σ₁ := σ₁) (σ₂ := σ₂)
                    (createdAccounts := createdAccounts) (A := A) hσ hXi')
              · have hveq : v = UInt256.ofNat 0 := by
                  simpa [bne] using hv
                have hvb : (!v == UInt256.ofNat 0) = false := by
                  simpa [bne] using hv
                have hXi' := hXi
                simp [bne, hv, hvb, hveq] at hXi'
                simpa [bne, hv, hvb, hveq] using
                  (thetaCodeResult_extensional_of_Xi_expanded (σ₁ := σ₁) (σ₂ := σ₂)
                    (createdAccounts := createdAccounts) (A := A) hσ hXi')
            have hTheta₁' :
                Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o r
                  (ToExecute.Code code) g p v v' d (1024 : Fin 1025) H w =
                (createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') := by
              simpa [hc] using hTheta₁
            have hTheta₂' :
                Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o r
                  (ToExecute.Code code) g p v v' d (1024 : Fin 1025) H w =
                (createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') := by
              simpa [hc] using hTheta₂
            rw [hTheta₁', hTheta₂'] at hrel
            simpa [thetaResultExtensionalEq] using hrel
      · intro hLambda₁ hLambda₂
        let n₁ : UInt256 := (σ₁.find? s |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩
        let lₐ := Lambda.L_A s n₁ ζ i
        let a : AccountAddress :=
          (ffi.KEC lₐ).extract 12 32 |> fromByteArrayBigEndian |> Fin.ofNat _
        let AStar := A.addAccessedAccount a
        let collision₁ : Bool :=
          (σ₁.findD a default).nonce ≠ ⟨0⟩ ||
            (σ₁.findD a default).code.size ≠ 0 ||
            (σ₁.findD a default).storage != default
        let collision₂ : Bool :=
          (σ₂.findD a default).nonce ≠ ⟨0⟩ ||
            (σ₂.findD a default).code.size ≠ 0 ||
            (σ₂.findD a default).storage != default
        let collisionResult₁ : ByteArray × Batteries.RBSet AccountAddress compare :=
          if collision₁ then (⟨#[0xfe]⟩, createdAccounts) else (i, createdAccounts.insert a)
        let collisionResult₂ : ByteArray × Batteries.RBSet AccountAddress compare :=
          if collision₂ then (⟨#[0xfe]⟩, createdAccounts) else (i, createdAccounts.insert a)
        let createdAccountsStar₁ := collisionResult₁.2
        let codeStar₁ := collisionResult₁.1
        have hnonce :
            ((σ₂.find? s |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩) = n₁ := by
          simp [n₁, accountMapExtensionalEq_nonceOf hσ s]
        have hcodeSize₁ :
            (σ₁.findD a default).code.size ≠ 0 ↔
              (σ₁.findD a default).code ≠ ByteArray.empty := by
          let b := (σ₁.findD a default).code
          change b.size ≠ 0 ↔ b ≠ ByteArray.empty
          constructor
          · intro hsize hempty
            apply hsize
            simp [hempty]
          · intro hne hsize
            apply hne
            revert hsize
            cases b with
            | mk data =>
                cases data with
                | mk xs =>
                    cases xs with
                    | nil =>
                        intro hsize
                        rfl
                    | cons x xs =>
                        intro hsize
                        simp at hsize
                        exact hsize
        have hcodeSize₂ :
            (σ₂.findD a default).code.size ≠ 0 ↔
              (σ₂.findD a default).code ≠ ByteArray.empty := by
          let b := (σ₂.findD a default).code
          change b.size ≠ 0 ↔ b ≠ ByteArray.empty
          constructor
          · intro hsize hempty
            apply hsize
            simp [hempty]
          · intro hne hsize
            apply hne
            revert hsize
            cases b with
            | mk data =>
                cases data with
                | mk xs =>
                    cases xs with
                    | nil =>
                        intro hsize
                        rfl
                    | cons x xs =>
                        intro hsize
                        simp at hsize
                        exact hsize
        have hcollisionBool : collision₂ = collision₁ := by
          simpa [collision₁, collision₂] using
            (accountMapExtensionalEq_create_collision_check hσ a).symm
        have hcollision : collisionResult₂ = collisionResult₁ := by
          simp [collisionResult₁, collisionResult₂, hcollisionBool]
        have hpre := accountMapExtensionalEq_create_prelude hσ a s v
        let xi₁ : Except EVM.ExecutionException
            (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate)) :=
          Ξ createdAccountsStar₁ genesisBlockHeader blocks
            (match σ₁.find? s with
             | none => σ₁
             | some ac =>
                σ₁.insert s { ac with balance := ac.balance - v }
                  |>.insert a
                    { (σ₁.findD a default) with
                      nonce := (σ₁.findD a default).nonce + ⟨1⟩
                      balance := v + (σ₁.findD a default).balance })
            σ₀ g AStar
            { codeOwner := a, sender := o, source := s, weiValue := v,
              calldata := default, code := codeStar₁, gasPrice := p.toNat,
              header := H, depth := (1024 : Fin 1025), perm := w,
              blobVersionedHashes := blobVersionedHashes }
        let xi₂ : Except EVM.ExecutionException
            (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate)) :=
          Ξ createdAccountsStar₁ genesisBlockHeader blocks
            (match σ₂.find? s with
             | none => σ₂
             | some ac =>
                σ₂.insert s { ac with balance := ac.balance - v }
                  |>.insert a
                    { (σ₂.findD a default) with
                      nonce := (σ₂.findD a default).nonce + ⟨1⟩
                      balance := v + (σ₂.findD a default).balance })
            σ₀ g AStar
            { codeOwner := a, sender := o, source := s, weiValue := v,
              calldata := default, code := codeStar₁, gasPrice := p.toNat,
              header := H, depth := (1024 : Fin 1025), perm := w,
              blobVersionedHashes := blobVersionedHashes }
        have hXi :
            exceptExecutionResultXiExtensionalEq
              (Ξ createdAccountsStar₁ genesisBlockHeader blocks
                (match σ₁.find? s with
                 | none => σ₁
                 | some ac =>
                    σ₁.insert s { ac with balance := ac.balance - v }
                      |>.insert a
                        { (σ₁.findD a default) with
                          nonce := (σ₁.findD a default).nonce + ⟨1⟩
                          balance := v + (σ₁.findD a default).balance })
                σ₀ g AStar
                { codeOwner := a, sender := o, source := s, weiValue := v,
                  calldata := default, code := codeStar₁, gasPrice := p.toNat,
                  header := H, depth := (1024 : Fin 1025), perm := w,
                  blobVersionedHashes := blobVersionedHashes })
              (Ξ createdAccountsStar₁ genesisBlockHeader blocks
                (match σ₂.find? s with
                 | none => σ₂
                 | some ac =>
                    σ₂.insert s { ac with balance := ac.balance - v }
                      |>.insert a
                        { (σ₂.findD a default) with
                          nonce := (σ₂.findD a default).nonce + ⟨1⟩
                          balance := v + (σ₂.findD a default).balance })
                σ₀ g AStar
                { codeOwner := a, sender := o, source := s, weiValue := v,
                  calldata := default, code := codeStar₁, gasPrice := p.toNat,
                  header := H, depth := (1024 : Fin 1025), perm := w,
                  blobVersionedHashes := blobVersionedHashes }) :=
          Xi_extensional_max_depth hpre (by simp)
        have hrel :
            lambdaResultExtensionalEq
              (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o
                g p v i (1024 : Fin 1025) ζ H w)
              (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o
                g p v i (1024 : Fin 1025) ζ H w) := by
          have hXiNamed : exceptExecutionResultXiExtensionalEq xi₁ xi₂ := by
            simpa [xi₁, xi₂] using hXi
          have hcore :=
            lambdaResult_extensional_of_Xi_named (σ₁ := σ₁) (σ₂ := σ₂)
              (createdAccounts₁ := createdAccountsStar₁)
              (createdAccounts₂ := createdAccountsStar₁)
              (xi₁ := xi₁) (xi₂ := xi₂) (AStar := AStar) (a := a)
              rfl hσ hXiNamed
          have hleft :
              Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o
                g p v i (1024 : Fin 1025) ζ H w =
              lambdaXiResult a createdAccountsStar₁ σ₁ AStar xi₁ := by
            unfold Lambda
            dsimp [lambdaXiResult, xi₁, AStar, a, lₐ, n₁,
              createdAccountsStar₁, codeStar₁, collisionResult₁, collision₁]
            rfl
          have hright :
              Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o
                g p v i (1024 : Fin 1025) ζ H w =
              lambdaXiResult a createdAccountsStar₁ σ₂ AStar xi₂ := by
            let lambdaBody (collisionResult : ByteArray ×
                Batteries.RBSet AccountAddress compare) :=
              lambdaXiResult a collisionResult.2 σ₂ AStar
                (Ξ collisionResult.2 genesisBlockHeader blocks
                  (match σ₂.find? s with
                   | none => σ₂
                   | some ac =>
                      σ₂.insert s { ac with balance := ac.balance - v }
                        |>.insert a
                          { (σ₂.findD a default) with
                            nonce := (σ₂.findD a default).nonce + ⟨1⟩
                            balance := v + (σ₂.findD a default).balance })
                  σ₀ g AStar
                  { codeOwner := a, sender := o, source := s, weiValue := v,
                    calldata := default, code := collisionResult.1, gasPrice := p.toNat,
                    header := H, depth := (1024 : Fin 1025), perm := w,
                    blobVersionedHashes := blobVersionedHashes })
            unfold Lambda
            rw [hnonce]
            change lambdaBody collisionResult₂ =
              lambdaXiResult a createdAccountsStar₁ σ₂ AStar xi₂
            rw [hcollision]
          rw [hleft, hright]
          exact hcore
        rw [hLambda₁, hLambda₂] at hrel
        simpa [lambdaResultExtensionalEq] using hrel
  | succ n' ih =>
      constructor
      · intro hTheta₁ hTheta₂
        cases hc : c with
        | Precompiled pc =>
            sorry
        | Code code =>
            have hpre := accountMapExtensionalEq_call_prelude hσ r s v
            have hXi :
                exceptExecutionResultXiExtensionalEq
                  (Ξ createdAccounts genesisBlockHeader blocks
                    (let σ' :=
                      match σ₁.find? r with
                      | none =>
                          if v != UInt256.ofNat 0 then
                            σ₁.insert r { (default : Account) with balance := v }
                          else
                            σ₁
                      | some acc =>
                          σ₁.insert r { acc with balance := acc.balance + v }
                     match σ'.find? s with
                     | none => σ'
                     | some acc => σ'.insert s { acc with balance := acc.balance - v })
                    σ₀ g A
                    { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
                      source := s, weiValue := v', depth := e, perm := w,
                      code := code, header := H, blobVersionedHashes := blobVersionedHashes })
                  (Ξ createdAccounts genesisBlockHeader blocks
                    (let σ' :=
                      match σ₂.find? r with
                      | none =>
                          if v != UInt256.ofNat 0 then
                            σ₂.insert r { (default : Account) with balance := v }
                          else
                            σ₂
                      | some acc =>
                          σ₂.insert r { acc with balance := acc.balance + v }
                     match σ'.find? s with
                     | none => σ'
                     | some acc => σ'.insert s { acc with balance := acc.balance - v })
                    σ₀ g A
                    { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
                      source := s, weiValue := v', depth := e, perm := w,
                      code := code, header := H, blobVersionedHashes := blobVersionedHashes }) := by
              apply Xi_extensional_of_Theta_Lambda_at_depth hpre (n := n')
              · simpa using hn
              · intro blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
                  σ₁ᵢ σ₂ᵢ σ₀ᵢ Aᵢ sᵢ oᵢ rᵢ cᵢ gᵢ pᵢ vᵢ v'ᵢ dᵢ eᵢ Hᵢ wᵢ
                  createdAccounts₁ᵢ createdAccounts₂ᵢ σ₁ᵢ' σ₂ᵢ'
                  g₁ᵢ' g₂ᵢ' A₁ᵢ' A₂ᵢ' z₁ᵢ z₂ᵢ o₁ᵢ' o₂ᵢ'
                  hσᵢ heᵢ hTheta₁ᵢ hTheta₂ᵢ
                exact (ih (blobVersionedHashes := blobVersionedHashesᵢ)
                  (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                  (createdAccounts := createdAccountsᵢ) (σ₁ := σ₁ᵢ) (σ₂ := σ₂ᵢ)
                  (σ₀ := σ₀ᵢ) (A := Aᵢ) (s := sᵢ) (o := oᵢ) (r := rᵢ)
                  (g := gᵢ) (p := pᵢ) (v := vᵢ) (v' := v'ᵢ) (d := dᵢ)
                  (i := default) (ζ := none) (H := Hᵢ) (w := wᵢ)
                  default default cᵢ createdAccounts₁ᵢ createdAccounts₂ᵢ
                  σ₁ᵢ' σ₂ᵢ' g₁ᵢ' g₂ᵢ' A₁ᵢ' A₂ᵢ' z₁ᵢ z₂ᵢ o₁ᵢ' o₂ᵢ' eᵢ
                  hσᵢ heᵢ).1 hTheta₁ᵢ hTheta₂ᵢ
              · intro blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
                  σ₁ᵢ σ₂ᵢ σ₀ᵢ Aᵢ sᵢ oᵢ gᵢ pᵢ vᵢ iᵢ eᵢ ζᵢ Hᵢ wᵢ
                  a₁ᵢ a₂ᵢ createdAccounts₁ᵢ createdAccounts₂ᵢ σ₁ᵢ' σ₂ᵢ'
                  g₁ᵢ' g₂ᵢ' A₁ᵢ' A₂ᵢ' z₁ᵢ z₂ᵢ o₁ᵢ' o₂ᵢ'
                  hσᵢ heᵢ hLambda₁ᵢ hLambda₂ᵢ
                exact (ih (blobVersionedHashes := blobVersionedHashesᵢ)
                  (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                  (createdAccounts := createdAccountsᵢ) (σ₁ := σ₁ᵢ) (σ₂ := σ₂ᵢ)
                  (σ₀ := σ₀ᵢ) (A := Aᵢ) (s := sᵢ) (o := oᵢ) (r := default)
                  (g := gᵢ) (p := pᵢ) (v := vᵢ) (v' := default) (d := default)
                  (i := iᵢ) (ζ := ζᵢ) (H := Hᵢ) (w := wᵢ)
                  a₁ᵢ a₂ᵢ (toExecute σ₁ᵢ default)
                  createdAccounts₁ᵢ createdAccounts₂ᵢ σ₁ᵢ' σ₂ᵢ'
                  g₁ᵢ' g₂ᵢ' A₁ᵢ' A₂ᵢ' z₁ᵢ z₂ᵢ o₁ᵢ' o₂ᵢ' eᵢ
                  hσᵢ heᵢ).2 hLambda₁ᵢ hLambda₂ᵢ
            have hrel :
                thetaResultExtensionalEq
                  (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o r
                    (ToExecute.Code code) g p v v' d e H w)
                  (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o r
                    (ToExecute.Code code) g p v v' d e H w) := by
              unfold Θ
              by_cases hv : v != UInt256.ofNat 0
              · have hvne : v ≠ UInt256.ofNat 0 := by
                  simpa [bne] using hv
                have hvb : (!v == UInt256.ofNat 0) = true := by
                  simpa [bne] using hv
                have hXi' := hXi
                simp [bne, hv, hvb, hvne] at hXi'
                simpa [bne, hv, hvb, hvne] using
                  (thetaCodeResult_extensional_of_Xi_expanded (σ₁ := σ₁) (σ₂ := σ₂)
                    (createdAccounts := createdAccounts) (A := A) hσ hXi')
              · have hveq : v = UInt256.ofNat 0 := by
                  simpa [bne] using hv
                have hvb : (!v == UInt256.ofNat 0) = false := by
                  simpa [bne] using hv
                have hXi' := hXi
                simp [bne, hv, hvb, hveq] at hXi'
                simpa [bne, hv, hvb, hveq] using
                  (thetaCodeResult_extensional_of_Xi_expanded (σ₁ := σ₁) (σ₂ := σ₂)
                    (createdAccounts := createdAccounts) (A := A) hσ hXi')
            have hTheta₁' :
                Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o r
                  (ToExecute.Code code) g p v v' d e H w =
                (createdAccounts₁', σ₁', g₁', A₁', z₁, o₁') := by
              simpa [hc] using hTheta₁
            have hTheta₂' :
                Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o r
                  (ToExecute.Code code) g p v v' d e H w =
                (createdAccounts₂', σ₂', g₂', A₂', z₂, o₂') := by
              simpa [hc] using hTheta₂
            rw [hTheta₁', hTheta₂'] at hrel
            simpa [thetaResultExtensionalEq] using hrel
      · intro hLambda₁ hLambda₂
        let n₁ : UInt256 := (σ₁.find? s |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩
        let lₐ := Lambda.L_A s n₁ ζ i
        let a : AccountAddress :=
          (ffi.KEC lₐ).extract 12 32 |> fromByteArrayBigEndian |> Fin.ofNat _
        let AStar := A.addAccessedAccount a
        let collision₁ : Bool :=
          (σ₁.findD a default).nonce ≠ ⟨0⟩ ||
            (σ₁.findD a default).code.size ≠ 0 ||
            (σ₁.findD a default).storage != default
        let collision₂ : Bool :=
          (σ₂.findD a default).nonce ≠ ⟨0⟩ ||
            (σ₂.findD a default).code.size ≠ 0 ||
            (σ₂.findD a default).storage != default
        let collisionResult₁ : ByteArray × Batteries.RBSet AccountAddress compare :=
          if collision₁ then (⟨#[0xfe]⟩, createdAccounts) else (i, createdAccounts.insert a)
        let collisionResult₂ : ByteArray × Batteries.RBSet AccountAddress compare :=
          if collision₂ then (⟨#[0xfe]⟩, createdAccounts) else (i, createdAccounts.insert a)
        let createdAccountsStar₁ := collisionResult₁.2
        let codeStar₁ := collisionResult₁.1
        have hnonce :
            ((σ₂.find? s |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩) = n₁ := by
          simp [n₁, accountMapExtensionalEq_nonceOf hσ s]
        have hcodeSize₁ :
            (σ₁.findD a default).code.size ≠ 0 ↔
              (σ₁.findD a default).code ≠ ByteArray.empty := by
          let b := (σ₁.findD a default).code
          change b.size ≠ 0 ↔ b ≠ ByteArray.empty
          constructor
          · intro hsize hempty
            apply hsize
            simp [hempty]
          · intro hne hsize
            apply hne
            revert hsize
            cases b with
            | mk data =>
                cases data with
                | mk xs =>
                    cases xs with
                    | nil =>
                        intro hsize
                        rfl
                    | cons x xs =>
                        intro hsize
                        simp at hsize
                        exact hsize
        have hcodeSize₂ :
            (σ₂.findD a default).code.size ≠ 0 ↔
              (σ₂.findD a default).code ≠ ByteArray.empty := by
          let b := (σ₂.findD a default).code
          change b.size ≠ 0 ↔ b ≠ ByteArray.empty
          constructor
          · intro hsize hempty
            apply hsize
            simp [hempty]
          · intro hne hsize
            apply hne
            revert hsize
            cases b with
            | mk data =>
                cases data with
                | mk xs =>
                    cases xs with
                    | nil =>
                        intro hsize
                        rfl
                    | cons x xs =>
                        intro hsize
                        simp at hsize
                        exact hsize
        have hcollisionBool : collision₂ = collision₁ := by
          simpa [collision₁, collision₂] using
            (accountMapExtensionalEq_create_collision_check hσ a).symm
        have hcollision : collisionResult₂ = collisionResult₁ := by
          simp [collisionResult₁, collisionResult₂, hcollisionBool]
        have hpre := accountMapExtensionalEq_create_prelude hσ a s v
        let xi₁ : Except EVM.ExecutionException
            (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate)) :=
          Ξ createdAccountsStar₁ genesisBlockHeader blocks
            (match σ₁.find? s with
             | none => σ₁
             | some ac =>
                σ₁.insert s { ac with balance := ac.balance - v }
                  |>.insert a
                    { (σ₁.findD a default) with
                      nonce := (σ₁.findD a default).nonce + ⟨1⟩
                      balance := v + (σ₁.findD a default).balance })
            σ₀ g AStar
            { codeOwner := a, sender := o, source := s, weiValue := v,
              calldata := default, code := codeStar₁, gasPrice := p.toNat,
              header := H, depth := e, perm := w,
              blobVersionedHashes := blobVersionedHashes }
        let xi₂ : Except EVM.ExecutionException
            (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate)) :=
          Ξ createdAccountsStar₁ genesisBlockHeader blocks
            (match σ₂.find? s with
             | none => σ₂
             | some ac =>
                σ₂.insert s { ac with balance := ac.balance - v }
                  |>.insert a
                    { (σ₂.findD a default) with
                      nonce := (σ₂.findD a default).nonce + ⟨1⟩
                      balance := v + (σ₂.findD a default).balance })
            σ₀ g AStar
            { codeOwner := a, sender := o, source := s, weiValue := v,
              calldata := default, code := codeStar₁, gasPrice := p.toNat,
              header := H, depth := e, perm := w,
              blobVersionedHashes := blobVersionedHashes }
        have hXi :
            exceptExecutionResultXiExtensionalEq
              (Ξ createdAccountsStar₁ genesisBlockHeader blocks
                (match σ₁.find? s with
                 | none => σ₁
                 | some ac =>
                    σ₁.insert s { ac with balance := ac.balance - v }
                      |>.insert a
                        { (σ₁.findD a default) with
                          nonce := (σ₁.findD a default).nonce + ⟨1⟩
                          balance := v + (σ₁.findD a default).balance })
                σ₀ g AStar
                { codeOwner := a, sender := o, source := s, weiValue := v,
                  calldata := default, code := codeStar₁, gasPrice := p.toNat,
                  header := H, depth := e, perm := w,
                  blobVersionedHashes := blobVersionedHashes })
              (Ξ createdAccountsStar₁ genesisBlockHeader blocks
                (match σ₂.find? s with
                 | none => σ₂
                 | some ac =>
                    σ₂.insert s { ac with balance := ac.balance - v }
                      |>.insert a
                        { (σ₂.findD a default) with
                          nonce := (σ₂.findD a default).nonce + ⟨1⟩
                          balance := v + (σ₂.findD a default).balance })
                σ₀ g AStar
                { codeOwner := a, sender := o, source := s, weiValue := v,
                  calldata := default, code := codeStar₁, gasPrice := p.toNat,
                  header := H, depth := e, perm := w,
                  blobVersionedHashes := blobVersionedHashes }) := by
          apply Xi_extensional_of_Theta_Lambda_at_depth hpre (n := n')
          · simpa using hn
          · intro blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ₁ᵢ σ₂ᵢ σ₀ᵢ Aᵢ sᵢ oᵢ rᵢ cᵢ gᵢ pᵢ vᵢ v'ᵢ dᵢ eᵢ Hᵢ wᵢ
              createdAccounts₁ᵢ createdAccounts₂ᵢ σ₁ᵢ' σ₂ᵢ'
              g₁ᵢ' g₂ᵢ' A₁ᵢ' A₂ᵢ' z₁ᵢ z₂ᵢ o₁ᵢ' o₂ᵢ'
              hσᵢ heᵢ hTheta₁ᵢ hTheta₂ᵢ
            exact (ih (blobVersionedHashes := blobVersionedHashesᵢ)
              (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
              (createdAccounts := createdAccountsᵢ) (σ₁ := σ₁ᵢ) (σ₂ := σ₂ᵢ)
              (σ₀ := σ₀ᵢ) (A := Aᵢ) (s := sᵢ) (o := oᵢ) (r := rᵢ)
              (g := gᵢ) (p := pᵢ) (v := vᵢ) (v' := v'ᵢ) (d := dᵢ)
              (i := default) (ζ := none) (H := Hᵢ) (w := wᵢ)
              default default cᵢ createdAccounts₁ᵢ createdAccounts₂ᵢ
              σ₁ᵢ' σ₂ᵢ' g₁ᵢ' g₂ᵢ' A₁ᵢ' A₂ᵢ' z₁ᵢ z₂ᵢ o₁ᵢ' o₂ᵢ' eᵢ
              hσᵢ heᵢ).1 hTheta₁ᵢ hTheta₂ᵢ
          · intro blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ₁ᵢ σ₂ᵢ σ₀ᵢ Aᵢ sᵢ oᵢ gᵢ pᵢ vᵢ iᵢ eᵢ ζᵢ Hᵢ wᵢ
              a₁ᵢ a₂ᵢ createdAccounts₁ᵢ createdAccounts₂ᵢ σ₁ᵢ' σ₂ᵢ'
              g₁ᵢ' g₂ᵢ' A₁ᵢ' A₂ᵢ' z₁ᵢ z₂ᵢ o₁ᵢ' o₂ᵢ'
              hσᵢ heᵢ hLambda₁ᵢ hLambda₂ᵢ
            exact (ih (blobVersionedHashes := blobVersionedHashesᵢ)
              (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
              (createdAccounts := createdAccountsᵢ) (σ₁ := σ₁ᵢ) (σ₂ := σ₂ᵢ)
              (σ₀ := σ₀ᵢ) (A := Aᵢ) (s := sᵢ) (o := oᵢ) (r := default)
              (g := gᵢ) (p := pᵢ) (v := vᵢ) (v' := default) (d := default)
              (i := iᵢ) (ζ := ζᵢ) (H := Hᵢ) (w := wᵢ)
              a₁ᵢ a₂ᵢ (toExecute σ₁ᵢ default)
              createdAccounts₁ᵢ createdAccounts₂ᵢ σ₁ᵢ' σ₂ᵢ'
              g₁ᵢ' g₂ᵢ' A₁ᵢ' A₂ᵢ' z₁ᵢ z₂ᵢ o₁ᵢ' o₂ᵢ' eᵢ
              hσᵢ heᵢ).2 hLambda₁ᵢ hLambda₂ᵢ
        have hrel :
            lambdaResultExtensionalEq
              (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o
                g p v i e ζ H w)
              (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o
                g p v i e ζ H w) := by
          have hXiNamed : exceptExecutionResultXiExtensionalEq xi₁ xi₂ := by
            simpa [xi₁, xi₂] using hXi
          have hcore :=
            lambdaResult_extensional_of_Xi_named (σ₁ := σ₁) (σ₂ := σ₂)
              (createdAccounts₁ := createdAccountsStar₁)
              (createdAccounts₂ := createdAccountsStar₁)
              (xi₁ := xi₁) (xi₂ := xi₂) (AStar := AStar) (a := a)
              rfl hσ hXiNamed
          have hleft :
              Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₁ σ₀ A s o
                g p v i e ζ H w =
              lambdaXiResult a createdAccountsStar₁ σ₁ AStar xi₁ := by
            unfold Lambda
            dsimp [lambdaXiResult, xi₁, AStar, a, lₐ, n₁,
              createdAccountsStar₁, codeStar₁, collisionResult₁, collision₁]
            rfl
          have hright :
              Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ₂ σ₀ A s o
                g p v i e ζ H w =
              lambdaXiResult a createdAccountsStar₁ σ₂ AStar xi₂ := by
            let lambdaBody (collisionResult : ByteArray ×
                Batteries.RBSet AccountAddress compare) :=
              lambdaXiResult a collisionResult.2 σ₂ AStar
                (Ξ collisionResult.2 genesisBlockHeader blocks
                  (match σ₂.find? s with
                   | none => σ₂
                   | some ac =>
                      σ₂.insert s { ac with balance := ac.balance - v }
                        |>.insert a
                          { (σ₂.findD a default) with
                            nonce := (σ₂.findD a default).nonce + ⟨1⟩
                            balance := v + (σ₂.findD a default).balance })
                  σ₀ g AStar
                  { codeOwner := a, sender := o, source := s, weiValue := v,
                    calldata := default, code := collisionResult.1, gasPrice := p.toNat,
                    header := H, depth := e, perm := w,
                    blobVersionedHashes := blobVersionedHashes })
            unfold Lambda
            rw [hnonce]
            change lambdaBody collisionResult₂ =
              lambdaXiResult a createdAccountsStar₁ σ₂ AStar xi₂
            rw [hcollision]
          rw [hleft, hright]
          exact hcore
        rw [hLambda₁, hLambda₂] at hrel
        simpa [lambdaResultExtensionalEq] using hrel

end EVM
end Ethereum
