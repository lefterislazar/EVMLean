import Ethereum.Theory.AccountLocality
import Ethereum.Theory.StorageExtensionality

import Batteries.Data.RBMap.Lemmas

namespace Ethereum
namespace EVM

def accountStorageState (σ : AccountMap) : AccountAddress → Storage × Storage :=
  fun addr => ((σ.findD addr default).storage, (σ.findD addr default).tstorage)

def stateStorageState (state : State) : AccountAddress → Storage × Storage :=
  accountStorageState state.accountMap

def accountStorageStateEq (σ τ : AccountMap) : Prop :=
  ∀ addr,
    (σ.findD addr default).storage = (τ.findD addr default).storage ∧
      (σ.findD addr default).tstorage = (τ.findD addr default).tstorage

def accountCodeStateEq (σ τ : AccountMap) : Prop :=
  ∀ addr : AccountAddress,
    (σ.findD addr default).code = (τ.findD addr default).code

def accountStaticStateEq (σ τ : AccountMap) : Prop :=
  ∀ addr : AccountAddress,
    (σ.findD addr default).storage = (τ.findD addr default).storage ∧
      (σ.findD addr default).tstorage = (τ.findD addr default).tstorage ∧
        (σ.findD addr default).code = (τ.findD addr default).code

def stateStaticStateEq (state₁ state₂ : State) : Prop :=
  accountStaticStateEq state₁.accountMap state₂.accountMap

theorem accountStorageState_eq_of_accountStorageStateEq {σ τ : AccountMap}
    (h : accountStorageStateEq σ τ) :
    accountStorageState σ = accountStorageState τ := by
  funext addr
  exact Prod.ext (h addr).1 (h addr).2

theorem accountStaticStateEq_of_storage_code {σ τ : AccountMap}
    (hstorage : accountStorageStateEq σ τ)
    (hcode : accountCodeStateEq σ τ) :
    accountStaticStateEq σ τ := by
  intro addr
  exact ⟨(hstorage addr).1, (hstorage addr).2, hcode addr⟩

@[simp] theorem accountStorageStateEq_refl (σ : AccountMap) :
    accountStorageStateEq σ σ := by
  intro addr
  exact ⟨rfl, rfl⟩

@[simp] theorem accountCodeStateEq_refl (σ : AccountMap) :
    accountCodeStateEq σ σ := by
  intro addr
  rfl

@[simp] theorem accountStaticStateEq_refl (σ : AccountMap) :
    accountStaticStateEq σ σ := by
  intro addr
  exact ⟨rfl, rfl, rfl⟩

theorem accountStorageStateEq_trans {σ τ υ : AccountMap}
    (hστ : accountStorageStateEq σ τ)
    (hτυ : accountStorageStateEq τ υ) :
    accountStorageStateEq σ υ := by
  intro addr
  exact ⟨(hστ addr).1.trans (hτυ addr).1,
    (hστ addr).2.trans (hτυ addr).2⟩

theorem accountCodeStateEq_trans {σ τ υ : AccountMap}
    (hστ : accountCodeStateEq σ τ)
    (hτυ : accountCodeStateEq τ υ) :
    accountCodeStateEq σ υ := by
  intro addr
  exact (hστ addr).trans (hτυ addr)

theorem accountStaticStateEq_trans {σ τ υ : AccountMap}
    (hστ : accountStaticStateEq σ τ)
    (hτυ : accountStaticStateEq τ υ) :
    accountStaticStateEq σ υ := by
  intro addr
  exact ⟨(hστ addr).1.trans (hτυ addr).1,
    (hστ addr).2.1.trans (hτυ addr).2.1,
    (hστ addr).2.2.trans (hτυ addr).2.2⟩

theorem accountStorageStateEq_insert_preserve
    (σ : AccountMap) (addr : AccountAddress) (acc : Account)
    (hstorage : acc.storage = (σ.findD addr default).storage)
    (htstorage : acc.tstorage = (σ.findD addr default).tstorage) :
    accountStorageStateEq σ (σ.insert addr acc) := by
  intro query
  by_cases hcmp : compare query addr = .eq
  · have hfind : (σ.insert addr acc).find? query = some acc := by
      exact Batteries.RBMap.find?_insert_of_eq σ hcmp
    have hcmp' : compare addr query = .eq := by
      have hswap :=
        (Std.OrientedCmp.eq_swap (cmp := compare) (a := query) (b := addr))
      rw [hcmp] at hswap
      simpa using hswap.symm
    have hquery : σ.find? addr = σ.find? query := by
      exact Batteries.RBMap.find?_congr σ hcmp'
    have hstorage' : acc.storage = (σ.findD query default).storage := by
      simpa [Batteries.RBMap.findD, hquery] using hstorage
    have htstorage' : acc.tstorage = (σ.findD query default).tstorage := by
      simpa [Batteries.RBMap.findD, hquery] using htstorage
    simp [Batteries.RBMap.findD, hfind, hstorage', htstorage']
  · have hfind : (σ.insert addr acc).find? query = σ.find? query := by
      exact Batteries.RBMap.find?_insert_of_ne σ hcmp
    simp [Batteries.RBMap.findD, hfind]

theorem accountStorageStateEq_debit_if_present
    (σ : AccountMap) (addr : AccountAddress) (value : UInt256) :
    accountStorageStateEq σ
      (match σ.find? addr with
      | none => σ
      | some acc => σ.insert addr { acc with balance := acc.balance - value }) := by
  cases hfind : σ.find? addr with
  | none =>
      simp
  | some acc =>
      simp
      exact accountStorageStateEq_insert_preserve σ addr { acc with balance := acc.balance - value }
        (by simp [Batteries.RBMap.findD, hfind])
        (by simp [Batteries.RBMap.findD, hfind])

theorem accountCodeStateEq_insert_preserve
    (σ : AccountMap) (addr : AccountAddress) (acc : Account)
    (hcode : acc.code = (σ.findD addr default).code) :
    accountCodeStateEq σ (σ.insert addr acc) := by
  intro query
  by_cases hcmp : compare query addr = .eq
  · have hfind : (σ.insert addr acc).find? query = some acc := by
      exact Batteries.RBMap.find?_insert_of_eq σ hcmp
    have hcmp' : compare addr query = .eq := by
      have hswap :=
        (Std.OrientedCmp.eq_swap (cmp := compare) (a := query) (b := addr))
      rw [hcmp] at hswap
      simpa using hswap.symm
    have hquery : σ.find? addr = σ.find? query := by
      exact Batteries.RBMap.find?_congr σ hcmp'
    have hcode' : acc.code = (σ.findD query default).code := by
      simpa [Batteries.RBMap.findD, hquery] using hcode
    simp [Batteries.RBMap.findD, hfind, hcode']
  · have hfind : (σ.insert addr acc).find? query = σ.find? query := by
      exact Batteries.RBMap.find?_insert_of_ne σ hcmp
    simp [Batteries.RBMap.findD, hfind]

theorem accountCodeStateEq_debit_if_present
    (σ : AccountMap) (addr : AccountAddress) (value : UInt256) :
    accountCodeStateEq σ
      (match σ.find? addr with
      | none => σ
      | some acc => σ.insert addr { acc with balance := acc.balance - value }) := by
  cases hfind : σ.find? addr with
  | none =>
      simp
  | some acc =>
      simp
      exact accountCodeStateEq_insert_preserve σ addr { acc with balance := acc.balance - value }
        (by simp [Batteries.RBMap.findD, hfind])

theorem sendEth_accountStorageStateEq
    (r s : AccountAddress) (v : UInt256) (z : Bool) (σ : AccountMap) :
    accountStorageStateEq σ (sendEth r s v z σ) := by
  unfold sendEth
  by_cases hz : z
  · simp [hz]
    let σ₁ : AccountMap :=
      match σ.find? r with
      | none =>
          if (v != UInt256.ofNat 0) = true then
            σ.insert r
              (let __src := (default : Account)
              { nonce := __src.nonce, balance := v, storage := __src.storage, code := __src.code,
                tstorage := __src.tstorage })
          else σ
      | some acc =>
          σ.insert r
            { nonce := acc.nonce, balance := acc.balance + v, storage := acc.storage, code := acc.code,
              tstorage := acc.tstorage }
    have hσ₁ : accountStorageStateEq σ σ₁ := by
      dsimp [σ₁]
      cases hr : σ.find? r with
      | none =>
          by_cases hv : (v != UInt256.ofNat 0) = true
          · simp [hv]
            apply accountStorageStateEq_insert_preserve
            · simp [Batteries.RBMap.findD, hr]
            · simp [Batteries.RBMap.findD, hr]
          · simp [hv]
      | some acc =>
          simp
          apply accountStorageStateEq_insert_preserve
          · simp [Batteries.RBMap.findD, hr]
          · simp [Batteries.RBMap.findD, hr]
    simpa [σ₁] using accountStorageStateEq_trans hσ₁
      (accountStorageStateEq_debit_if_present σ₁ s v)
  · simp [hz]

theorem sendEth_accountCodeStateEq
    (r s : AccountAddress) (v : UInt256) (z : Bool) (σ : AccountMap) :
    accountCodeStateEq σ (sendEth r s v z σ) := by
  unfold sendEth
  by_cases hz : z
  · simp [hz]
    let σ₁ : AccountMap :=
      match σ.find? r with
      | none =>
          if (v != UInt256.ofNat 0) = true then
            σ.insert r
              (let __src := (default : Account)
              { nonce := __src.nonce, balance := v, storage := __src.storage, code := __src.code,
                tstorage := __src.tstorage })
          else σ
      | some acc =>
          σ.insert r
            { nonce := acc.nonce, balance := acc.balance + v, storage := acc.storage, code := acc.code,
              tstorage := acc.tstorage }
    have hσ₁ : accountCodeStateEq σ σ₁ := by
      dsimp [σ₁]
      cases hr : σ.find? r with
      | none =>
          by_cases hv : (v != UInt256.ofNat 0) = true
          · simp [hv]
            apply accountCodeStateEq_insert_preserve
            simp [Batteries.RBMap.findD, hr]
          · simp [hv]
      | some acc =>
          simp
          apply accountCodeStateEq_insert_preserve
          simp [Batteries.RBMap.findD, hr]
    simpa [σ₁] using accountCodeStateEq_trans hσ₁
      (accountCodeStateEq_debit_if_present σ₁ s v)
  · simp [hz]

theorem sendEth_accountStaticStateEq
    (r s : AccountAddress) (v : UInt256) (z : Bool) (σ : AccountMap) :
    accountStaticStateEq σ (sendEth r s v z σ) := by
  exact accountStaticStateEq_of_storage_code
    (sendEth_accountStorageStateEq r s v z σ)
    (sendEth_accountCodeStateEq r s v z σ)

theorem accountStorageStateEq_final_of_empty_or_self {σ τ ρ : AccountMap}
    (hστ : accountStorageStateEq σ τ) (hρ : ρ = ∅ ∨ ρ = τ) :
    accountStorageStateEq σ (if ρ == ∅ then σ else ρ) := by
  rcases hρ with rfl | rfl
  · simp [rbMap_empty_beq_empty]
  · by_cases hempty : (ρ == ∅) = true
    · simp [hempty]
    · simp [hempty, hστ]

theorem accountCodeStateEq_final_of_empty_or_self {σ τ ρ : AccountMap}
    (hστ : accountCodeStateEq σ τ) (hρ : ρ = ∅ ∨ ρ = τ) :
    accountCodeStateEq σ (if ρ == ∅ then σ else ρ) := by
  rcases hρ with rfl | rfl
  · simp [rbMap_empty_beq_empty]
  · by_cases hempty : (ρ == ∅) = true
    · simp [hempty]
    · simp [hempty, hστ]

theorem precompile_ECREC_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_ECREC σ g A I).1 = ∅ ∨ (Ξ_ECREC σ g A I).1 = σ := by
  simp only [Ξ_ECREC]
  split <;> simp

theorem precompile_SHA256_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_SHA256 σ g A I).1 = ∅ ∨ (Ξ_SHA256 σ g A I).1 = σ := by
  simp only [Ξ_SHA256]
  split <;> simp

theorem precompile_RIP160_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_RIP160 σ g A I).1 = ∅ ∨ (Ξ_RIP160 σ g A I).1 = σ := by
  simp only [Ξ_RIP160]
  split <;> simp

theorem precompile_ID_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_ID σ g A I).1 = ∅ ∨ (Ξ_ID σ g A I).1 = σ := by
  simp only [Ξ_ID]
  split <;> simp

theorem precompile_EXPMOD_accountMap_empty_or_self
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

theorem precompile_BN_ADD_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BN_ADD σ g A I).1 = ∅ ∨ (Ξ_BN_ADD σ g A I).1 = σ := by
  simp only [Ξ_BN_ADD]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem precompile_BN_MUL_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BN_MUL σ g A I).1 = ∅ ∨ (Ξ_BN_MUL σ g A I).1 = σ := by
  simp only [Ξ_BN_MUL]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem precompile_SNARKV_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_SNARKV σ g A I).1 = ∅ ∨ (Ξ_SNARKV σ g A I).1 = σ := by
  simp only [Ξ_SNARKV]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem precompile_BLAKE2_F_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BLAKE2_F σ g A I).1 = ∅ ∨ (Ξ_BLAKE2_F σ g A I).1 = σ := by
  simp only [Ξ_BLAKE2_F]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem precompile_PointEval_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_PointEval σ g A I).1 = ∅ ∨ (Ξ_PointEval σ g A I).1 = σ := by
  simp only [Ξ_PointEval]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem precompiled_result_accountMap_empty_or_self
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

theorem precompiled_Theta_accountMap_eq
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

theorem accountStorageStateEq_of_precompiled_Theta
    {blobVersionedHashes : List ByteArray}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {A A' : Substate}
    {s o r pc : AccountAddress} {g g' p v v' : UInt256}
    {d out : ByteArray} {e : Fin 1025} {H : BlockHeader} {w z : Bool}
    (hTheta : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Precompiled pc) g p v v' d e H w =
      (createdAccounts', σ', g', A', z, out)) :
    accountStorageStateEq σ σ' := by
  let σ₁ := sendEth r s v true σ
  let I : ExecutionEnv :=
    { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d,
      code := default, gasPrice := p.toNat, header := H, depth := e, perm := w,
      blobVersionedHashes := blobVersionedHashes }
  have hproj :
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Precompiled pc) g p v v' d e H w).2.1 = σ' := by
    simpa using congrArg (fun x => x.2.1) hTheta
  rw [← hproj]
  rw [precompiled_Theta_accountMap_eq blobVersionedHashes createdAccounts
    genesisBlockHeader blocks σ σ₀ A s o r pc g p v v' d e H w]
  exact accountStorageStateEq_final_of_empty_or_self
    (sendEth_accountStorageStateEq r s v true σ)
    (by simpa [σ₁, I] using precompiled_result_accountMap_empty_or_self pc σ₁ g A I)

theorem accountCodeStateEq_of_precompiled_Theta
    {blobVersionedHashes : List ByteArray}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {A A' : Substate}
    {s o r pc : AccountAddress} {g g' p v v' : UInt256}
    {d out : ByteArray} {e : Fin 1025} {H : BlockHeader} {w z : Bool}
    (hTheta : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Precompiled pc) g p v v' d e H w =
      (createdAccounts', σ', g', A', z, out)) :
    accountCodeStateEq σ σ' := by
  let σ₁ := sendEth r s v true σ
  let I : ExecutionEnv :=
    { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d,
      code := default, gasPrice := p.toNat, header := H, depth := e, perm := w,
      blobVersionedHashes := blobVersionedHashes }
  have hproj :
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Precompiled pc) g p v v' d e H w).2.1 = σ' := by
    simpa using congrArg (fun x => x.2.1) hTheta
  rw [← hproj]
  rw [precompiled_Theta_accountMap_eq blobVersionedHashes createdAccounts
    genesisBlockHeader blocks σ σ₀ A s o r pc g p v v' d e H w]
  exact accountCodeStateEq_final_of_empty_or_self
    (sendEth_accountCodeStateEq r s v true σ)
    (by simpa [σ₁, I] using precompiled_result_accountMap_empty_or_self pc σ₁ g A I)

theorem accountStaticStateEq_of_precompiled_Theta
    {blobVersionedHashes : List ByteArray}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {A A' : Substate}
    {s o r pc : AccountAddress} {g g' p v v' : UInt256}
    {d out : ByteArray} {e : Fin 1025} {H : BlockHeader} {w z : Bool}
    (hTheta : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Precompiled pc) g p v v' d e H w =
      (createdAccounts', σ', g', A', z, out)) :
    accountStaticStateEq σ σ' := by
  exact accountStaticStateEq_of_storage_code
    (accountStorageStateEq_of_precompiled_Theta hTheta)
    (accountCodeStateEq_of_precompiled_Theta hTheta)

def thetaXiResult
    (createdAccounts : Batteries.RBSet AccountAddress compare) (A : Substate)
    (xi : Except EVM.ExecutionException
      (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))) :
    Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
  match xi with
  | .error _ => (createdAccounts, ∅, ⟨0⟩, A, .empty)
  | .ok (.revert g' o) => (createdAccounts, ∅, g', A, o)
  | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
      (createdAccounts', σStarStar, gStarStar, AStarStar, returnedData)

def thetaXiAccountMap
    (σ : AccountMap) (createdAccounts : Batteries.RBSet AccountAddress compare)
    (A : Substate)
    (xi : Except EVM.ExecutionException
      (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))) :
    AccountMap :=
  let result := thetaXiResult createdAccounts A xi
  if result.2.1 == (∅ : AccountMap) then σ else result.2.1

def stateStorageStateEq (state₁ state₂ : State) : Prop :=
  accountStorageStateEq state₁.accountMap state₂.accountMap

@[simp] theorem stateStorageStateEq_refl (state : State) :
    stateStorageStateEq state state := by
  simp [stateStorageStateEq]

theorem stateStorageStateEq_trans {state₁ state₂ state₃ : State}
    (h₁₂ : stateStorageStateEq state₁ state₂)
    (h₂₃ : stateStorageStateEq state₂ state₃) :
    stateStorageStateEq state₁ state₃ := by
  exact accountStorageStateEq_trans h₁₂ h₂₃

theorem stateStorageStateEq_with_executionEnv_depth {state₁ state₂ : State}
    (h : stateStorageStateEq state₁ state₂) (depth : Fin 1025) :
    stateStorageStateEq state₁ ({state₂ with executionEnv.depth := depth} : State) := by
  simpa [stateStorageStateEq] using h

theorem stateStorageStateEq_with_executionEnv {state₁ state₂ : State}
    (h : stateStorageStateEq state₁ state₂) (executionEnv : ExecutionEnv) :
    stateStorageStateEq state₁ ({state₂ with executionEnv := executionEnv} : State) := by
  simpa [stateStorageStateEq] using h

theorem stateStorageStateEq_of_accountMap_eq {state state' : State}
    (h : state'.accountMap = state.accountMap) :
    stateStorageStateEq state state' := by
  simp [stateStorageStateEq, h]

def stateCodeStateEq (state₁ state₂ : State) : Prop :=
  accountCodeStateEq state₁.accountMap state₂.accountMap

@[simp] theorem stateStaticStateEq_refl (state : State) :
    stateStaticStateEq state state := by
  simp [stateStaticStateEq]

theorem stateStaticStateEq_trans {state₁ state₂ state₃ : State}
    (h₁₂ : stateStaticStateEq state₁ state₂)
    (h₂₃ : stateStaticStateEq state₂ state₃) :
    stateStaticStateEq state₁ state₃ := by
  exact accountStaticStateEq_trans h₁₂ h₂₃

theorem stateStaticStateEq_with_executionEnv_depth {state₁ state₂ : State}
    (h : stateStaticStateEq state₁ state₂) (depth : Fin 1025) :
    stateStaticStateEq state₁ ({state₂ with executionEnv.depth := depth} : State) := by
  simpa [stateStaticStateEq] using h

theorem stateStaticStateEq_with_executionEnv {state₁ state₂ : State}
    (h : stateStaticStateEq state₁ state₂) (executionEnv : ExecutionEnv) :
    stateStaticStateEq state₁ ({state₂ with executionEnv := executionEnv} : State) := by
  simpa [stateStaticStateEq] using h

theorem stateStaticStateEq_of_accountMap_eq {state state' : State}
    (h : state'.accountMap = state.accountMap) :
    stateStaticStateEq state state' := by
  simp [stateStaticStateEq, h]

theorem Z_static_stateStaticStateEq
    {validJumps : Array UInt256} {op : Operation} {state stateZ : State}
    {cost : Nat} :
    Z validJumps op state = .ok (stateZ, cost) →
    stateStaticStateEq state stateZ := by
  intro hZ
  rcases Z_ok_eq_charged_cost hZ with ⟨hstate, _hcost⟩
  subst stateZ
  simp [stateStaticStateEq]

theorem Z_static_stateStorageStateEq
    {validJumps : Array UInt256} {op : Operation} {state stateZ : State}
    {cost : Nat} :
    Z validJumps op state = .ok (stateZ, cost) →
    stateStorageStateEq state stateZ := by
  intro hZ
  rcases Z_ok_eq_charged_cost hZ with ⟨hstate, _hcost⟩
  subst stateZ
  simp [stateStorageStateEq]

theorem Z_static_forbidden_mem_false
    {validJumps : Array UInt256} {op : Operation} {state stateZ : State}
    {cost : Nat}
    (hperm : state.executionEnv.perm = false)
    (hforbidden :
      op ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT,
        .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE])
    (hZ : Z validJumps op state = .ok (stateZ, cost)) :
    False := by
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
  let state₁ : State :=
    { state with machineState.gasAvailable :=
        state.machineState.gasAvailable.subNat (memoryExpansionCost state op) }
  by_cases hcost₂ : state₁.machineState.gasAvailable.toNat < C' state₁ op
  · rw [if_pos (by simpa [state₁] using hcost₂)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hcost₂)] at hZ
  by_cases hjump :
      op = Operation.JUMP ∧ Z.notIn state₁.machineState.stack[0]? validJumps = true
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
  have hstatic :
      (¬ state₁.executionEnv.perm) ∧
        (op ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT,
          .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
          (op = .CALL ∧ state₁.machineState.stack[2]? ≠ some ⟨0⟩)) := by
    constructor
    · simp [state₁, hperm]
    · exact Or.inl hforbidden
  rw [if_pos (by simpa [state₁] using hstatic)] at hZ
  contradiction

lemma static_execUnOp_accountMap_eq
    {f : Primop.Unary} {state state' : State}
    (h : execUnOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold execUnOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

lemma static_execBinOp_accountMap_eq
    {f : Primop.Binary} {state state' : State}
    (h : execBinOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold execBinOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

lemma static_execTriOp_accountMap_eq
    {f : Primop.Ternary} {state state' : State}
    (h : execTriOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold execTriOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

lemma static_machineStateOp_accountMap_eq
    {f : MachineState → UInt256} {state state' : State}
    (h : machineStateOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold machineStateOp at h
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

lemma static_executionEnvOp_accountMap_eq
    {f : ExecutionEnv → UInt256} {state state' : State}
    (h : executionEnvOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold executionEnvOp at h
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

lemma static_unaryExecutionEnvOp_accountMap_eq
    {f : ExecutionEnv → UInt256 → UInt256} {state state' : State}
    (h : unaryExecutionEnvOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold unaryExecutionEnvOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

lemma static_unaryStateOp_sameState_accountMap_eq
    {f : State → UInt256 → UInt256} {state state' : State}
    (h : unaryStateOp (fun s v => (s, f s v)) state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold unaryStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

lemma static_unaryStateOp_accountMap_eq
    {f : State → UInt256 → State × UInt256} {state state' : State}
    (hf : ∀ s v, (f s v).1.accountMap = s.accountMap)
    (h : unaryStateOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold unaryStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hf]

lemma static_stateOp_accountMap_eq
    {f : State → UInt256} {state state' : State}
    (h : stateOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold stateOp at h
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

lemma static_binaryMachineStateOp_accountMap_eq
    {f : MachineState → UInt256 → UInt256 → MachineState} {state state' : State}
    (h : binaryMachineStateOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold binaryMachineStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

lemma static_binaryMachineStateOp'_accountMap_eq
    {f : MachineState → UInt256 → UInt256 → UInt256 × MachineState} {state state' : State}
    (h : binaryMachineStateOp' f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold binaryMachineStateOp' at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

lemma static_ternaryMachineStateOp_accountMap_eq
    {f : MachineState → UInt256 → UInt256 → UInt256 → MachineState} {state state' : State}
    (h : ternaryMachineStateOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold ternaryMachineStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]

lemma static_ternaryCopyOp_accountMap_eq
    {f : State → UInt256 → UInt256 → UInt256 → State} {state state' : State}
    (hcopy : ∀ s a b c, (f s a b c).accountMap = s.accountMap)
    (h : ternaryCopyOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold ternaryCopyOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hcopy]

lemma static_quaternaryCopyOp_accountMap_eq
    {f : State → UInt256 → UInt256 → UInt256 → UInt256 → State} {state state' : State}
    (hcopy : ∀ s a b c d, (f s a b c d).accountMap = s.accountMap)
    (h : quaternaryCopyOp f state = .ok state') :
    state'.accountMap = state.accountMap := by
  unfold quaternaryCopyOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hcopy]

lemma static_calldatacopy_accountMap_eq
    (state : State) (mstart datastart size : UInt256) :
    (calldatacopy state mstart datastart size).accountMap = state.accountMap := by
  simp [calldatacopy]

lemma static_codeCopy_accountMap_eq
    (state : State) (mstart cstart size : UInt256) :
    (codeCopy state mstart cstart size).accountMap = state.accountMap := by
  simp [codeCopy]

lemma static_extCodeCopy'_accountMap_eq
    (state : State) (a mstart cstart size : UInt256) :
    (extCodeCopy' state a mstart cstart size).accountMap = state.accountMap := by
  simp [extCodeCopy', Ethereum.State.lookupAccount]

lemma static_dup_accountMap_eq
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

lemma static_swap_accountMap_eq
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

lemma static_depth_succ_measure {e : Fin 1025} {n : Nat}
    (hdepth : 1024 - e.val = n + 1) (hlt : e < 1024) :
    1024 - (e + 1).val = n := by
  have hltVal : e.val < 1024 := by simpa using hlt
  have hval : (e + 1).val = e.val + 1 := by
    rw [Fin.val_add_eq_of_add_lt]
    simp
    omega
  omega

lemma static_step_stoparith_accountMap_eq
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
      simpa using static_execBinOp_accountMap_eq h
  | MUL =>
      simp [step] at h
      simpa using static_execBinOp_accountMap_eq h
  | SUB =>
      simp [step] at h
      simpa using static_execBinOp_accountMap_eq h
  | DIV =>
      simp [step] at h
      simpa using static_execBinOp_accountMap_eq h
  | SDIV =>
      simp [step] at h
      simpa using static_execBinOp_accountMap_eq h
  | MOD =>
      simp [step] at h
      simpa using static_execBinOp_accountMap_eq h
  | SMOD =>
      simp [step] at h
      simpa using static_execBinOp_accountMap_eq h
  | ADDMOD =>
      simp [step] at h
      simpa using static_execTriOp_accountMap_eq h
  | MULMOD =>
      simp [step] at h
      simpa using static_execTriOp_accountMap_eq h
  | EXP =>
      simp [step] at h
      simpa using static_execBinOp_accountMap_eq h
  | SIGNEXTEND =>
      simp [step] at h
      simpa using static_execBinOp_accountMap_eq h

lemma static_step_compbit_accountMap_eq
    {op : Operation.CBLOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.CompBit op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op <;> simp [step] at h
  · simpa using static_execBinOp_accountMap_eq h
  · simpa using static_execBinOp_accountMap_eq h
  · simpa using static_execBinOp_accountMap_eq h
  · simpa using static_execBinOp_accountMap_eq h
  · simpa using static_execBinOp_accountMap_eq h
  · simpa using static_execUnOp_accountMap_eq h
  · simpa using static_execBinOp_accountMap_eq h
  · simpa using static_execBinOp_accountMap_eq h
  · simpa using static_execBinOp_accountMap_eq h
  · simpa using static_execUnOp_accountMap_eq h
  · simpa using static_execBinOp_accountMap_eq h
  · simpa using static_execBinOp_accountMap_eq h
  · simpa using static_execBinOp_accountMap_eq h
  · simpa using static_execBinOp_accountMap_eq h

lemma static_step_keccak_accountMap_eq
    {op : Operation.KOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.Keccak op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op
  simp [step] at h
  simpa using static_binaryMachineStateOp'_accountMap_eq h

lemma static_step_env_accountMap_eq
    {op : Operation.EOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.Env op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op <;> simp [step] at h
  · simpa using static_executionEnvOp_accountMap_eq h
  · have hm := static_unaryStateOp_accountMap_eq
      (f := Ethereum.State.balance)
      (by intro s v; simp [Ethereum.State.balance, Ethereum.State.addAccessedAccount])
      h
    simpa using hm
  · simpa using static_executionEnvOp_accountMap_eq h
  · simpa using static_executionEnvOp_accountMap_eq h
  · simpa using static_executionEnvOp_accountMap_eq h
  · simpa using static_unaryStateOp_sameState_accountMap_eq h
  · simpa using static_executionEnvOp_accountMap_eq h
  · have hm := static_ternaryCopyOp_accountMap_eq static_calldatacopy_accountMap_eq h
    simpa using hm
  · simpa using static_executionEnvOp_accountMap_eq h
  · simpa using static_executionEnvOp_accountMap_eq h
  · have hm := static_ternaryCopyOp_accountMap_eq static_codeCopy_accountMap_eq h
    simpa using hm
  · have hm := static_unaryStateOp_accountMap_eq
      (f := Ethereum.State.extCodeSize)
      (by intro s v; simp [Ethereum.State.extCodeSize, Ethereum.State.addAccessedAccount])
      h
    simpa using hm
  · have hm := static_quaternaryCopyOp_accountMap_eq static_extCodeCopy'_accountMap_eq h
    simpa using hm
  · simpa using static_machineStateOp_accountMap_eq h
  · split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
  · have hm := static_unaryStateOp_accountMap_eq
      (f := Ethereum.State.extCodeHash)
      (by
        intro s v
        simp [Ethereum.State.extCodeHash, Ethereum.State.addAccessedAccount,
          Ethereum.State.lookupAccount]
        split <;> simp)
      h
    simpa using hm

lemma static_step_push_accountMap_eq
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

lemma static_step_dup_accountMap_eq
    {op : Operation.DOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.Dup op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op <;> simp [step] at h <;>
    first | simpa using static_dup_accountMap_eq h

lemma static_step_exchange_accountMap_eq
    {op : Operation.ExOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.Exchange op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op <;> simp [step] at h <;>
    first | simpa using static_swap_accountMap_eq h

lemma static_step_block_accountMap_eq
    {op : Operation.BOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State}
    (h : step gasCost (.Block op, arg) state = .ok state') :
    state'.accountMap = state.accountMap := by
  cases op <;> simp [step] at h
  · simpa using static_unaryStateOp_sameState_accountMap_eq h
  · simpa using static_stateOp_accountMap_eq h
  · simpa using static_stateOp_accountMap_eq h
  · simpa using static_stateOp_accountMap_eq h
  · simpa using static_executionEnvOp_accountMap_eq h
  · simpa using static_stateOp_accountMap_eq h
  · simpa using static_stateOp_accountMap_eq h
  · simpa using static_stateOp_accountMap_eq h
  · simpa using static_executionEnvOp_accountMap_eq h
  · simpa using static_unaryExecutionEnvOp_accountMap_eq h
  · simpa using static_executionEnvOp_accountMap_eq h

lemma static_step_log_accountMap_eq
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

lemma static_step_stackmemflow_static_stateStorageStateEq_of_Z
    {validJumps : Array UInt256} {op : Operation.SMSFOp} {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state stateZ stepped : State}
    (hperm : state.executionEnv.perm = false)
    (hZ : Z validJumps (.StackMemFlow op) state = .ok (stateZ, gasCost))
    (hstep :
      step gasCost (.StackMemFlow op, arg)
        {stateZ with executionEnv.depth := state.executionEnv.depth} = .ok stepped) :
    stateStorageStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  cases op <;> simp [step] at hstep
  · split at hstep <;> try contradiction
    injection hstep with hstate
    rw [← hstate]
    exact stateStorageStateEq_refl _
  · split at hstep <;> try contradiction
    injection hstep with hstate
    rw [← hstate]
    exact stateStorageStateEq_refl _
  · have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateStorageStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · have hm := static_unaryStateOp_accountMap_eq
      (f := Ethereum.State.sload)
      (by
        intro s v
        simp [Ethereum.State.sload, Ethereum.State.addAccessedStorageKey,
          Ethereum.State.lookupAccount])
      hstep
    exact stateStorageStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateStorageStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · split at hstep <;> try contradiction
    injection hstep with hstate
    rw [← hstate]
    exact stateStorageStateEq_refl _
  · split at hstep <;> try contradiction
    injection hstep with hstate
    rw [← hstate]
    exact stateStorageStateEq_refl _
  · rw [← hstep]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, stateStorageStateEq]
  · have hm := static_machineStateOp_accountMap_eq hstep
    exact stateStorageStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · have hm := static_machineStateOp_accountMap_eq hstep
    exact stateStorageStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · rw [← hstep]
    simp [Ethereum.State.incrPC, stateStorageStateEq]
  · have hm := static_unaryStateOp_accountMap_eq
      (f := Ethereum.State.tload)
      (by intro s v; simp [Ethereum.State.tload])
      hstep
    exact stateStorageStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · have hm := static_ternaryMachineStateOp_accountMap_eq hstep
    exact stateStorageStateEq_of_accountMap_eq (by simpa [stepState] using hm)

lemma call_static_stateStorageStateEq_at_depth
    {n gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State}
    (hdepth : 1024 - evmState.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStorageStateEq σ σ')
    (hperm : permission = false)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    stateStorageStateEq evmState state' := by
  unfold call at h
  simp at h
  split at h
  · rename_i hcall
    rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateStorageStateEq]
    let θ :=
      Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
        evmState.blocks evmState.accountMap evmState.σ₀
        (evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header false
    have hθ :
        Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
          evmState.blocks evmState.accountMap evmState.σ₀
          (evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate
          (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
          (AccountAddress.ofUInt256 recipient)
          (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
          (UInt256.ofNat
            (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
              value gas evmState.accountMap evmState.machineState evmState.substate))
          (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
          (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evmState.executionEnv.depth + 1) evmState.executionEnv.header false =
        (θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1, θ.2.2.2.2.1, θ.2.2.2.2.2) := by
      rfl
    have hpres : accountStorageStateEq evmState.accountMap θ.2.1 :=
      ihTheta blobVersionedHashes evmState.genesisBlockHeader evmState.blocks
        evmState.createdAccounts (evmState.executionEnv.depth + 1)
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
        evmState.executionEnv.header
        θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2
        (static_depth_succ_measure hdepth hcall.2)
        hθ
    simpa [θ, hperm] using hpres
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateStorageStateEq]

lemma call_static_stateStorageStateEq_max_depth
    {gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State}
    (hdepth : evmState.executionEnv.depth = 1024)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    stateStorageStateEq evmState state' := by
  unfold call at h
  simp at h
  split at h
  · rename_i hcall
    exact False.elim (by
      have hlt := hcall.2
      omega)
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateStorageStateEq]

lemma step_system_call_static_stateStorageStateEq_of_Z_at_depth
    {n : Nat} {validJumps : Array UInt256} {op : Operation.SOp}
    {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat}
    (hcallkind : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL)
    (hdepth : 1024 - state.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStorageStateEq σ σ')
    (hperm : state.executionEnv.perm = false)
    (hZ : Z validJumps (.System op) state = .ok (stateZ, cost))
    (hstep :
      step cost (.System op, arg)
        {stateZ with executionEnv.depth := state.executionEnv.depth} = .ok stepped) :
    stateStorageStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  have hZEnv : stateZ.executionEnv = state.executionEnv :=
    Z_executionEnv_eq (validJumps := validJumps) (state := state) (op := .System op) hZ
  cases op
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStorageStateEq_at_depth
      (n := n)
      (hdepth := by simp [hdepth])
      ihTheta
      (by simpa [stepState, hZEnv] using hperm)
      hcall
    simpa [stepState, stateStorageStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStorageStateEq_at_depth
      (n := n)
      (hdepth := by simp [hdepth])
      ihTheta
      (by simpa [stepState, hZEnv] using hperm)
      hcall
    simpa [stepState, stateStorageStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStorageStateEq_at_depth
      (n := n)
      (hdepth := by simp [hdepth])
      ihTheta
      (by simpa [stepState, hZEnv] using hperm)
      hcall
    simpa [stepState, stateStorageStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStorageStateEq_at_depth
      (n := n)
      (hdepth := by simp [hdepth])
      ihTheta
      rfl
      hcall
    simpa [stepState, stateStorageStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse

lemma step_system_call_static_stateStorageStateEq_of_Z_max_depth
    {validJumps : Array UInt256} {op : Operation.SOp} {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat}
    (hcallkind : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL)
    (hdepth : state.executionEnv.depth = 1024)
    (hZ : Z validJumps (.System op) state = .ok (stateZ, cost))
    (hstep :
      step cost (.System op, arg)
        {stateZ with executionEnv.depth := state.executionEnv.depth} = .ok stepped) :
    stateStorageStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  cases op
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStorageStateEq_max_depth
      (hdepth := by simp [hdepth])
      hcall
    simpa [stepState, stateStorageStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStorageStateEq_max_depth
      (hdepth := by simp [hdepth])
      hcall
    simpa [stepState, stateStorageStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStorageStateEq_max_depth
      (hdepth := by simp [hdepth])
      hcall
    simpa [stepState, stateStorageStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStorageStateEq_max_depth
      (hdepth := by simp [hdepth])
      hcall
    simpa [stepState, stateStorageStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse

theorem step_system_static_stateStorageStateEq_of_Z_max_depth
    {validJumps : Array UInt256} {op : Operation.SOp} {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat} :
    state.executionEnv.perm = false →
    state.executionEnv.depth = 1024 →
    Z validJumps (.System op) state = .ok (stateZ, cost) →
    step cost (.System op, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} =
      .ok stepped →
    stateStorageStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  intro hperm hdepth hZ hstep
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  cases op
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · exact step_system_call_static_stateStorageStateEq_of_Z_max_depth (by simp) hdepth hZ hstep
  · exact step_system_call_static_stateStorageStateEq_of_Z_max_depth (by simp) hdepth hZ hstep
  · simp [step] at hstep
    have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateStorageStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · exact step_system_call_static_stateStorageStateEq_of_Z_max_depth (by simp) hdepth hZ hstep
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · exact step_system_call_static_stateStorageStateEq_of_Z_max_depth (by simp) hdepth hZ hstep
  · simp [step] at hstep
    have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateStorageStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · simp [step] at hstep
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)

theorem step_system_static_stateStorageStateEq_of_Z_succ_depth
    {n : Nat} {validJumps : Array UInt256} {op : Operation.SOp}
    {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat} :
    state.executionEnv.perm = false →
    1024 - state.executionEnv.depth.val = n + 1 →
    (∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStorageStateEq σ σ') →
    Z validJumps (.System op) state = .ok (stateZ, cost) →
    step cost (.System op, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} =
      .ok stepped →
    stateStorageStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  intro hperm hdepth ihTheta hZ hstep
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  cases op
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · exact step_system_call_static_stateStorageStateEq_of_Z_at_depth (by simp)
      hdepth ihTheta hperm hZ hstep
  · exact step_system_call_static_stateStorageStateEq_of_Z_at_depth (by simp)
      hdepth ihTheta hperm hZ hstep
  · simp [step] at hstep
    have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateStorageStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · exact step_system_call_static_stateStorageStateEq_of_Z_at_depth (by simp)
      hdepth ihTheta hperm hZ hstep
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · exact step_system_call_static_stateStorageStateEq_of_Z_at_depth (by simp)
      hdepth ihTheta hperm hZ hstep
  · simp [step] at hstep
    have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateStorageStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · simp [step] at hstep
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)

theorem step_static_stateStorageStateEq_of_Z_max_depth
    {validJumps : Array UInt256} {op : Operation} {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat} :
    state.executionEnv.perm = false →
    state.executionEnv.depth = 1024 →
    Z validJumps op state = .ok (stateZ, cost) →
    step cost (op, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} =
      .ok stepped →
    stateStorageStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  intro hperm hdepth hZ hstep
  rcases op with op | op | op | op | op | op | op | op | op | op
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_stoparith_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_compbit_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_keccak_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_env_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_block_accountMap_eq hstep)
  · exact static_step_stackmemflow_static_stateStorageStateEq_of_Z hperm hZ hstep
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_push_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_dup_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_exchange_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_log_accountMap_eq hstep)
  · exact step_system_static_stateStorageStateEq_of_Z_max_depth hperm hdepth hZ hstep

theorem step_static_stateStorageStateEq_of_Z_succ_depth
    {n : Nat} {validJumps : Array UInt256} {op : Operation}
    {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat} :
    state.executionEnv.perm = false →
    1024 - state.executionEnv.depth.val = n + 1 →
    (∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStorageStateEq σ σ') →
    Z validJumps op state = .ok (stateZ, cost) →
    step cost (op, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} =
      .ok stepped →
    stateStorageStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  intro hperm hdepth ihTheta hZ hstep
  rcases op with op | op | op | op | op | op | op | op | op | op
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_stoparith_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_compbit_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_keccak_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_env_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_block_accountMap_eq hstep)
  · exact static_step_stackmemflow_static_stateStorageStateEq_of_Z hperm hZ hstep
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_push_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_dup_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_exchange_accountMap_eq hstep)
  · exact stateStorageStateEq_of_accountMap_eq
      (static_step_log_accountMap_eq hstep)
  · exact step_system_static_stateStorageStateEq_of_Z_succ_depth
      hperm hdepth ihTheta hZ hstep

theorem Xstep_static_stateStorageStateEq_max_depth
    {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)} :
    state.executionEnv.perm = false →
    state.executionEnv.depth = 1024 →
    Xstep validJumps state = .ok (state', ret) →
    stateStorageStateEq state state' := by
  intro hperm hdepth hstep
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  unfold Xstep at hstep
  simp only [bind, Except.bind] at hstep
  split at hstep
  · simp at hstep
  · rename_i stateZ cost hZ
    have hZ' : Z validJumps op state = .ok (stateZ, cost) := by
      simpa [← hinstr] using hZ
    cases hstep' :
        step cost (op, arg)
          {stateZ with executionEnv.depth := state.executionEnv.depth} with
    | error e =>
        simp [← hinstr, hstep'] at hstep
    | ok stepped =>
        have hstep'' :
            step cost (op, arg)
              {stateZ with executionEnv.depth := state.executionEnv.depth} =
            .ok stepped := hstep'
        have hZpres : stateStorageStateEq state stateZ :=
          Z_static_stateStorageStateEq hZ'
        have hstepPres :
            stateStorageStateEq
              ({stateZ with executionEnv.depth := state.executionEnv.depth} : State)
              stepped :=
          step_static_stateStorageStateEq_of_Z_max_depth hperm hdepth hZ' hstep''
        have hprefix : stateStorageStateEq state stepped :=
          stateStorageStateEq_trans
            (stateStorageStateEq_with_executionEnv_depth hZpres state.executionEnv.depth)
            hstepPres
        simp [← hinstr, hstep'] at hstep
        split at hstep
        · injection hstep with hstate
          have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
            congrArg Prod.fst hstate
          subst state'
          exact stateStorageStateEq_with_executionEnv hprefix state.executionEnv
        · split at hstep
          · injection hstep with hstate
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hstate
            subst state'
            exact stateStorageStateEq_with_executionEnv hprefix state.executionEnv
          · injection hstep with hstate
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hstate
            subst state'
            exact stateStorageStateEq_with_executionEnv hprefix state.executionEnv

theorem Xstep_static_stateStorageStateEq_succ_depth
    {n : Nat} {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)} :
    state.executionEnv.perm = false →
    1024 - state.executionEnv.depth.val = n + 1 →
    (∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStorageStateEq σ σ') →
    Xstep validJumps state = .ok (state', ret) →
    stateStorageStateEq state state' := by
  intro hperm hdepth ihTheta hstep
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  unfold Xstep at hstep
  simp only [bind, Except.bind] at hstep
  split at hstep
  · simp at hstep
  · rename_i stateZ cost hZ
    have hZ' : Z validJumps op state = .ok (stateZ, cost) := by
      simpa [← hinstr] using hZ
    cases hstep' :
        step cost (op, arg)
          {stateZ with executionEnv.depth := state.executionEnv.depth} with
    | error e =>
        simp [← hinstr, hstep'] at hstep
    | ok stepped =>
        have hstep'' :
            step cost (op, arg)
              {stateZ with executionEnv.depth := state.executionEnv.depth} =
            .ok stepped := hstep'
        have hZpres : stateStorageStateEq state stateZ :=
          Z_static_stateStorageStateEq hZ'
        have hstepPres :
            stateStorageStateEq
              ({stateZ with executionEnv.depth := state.executionEnv.depth} : State)
              stepped :=
          step_static_stateStorageStateEq_of_Z_succ_depth
            hperm hdepth ihTheta hZ' hstep''
        have hprefix : stateStorageStateEq state stepped :=
          stateStorageStateEq_trans
            (stateStorageStateEq_with_executionEnv_depth hZpres state.executionEnv.depth)
            hstepPres
        simp [← hinstr, hstep'] at hstep
        split at hstep
        · injection hstep with hstate
          have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
            congrArg Prod.fst hstate
          subst state'
          exact stateStorageStateEq_with_executionEnv hprefix state.executionEnv
        · split at hstep
          · injection hstep with hstate
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hstate
            subst state'
            exact stateStorageStateEq_with_executionEnv hprefix state.executionEnv
          · injection hstep with hstate
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hstate
            subst state'
            exact stateStorageStateEq_with_executionEnv hprefix state.executionEnv

theorem Xstep_static_preserves_perm
    {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)} :
    state.executionEnv.perm = false →
    Xstep validJumps state = .ok (state', ret) →
    state'.executionEnv.perm = false := by
  intro hperm hstep
  unfold Xstep at hstep
  simp only [bind, Except.bind] at hstep
  split at hstep
  · simp at hstep
  · rename_i stateZ cost hZ
    cases hstep' :
        step cost
          (decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none))
          {stateZ with executionEnv.depth := state.executionEnv.depth} with
    | error e =>
        simp [hstep'] at hstep
    | ok stepped =>
        simp [hstep'] at hstep
        split at hstep
        · injection hstep with hstate
          have hstateEq := congrArg Prod.fst hstate
          simp at hstateEq
          subst state'
          simpa using hperm
        · split at hstep
          · injection hstep with hstate
            have hstateEq := congrArg Prod.fst hstate
            simp at hstateEq
            subst state'
            simpa using hperm
          · injection hstep with hstate
            have hstateEq := congrArg Prod.fst hstate
            simp at hstateEq
            subst state'
            simpa using hperm

theorem X_static_stateStorageStateEq_max_depth
    {validJumps : Array UInt256} {state state' : State} {out : ByteArray}
    (fuel : Nat)
    (hperm : state.executionEnv.perm = false)
    (hdepth : state.executionEnv.depth = 1024)
    (hX : X fuel validJumps state = .ok (.success state' out)) :
    stateStorageStateEq state state' := by
  induction fuel generalizing state with
  | zero =>
      simp [X] at hX
  | succ fuel ih =>
      simp [X] at hX
      cases hstep : Xstep validJumps state with
      | error e =>
          simp [hstep, bind, Except.bind] at hX
      | ok stepResult =>
          rcases stepResult with ⟨next, ret⟩
          have hnext : stateStorageStateEq state next :=
            Xstep_static_stateStorageStateEq_max_depth
              (validJumps := validJumps) hperm hdepth hstep
          cases ret with
          | none =>
              have htailPerm :
                  ({next with executionEnv.depth := state.executionEnv.depth} : State).executionEnv.perm =
                    false := by
                simpa using Xstep_static_preserves_perm
                  (validJumps := validJumps) (ret := none) hperm hstep
              have htail :
                  stateStorageStateEq
                    ({next with executionEnv.depth := state.executionEnv.depth} : State) state' :=
                ih htailPerm (by simp [hdepth])
                  (by simpa [hstep, bind, Except.bind] using hX)
              exact stateStorageStateEq_trans
                (stateStorageStateEq_with_executionEnv_depth hnext state.executionEnv.depth)
                htail
          | some ret =>
              rcases ret with ⟨cause, out'⟩
              cases cause with
              | revert =>
                  simp [hstep, bind, Except.bind] at hX
              | success =>
                  simp [hstep, bind, Except.bind] at hX
                  rcases hX with ⟨hstate, _hout⟩
                  subst state'
                  exact hnext

theorem X_static_stateStorageStateEq_succ_depth
    {n : Nat} {validJumps : Array UInt256} {state state' : State} {out : ByteArray}
    (fuel : Nat)
    (hperm : state.executionEnv.perm = false)
    (hdepth : 1024 - state.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStorageStateEq σ σ')
    (hX : X fuel validJumps state = .ok (.success state' out)) :
    stateStorageStateEq state state' := by
  induction fuel generalizing state with
  | zero =>
      simp [X] at hX
  | succ fuel ih =>
      simp [X] at hX
      cases hstep : Xstep validJumps state with
      | error e =>
          simp [hstep, bind, Except.bind] at hX
      | ok stepResult =>
          rcases stepResult with ⟨next, ret⟩
          have hnext : stateStorageStateEq state next :=
            Xstep_static_stateStorageStateEq_succ_depth
              (validJumps := validJumps) hperm hdepth ihTheta hstep
          cases ret with
          | none =>
              have htailPerm :
                  ({next with executionEnv.depth := state.executionEnv.depth} : State).executionEnv.perm =
                    false := by
                simpa using Xstep_static_preserves_perm
                  (validJumps := validJumps) (ret := none) hperm hstep
              have htail :
                  stateStorageStateEq
                    ({next with executionEnv.depth := state.executionEnv.depth} : State) state' :=
                ih htailPerm (by simp [hdepth])
                  (by simpa [hstep, bind, Except.bind] using hX)
              exact stateStorageStateEq_trans
                (stateStorageStateEq_with_executionEnv_depth hnext state.executionEnv.depth)
                htail
          | some ret =>
              rcases ret with ⟨cause, out'⟩
              cases cause with
              | revert =>
                  simp [hstep, bind, Except.bind] at hX
              | success =>
                  simp [hstep, bind, Except.bind] at hX
                  rcases hX with ⟨hstate, _hout⟩
                  subst state'
                  exact hnext

theorem Xi_static_accountStorageStateEq_max_depth
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {out : ByteArray} :
    I.perm = false →
    I.depth = 1024 →
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success (createdAccounts', σ', g', A') out) →
    accountStorageStateEq σ σ' := by
  intro hperm hdepth hXi
  let freshEvmState : State :=
    { (default : State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := .ofUInt256 g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader
    }
  unfold Ξ at hXi
  simp only [bind, Except.bind] at hXi
  cases hX :
      X (UInt256.toNat g + 1) (D_J I.code 0) freshEvmState with
  | error e =>
      rw [hX] at hXi
      simp at hXi
  | ok result =>
      cases result with
      | revert gRevert outRevert =>
          rw [hX] at hXi
          simp at hXi
      | success stateSuccess outSuccess =>
          have hstate :
              stateStorageStateEq freshEvmState stateSuccess :=
            X_static_stateStorageStateEq_max_depth (UInt256.toNat g + 1)
              (by simpa [freshEvmState] using hperm)
              (by simpa [freshEvmState] using hdepth)
              hX
          rw [hX] at hXi
          simp at hXi
          rcases hXi with ⟨hcomponents, _hout⟩
          rcases hcomponents with ⟨_hcreated, hσ, _hg, _hA⟩
          subst σ'
          simpa [stateStorageStateEq, freshEvmState] using hstate

theorem Xi_static_accountStorageStateEq_succ_depth
    {n : Nat}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {out : ByteArray} :
    I.perm = false →
    1024 - I.depth.val = n + 1 →
    (∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStorageStateEq σ σ') →
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success (createdAccounts', σ', g', A') out) →
    accountStorageStateEq σ σ' := by
  intro hperm hdepth ihTheta hXi
  let freshEvmState : State :=
    { (default : State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := .ofUInt256 g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader
    }
  unfold Ξ at hXi
  simp only [bind, Except.bind] at hXi
  cases hX :
      X (UInt256.toNat g + 1) (D_J I.code 0) freshEvmState with
  | error e =>
      rw [hX] at hXi
      simp at hXi
  | ok result =>
      cases result with
      | revert gRevert outRevert =>
          rw [hX] at hXi
          simp at hXi
      | success stateSuccess outSuccess =>
          have hstate :
              stateStorageStateEq freshEvmState stateSuccess :=
            X_static_stateStorageStateEq_succ_depth (UInt256.toNat g + 1)
              (by simpa [freshEvmState] using hperm)
              (by simpa [freshEvmState] using hdepth)
              ihTheta
              hX
          rw [hX] at hXi
          simp at hXi
          rcases hXi with ⟨hcomponents, _hout⟩
          rcases hcomponents with ⟨_hcreated, hσ, _hg, _hA⟩
          subst σ'
          simpa [stateStorageStateEq, freshEvmState] using hstate

theorem thetaXiAccountMap_static
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {σ σPre : AccountMap} {A : Substate}
    {xi : Except EVM.ExecutionException
      (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))}
    (hpre : accountStorageStateEq σ σPre)
    (hxi : ∀ {createdAccounts' σ' g' A' out},
      xi = .ok (.success (createdAccounts', σ', g', A') out) →
      accountStorageStateEq σPre σ') :
    accountStorageStateEq σ (thetaXiAccountMap σ createdAccounts A xi) := by
  cases h : xi with
  | error e =>
      simp [thetaXiAccountMap, thetaXiResult]
  | ok result =>
      cases result with
      | revert g' out =>
          simp [thetaXiAccountMap, thetaXiResult]
      | success result out =>
          rcases result with ⟨createdAccounts', σ', g', A'⟩
          by_cases hempty : (σ' == (∅ : AccountMap)) = true
          · simp [thetaXiAccountMap, thetaXiResult, hempty]
          · simpa [thetaXiAccountMap, thetaXiResult, hempty] using
              accountStorageStateEq_trans hpre (hxi h)

theorem code_Theta_accountMap_eq
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader)
    (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap)
    (A : Substate)
    (s o r : AccountAddress)
    (code : ByteArray)
    (g p v v' : UInt256)
    (d : ByteArray)
    (e : Fin 1025)
    (H : BlockHeader) :
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Code code) g p v v' d e H false).2.1 =
      (let σ₁ := sendEth r s v true σ
       let I : ExecutionEnv :=
        { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
          source := s, weiValue := v', depth := e, perm := false,
          code := code, header := H, blobVersionedHashes := blobVersionedHashes }
       thetaXiAccountMap σ createdAccounts A
        (Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I)) := by
  unfold Θ sendEth thetaXiAccountMap thetaXiResult
  simp
  rfl

theorem Theta_static_accountStorageStateEq
    {blobVersionedHashes : List ByteArray}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {A A' : Substate}
    {s o r : AccountAddress} {c : ToExecute}
    {g g' p v v' : UInt256} {d out : ByteArray} {e : Fin 1025}
    {H : BlockHeader} {z : Bool}
    (hTheta : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c
        g p v v' d e H false =
      (createdAccounts', σ', g', A', z, out)) :
    accountStorageStateEq σ σ' := by
  generalize hn : 1024 - e.val = n
  induction n generalizing blobVersionedHashes createdAccounts genesisBlockHeader blocks
      createdAccounts' σ σ₀ σ' A A' s o r c g g' p v v' d out e H z with
  | zero =>
      have he : e = 1024 := by omega
      subst e
      cases hc : c with
      | Precompiled pc =>
          exact accountStorageStateEq_of_precompiled_Theta
            (createdAccounts' := createdAccounts') (pc := pc) (by simpa [hc] using hTheta)
      | Code code =>
          let σ₁ := sendEth r s v true σ
          let I : ExecutionEnv :=
            { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
              source := s, weiValue := v', depth := (1024 : Fin 1025), perm := false,
              code := code, header := H, blobVersionedHashes := blobVersionedHashes }
          let xi := Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I
          have hproj :
              (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
                (.Code code) g p v v' d (1024 : Fin 1025) H false).2.1 = σ' := by
            simpa [hc] using congrArg (fun x => x.2.1) hTheta
          rw [← hproj]
          rw [code_Theta_accountMap_eq blobVersionedHashes createdAccounts
            genesisBlockHeader blocks σ σ₀ A s o r code g p v v' d (1024 : Fin 1025) H]
          exact thetaXiAccountMap_static (sendEth_accountStorageStateEq r s v true σ)
            (by
              intro createdAccounts' σ' g' A' out hsuccess
              exact Xi_static_accountStorageStateEq_max_depth (I := I)
                rfl rfl (by simpa [σ₁, I, xi] using hsuccess))
  | succ n ih =>
      cases hc : c with
      | Precompiled pc =>
          exact accountStorageStateEq_of_precompiled_Theta
            (createdAccounts' := createdAccounts') (pc := pc) (by simpa [hc] using hTheta)
      | Code code =>
          let σ₁ := sendEth r s v true σ
          let I : ExecutionEnv :=
            { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
              source := s, weiValue := v', depth := e, perm := false,
              code := code, header := H, blobVersionedHashes := blobVersionedHashes }
          let xi := Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I
          have hproj :
              (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
                (.Code code) g p v v' d e H false).2.1 = σ' := by
            simpa [hc] using congrArg (fun x => x.2.1) hTheta
          rw [← hproj]
          rw [code_Theta_accountMap_eq blobVersionedHashes createdAccounts
            genesisBlockHeader blocks σ σ₀ A s o r code g p v v' d e H]
          exact thetaXiAccountMap_static (sendEth_accountStorageStateEq r s v true σ)
            (by
              intro createdAccounts' σ' g' A' out hsuccess
              exact Xi_static_accountStorageStateEq_succ_depth (n := n) (I := I)
                rfl (by simpa [I] using hn)
                (by
                  intro blobVersionedHashesᵢ genesisBlockHeaderᵢ blocksᵢ
                    createdAccountsᵢ eᵢ σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ rᵢ cᵢ gᵢ pᵢ vᵢ v'ᵢ dᵢ Hᵢ
                    createdAccounts'ᵢ σ'ᵢ g'ᵢ A'ᵢ zᵢ outᵢ heᵢ hThetaᵢ
                  exact ih (blobVersionedHashes := blobVersionedHashesᵢ)
                    (createdAccounts := createdAccountsᵢ)
                    (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                    (σ := σᵢ) (σ₀ := σ₀ᵢ) (σ' := σ'ᵢ) (A := Aᵢ) (A' := A'ᵢ)
                    (s := sᵢ) (o := oᵢ) (r := rᵢ) (c := cᵢ) (g := gᵢ) (g' := g'ᵢ)
                    (p := pᵢ) (v := vᵢ) (v' := v'ᵢ) (d := dᵢ) (out := outᵢ)
                    (e := eᵢ) (H := Hᵢ) (z := zᵢ) hThetaᵢ heᵢ)
                (by simpa [σ₁, I, xi] using hsuccess))

lemma static_step_stackmemflow_static_stateStaticStateEq_of_Z
    {validJumps : Array UInt256} {op : Operation.SMSFOp} {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state stateZ stepped : State}
    (hperm : state.executionEnv.perm = false)
    (hZ : Z validJumps (.StackMemFlow op) state = .ok (stateZ, gasCost))
    (hstep :
      step gasCost (.StackMemFlow op, arg)
        {stateZ with executionEnv.depth := state.executionEnv.depth} = .ok stepped) :
    stateStaticStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  cases op <;> simp [step] at hstep
  · split at hstep <;> try contradiction
    injection hstep with hstate
    rw [← hstate]
    exact stateStaticStateEq_refl _
  · split at hstep <;> try contradiction
    injection hstep with hstate
    rw [← hstate]
    exact stateStaticStateEq_refl _
  · have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateStaticStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · have hm := static_unaryStateOp_accountMap_eq
      (f := Ethereum.State.sload)
      (by
        intro s v
        simp [Ethereum.State.sload, Ethereum.State.addAccessedStorageKey,
          Ethereum.State.lookupAccount])
      hstep
    exact stateStaticStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateStaticStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · split at hstep <;> try contradiction
    injection hstep with hstate
    rw [← hstate]
    exact stateStaticStateEq_refl _
  · split at hstep <;> try contradiction
    injection hstep with hstate
    rw [← hstate]
    exact stateStaticStateEq_refl _
  · rw [← hstep]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, stateStaticStateEq]
  · have hm := static_machineStateOp_accountMap_eq hstep
    exact stateStaticStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · have hm := static_machineStateOp_accountMap_eq hstep
    exact stateStaticStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · rw [← hstep]
    simp [Ethereum.State.incrPC, stateStaticStateEq]
  · have hm := static_unaryStateOp_accountMap_eq
      (f := Ethereum.State.tload)
      (by intro s v; simp [Ethereum.State.tload])
      hstep
    exact stateStaticStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · have hm := static_ternaryMachineStateOp_accountMap_eq hstep
    exact stateStaticStateEq_of_accountMap_eq (by simpa [stepState] using hm)

lemma call_static_stateStaticStateEq_at_depth
    {n gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State}
    (hdepth : 1024 - evmState.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStaticStateEq σ σ')
    (hperm : permission = false)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    stateStaticStateEq evmState state' := by
  unfold call at h
  simp at h
  split at h
  · rename_i hcall
    rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateStaticStateEq]
    let θ :=
      Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
        evmState.blocks evmState.accountMap evmState.σ₀
        (evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header false
    have hθ :
        Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
          evmState.blocks evmState.accountMap evmState.σ₀
          (evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate
          (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
          (AccountAddress.ofUInt256 recipient)
          (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
          (UInt256.ofNat
            (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
              value gas evmState.accountMap evmState.machineState evmState.substate))
          (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
          (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evmState.executionEnv.depth + 1) evmState.executionEnv.header false =
        (θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1, θ.2.2.2.2.1, θ.2.2.2.2.2) := by
      rfl
    have hpres : accountStaticStateEq evmState.accountMap θ.2.1 :=
      ihTheta blobVersionedHashes evmState.genesisBlockHeader evmState.blocks
        evmState.createdAccounts (evmState.executionEnv.depth + 1)
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
        evmState.executionEnv.header
        θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2
        (static_depth_succ_measure hdepth hcall.2)
        hθ
    simpa [θ, hperm] using hpres
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateStaticStateEq]

lemma call_static_stateStaticStateEq_max_depth
    {gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State}
    (hdepth : evmState.executionEnv.depth = 1024)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    stateStaticStateEq evmState state' := by
  unfold call at h
  simp at h
  split at h
  · rename_i hcall
    exact False.elim (by
      have hlt := hcall.2
      omega)
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateStaticStateEq]

lemma step_system_call_static_stateStaticStateEq_of_Z_at_depth
    {n : Nat} {validJumps : Array UInt256} {op : Operation.SOp}
    {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat}
    (hcallkind : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL)
    (hdepth : 1024 - state.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStaticStateEq σ σ')
    (hperm : state.executionEnv.perm = false)
    (hZ : Z validJumps (.System op) state = .ok (stateZ, cost))
    (hstep :
      step cost (.System op, arg)
        {stateZ with executionEnv.depth := state.executionEnv.depth} = .ok stepped) :
    stateStaticStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  have hZEnv : stateZ.executionEnv = state.executionEnv :=
    Z_executionEnv_eq (validJumps := validJumps) (state := state) (op := .System op) hZ
  cases op
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStaticStateEq_at_depth
      (n := n)
      (hdepth := by simp [hdepth])
      ihTheta
      (by simpa [stepState, hZEnv] using hperm)
      hcall
    simpa [stepState, stateStaticStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStaticStateEq_at_depth
      (n := n)
      (hdepth := by simp [hdepth])
      ihTheta
      (by simpa [stepState, hZEnv] using hperm)
      hcall
    simpa [stepState, stateStaticStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStaticStateEq_at_depth
      (n := n)
      (hdepth := by simp [hdepth])
      ihTheta
      (by simpa [stepState, hZEnv] using hperm)
      hcall
    simpa [stepState, stateStaticStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStaticStateEq_at_depth
      (n := n)
      (hdepth := by simp [hdepth])
      ihTheta
      rfl
      hcall
    simpa [stepState, stateStaticStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse

lemma step_system_call_static_stateStaticStateEq_of_Z_max_depth
    {validJumps : Array UInt256} {op : Operation.SOp} {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat}
    (hcallkind : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL)
    (hdepth : state.executionEnv.depth = 1024)
    (hZ : Z validJumps (.System op) state = .ok (stateZ, cost))
    (hstep :
      step cost (.System op, arg)
        {stateZ with executionEnv.depth := state.executionEnv.depth} = .ok stepped) :
    stateStaticStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  cases op
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStaticStateEq_max_depth
      (hdepth := by simp [hdepth])
      hcall
    simpa [stepState, stateStaticStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStaticStateEq_max_depth
      (hdepth := by simp [hdepth])
      hcall
    simpa [stepState, stateStaticStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStaticStateEq_max_depth
      (hdepth := by simp [hdepth])
      hcall
    simpa [stepState, stateStaticStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateStaticStateEq_max_depth
      (hdepth := by simp [hdepth])
      hcall
    simpa [stepState, stateStaticStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse

theorem step_system_static_stateStaticStateEq_of_Z_max_depth
    {validJumps : Array UInt256} {op : Operation.SOp} {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat} :
    state.executionEnv.perm = false →
    state.executionEnv.depth = 1024 →
    Z validJumps (.System op) state = .ok (stateZ, cost) →
    step cost (.System op, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} =
      .ok stepped →
    stateStaticStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  intro hperm hdepth hZ hstep
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  cases op
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · exact step_system_call_static_stateStaticStateEq_of_Z_max_depth (by simp) hdepth hZ hstep
  · exact step_system_call_static_stateStaticStateEq_of_Z_max_depth (by simp) hdepth hZ hstep
  · simp [step] at hstep
    have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateStaticStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · exact step_system_call_static_stateStaticStateEq_of_Z_max_depth (by simp) hdepth hZ hstep
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · exact step_system_call_static_stateStaticStateEq_of_Z_max_depth (by simp) hdepth hZ hstep
  · simp [step] at hstep
    have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateStaticStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · simp [step] at hstep
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)

theorem step_system_static_stateStaticStateEq_of_Z_succ_depth
    {n : Nat} {validJumps : Array UInt256} {op : Operation.SOp}
    {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat} :
    state.executionEnv.perm = false →
    1024 - state.executionEnv.depth.val = n + 1 →
    (∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStaticStateEq σ σ') →
    Z validJumps (.System op) state = .ok (stateZ, cost) →
    step cost (.System op, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} =
      .ok stepped →
    stateStaticStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  intro hperm hdepth ihTheta hZ hstep
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  cases op
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · exact step_system_call_static_stateStaticStateEq_of_Z_at_depth (by simp)
      hdepth ihTheta hperm hZ hstep
  · exact step_system_call_static_stateStaticStateEq_of_Z_at_depth (by simp)
      hdepth ihTheta hperm hZ hstep
  · simp [step] at hstep
    have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateStaticStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · exact step_system_call_static_stateStaticStateEq_of_Z_at_depth (by simp)
      hdepth ihTheta hperm hZ hstep
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · exact step_system_call_static_stateStaticStateEq_of_Z_at_depth (by simp)
      hdepth ihTheta hperm hZ hstep
  · simp [step] at hstep
    have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateStaticStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · simp [step] at hstep
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)

theorem step_static_stateStaticStateEq_of_Z_max_depth
    {validJumps : Array UInt256} {op : Operation} {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat} :
    state.executionEnv.perm = false →
    state.executionEnv.depth = 1024 →
    Z validJumps op state = .ok (stateZ, cost) →
    step cost (op, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} =
      .ok stepped →
    stateStaticStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  intro hperm hdepth hZ hstep
  rcases op with op | op | op | op | op | op | op | op | op | op
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_stoparith_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_compbit_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_keccak_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_env_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_block_accountMap_eq hstep)
  · exact static_step_stackmemflow_static_stateStaticStateEq_of_Z hperm hZ hstep
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_push_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_dup_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_exchange_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_log_accountMap_eq hstep)
  · exact step_system_static_stateStaticStateEq_of_Z_max_depth hperm hdepth hZ hstep

theorem step_static_stateStaticStateEq_of_Z_succ_depth
    {n : Nat} {validJumps : Array UInt256} {op : Operation}
    {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat} :
    state.executionEnv.perm = false →
    1024 - state.executionEnv.depth.val = n + 1 →
    (∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStaticStateEq σ σ') →
    Z validJumps op state = .ok (stateZ, cost) →
    step cost (op, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} =
      .ok stepped →
    stateStaticStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  intro hperm hdepth ihTheta hZ hstep
  rcases op with op | op | op | op | op | op | op | op | op | op
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_stoparith_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_compbit_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_keccak_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_env_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_block_accountMap_eq hstep)
  · exact static_step_stackmemflow_static_stateStaticStateEq_of_Z hperm hZ hstep
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_push_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_dup_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_exchange_accountMap_eq hstep)
  · exact stateStaticStateEq_of_accountMap_eq
      (static_step_log_accountMap_eq hstep)
  · exact step_system_static_stateStaticStateEq_of_Z_succ_depth
      hperm hdepth ihTheta hZ hstep

theorem Xstep_static_stateStaticStateEq_max_depth
    {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)} :
    state.executionEnv.perm = false →
    state.executionEnv.depth = 1024 →
    Xstep validJumps state = .ok (state', ret) →
    stateStaticStateEq state state' := by
  intro hperm hdepth hstep
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  unfold Xstep at hstep
  simp only [bind, Except.bind] at hstep
  split at hstep
  · simp at hstep
  · rename_i stateZ cost hZ
    have hZ' : Z validJumps op state = .ok (stateZ, cost) := by
      simpa [← hinstr] using hZ
    cases hstep' :
        step cost (op, arg)
          {stateZ with executionEnv.depth := state.executionEnv.depth} with
    | error e =>
        simp [← hinstr, hstep'] at hstep
    | ok stepped =>
        have hstep'' :
            step cost (op, arg)
              {stateZ with executionEnv.depth := state.executionEnv.depth} =
            .ok stepped := hstep'
        have hZpres : stateStaticStateEq state stateZ :=
          Z_static_stateStaticStateEq hZ'
        have hstepPres :
            stateStaticStateEq
              ({stateZ with executionEnv.depth := state.executionEnv.depth} : State)
              stepped :=
          step_static_stateStaticStateEq_of_Z_max_depth hperm hdepth hZ' hstep''
        have hprefix : stateStaticStateEq state stepped :=
          stateStaticStateEq_trans
            (stateStaticStateEq_with_executionEnv_depth hZpres state.executionEnv.depth)
            hstepPres
        simp [← hinstr, hstep'] at hstep
        split at hstep
        · injection hstep with hstate
          have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
            congrArg Prod.fst hstate
          subst state'
          exact stateStaticStateEq_with_executionEnv hprefix state.executionEnv
        · split at hstep
          · injection hstep with hstate
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hstate
            subst state'
            exact stateStaticStateEq_with_executionEnv hprefix state.executionEnv
          · injection hstep with hstate
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hstate
            subst state'
            exact stateStaticStateEq_with_executionEnv hprefix state.executionEnv

theorem Xstep_static_stateStaticStateEq_succ_depth
    {n : Nat} {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)} :
    state.executionEnv.perm = false →
    1024 - state.executionEnv.depth.val = n + 1 →
    (∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStaticStateEq σ σ') →
    Xstep validJumps state = .ok (state', ret) →
    stateStaticStateEq state state' := by
  intro hperm hdepth ihTheta hstep
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  unfold Xstep at hstep
  simp only [bind, Except.bind] at hstep
  split at hstep
  · simp at hstep
  · rename_i stateZ cost hZ
    have hZ' : Z validJumps op state = .ok (stateZ, cost) := by
      simpa [← hinstr] using hZ
    cases hstep' :
        step cost (op, arg)
          {stateZ with executionEnv.depth := state.executionEnv.depth} with
    | error e =>
        simp [← hinstr, hstep'] at hstep
    | ok stepped =>
        have hstep'' :
            step cost (op, arg)
              {stateZ with executionEnv.depth := state.executionEnv.depth} =
            .ok stepped := hstep'
        have hZpres : stateStaticStateEq state stateZ :=
          Z_static_stateStaticStateEq hZ'
        have hstepPres :
            stateStaticStateEq
              ({stateZ with executionEnv.depth := state.executionEnv.depth} : State)
              stepped :=
          step_static_stateStaticStateEq_of_Z_succ_depth
            hperm hdepth ihTheta hZ' hstep''
        have hprefix : stateStaticStateEq state stepped :=
          stateStaticStateEq_trans
            (stateStaticStateEq_with_executionEnv_depth hZpres state.executionEnv.depth)
            hstepPres
        simp [← hinstr, hstep'] at hstep
        split at hstep
        · injection hstep with hstate
          have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
            congrArg Prod.fst hstate
          subst state'
          exact stateStaticStateEq_with_executionEnv hprefix state.executionEnv
        · split at hstep
          · injection hstep with hstate
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hstate
            subst state'
            exact stateStaticStateEq_with_executionEnv hprefix state.executionEnv
          · injection hstep with hstate
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hstate
            subst state'
            exact stateStaticStateEq_with_executionEnv hprefix state.executionEnv

theorem X_static_stateStaticStateEq_max_depth
    {validJumps : Array UInt256} {state state' : State} {out : ByteArray}
    (fuel : Nat)
    (hperm : state.executionEnv.perm = false)
    (hdepth : state.executionEnv.depth = 1024)
    (hX : X fuel validJumps state = .ok (.success state' out)) :
    stateStaticStateEq state state' := by
  induction fuel generalizing state with
  | zero =>
      simp [X] at hX
  | succ fuel ih =>
      simp [X] at hX
      cases hstep : Xstep validJumps state with
      | error e =>
          simp [hstep, bind, Except.bind] at hX
      | ok stepResult =>
          rcases stepResult with ⟨next, ret⟩
          have hnext : stateStaticStateEq state next :=
            Xstep_static_stateStaticStateEq_max_depth
              (validJumps := validJumps) hperm hdepth hstep
          cases ret with
          | none =>
              have htailPerm :
                  ({next with executionEnv.depth := state.executionEnv.depth} : State).executionEnv.perm =
                    false := by
                simpa using Xstep_static_preserves_perm
                  (validJumps := validJumps) (ret := none) hperm hstep
              have htail :
                  stateStaticStateEq
                    ({next with executionEnv.depth := state.executionEnv.depth} : State) state' :=
                ih htailPerm (by simp [hdepth])
                  (by simpa [hstep, bind, Except.bind] using hX)
              exact stateStaticStateEq_trans
                (stateStaticStateEq_with_executionEnv_depth hnext state.executionEnv.depth)
                htail
          | some ret =>
              rcases ret with ⟨cause, out'⟩
              cases cause with
              | revert =>
                  simp [hstep, bind, Except.bind] at hX
              | success =>
                  simp [hstep, bind, Except.bind] at hX
                  rcases hX with ⟨hstate, _hout⟩
                  subst state'
                  exact hnext

theorem X_static_stateStaticStateEq_succ_depth
    {n : Nat} {validJumps : Array UInt256} {state state' : State} {out : ByteArray}
    (fuel : Nat)
    (hperm : state.executionEnv.perm = false)
    (hdepth : 1024 - state.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStaticStateEq σ σ')
    (hX : X fuel validJumps state = .ok (.success state' out)) :
    stateStaticStateEq state state' := by
  induction fuel generalizing state with
  | zero =>
      simp [X] at hX
  | succ fuel ih =>
      simp [X] at hX
      cases hstep : Xstep validJumps state with
      | error e =>
          simp [hstep, bind, Except.bind] at hX
      | ok stepResult =>
          rcases stepResult with ⟨next, ret⟩
          have hnext : stateStaticStateEq state next :=
            Xstep_static_stateStaticStateEq_succ_depth
              (validJumps := validJumps) hperm hdepth ihTheta hstep
          cases ret with
          | none =>
              have htailPerm :
                  ({next with executionEnv.depth := state.executionEnv.depth} : State).executionEnv.perm =
                    false := by
                simpa using Xstep_static_preserves_perm
                  (validJumps := validJumps) (ret := none) hperm hstep
              have htail :
                  stateStaticStateEq
                    ({next with executionEnv.depth := state.executionEnv.depth} : State) state' :=
                ih htailPerm (by simp [hdepth])
                  (by simpa [hstep, bind, Except.bind] using hX)
              exact stateStaticStateEq_trans
                (stateStaticStateEq_with_executionEnv_depth hnext state.executionEnv.depth)
                htail
          | some ret =>
              rcases ret with ⟨cause, out'⟩
              cases cause with
              | revert =>
                  simp [hstep, bind, Except.bind] at hX
              | success =>
                  simp [hstep, bind, Except.bind] at hX
                  rcases hX with ⟨hstate, _hout⟩
                  subst state'
                  exact hnext

theorem Xi_static_accountStaticStateEq_max_depth
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {out : ByteArray} :
    I.perm = false →
    I.depth = 1024 →
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success (createdAccounts', σ', g', A') out) →
    accountStaticStateEq σ σ' := by
  intro hperm hdepth hXi
  let freshEvmState : State :=
    { (default : State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := .ofUInt256 g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader
    }
  unfold Ξ at hXi
  simp only [bind, Except.bind] at hXi
  cases hX :
      X (UInt256.toNat g + 1) (D_J I.code 0) freshEvmState with
  | error e =>
      rw [hX] at hXi
      simp at hXi
  | ok result =>
      cases result with
      | revert gRevert outRevert =>
          rw [hX] at hXi
          simp at hXi
      | success stateSuccess outSuccess =>
          have hstate :
              stateStaticStateEq freshEvmState stateSuccess :=
            X_static_stateStaticStateEq_max_depth (UInt256.toNat g + 1)
              (by simpa [freshEvmState] using hperm)
              (by simpa [freshEvmState] using hdepth)
              hX
          rw [hX] at hXi
          simp at hXi
          rcases hXi with ⟨hcomponents, _hout⟩
          rcases hcomponents with ⟨_hcreated, hσ, _hg, _hA⟩
          subst σ'
          simpa [stateStaticStateEq, freshEvmState] using hstate

theorem Xi_static_accountStaticStateEq_succ_depth
    {n : Nat}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {out : ByteArray} :
    I.perm = false →
    1024 - I.depth.val = n + 1 →
    (∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountStaticStateEq σ σ') →
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success (createdAccounts', σ', g', A') out) →
    accountStaticStateEq σ σ' := by
  intro hperm hdepth ihTheta hXi
  let freshEvmState : State :=
    { (default : State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := .ofUInt256 g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader
    }
  unfold Ξ at hXi
  simp only [bind, Except.bind] at hXi
  cases hX :
      X (UInt256.toNat g + 1) (D_J I.code 0) freshEvmState with
  | error e =>
      rw [hX] at hXi
      simp at hXi
  | ok result =>
      cases result with
      | revert gRevert outRevert =>
          rw [hX] at hXi
          simp at hXi
      | success stateSuccess outSuccess =>
          have hstate :
              stateStaticStateEq freshEvmState stateSuccess :=
            X_static_stateStaticStateEq_succ_depth (UInt256.toNat g + 1)
              (by simpa [freshEvmState] using hperm)
              (by simpa [freshEvmState] using hdepth)
              ihTheta
              hX
          rw [hX] at hXi
          simp at hXi
          rcases hXi with ⟨hcomponents, _hout⟩
          rcases hcomponents with ⟨_hcreated, hσ, _hg, _hA⟩
          subst σ'
          simpa [stateStaticStateEq, freshEvmState] using hstate

theorem thetaXiAccountMap_static_accountStaticStateEq
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {σ σPre : AccountMap} {A : Substate}
    {xi : Except EVM.ExecutionException
      (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))}
    (hpre : accountStaticStateEq σ σPre)
    (hxi : ∀ {createdAccounts' σ' g' A' out},
      xi = .ok (.success (createdAccounts', σ', g', A') out) →
      accountStaticStateEq σPre σ') :
    accountStaticStateEq σ (thetaXiAccountMap σ createdAccounts A xi) := by
  cases h : xi with
  | error e =>
      simp [thetaXiAccountMap, thetaXiResult]
  | ok result =>
      cases result with
      | revert g' out =>
          simp [thetaXiAccountMap, thetaXiResult]
      | success result out =>
          rcases result with ⟨createdAccounts', σ', g', A'⟩
          by_cases hempty : (σ' == (∅ : AccountMap)) = true
          · simp [thetaXiAccountMap, thetaXiResult, hempty]
          · simpa [thetaXiAccountMap, thetaXiResult, hempty] using
              accountStaticStateEq_trans hpre (hxi h)

theorem Theta_static_accountStaticStateEq
    {blobVersionedHashes : List ByteArray}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {A A' : Substate}
    {s o r : AccountAddress} {c : ToExecute}
    {g g' p v v' : UInt256} {d out : ByteArray} {e : Fin 1025}
    {H : BlockHeader} {z : Bool}
    (hTheta : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c
        g p v v' d e H false =
      (createdAccounts', σ', g', A', z, out)) :
    accountStaticStateEq σ σ' := by
  generalize hn : 1024 - e.val = n
  induction n generalizing blobVersionedHashes createdAccounts genesisBlockHeader blocks
      createdAccounts' σ σ₀ σ' A A' s o r c g g' p v v' d out e H z with
  | zero =>
      have he : e = 1024 := by omega
      subst e
      cases hc : c with
      | Precompiled pc =>
          exact accountStaticStateEq_of_precompiled_Theta
            (createdAccounts' := createdAccounts') (pc := pc) (by simpa [hc] using hTheta)
      | Code code =>
          let σ₁ := sendEth r s v true σ
          let I : ExecutionEnv :=
            { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
              source := s, weiValue := v', depth := (1024 : Fin 1025), perm := false,
              code := code, header := H, blobVersionedHashes := blobVersionedHashes }
          let xi := Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I
          have hproj :
              (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
                (.Code code) g p v v' d (1024 : Fin 1025) H false).2.1 = σ' := by
            simpa [hc] using congrArg (fun x => x.2.1) hTheta
          rw [← hproj]
          rw [code_Theta_accountMap_eq blobVersionedHashes createdAccounts
            genesisBlockHeader blocks σ σ₀ A s o r code g p v v' d (1024 : Fin 1025) H]
          exact thetaXiAccountMap_static_accountStaticStateEq (sendEth_accountStaticStateEq r s v true σ)
            (by
              intro createdAccounts' σ' g' A' out hsuccess
              exact Xi_static_accountStaticStateEq_max_depth (I := I)
                rfl rfl (by simpa [σ₁, I, xi] using hsuccess))
  | succ n ih =>
      cases hc : c with
      | Precompiled pc =>
          exact accountStaticStateEq_of_precompiled_Theta
            (createdAccounts' := createdAccounts') (pc := pc) (by simpa [hc] using hTheta)
      | Code code =>
          let σ₁ := sendEth r s v true σ
          let I : ExecutionEnv :=
            { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
              source := s, weiValue := v', depth := e, perm := false,
              code := code, header := H, blobVersionedHashes := blobVersionedHashes }
          let xi := Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I
          have hproj :
              (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
                (.Code code) g p v v' d e H false).2.1 = σ' := by
            simpa [hc] using congrArg (fun x => x.2.1) hTheta
          rw [← hproj]
          rw [code_Theta_accountMap_eq blobVersionedHashes createdAccounts
            genesisBlockHeader blocks σ σ₀ A s o r code g p v v' d e H]
          exact thetaXiAccountMap_static_accountStaticStateEq (sendEth_accountStaticStateEq r s v true σ)
            (by
              intro createdAccounts' σ' g' A' out hsuccess
              exact Xi_static_accountStaticStateEq_succ_depth (n := n) (I := I)
                rfl (by simpa [I] using hn)
                (by
                  intro blobVersionedHashesᵢ genesisBlockHeaderᵢ blocksᵢ
                    createdAccountsᵢ eᵢ σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ rᵢ cᵢ gᵢ pᵢ vᵢ v'ᵢ dᵢ Hᵢ
                    createdAccounts'ᵢ σ'ᵢ g'ᵢ A'ᵢ zᵢ outᵢ heᵢ hThetaᵢ
                  exact ih (blobVersionedHashes := blobVersionedHashesᵢ)
                    (createdAccounts := createdAccountsᵢ)
                    (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                    (σ := σᵢ) (σ₀ := σ₀ᵢ) (σ' := σ'ᵢ) (A := Aᵢ) (A' := A'ᵢ)
                    (s := sᵢ) (o := oᵢ) (r := rᵢ) (c := cᵢ) (g := gᵢ) (g' := g'ᵢ)
                    (p := pᵢ) (v := vᵢ) (v' := v'ᵢ) (d := dᵢ) (out := outᵢ)
                    (e := eᵢ) (H := Hᵢ) (z := zᵢ) hThetaᵢ heᵢ)
                (by simpa [σ₁, I, xi] using hsuccess))


theorem Theta_static_accountStorageState_eq
    {blobVersionedHashes : List ByteArray}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {A A' : Substate}
    {s o r : AccountAddress} {c : ToExecute}
    {g g' p v v' : UInt256} {d out : ByteArray} {e : Fin 1025}
    {H : BlockHeader} {z : Bool}
    (hTheta : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c
        g p v v' d e H false =
      (createdAccounts', σ', g', A', z, out)) :
    accountStorageState σ = accountStorageState σ' := by
  exact accountStorageState_eq_of_accountStorageStateEq
    (Theta_static_accountStorageStateEq hTheta)

lemma call_static_stateStorageStateEq
    {gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State}
    (hperm : permission = false)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    stateStorageStateEq evmState state' := by
  unfold call at h
  simp at h
  split at h
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateStorageStateEq]
    let θ :=
      Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
        evmState.blocks evmState.accountMap evmState.σ₀
        (evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header false
    have hθ :
        Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
          evmState.blocks evmState.accountMap evmState.σ₀
          (evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate
          (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
          (AccountAddress.ofUInt256 recipient)
          (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
          (UInt256.ofNat
            (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
              value gas evmState.accountMap evmState.machineState evmState.substate))
          (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
          (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evmState.executionEnv.depth + 1) evmState.executionEnv.header false =
        (θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1, θ.2.2.2.2.1, θ.2.2.2.2.2) := by
      rfl
    have hpres : accountStorageStateEq evmState.accountMap θ.2.1 :=
      Theta_static_accountStorageStateEq hθ
    simpa [θ, hperm] using hpres
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateStorageStateEq]

theorem Theta_static_accountCodeStateEq
    {blobVersionedHashes : List ByteArray}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {A A' : Substate}
    {s o r : AccountAddress} {c : ToExecute}
    {g g' p v v' : UInt256} {d out : ByteArray} {e : Fin 1025}
    {H : BlockHeader} {z : Bool}
    (hTheta : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c
        g p v v' d e H false =
      (createdAccounts', σ', g', A', z, out)) :
    accountCodeStateEq σ σ' := by
  intro addr
  exact (Theta_static_accountStaticStateEq hTheta addr).2.2

lemma call_static_stateStaticStateEq
    {gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State}
    (hperm : permission = false)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    stateStaticStateEq evmState state' := by
  unfold call at h
  simp at h
  split at h
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateStaticStateEq]
    let θ :=
      Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
        evmState.blocks evmState.accountMap evmState.σ₀
        (evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header false
    have hθ :
        Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
          evmState.blocks evmState.accountMap evmState.σ₀
          (evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate
          (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
          (AccountAddress.ofUInt256 recipient)
          (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
          (UInt256.ofNat
            (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
              value gas evmState.accountMap evmState.machineState evmState.substate))
          (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
          (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evmState.executionEnv.depth + 1) evmState.executionEnv.header false =
        (θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1, θ.2.2.2.2.1, θ.2.2.2.2.2) := by
      rfl
    have hpres : accountStaticStateEq evmState.accountMap θ.2.1 :=
      Theta_static_accountStaticStateEq hθ
    simpa [θ, hperm, stateStaticStateEq] using hpres
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateStaticStateEq]

lemma call_static_stateCodeStateEq
    {gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State}
    (hperm : permission = false)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    stateCodeStateEq evmState state' := by
  intro addr
  exact (call_static_stateStaticStateEq hperm h addr).2.2

end EVM
end Ethereum
