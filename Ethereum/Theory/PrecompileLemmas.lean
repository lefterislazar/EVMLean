import Ethereum.Semantics

/-!
# Precompile lemmas

Facts about the precompiled contracts that hold for every precompile, lifted
to the dispatch `Ξ_PRECOMPILE` with `Ξ_PRECOMPILE_induction`.
-/

namespace Ethereum
namespace EVM

lemma precompile_ECREC_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_ECREC σ g A I).1 = ∅ ∨ (Ξ_ECREC σ g A I).1 = σ := by
  simp only [Ξ_ECREC]
  split <;> simp

lemma precompile_SHA256_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_SHA256 σ g A I).1 = ∅ ∨ (Ξ_SHA256 σ g A I).1 = σ := by
  simp only [Ξ_SHA256]
  split <;> simp

lemma precompile_RIP160_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_RIP160 σ g A I).1 = ∅ ∨ (Ξ_RIP160 σ g A I).1 = σ := by
  simp only [Ξ_RIP160]
  split <;> simp

lemma precompile_ID_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_ID σ g A I).1 = ∅ ∨ (Ξ_ID σ g A I).1 = σ := by
  simp only [Ξ_ID]
  split <;> simp

lemma precompile_EXPMOD_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_EXPMOD σ g A I).1 = ∅ ∨ (Ξ_EXPMOD σ g A I).1 = σ := by
  simp only [Ξ_EXPMOD]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl

lemma precompile_BN_ADD_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BN_ADD σ g A I).1 = ∅ ∨ (Ξ_BN_ADD σ g A I).1 = σ := by
  simp only [Ξ_BN_ADD]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

lemma precompile_BN_MUL_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BN_MUL σ g A I).1 = ∅ ∨ (Ξ_BN_MUL σ g A I).1 = σ := by
  simp only [Ξ_BN_MUL]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

lemma precompile_SNARKV_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_SNARKV σ g A I).1 = ∅ ∨ (Ξ_SNARKV σ g A I).1 = σ := by
  simp only [Ξ_SNARKV]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

lemma precompile_BLAKE2_F_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BLAKE2_F σ g A I).1 = ∅ ∨ (Ξ_BLAKE2_F σ g A I).1 = σ := by
  simp only [Ξ_BLAKE2_F]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

lemma precompile_PointEval_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_PointEval σ g A I).1 = ∅ ∨ (Ξ_PointEval σ g A I).1 = σ := by
  simp only [Ξ_PointEval]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

lemma precompile_BLS12_381_accountMap_empty_or_self
    (op : ℕ) (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BLS12_381 op σ g A I).1 = ∅ ∨ (Ξ_BLS12_381 op σ g A I).1 = σ := by
  simp only [Ξ_BLS12_381]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

lemma precompile_P256VERIFY_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_P256VERIFY σ g A I).1 = ∅ ∨ (Ξ_P256VERIFY σ g A I).1 = σ := by
  simp only [Ξ_P256VERIFY]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

/--
A BLS12-381 precompile (EIP-2537) called with no gas fails: a valid input
always costs gas (`blsRequiredGas_pos_of_valid`), and an invalid input length
is rejected in Lean before the external implementation runs.
-/
theorem precompile_BLS12_381_zero_gas
    (op : ℕ) (σ : AccountMap) (A : Substate) (I : ExecutionEnv) :
    Ξ_BLS12_381 op σ ⟨0⟩ A I = (∅, ⟨0⟩, A, .empty) := by
  unfold Ξ_BLS12_381
  by_cases hpos : 0 < blsRequiredGas op I.calldata.size
  · have hlt : (⟨0⟩ : UInt256).toNat < blsRequiredGas op I.calldata.size := hpos
    rw [if_pos hlt]
  · have hlt : ¬(⟨0⟩ : UInt256).toNat < blsRequiredGas op I.calldata.size := hpos
    rw [if_neg hlt]
    have hvalid : blsInputLengthValid op I.calldata.size = false := by
      cases h : blsInputLengthValid op I.calldata.size
      · rfl
      · exact absurd (blsRequiredGas_pos_of_valid h) hpos
    have hbls : BLS12_381 op (blsOutputSize op) I.calldata =
        .error "BLS12-381: invalid input length" := by
      unfold BLS12_381
      simp [hvalid]
    rw [hbls]

/-- The precompile dispatch at a BLS12-381 address (`0x0b`–`0x11`) fails
    when called with no gas. -/
theorem precompile_dispatch_BLS12_381_zero_gas {p : AccountAddress}
    (hp : 11 ≤ p.val ∧ p.val ≤ 17) (σ : AccountMap) (A : Substate) (I : ExecutionEnv) :
    Ξ_PRECOMPILE p σ ⟨0⟩ A I = (∅, ⟨0⟩, A, .empty) := by
  have hcases : p.val = 11 ∨ p.val = 12 ∨ p.val = 13 ∨ p.val = 14 ∨
      p.val = 15 ∨ p.val = 16 ∨ p.val = 17 := by omega
  rcases hcases with h | h | h | h | h | h | h
  · obtain rfl : p = (11 : AccountAddress) := Fin.ext (h.trans (by decide))
    simp [Ξ_PRECOMPILE, precompile_BLS12_381_zero_gas]
  · obtain rfl : p = (12 : AccountAddress) := Fin.ext (h.trans (by decide))
    simp [Ξ_PRECOMPILE, precompile_BLS12_381_zero_gas]
  · obtain rfl : p = (13 : AccountAddress) := Fin.ext (h.trans (by decide))
    simp [Ξ_PRECOMPILE, precompile_BLS12_381_zero_gas]
  · obtain rfl : p = (14 : AccountAddress) := Fin.ext (h.trans (by decide))
    simp [Ξ_PRECOMPILE, precompile_BLS12_381_zero_gas]
  · obtain rfl : p = (15 : AccountAddress) := Fin.ext (h.trans (by decide))
    simp [Ξ_PRECOMPILE, precompile_BLS12_381_zero_gas]
  · obtain rfl : p = (16 : AccountAddress) := Fin.ext (h.trans (by decide))
    simp [Ξ_PRECOMPILE, precompile_BLS12_381_zero_gas]
  · obtain rfl : p = (17 : AccountAddress) := Fin.ext (h.trans (by decide))
    simp [Ξ_PRECOMPILE, precompile_BLS12_381_zero_gas]

/-- A precompile either fails, with an empty account map, or keeps the state. -/
theorem precompiled_result_accountMap_empty_or_self
    (pc : AccountAddress) (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_PRECOMPILE pc σ g A I).1 = ∅ ∨ (Ξ_PRECOMPILE pc σ g A I).1 = σ :=
  Ξ_PRECOMPILE_induction (fun r => r.1 = ∅ ∨ r.1 = σ)
    (precompile_ECREC_accountMap_empty_or_self σ g A I)
    (precompile_SHA256_accountMap_empty_or_self σ g A I)
    (precompile_RIP160_accountMap_empty_or_self σ g A I)
    (precompile_ID_accountMap_empty_or_self σ g A I)
    (precompile_EXPMOD_accountMap_empty_or_self σ g A I)
    (precompile_BN_ADD_accountMap_empty_or_self σ g A I)
    (precompile_BN_MUL_accountMap_empty_or_self σ g A I)
    (precompile_SNARKV_accountMap_empty_or_self σ g A I)
    (precompile_BLAKE2_F_accountMap_empty_or_self σ g A I)
    (precompile_PointEval_accountMap_empty_or_self σ g A I)
    (fun op => precompile_BLS12_381_accountMap_empty_or_self op σ g A I)
    (precompile_P256VERIFY_accountMap_empty_or_self σ g A I)
    (Or.inl rfl)

end EVM
end Ethereum
