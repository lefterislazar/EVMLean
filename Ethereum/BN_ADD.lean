import Ethereum.Crypto.BN254

def BN_ADD (x₀ y₀ x₁ y₁ : ByteArray) : Except String ByteArray :=
  match Ethereum.Crypto.BN254.add x₀ y₀ x₁ y₁ with
  | some o => .ok o
  | none => .error "BN_ADD failed"

theorem BN_ADD_ok_size {x₀ y₀ x₁ y₁ out : ByteArray}
    (h : BN_ADD x₀ y₀ x₁ y₁ = .ok out) : out.size = 64 := by
  unfold BN_ADD at h
  split at h
  · cases h; exact Ethereum.Crypto.BN254.add_size ‹_›
  · cases h
