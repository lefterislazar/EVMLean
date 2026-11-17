import Ethereum.Crypto.BN254

def BN_MUL (x₀ y₀ n : ByteArray) : Except String ByteArray :=
  match Ethereum.Crypto.BN254.mul x₀ y₀ n with
  | some o => .ok o
  | none => .error "BN_MUL failed"

theorem BN_MUL_ok_size {x₀ y₀ n out : ByteArray}
    (h : BN_MUL x₀ y₀ n = .ok out) : out.size = 64 := by
  unfold BN_MUL at h
  split at h
  · cases h; exact Ethereum.Crypto.BN254.mul_size ‹_›
  · cases h
