import Ethereum.Crypto.BN254

def SNARKV (data : ByteArray) : Except String ByteArray :=
  match Ethereum.Crypto.BN254.snarkv data with
  | some o => .ok o
  | none => .error "SNARKV failed"

theorem SNARKV_ok_size {data out : ByteArray} (h : SNARKV data = .ok out) : out.size = 32 := by
  unfold SNARKV at h
  split at h
  · cases h; exact Ethereum.Crypto.BN254.snarkv_size ‹_›
  · cases h
