import Ethereum.Crypto.BLAKE2F

def BLAKE2_F (data : ByteArray) : Except String ByteArray :=
  match Ethereum.Crypto.BLAKE2F.blake2f data with
  | some o => .ok o
  | none => .error "BLAKE2_F failed"

theorem BLAKE2_F_ok_size {data out : ByteArray} (h : BLAKE2_F data = .ok out) : out.size = 64 := by
  unfold BLAKE2_F at h
  split at h
  · cases h; exact Ethereum.Crypto.BLAKE2F.blake2f_size ‹_›
  · cases h
