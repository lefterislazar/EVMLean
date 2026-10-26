import Ethereum.Crypto.BLS12_381

def PointEval (data : ByteArray) : Except String ByteArray :=
  match Ethereum.Crypto.BLS12_381.pointEvaluation data with
  | some o => .ok o
  | none => .error "PointEval failed"

theorem PointEval_ok_size {data out : ByteArray} (h : PointEval data = .ok out) : out.size = 64 := by
  unfold PointEval at h
  split at h
  · cases h; exact Ethereum.Crypto.BLS12_381.pointEvaluation_size ‹_›
  · cases h
