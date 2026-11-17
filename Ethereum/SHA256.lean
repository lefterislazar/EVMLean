import Ethereum.Crypto.SHA256

def SHA256 (d : ByteArray) : Except String ByteArray :=
  .ok (Ethereum.Crypto.SHA256.hash d)

theorem SHA256_ok_size {d out : ByteArray} (h : SHA256 d = .ok out) : out.size = 32 := by
  rw [← Except.ok.inj h]
  exact Ethereum.Crypto.SHA256.hash_size d
