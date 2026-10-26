import Ethereum.Crypto.RIPEMD160
import Ethereum.Wheels

/-- The RIPEMD-160 digest of `d`, left-padded to 32 bytes. -/
def RIP160 (d : ByteArray) : Except String ByteArray :=
  .ok (ByteArray.zeroes 12 ++ Ethereum.Crypto.RIPEMD160.hash d)

theorem RIP160_ok_size {d out : ByteArray} (h : RIP160 d = .ok out) : out.size = 32 := by
  rw [← Except.ok.inj h]
  simp only [ByteArray.size_append, ByteArray_zeroes_size, Ethereum.Crypto.RIPEMD160.hash_size]
