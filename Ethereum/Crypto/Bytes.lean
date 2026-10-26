/-!
# Byte conversions for the cryptographic primitives
-/

namespace Ethereum.Crypto

/-- The big-endian number encoded by `b`. -/
def ofBytesBE (b : ByteArray) : Nat :=
  b.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- The `len`-byte big-endian encoding of `n` modulo `2^(8·len)`. -/
def toBytesBE (n len : Nat) : ByteArray :=
  ⟨Array.ofFn (n := len) fun i => (n >>> (8 * (len - 1 - i.val))).toUInt8⟩

theorem toBytesBE_size (n len : Nat) : (toBytesBE n len).size = len := by
  simp [toBytesBE, ByteArray.size]

/-- The results of `f <$> x` have size `n` when every value of `f` does. -/
theorem map_eq_some_size {α : Type} {f : α → ByteArray} {x : Option α} {n : Nat} {o : ByteArray}
    (hf : ∀ a, (f a).size = n) (h : f <$> x = some o) : o.size = n := by
  cases x with
  | none => cases h
  | some a => cases h; exact hf a

end Ethereum.Crypto
