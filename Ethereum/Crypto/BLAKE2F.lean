/-!
# The BLAKE2b compression function `F` (RFC 7693, EIP-152)

The working vector is a structure of sixteen `UInt64` fields, which Lean
stores unboxed, so that a round allocates once rather than once per word.
-/

namespace Ethereum.Crypto.BLAKE2F

private def IV : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

private def SIGMA : Array (Array Nat) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- The working vector `v₀ … v₁₅`. -/
private structure V where
  v0 : UInt64
  v1 : UInt64
  v2 : UInt64
  v3 : UInt64
  v4 : UInt64
  v5 : UInt64
  v6 : UInt64
  v7 : UInt64
  v8 : UInt64
  v9 : UInt64
  v10 : UInt64
  v11 : UInt64
  v12 : UInt64
  v13 : UInt64
  v14 : UInt64
  v15 : UInt64

@[inline] private def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- The mixing function `G`. -/
@[inline] private def G (a b c d x y : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let a := a + b + x
  let d := rotr (d ^^^ a) 32
  let c := c + d
  let b := rotr (b ^^^ c) 24
  let a := a + b + y
  let d := rotr (d ^^^ a) 16
  let c := c + d
  let b := rotr (b ^^^ c) 63
  (a, b, c, d)

private def round (v : V) (m : Array UInt64) (s : Array Nat) : V :=
  let (v0, v4, v8, v12) := G v.v0 v.v4 v.v8 v.v12 m[s[0]!]! m[s[1]!]!
  let (v1, v5, v9, v13) := G v.v1 v.v5 v.v9 v.v13 m[s[2]!]! m[s[3]!]!
  let (v2, v6, v10, v14) := G v.v2 v.v6 v.v10 v.v14 m[s[4]!]! m[s[5]!]!
  let (v3, v7, v11, v15) := G v.v3 v.v7 v.v11 v.v15 m[s[6]!]! m[s[7]!]!
  let (v0, v5, v10, v15) := G v0 v5 v10 v15 m[s[8]!]! m[s[9]!]!
  let (v1, v6, v11, v12) := G v1 v6 v11 v12 m[s[10]!]! m[s[11]!]!
  let (v2, v7, v8, v13) := G v2 v7 v8 v13 m[s[12]!]! m[s[13]!]!
  let (v3, v4, v9, v14) := G v3 v4 v9 v14 m[s[14]!]! m[s[15]!]!
  ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩

/-- The little-endian 64-bit word at `offset`. -/
private def word (d : ByteArray) (offset : Nat) : UInt64 := Id.run do
  let mut w : UInt64 := 0
  for k in [0:8] do
    w := w ||| (d[offset + k]!.toUInt64 <<< (8 * k).toUInt64)
  return w

/-- The compression function `F` with `rounds` rounds, state `h`, message
    block `m`, offset counters `t₀`, `t₁` and final-block flag `f`. -/
def compress (rounds : Nat) (h m : Array UInt64) (t₀ t₁ : UInt64) (f : Bool) : Array UInt64 :=
  Id.run do
  let mut v : V :=
    ⟨h[0]!, h[1]!, h[2]!, h[3]!, h[4]!, h[5]!, h[6]!, h[7]!,
     IV[0]!, IV[1]!, IV[2]!, IV[3]!, IV[4]! ^^^ t₀, IV[5]! ^^^ t₁,
     if f then ~~~IV[6]! else IV[6]!, IV[7]!⟩
  for i in [0:rounds] do
    v := round v m SIGMA[i % 10]!
  return #[h[0]! ^^^ v.v0 ^^^ v.v8, h[1]! ^^^ v.v1 ^^^ v.v9, h[2]! ^^^ v.v2 ^^^ v.v10,
    h[3]! ^^^ v.v3 ^^^ v.v11, h[4]! ^^^ v.v4 ^^^ v.v12, h[5]! ^^^ v.v5 ^^^ v.v13,
    h[6]! ^^^ v.v6 ^^^ v.v14, h[7]! ^^^ v.v7 ^^^ v.v15]

/-- The eight state words in little-endian order. -/
private def serialize (h : Array UInt64) : ByteArray :=
  ⟨Array.ofFn (n := 64) fun i => (h[i.val / 8]! >>> (8 * (i.val % 8)).toUInt64).toUInt8⟩

private theorem serialize_size (h : Array UInt64) : (serialize h).size = 64 := by
  simp [serialize, ByteArray.size]

/--
The EIP-152 precompile on its 213-byte input `rounds ‖ h ‖ m ‖ t ‖ f`: the
64-byte state after compression, or `none` for an input of the wrong length or
a final-block flag other than `0` or `1`.
-/
def blake2f (d : ByteArray) : Option ByteArray :=
  if d.size == 213 && d[212]! ≤ 1 then
    let rounds := (d.extract 0 4).foldl (fun acc b => acc * 256 + b.toNat) 0
    let h := Array.ofFn (n := 8) fun i => word d (4 + 8 * i.val)
    let m := Array.ofFn (n := 16) fun i => word d (68 + 8 * i.val)
    some (serialize (compress rounds h m (word d 196) (word d 204) (d[212]! == 1)))
  else none

theorem blake2f_size {d o : ByteArray} (h : blake2f d = some o) : o.size = 64 := by
  unfold blake2f at h
  split at h
  · rw [← Option.some.inj h]; exact serialize_size _
  · nomatch h

end Ethereum.Crypto.BLAKE2F
