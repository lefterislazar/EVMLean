/-!
# RIPEMD-160

As specified by Dobbertin, Bosselaers and Preneel, "RIPEMD-160: A
strengthened version of RIPEMD".
-/

namespace Ethereum.Crypto.RIPEMD160

/-- The message words selected by the left line. -/
private def r : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]

/-- The message words selected by the right line. -/
private def r' : Array Nat := #[
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]

/-- The rotation amounts of the left line. -/
private def s : Array UInt32 := #[
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]

/-- The rotation amounts of the right line. -/
private def s' : Array UInt32 := #[
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

private def K : Array UInt32 := #[0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]

private def K' : Array UInt32 := #[0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

@[inline] private def rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- The nonlinear function of round `j / 16`. -/
@[inline] private def f (round : Nat) (x y z : UInt32) : UInt32 :=
  match round with
  | 0 => x ^^^ y ^^^ z
  | 1 => (x &&& y) ||| (~~~x &&& z)
  | 2 => (x ||| ~~~y) ^^^ z
  | 3 => (x &&& z) ||| (y &&& ~~~z)
  | _ => x ^^^ (y ||| ~~~z)

/-- The message padded to a multiple of 64 bytes, with its bit length in
    little-endian order. -/
private def pad (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let mut out := msg.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0
  let bits := len * 8
  for k in [0:8] do
    out := out.push (bits >>> (8 * k)).toUInt8
  return out

private def compress (h : Array UInt32) (block : ByteArray) (offset : Nat) : Array UInt32 := Id.run do
  let x : Array UInt32 := Array.ofFn (n := 16) fun t =>
    let i := offset + 4 * t.val
    block[i]!.toUInt32 ||| (block[i + 1]!.toUInt32 <<< 8) |||
      (block[i + 2]!.toUInt32 <<< 16) ||| (block[i + 3]!.toUInt32 <<< 24)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut a' := h[0]!
  let mut b' := h[1]!
  let mut c' := h[2]!
  let mut d' := h[3]!
  let mut e' := h[4]!
  for j in [0:80] do
    let round := j / 16
    let t := rotl (a + f round b c d + x[r[j]!]! + K[round]!) s[j]! + e
    a := e
    e := d
    d := rotl c 10
    c := b
    b := t
    let t' := rotl (a' + f (4 - round) b' c' d' + x[r'[j]!]! + K'[round]!) s'[j]! + e'
    a' := e'
    e' := d'
    d' := rotl c' 10
    c' := b'
    b' := t'
  return #[h[1]! + c + d', h[2]! + d + e', h[3]! + e + a', h[4]! + a + b', h[0]! + b + c']

/-- The state after absorbing `msg`. -/
private def digestWords (msg : ByteArray) : Array UInt32 := Id.run do
  let padded := pad msg
  let mut h : Array UInt32 := #[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]
  for i in [0:padded.size / 64] do
    h := compress h padded (64 * i)
  return h

/-- The 20-byte RIPEMD-160 digest of `msg`: the state words in little-endian
    order. -/
def hash (msg : ByteArray) : ByteArray :=
  let h := digestWords msg
  ⟨Array.ofFn (n := 20) fun i => (h[i.val / 4]! >>> (8 * (i.val % 4)).toUInt32).toUInt8⟩

theorem hash_size (msg : ByteArray) : (hash msg).size = 20 := by
  simp [hash, ByteArray.size]

end Ethereum.Crypto.RIPEMD160
