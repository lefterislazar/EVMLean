/-!
Pure Lean implementation of the Keccak-256 function used by Ethereum.

The lane layout, rotations, and round constants below follow the published
Keccak-f[1600] specification. Keccak lanes and the sponge byte stream are
little endian. Ethereum uses the original Keccak domain suffix (`0x01`), not
the later SHA3 suffix (`0x06`).

There are two implementations. `referenceHash` computes on `UInt64` lanes and is
the one compiled code runs. `hash` (and so `KEC`) computes on `Nat` lanes so that
the kernel can evaluate it on concrete inputs quickly, e.g. in `decide +kernel`
proofs about function selectors and storage slots. `hash_eq_referenceHash` proves
them equal.
-/

namespace Ethereum.Keccak256

/-- A Keccak-f[1600] state: 25 lanes of 64 bits. -/
abbrev State := Vector UInt64 25

/-- One Keccak-256 rate block (1088 bits). -/
abbrev Block := Vector UInt8 136

def rateBytes : Nat := 136
def digestBytes : Nat := 32

private def rotationOffsets : Vector Nat 25 := ⟨#[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14
], by decide⟩

private def roundConstants : Vector UInt64 24 := ⟨#[
  0x0000000000000001, 0x0000000000008082,
  0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088,
  0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b,
  0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080,
  0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080,
  0x0000000080000001, 0x8000000080008008
], by decide⟩

private def laneIndex (x y : Nat) : Fin 25 :=
  Fin.ofNat 25 (x + 5 * y)

private def lane (state : State) (x y : Nat) : UInt64 :=
  state[laneIndex x y]

private def rotateLeft (word : UInt64) (amount : Nat) : UInt64 :=
  if amount = 0 then word
  else word.shiftLeft amount.toUInt64 ||| word.shiftRight (64 - amount).toUInt64

/-- One Keccak-f[1600] round (theta, rho, pi, chi, then iota). -/
def round (state : State) (roundConstant : UInt64) : State := Id.run do
  -- theta
  let mut columns : Vector UInt64 5 := Vector.replicate 5 0
  for x in [0:5] do
    let index := Fin.ofNat 5 x
    columns := columns.set index.val
      (lane state x 0 ^^^ lane state x 1 ^^^ lane state x 2 ^^^
       lane state x 3 ^^^ lane state x 4) index.isLt

  let mut afterTheta := state
  for y in [0:5] do
    for x in [0:5] do
      let delta := columns[Fin.ofNat 5 (x + 4)] ^^^ rotateLeft columns[Fin.ofNat 5 (x + 1)] 1
      let index := laneIndex x y
      afterTheta := afterTheta.set index.val (lane state x y ^^^ delta) index.isLt

  -- rho and pi: B[y, 2*x+3*y] = rot(A[x,y], r[x,y])
  let mut afterPi : State := Vector.replicate 25 0
  for y in [0:5] do
    for x in [0:5] do
      let destination := laneIndex y (2 * x + 3 * y)
      afterPi := afterPi.set destination.val
        (rotateLeft (lane afterTheta x y) rotationOffsets[laneIndex x y]) destination.isLt

  -- chi
  let mut afterChi := afterPi
  for y in [0:5] do
    for x in [0:5] do
      let value := lane afterPi x y ^^^
        ((~~~lane afterPi ((x + 1) % 5) y) &&& lane afterPi ((x + 2) % 5) y)
      let index := laneIndex x y
      afterChi := afterChi.set index.val value index.isLt

  -- iota
  return afterChi.set 0 (afterChi[0] ^^^ roundConstant)

/-- The 24-round Keccak-f[1600] permutation. -/
def permute (state : State) : State := Id.run do
  let mut result := state
  for roundConstant in roundConstants do
    result := round result roundConstant
  return result

private def blockAt (input : ByteArray) (offset : Nat) : Block :=
  Vector.ofFn fun i => input[offset + i]!

private def finalBlock (input : ByteArray) (offset : Nat) : Block :=
  let remaining := input.size - offset
  Vector.ofFn fun i =>
    if i < remaining then
      input[offset + i]!
    else if i = remaining then
      -- When the suffix occupies the final rate byte, combine it with the
      -- terminal bit. This is the important single-byte `0x81` case.
      if i = rateBytes - 1 then 0x81 else 0x01
    else if i = rateBytes - 1 then
      0x80
    else
      0

private def decodeLane (block : Block) (i : Nat) : UInt64 := Id.run do
  let mut result : UInt64 := 0
  for j in [0:8] do
    result := result |||
      block[Fin.ofNat 136 (8 * i + j)].toUInt64.shiftLeft (8 * j).toUInt64
  return result

private def absorbBlock (state : State) (block : Block) : State :=
  let mixed := Id.run do
    let mut result := state
    for i in [0:17] do
      let index := Fin.ofNat 25 i
      result := result.set index.val (result[index] ^^^ decodeLane block i) index.isLt
    return result
  permute mixed

private def absorb (input : ByteArray) : State := Id.run do
  let fullBlocks := input.size / rateBytes
  let mut state : State := Vector.replicate 25 0
  for i in [0:fullBlocks] do
    state := absorbBlock state (blockAt input (i * rateBytes))
  state := absorbBlock state (finalBlock input (fullBlocks * rateBytes))
  return state

private def encodeDigest (state : State) : ByteArray :=
  ByteArray.mk <| Array.ofFn fun i : Fin digestBytes =>
    let laneNumber := i.val / 8
    let byteNumber := i.val % 8
    (state[Fin.ofNat 25 laneNumber].shiftRight (8 * byteNumber).toUInt64).toUInt8

/-- Ethereum Keccak-256 with the legacy `0x01` domain suffix, computed on `UInt64` lanes. -/
def referenceHash (input : ByteArray) : ByteArray :=
  encodeDigest (absorb input)

/-! ## Kernel evaluation

The kernel computes `Nat` arithmetic and bitwise operations on literals with GMP, but it
reduces `UInt64` operations, `Vector` indexing, and `for` loops over ranges step by step. So
`hash` keeps the lanes as natural numbers below `2 ^ 64` in a structure, writes the round out
lane by lane, and reads the padded input as one little-endian number. The hot paths call
`Nat.xor` and the other primitives directly rather than through `^^^` and its instances, which
halves the kernel's work.
-/

/-- A Keccak-f[1600] state with lane `(x, y)` in field `a(x + 5 * y)`, each below `2 ^ 64`. -/
structure Lanes where
  (a0 a1 a2 a3 a4 : Nat)
  (a5 a6 a7 a8 a9 : Nat)
  (a10 a11 a12 a13 a14 : Nat)
  (a15 a16 a17 a18 a19 : Nat)
  (a20 a21 a22 a23 a24 : Nat)

/-- The all-zero state. -/
def Lanes.zero : Lanes :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The lanes of a reference `State`. -/
def Lanes.ofState (s : State) : Lanes :=
  ⟨s[0].toNat, s[1].toNat, s[2].toNat, s[3].toNat, s[4].toNat,
    s[5].toNat, s[6].toNat, s[7].toNat, s[8].toNat, s[9].toNat,
    s[10].toNat, s[11].toNat, s[12].toNat, s[13].toNat, s[14].toNat,
    s[15].toNat, s[16].toNat, s[17].toNat, s[18].toNat, s[19].toNat,
    s[20].toNat, s[21].toNat, s[22].toNat, s[23].toNat, s[24].toNat⟩

private def laneMask : Nat := 2 ^ 64 - 1

/-- Rotates a lane left by `n` bits, for `0 < n < 64`. -/
private def rotl (x n : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft x n % 2 ^ 64) (Nat.shiftRight x (64 - n))

/-- The parity of a column. -/
private def xor5 (a b c d e : Nat) : Nat := Nat.xor (Nat.xor (Nat.xor (Nat.xor a b) c) d) e

/-- The chi step for one lane, given it and its next two neighbours in the row. -/
private def chi (a b c : Nat) : Nat := Nat.xor a (Nat.land (Nat.xor laneMask b) c)

/-- One Keccak-f[1600] round (theta, rho, pi, chi, then iota) on `Lanes`. -/
def Lanes.round (a : Lanes) (rc : Nat) : Lanes :=
  -- theta: column parities `c` and the values `d` to mix into each column
  let c0 := xor5 a.a0 a.a5 a.a10 a.a15 a.a20
  let c1 := xor5 a.a1 a.a6 a.a11 a.a16 a.a21
  let c2 := xor5 a.a2 a.a7 a.a12 a.a17 a.a22
  let c3 := xor5 a.a3 a.a8 a.a13 a.a18 a.a23
  let c4 := xor5 a.a4 a.a9 a.a14 a.a19 a.a24
  let d0 := Nat.xor c4 (rotl c1 1)
  let d1 := Nat.xor c0 (rotl c2 1)
  let d2 := Nat.xor c1 (rotl c3 1)
  let d3 := Nat.xor c2 (rotl c4 1)
  let d4 := Nat.xor c3 (rotl c0 1)
  -- theta, rho, and pi: b[y, 2*x+3*y] = rot(a[x,y] ^ d[x], r[x,y])
  let b0 := Nat.xor a.a0 d0
  let b1 := rotl (Nat.xor a.a6 d1) 44
  let b2 := rotl (Nat.xor a.a12 d2) 43
  let b3 := rotl (Nat.xor a.a18 d3) 21
  let b4 := rotl (Nat.xor a.a24 d4) 14
  let b5 := rotl (Nat.xor a.a3 d3) 28
  let b6 := rotl (Nat.xor a.a9 d4) 20
  let b7 := rotl (Nat.xor a.a10 d0) 3
  let b8 := rotl (Nat.xor a.a16 d1) 45
  let b9 := rotl (Nat.xor a.a22 d2) 61
  let b10 := rotl (Nat.xor a.a1 d1) 1
  let b11 := rotl (Nat.xor a.a7 d2) 6
  let b12 := rotl (Nat.xor a.a13 d3) 25
  let b13 := rotl (Nat.xor a.a19 d4) 8
  let b14 := rotl (Nat.xor a.a20 d0) 18
  let b15 := rotl (Nat.xor a.a4 d4) 27
  let b16 := rotl (Nat.xor a.a5 d0) 36
  let b17 := rotl (Nat.xor a.a11 d1) 10
  let b18 := rotl (Nat.xor a.a17 d2) 15
  let b19 := rotl (Nat.xor a.a23 d3) 56
  let b20 := rotl (Nat.xor a.a2 d2) 62
  let b21 := rotl (Nat.xor a.a8 d3) 55
  let b22 := rotl (Nat.xor a.a14 d4) 39
  let b23 := rotl (Nat.xor a.a15 d0) 41
  let b24 := rotl (Nat.xor a.a21 d1) 2
  -- chi, then iota
  ⟨Nat.xor (chi b0 b1 b2) rc, chi b1 b2 b3, chi b2 b3 b4, chi b3 b4 b0, chi b4 b0 b1,
   chi b5 b6 b7, chi b6 b7 b8, chi b7 b8 b9, chi b8 b9 b5, chi b9 b5 b6,
   chi b10 b11 b12, chi b11 b12 b13, chi b12 b13 b14, chi b13 b14 b10, chi b14 b10 b11,
   chi b15 b16 b17, chi b16 b17 b18, chi b17 b18 b19, chi b18 b19 b15, chi b19 b15 b16,
   chi b20 b21 b22, chi b21 b22 b23, chi b22 b23 b24, chi b23 b24 b20, chi b24 b20 b21⟩

/-- The 24-round Keccak-f[1600] permutation on `Lanes`. -/
def Lanes.permute (a : Lanes) : Lanes :=
  roundConstants.toList.foldl (fun a rc => a.round rc.toNat) a

/-- Lane `j` of a block given as a little-endian number. -/
private def blockLane (block j : Nat) : Nat := block >>> (64 * j) % 2 ^ 64

/-- XORs the rate block in the low `8 * rateBytes` bits of `block` into the lanes, then permutes. -/
def Lanes.absorb (a : Lanes) (block : Nat) : Lanes :=
  let mix (lane j : Nat) := Nat.xor lane (blockLane block j)
  Lanes.permute
    ⟨mix a.a0 0, mix a.a1 1, mix a.a2 2, mix a.a3 3, mix a.a4 4,
      mix a.a5 5, mix a.a6 6, mix a.a7 7, mix a.a8 8, mix a.a9 9,
      mix a.a10 10, mix a.a11 11, mix a.a12 12, mix a.a13 13, mix a.a14 14,
      mix a.a15 15, mix a.a16 16, a.a17, a.a18, a.a19,
      a.a20, a.a21, a.a22, a.a23, a.a24⟩

/-- The little-endian number with bytes `bytes`. -/
private def ofBytes : List UInt8 → Nat
  | [] => 0
  | b :: bytes => b.toNat ||| ofBytes bytes <<< 8

/-- `input` padded to `blocks` rate blocks, as one little-endian number: the input bytes, the
domain suffix bit after them, and the final bit of the last block. -/
private def padded (input : ByteArray) (blocks : Nat) : Nat :=
  ofBytes input.data.toList ||| 2 ^ (8 * input.size) ||| 2 ^ (8 * rateBytes * blocks - 1)

/-- Absorbs `blocks` rate blocks of `message`, least significant first. -/
private def absorbBlocks (a : Lanes) (message : Nat) : Nat → Lanes
  | 0 => a
  | blocks + 1 => absorbBlocks (a.absorb message) (message >>> (8 * rateBytes)) blocks

/-- The eight bytes of a lane, little endian. -/
private def laneBytes (x : Nat) : List UInt8 :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8,
    (x >>> 32).toUInt8, (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8]

/-- Ethereum Keccak-256 with the legacy `0x01` domain suffix. -/
def hash (input : ByteArray) : ByteArray :=
  let blocks := input.size / rateBytes + 1
  let a := absorbBlocks Lanes.zero (padded input blocks) blocks
  ⟨⟨laneBytes a.a0 ++ laneBytes a.a1 ++ laneBytes a.a2 ++ laneBytes a.a3⟩⟩

/-! ## Equivalence with the reference implementation -/

private theorem rotateLeft_zero (w : UInt64) : rotateLeft w 0 = w := rfl

private theorem toNat_rotateLeft (w : UInt64) (n : Nat) (h0 : 0 < n) (h : n < 64) :
    (rotateLeft w n).toNat = rotl w.toNat n := by
  have h1 : (UInt64.ofNat n).toNat % 64 = n := by rw [UInt64.toNat_ofNat']; omega
  have h2 : (UInt64.ofNat (64 - n)).toNat % 64 = 64 - n := by rw [UInt64.toNat_ofNat']; omega
  simp only [rotateLeft, show n ≠ 0 by omega, ↓reduceIte, rotl]
  change (w <<< UInt64.ofNat n ||| w >>> UInt64.ofNat (64 - n)).toNat = _
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, h1, h2]
  rfl

private theorem toNat_complement (w : UInt64) : (~~~w).toNat = laneMask ^^^ w.toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [UInt64.toNat_not, show UInt64.size - 1 - w.toNat = 2 ^ 64 - (w.toNat + 1) by
      simp only [UInt64.size]; omega,
    Nat.testBit_two_pow_sub_succ w.toNat_lt, laneMask, Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 64
  · simp [hi]
  · simp [hi, Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le w.toNat_lt (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi)))]

private theorem xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem ofState_round (s : State) (rc : UInt64) :
    Lanes.ofState (round s rc) = (Lanes.ofState s).round rc.toNat := by
  simp only [Lanes.ofState, round, Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.forIn_pure_yield_eq_foldl, pure_bind, List.range'_succ,
    List.range'_zero, List.foldl_cons, List.foldl_nil, lane, laneIndex, Fin.ofNat, Nat.reduceAdd,
    Nat.reduceMul, Nat.reduceMod, Vector.getElem_set, rotationOffsets, Fin.getElem_fin,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    ↓reduceIte, Nat.reduceEqDiff, rotateLeft_zero, UInt64.toNat_xor, UInt64.toNat_and,
    toNat_complement, toNat_rotateLeft, Nat.reduceSub, Nat.reduceLT, Lanes.round, xor5, chi]
  rfl

theorem ofState_permute (s : State) : Lanes.ofState (permute s) = (Lanes.ofState s).permute := by
  suffices ∀ (rcs : List UInt64) (s : State), Lanes.ofState (rcs.foldl round s) =
      rcs.foldl (fun a rc => a.round rc.toNat) (Lanes.ofState s) by
    have hfold : ∀ v : Vector UInt64 24, v.foldl round s = v.toList.foldl round s := by
      intro ⟨xs, h⟩
      simp only [Vector.foldl_mk, Vector.toList_mk, Array.foldl_toList]
    simp only [permute, Lanes.permute, pure_bind, bind_pure, Vector.forIn_pure_yield_eq_foldl,
      Id.run_pure]
    rw [hfold, this]
  intro rcs
  induction rcs with
  | nil => intro s; rfl
  | cons rc rcs ih => intro s; simp only [List.foldl_cons, ih, ofState_round]

private theorem toNat_shiftLeft_toUInt64 (b : UInt8) (k : Nat) (hk : k ≤ 56) :
    (b.toUInt64.shiftLeft k.toUInt64).toNat = b.toNat * 2 ^ k := by
  have hlt : b.toNat * 2 ^ k < 2 ^ 64 :=
    calc b.toNat * 2 ^ k < 2 ^ 8 * 2 ^ k :=
          Nat.mul_lt_mul_of_pos_right b.toNat_lt (Nat.two_pow_pos k)
      _ = 2 ^ (8 + k) := (Nat.pow_add 2 8 k).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  change (b.toUInt64 <<< UInt64.ofNat k).toNat = _
  rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, UInt64.toNat_ofNat', Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show k < 2 ^ 64 from Nat.lt_of_le_of_lt hk (by decide)),
    Nat.mod_eq_of_lt (show k < 64 by omega), Nat.mod_eq_of_lt hlt]

private theorem or_mul_two_pow {a x i : Nat} (ha : a < 2 ^ i) :
    a ||| x * 2 ^ i = a + x * 2 ^ i := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.add_comm]

private theorem toNat_decodeLane (block : Block) (M i : Nat) (hi : i < 17)
    (hb : ∀ t (ht : t < 8), (block[8 * i + t]'(by omega)).toNat = M >>> (8 * t) % 2 ^ 8) :
    (decodeLane block i).toNat = M % 2 ^ 64 := by
  have hidx : ∀ t, t < 8 → (8 * i + t) % 136 = 8 * i + t := fun t ht => Nat.mod_eq_of_lt (by omega)
  simp only [decodeLane, Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, pure_bind, List.range'_succ, List.range'_zero, List.foldl_cons,
    List.foldl_nil, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Fin.getElem_fin,
    UInt64.toNat_or, Fin.val_ofNat, hidx, Nat.reduceLT, toNat_shiftLeft_toUInt64, Nat.reduceLeDiff]
  have h0 := hb 0 (by decide); have h1 := hb 1 (by decide); have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide); have h4 := hb 4 (by decide); have h5 := hb 5 (by decide)
  have h6 := hb 6 (by decide); have h7 := hb 7 (by decide)
  simp only [Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  rw [h0, h1, h2, h3, h4, h5, h6, h7, UInt64.toNat_zero, Nat.zero_or]
  simp (disch := omega) only [or_mul_two_pow]
  omega

private theorem ofState_absorbBlock (s : State) (block : Block) (N : Nat)
    (hb : ∀ m (hm : m < 136), block[m].toNat = N >>> (8 * m) % 2 ^ 8) :
    Lanes.ofState (absorbBlock s block) = (Lanes.ofState s).absorb N := by
  have hl : ∀ i, i < 17 → (decodeLane block i).toNat = blockLane N i := fun i hi =>
    toNat_decodeLane block _ i hi fun t ht => by
      rw [hb _ (by omega), show 8 * (8 * i + t) = 64 * i + 8 * t by omega, Nat.shiftRight_add]
  simp only [absorbBlock, Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.forIn_pure_yield_eq_foldl, pure_bind, List.range'_succ,
    List.range'_zero, List.foldl_cons, List.foldl_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv,
    Nat.reduceMod, Fin.getElem_fin, Fin.val_ofNat, Vector.getElem_set, ↓reduceIte, Nat.reduceEqDiff]
  rw [ofState_permute]
  unfold Lanes.absorb
  refine congrArg Lanes.permute ?_
  simp only [Lanes.ofState, Vector.getElem_set, ↓reduceIte, Nat.reduceEqDiff, UInt64.toNat_xor, hl,
    Nat.reduceLT, xor_eq]

private theorem absorbBlocks_succ (a : Lanes) (message k : Nat) :
    absorbBlocks a message (k + 1) =
      (absorbBlocks a message k).absorb (message >>> (8 * rateBytes * k)) := by
  induction k generalizing a message with
  | zero => rfl
  | succ k ih =>
    show absorbBlocks (a.absorb message) (message >>> (8 * rateBytes)) (k + 1) = _
    rw [ih, ← Nat.shiftRight_add, Nat.mul_succ, Nat.add_comm]
    rfl

private theorem testBit_ofBytes (bytes : List UInt8) (q : Nat) :
    (ofBytes bytes).testBit q = (bytes.getD (q / 8) 0).toNat.testBit (q % 8) := by
  induction bytes generalizing q with
  | nil => simp [ofBytes]
  | cons b bytes ih =>
    simp only [ofBytes, Nat.testBit_or, Nat.testBit_shiftLeft, ih]
    by_cases hq : q < 8
    · simp [Nat.div_eq_of_lt hq, Nat.mod_eq_of_lt hq, show ¬8 ≤ q by omega]
    · have hb : b.toNat.testBit q = false := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le b.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hb, show 8 ≤ q by omega, show q / 8 = (q - 8) / 8 + 1 by omega,
        show (q - 8) % 8 = q % 8 by omega]

private theorem padded_byte (input : ByteArray) (blocks p : Nat) (hblocks : 0 < blocks) :
    padded input blocks >>> (8 * p) % 2 ^ 8 =
      (input.data.toList.getD p 0).toNat ||| (if p = input.size then 1 else 0) |||
        (if p = rateBytes * blocks - 1 then 0x80 else 0) := by
  have one : ∀ r < 8, Nat.testBit 1 r = decide (r = 0) := by decide
  have high : ∀ r < 8, Nat.testBit 0x80 r = decide (r = 7) := by decide
  apply Nat.eq_of_testBit_eq
  intro r
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, padded, Nat.testBit_or,
    testBit_ofBytes, Nat.testBit_two_pow, rateBytes]
  by_cases hr : r < 8
  · have e1 : decide (8 * input.size = 8 * p + r) = decide (p = input.size ∧ r = 0) := by
      simp only [decide_eq_decide]; omega
    have e2 : decide (8 * 136 * blocks - 1 = 8 * p + r) =
        decide (p = 136 * blocks - 1 ∧ r = 7) := by
      simp only [decide_eq_decide]; omega
    simp only [hr, decide_true, Bool.true_and, show (8 * p + r) / 8 = p by omega,
      show (8 * p + r) % 8 = r by omega, e1, e2]
    have hn : (p = input.size) = True ∨ (p = input.size) = False := by
      by_cases h : p = input.size
      · exact .inl (eq_true h)
      · exact .inr (eq_false h)
    have hl : (p = 136 * blocks - 1) = True ∨ (p = 136 * blocks - 1) = False := by
      by_cases h : p = 136 * blocks - 1
      · exact .inl (eq_true h)
      · exact .inr (eq_false h)
    rcases hn with hn | hn <;> rcases hl with hl | hl <;>
      simp only [hn, hl, true_and, false_and, decide_false, if_true, if_false, one r hr,
        high r hr, Nat.zero_testBit, Bool.or_false]
  · have hb : ∀ x : UInt8, x.toNat.testBit r = false := fun x => Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega)))
    have hs : ∀ (c : Prop) [Decidable c] (k : Nat), k < 2 ^ 8 →
        (if c then k else 0).testBit r = false :=
      fun c _ k hk => Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by split <;> omega)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hr, hb, hs _ 1 (by decide), hs _ 0x80 (by decide)]

private theorem getElem!_eq_getD (input : ByteArray) (p : Nat) :
    input[p]! = input.data.toList.getD p 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : p < input.size
  · rw [getElem!_pos input p h, List.getElem?_eq_getElem (by rw [Array.length_toList]; exact h)]
    rfl
  · rw [getElem!_neg input p h,
      List.getElem?_eq_none (by rw [Array.length_toList]; exact Nat.le_of_not_lt h)]
    rfl

private theorem getD_of_size_le (input : ByteArray) (p : Nat) (h : input.size ≤ p) :
    input.data.toList.getD p 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [Array.length_toList]; exact h)]
  rfl

private theorem ofState_absorb (input : ByteArray) :
    Lanes.ofState (absorb input) =
      absorbBlocks Lanes.zero (padded input (input.size / rateBytes + 1))
        (input.size / rateBytes + 1) := by
  have hbyte := padded_byte input (input.size / rateBytes + 1)
  have hfull : ∀ k, k ≤ input.size / rateBytes →
      Lanes.ofState ((List.range' 0 k).foldl
        (fun s i => absorbBlock s (blockAt input (i * rateBytes))) (Vector.replicate 25 0)) =
      absorbBlocks Lanes.zero (padded input (input.size / rateBytes + 1)) k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, absorbBlocks_succ,
        ← ih (by omega)]
      apply ofState_absorbBlock
      intro m hm
      rw [← Nat.shiftRight_add, show 8 * rateBytes * k + 8 * m = 8 * (rateBytes * k + m) by
        rw [Nat.mul_add, Nat.mul_assoc], hbyte _ (Nat.succ_pos _)]
      have h1 : ¬rateBytes * k + m = input.size := by simp only [rateBytes] at hk ⊢; omega
      have h2 : ¬rateBytes * k + m = rateBytes * (input.size / rateBytes + 1) - 1 := by
        simp only [rateBytes] at hk ⊢; omega
      simp only [blockAt, Vector.getElem_ofFn, getElem!_eq_getD, h1, h2, if_false, Nat.or_zero,
        Nat.zero_add, Nat.one_mul, Nat.mul_comm k]
  simp only [absorb, Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, pure_bind, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [absorbBlocks_succ, ← hfull _ (Nat.le_refl _)]
  apply ofState_absorbBlock
  intro m hm
  rw [← Nat.shiftRight_add, show 8 * rateBytes * (input.size / rateBytes) + 8 * m =
    8 * (rateBytes * (input.size / rateBytes) + m) by rw [Nat.mul_add, Nat.mul_assoc],
    hbyte _ (Nat.succ_pos _)]
  simp only [finalBlock, Vector.getElem_ofFn, rateBytes, Nat.mul_comm (input.size / 136) 136]
  have hlast :
      (136 * (input.size / 136) + m = 136 * (input.size / 136 + 1) - 1) = (m = 136 - 1) := by
    simp only [eq_iff_iff]; omega
  simp only [hlast]
  rcases Nat.lt_trichotomy m (input.size - 136 * (input.size / 136)) with h | h | h
  · have h1 : ¬136 * (input.size / 136) + m = input.size := by omega
    have h2 : ¬m = 136 - 1 := by omega
    simp only [if_pos h, if_neg h1, if_neg h2, getElem!_eq_getD, Nat.or_zero]
  · have h0 : ¬m < input.size - 136 * (input.size / 136) := by omega
    have h1 : 136 * (input.size / 136) + m = input.size := by omega
    simp only [if_neg h0, if_pos h, if_pos h1, getD_of_size_le _ _ (Nat.le_of_eq h1.symm)]
    by_cases h3 : m = 136 - 1
    · simp only [if_pos h3]; rfl
    · simp only [if_neg h3]; rfl
  · have h0 : ¬m < input.size - 136 * (input.size / 136) := by omega
    have h1 : ¬m = input.size - 136 * (input.size / 136) := by omega
    have h2 : ¬136 * (input.size / 136) + m = input.size := by omega
    simp only [if_neg h0, if_neg h1, if_neg h2,
      getD_of_size_le input (136 * (input.size / 136) + m) (by omega)]
    by_cases h3 : m = 136 - 1
    · simp only [if_pos h3]; rfl
    · simp only [if_neg h3]; rfl

private theorem toUInt8_shiftRight (w : UInt64) (k : Nat) (hk : k < 64) :
    (w.shiftRight k.toUInt64).toUInt8 = (w.toNat >>> k).toUInt8 := by
  change (w >>> UInt64.ofNat k).toNat.toUInt8 = _
  rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (show k < 2 ^ 64 from Nat.lt_trans hk (by decide)), Nat.mod_eq_of_lt hk]

private theorem encodeDigest_eq (s : State) :
    encodeDigest s = ⟨⟨laneBytes s[0].toNat ++ laneBytes s[1].toNat ++ laneBytes s[2].toNat ++
      laneBytes s[3].toNat⟩⟩ := by
  simp only [encodeDigest, digestBytes]
  refine congrArg ByteArray.mk (Array.ext' ?_)
  simp only [Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, Fin.val_succ, Fin.val_zero,
    Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Fin.getElem_fin, Fin.val_ofNat,
    toUInt8_shiftRight, Nat.reduceLT, Nat.shiftRight_zero, laneBytes, List.cons_append,
    List.nil_append]

/-- `hash` agrees with the reference implementation on every input, so compiled code runs
`referenceHash` in its place. -/
@[csimp] theorem hash_eq_referenceHash : @hash = @referenceHash := by
  funext input
  rw [referenceHash, encodeDigest_eq, hash, ← ofState_absorb]
  rfl

theorem hash_size (input : ByteArray) : (hash input).size = digestBytes := rfl

theorem hash_size_eq_32 (input : ByteArray) : (hash input).size = 32 := rfl

end Ethereum.Keccak256

namespace Ethereum

def KEC := Ethereum.Keccak256.hash

end Ethereum
