/-!
Pure Lean implementation of the Keccak-256 function used by Ethereum.

The lane layout, rotations, and round constants below follow the published
Keccak-f[1600] specification. Keccak lanes and the sponge byte stream are
little endian. Ethereum uses the original Keccak domain suffix (`0x01`), not
the later SHA3 suffix (`0x06`).
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

/-- Ethereum Keccak-256 with the legacy `0x01` domain suffix. -/
def hash (input : ByteArray) : ByteArray :=
  encodeDigest (absorb input)

theorem hash_size (input : ByteArray) : (hash input).size = digestBytes := by
  unfold hash encodeDigest
  exact Array.size_ofFn

theorem hash_size_eq_32 (input : ByteArray) : (hash input).size = 32 := by
  simpa [digestBytes] using hash_size input

end Ethereum.Keccak256

namespace Ethereum

def KEC := Ethereum.Keccak256.hash

end Ethereum
