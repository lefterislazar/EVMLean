import Ethereum.Crypto.BLS12_381

/--
Whether `size` is a valid input length for the EIP-2537 precompile at address
`operation`: a fixed length for the additions and the mappings, and a nonzero
multiple of the pair length for the multi-scalar multiplications and the
pairing. Any other length makes the call fail.
-/
def blsInputLengthValid (operation size : Nat) : Bool :=
  match operation with
  | 11 => size == 256
  | 12 => size != 0 && size % 160 == 0
  | 13 => size == 512
  | 14 => size != 0 && size % 288 == 0
  | 15 => size != 0 && size % 384 == 0
  | 16 => size == 64
  | 17 => size == 128
  | _ => false

/--
The EIP-2537 BLS12-381 precompile at address `operation` (`0x0b`–`0x11`).
The input length is checked here, before the curve operations, which check
it again.
-/
def BLS12_381 (operation : Nat) (data : ByteArray) : Except String ByteArray :=
  if !blsInputLengthValid operation data.size then
    .error "BLS12-381: invalid input length"
  else
    match Ethereum.Crypto.BLS12_381.precompile operation data with
    | some output => .ok output
    | none => .error "BLS12-381 operation failed"

/-- Output size of the EIP-2537 precompile at address `operation`. -/
abbrev blsOutputSize : Nat → Nat := Ethereum.Crypto.BLS12_381.outputSize

/-- A successful BLS12-381 result has the size prescribed for its operation. -/
theorem BLS12_381_ok_size {operation : Nat} {data out : ByteArray}
    (h : BLS12_381 operation data = .ok out) : out.size = blsOutputSize operation := by
  unfold BLS12_381 at h
  split at h
  · cases h
  · split at h
    · cases h; exact Ethereum.Crypto.BLS12_381.precompile_size ‹_›
    · cases h
