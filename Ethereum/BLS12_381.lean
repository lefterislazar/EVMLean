import Ethereum.PerformIO
import Ethereum.PrecompileOutput
import Ethereum.Wheels

def blobBLS12_381 (operation : Nat) (data : String) : String :=
  totallySafePerformIO <|
    Ethereum.PythonHelper.run "bls12_381.py" #[toString operation] data

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
The input length is checked here, in Lean, before the external
implementation runs; the external implementation checks it again.
-/
def BLS12_381 (operation expectedSize : Nat) (data : ByteArray) : Except String ByteArray :=
  if !blsInputLengthValid operation data.size then
    .error "BLS12-381: invalid input length"
  else
  Ethereum.checkedPrecompileOutput s!"BLS12_381_{operation}" expectedSize <|
    match blobBLS12_381 operation (toHex data) with
    | "error" => .error "BLS12-381 operation failed"
    | output => ByteArray.ofBlob output

/-- A successful BLS12-381 result has the expected size. -/
theorem BLS12_381_ok_size {operation expectedSize : Nat} {data out : ByteArray}
    (h : BLS12_381 operation expectedSize data = .ok out) : out.size = expectedSize := by
  unfold BLS12_381 at h
  split at h
  · cases h
  · exact Ethereum.checkedPrecompileOutput_ok_size h
