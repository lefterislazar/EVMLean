import Ethereum.Wheels
import Ethereum.PerformIO
import Conform.Wheels

def blobBLAKE2_F (data : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["Ethereum/EllipticCurvesPy/blake2_f.py", data]
  }

def BLAKE2_F (data : ByteArray) : Except String ByteArray :=
  match blobBLAKE2_F (toHex data) with
    | "error" => .error "BLAKE2_F failed"
    | s => ByteArray.ofBlob s
