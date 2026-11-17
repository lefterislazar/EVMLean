import Ethereum.Wheels
import Ethereum.PerformIO

def blobBLAKE2_F (data : String) : String :=
  totallySafePerformIO <|
    Ethereum.PythonHelper.run "blake2_f.py" #[data]

def BLAKE2_F (data : ByteArray) : Except String ByteArray :=
  match blobBLAKE2_F (toHex data) with
    | "error" => .error "BLAKE2_F failed"
    | s => ByteArray.ofBlob s
