import Ethereum.Wheels
import Ethereum.PerformIO
import Ethereum.PrecompileOutput

def blobSNARKV (data : String) : String :=
  totallySafePerformIO <|
    Ethereum.PythonHelper.run "snarkv.py" #[] data

def SNARKV (data : ByteArray) : Except String ByteArray :=
  Ethereum.checkedPrecompileOutput "SNARKV" 32 <| match blobSNARKV (toHex data) with
    | "error" => .error "SNARKV failed"
    | s => ByteArray.ofBlob s
