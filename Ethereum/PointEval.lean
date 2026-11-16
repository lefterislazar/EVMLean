import Ethereum.Wheels
import Ethereum.PerformIO
import Ethereum.PrecompileOutput

def blobPointEval (data : String) : String :=
  totallySafePerformIO <|
    Ethereum.PythonHelper.run "point_evaluation.py" #[data]

def PointEval (data : ByteArray) : Except String ByteArray :=
  Ethereum.checkedPrecompileOutput "PointEval" 64 <| match blobPointEval (toHex data) with
    | "error" => .error "PointEval failed"
    | s => ByteArray.ofBlob s
