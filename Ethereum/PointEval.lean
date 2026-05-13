import Ethereum.Wheels
import Ethereum.PerformIO
import Conform.Wheels

def blobPointEval (data : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["Ethereum/EllipticCurvesPy/point_evaluation.py", data]
  }

def PointEval (data : ByteArray) : Except String ByteArray :=
  match blobPointEval (toHex data) with
    | "error" => .error "PointEval failed"
    | s => ByteArray.ofBlob s
