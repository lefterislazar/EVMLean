import Ethereum.PerformIO
import Ethereum.Wheels
import Conform.Wheels

def blobSHA256 (d : String) : String :=
  dbg_trace s!"Ethereum/EllipticCurvesPy/sha256.py"
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput d
  where pythonCommandOfInput (d : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["Ethereum/EllipticCurvesPy/sha256.py", d]
  }

def SHA256 (d : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobSHA256 (toHex d)
