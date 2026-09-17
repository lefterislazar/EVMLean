import Ethereum.PerformIO
import Ethereum.PrecompileOutput
import Ethereum.Wheels
import Conform.Wheels

def blobRIP160 (d : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput d
  where pythonCommandOfInput (d : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["Ethereum/EllipticCurvesPy/rip160.py", d]
  }

def RIP160 (d : ByteArray) : Except String ByteArray :=
  Ethereum.checkedPrecompileOutput "RIP160" 32 <|
    ByteArray.ofBlob <| blobRIP160 (toHex d)
