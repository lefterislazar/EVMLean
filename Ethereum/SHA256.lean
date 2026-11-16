import Ethereum.PerformIO
import Ethereum.Wheels

def blobSHA256 (d : String) : String :=
  totallySafePerformIO <|
    Ethereum.PythonHelper.run "sha256.py" #[d]

def SHA256 (d : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobSHA256 (toHex d)
