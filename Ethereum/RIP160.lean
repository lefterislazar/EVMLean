import Ethereum.PerformIO
import Ethereum.PrecompileOutput
import Ethereum.Wheels

def blobRIP160 (d : String) : String :=
  totallySafePerformIO <|
    Ethereum.PythonHelper.run "rip160.py" #[] d

def RIP160 (d : ByteArray) : Except String ByteArray :=
  Ethereum.checkedPrecompileOutput "RIP160" 32 <|
    ByteArray.ofBlob <| blobRIP160 (toHex d)
