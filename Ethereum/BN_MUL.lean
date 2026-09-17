import Ethereum.Wheels
import Ethereum.PerformIO
import Ethereum.PrecompileOutput
import Conform.Wheels

def blobBN_MUL (x₀ y₀ n : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput x₀ y₀ n
  where pythonCommandOfInput (x₀ y₀ n : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["Ethereum/EllipticCurvesPy/bn_mul.py", x₀, y₀, n]
  }

def BN_MUL (x₀ y₀ n : ByteArray) : Except String ByteArray :=
  Ethereum.checkedPrecompileOutput "BN_MUL" 64 <| match
      blobBN_MUL (toHex x₀) (toHex y₀) (toHex n) with
    | "error" => .error "BN_MUL failed"
    | s => ByteArray.ofBlob s
