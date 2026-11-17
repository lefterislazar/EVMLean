import Ethereum.Wheels
import Ethereum.PerformIO
import Ethereum.PrecompileOutput

def blobBN_ADD (x₀ y₀ x₁ y₁ : String) : String :=
  totallySafePerformIO <|
    Ethereum.PythonHelper.run "bn_add.py" #[x₀, y₀, x₁, y₁]

def BN_ADD (x₀ y₀ x₁ y₁ : ByteArray) : Except String ByteArray :=
  Ethereum.checkedPrecompileOutput "BN_ADD" 64 <| match
      blobBN_ADD (toHex x₀) (toHex y₀) (toHex x₁) (toHex y₁) with
    | "error" => .error "BN_ADD failed"
    | s => ByteArray.ofBlob s
