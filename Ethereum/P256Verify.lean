import Ethereum.PerformIO
import Ethereum.Wheels

def blobP256Verify (data : String) : String :=
  totallySafePerformIO <|
    Ethereum.PythonHelper.run "p256_verify.py" #[] data

/--
EIP-7951 `P256VERIFY` (Osaka). A valid signature yields the 32-byte word `1`;
any invalid input yields empty output. Both outcomes are successful calls.
-/
def P256Verify (data : ByteArray) : Except String ByteArray :=
  match blobP256Verify (toHex data) with
  | "01" => .ok (ByteArray.zeroes 31 ++ ⟨#[1]⟩)
  | "invalid" => .ok .empty
  | _ => .error "P256Verify helper failed"
