import Ethereum.Crypto.P256
import Ethereum.Wheels

/--
EIP-7951 `P256VERIFY` (Osaka). A valid signature yields the 32-byte word `1`;
any invalid input yields empty output. Both outcomes are successful calls.
-/
def P256Verify (data : ByteArray) : Except String ByteArray :=
  if Ethereum.Crypto.P256.verifyInput data then .ok (ByteArray.zeroes 31 ++ ⟨#[1]⟩)
  else .ok .empty
