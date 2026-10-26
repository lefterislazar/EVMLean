import Ethereum.Crypto.Secp256k1

def secp256k1n : Nat := 115792089237316195423570985008687907852837564279074904382605163141518161494337

-- Appendix F. Signing Transactions

/-- `ECDSARECOVER(e, v, r, s)`: the 64-byte public key that signed the hash `e`
    with recovery id `v` and signature `(r, s)`. -/
def ECDSARECOVER (e v r s : ByteArray) : Except String ByteArray :=
  Ethereum.Crypto.Secp256k1.ecdsaRecover e v r s
