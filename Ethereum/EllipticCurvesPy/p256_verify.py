import sys

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec, utils

P256_FIELD_MODULUS = (
    0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
)


def verify(data: bytes) -> bool:
    if len(data) != 160:
        return False
    message_hash = data[0:32]
    r = int.from_bytes(data[32:64], "big")
    s = int.from_bytes(data[64:96], "big")
    x = int.from_bytes(data[96:128], "big")
    y = int.from_bytes(data[128:160], "big")
    if r == 0 or s == 0:
        return False
    # OpenSSL accepts some non-canonical coordinates by reducing them modulo
    # the field prime.  EIP-7951 requires the encoded coordinates themselves
    # to be canonical field elements.
    if x >= P256_FIELD_MODULUS or y >= P256_FIELD_MODULUS:
        return False
    try:
        public_key = ec.EllipticCurvePublicNumbers(x, y, ec.SECP256R1()).public_key()
        signature = utils.encode_dss_signature(r, s)
        public_key.verify(
            signature, message_hash, ec.ECDSA(utils.Prehashed(hashes.SHA256()))
        )
        return True
    except (ValueError, InvalidSignature):
        return False


if __name__ == "__main__":
    try:
        encoded = sys.argv[1] if len(sys.argv) > 1 else sys.stdin.read().strip()
        raw = bytes.fromhex(encoded)
        print("01" if verify(raw) else "invalid")
    except Exception:
        print("error")
