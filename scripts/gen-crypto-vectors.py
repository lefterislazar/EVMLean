#!/usr/bin/env python3
"""
Generate the test vectors of `CryptoTests/Vectors.lean`.

The vectors check the pure Lean cryptographic primitives (`Ethereum/Crypto`)
against independent reference implementations:

- SHA-256 and BLAKE2b (`hashlib`), RIPEMD-160 (`pycryptodome`);
- secp256k1 recovery (`coincurve`, which wraps libsecp256k1);
- secp256r1 verification (`cryptography`, which wraps OpenSSL);
- alt_bn128 and BLS12-381 (`py_ecc`);
- trie roots (the `TrieTests` of the `EthereumTests` submodule).

This script is a development tool only: the model and its tests do not run
Python. Run it from the repository root with the packages of
`requirements.txt` installed:

    python3 scripts/gen-crypto-vectors.py > CryptoTests/Vectors.lean
"""

import hashlib
import json
import random
import struct

import coincurve
from Crypto.Hash import RIPEMD160
from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec, utils
from py_ecc import optimized_bls12_381 as bls
from py_ecc import optimized_bn128 as bn
from py_ecc.bls.hash_to_curve import (
    clear_cofactor_G1,
    clear_cofactor_G2,
    map_to_curve_G1,
    map_to_curve_G2,
)
from py_ecc.bls.point_compression import compress_G1

rng = random.Random(20251025)
vectors = []


def add(name, data, expected):
    """Record a vector; `expected` is bytes, or None when the call fails."""
    vectors.append((name, data.hex(), "error" if expected is None else expected.hex()))


def rand_bytes(n):
    return bytes(rng.getrandbits(8) for _ in range(n))


def u256(x):
    return (x % 2**256).to_bytes(32, "big")


# --- Hashes -----------------------------------------------------------------

for n in [0, 1, 3, 55, 56, 63, 64, 65, 119, 120, 127, 128, 129, 200, 1000]:
    msg = rand_bytes(n)
    add("sha256", msg, hashlib.sha256(msg).digest())
    add("ripemd160", msg, RIPEMD160.new(msg).digest())
add("sha256", b"abc", hashlib.sha256(b"abc").digest())
add("ripemd160", b"abc", RIPEMD160.new(b"abc").digest())

BLAKE2B_IV = [
    0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
    0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179,
]


def blake2f_input(rounds, h, m, t0, t1, f):
    return (struct.pack(">I", rounds) + struct.pack("<8Q", *h) + m.ljust(128, b"\0")
            + struct.pack("<2Q", t0, t1) + bytes([f]))


# A one-block BLAKE2b-512 hash is a single compression with 12 rounds.
for n in [0, 3, 64, 127, 128]:
    msg = rand_bytes(n)
    h = list(BLAKE2B_IV)
    h[0] ^= 0x01010040
    add("blake2f", blake2f_input(12, h, msg, n, 0, 1), hashlib.blake2b(msg).digest())
good = blake2f_input(12, BLAKE2B_IV, b"abc", 3, 0, 1)
add("blake2f", good[:-1], None)
add("blake2f", good + b"\0", None)
add("blake2f", good[:-1] + b"\x02", None)

# --- secp256k1 ----------------------------------------------------------------

SECP256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def recover(e, v, r, s):
    if v > 3:
        return None
    try:
        sig = r.to_bytes(32, "big") + s.to_bytes(32, "big") + bytes([v])
        key = coincurve.PublicKey.from_signature_and_message(sig, e, hasher=None)
        return key.format(compressed=False)[1:]
    except Exception:
        return None


def add_recover(e, v, r, s):
    add("ecrecover", e + bytes([v]) + u256(r) + u256(s), recover(e, v, r, s))


for _ in range(8):
    key = coincurve.PrivateKey(rand_bytes(32))
    e = rand_bytes(32)
    sig = key.sign_recoverable(e, hasher=None)
    r, s, v = int.from_bytes(sig[:32], "big"), int.from_bytes(sig[32:64], "big"), sig[64]
    add_recover(e, v, r, s)
    add_recover(e, v ^ 1, r, s)
    add_recover(e, v + 2, r, s)
add_recover(rand_bytes(32), 0, 0, 1)
add_recover(rand_bytes(32), 0, 1, 0)
add_recover(rand_bytes(32), 0, SECP256K1_N, 1)
add_recover(rand_bytes(32), 0, 1, SECP256K1_N)
add_recover(rand_bytes(32), 4, 1, 1)
for _ in range(4):
    add_recover(rand_bytes(32), rng.randrange(2), rng.randrange(1, SECP256K1_N),
                rng.randrange(1, SECP256K1_N))

# --- secp256r1 ----------------------------------------------------------------

P256_P = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
P256_N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551


def p256_verify(data):
    if len(data) != 160:
        return False
    h = data[:32]
    r, s, x, y = (int.from_bytes(data[i:i + 32], "big") for i in range(32, 160, 32))
    if r == 0 or s == 0 or x >= P256_P or y >= P256_P:
        return False
    try:
        key = ec.EllipticCurvePublicNumbers(x, y, ec.SECP256R1()).public_key()
        key.verify(utils.encode_dss_signature(r, s), h,
                   ec.ECDSA(utils.Prehashed(hashes.SHA256())))
        return True
    except (ValueError, InvalidSignature):
        return False


def add_p256(data):
    add("p256verify", data, u256(1) if p256_verify(data) else b"")


for _ in range(6):
    key = ec.generate_private_key(ec.SECP256R1())
    h = rand_bytes(32)
    r, s = utils.decode_dss_signature(key.sign(h, ec.ECDSA(utils.Prehashed(hashes.SHA256()))))
    pub = key.public_key().public_numbers()
    data = h + u256(r) + u256(s) + u256(pub.x) + u256(pub.y)
    add_p256(data)
    add_p256(data[:31] + bytes([data[31] ^ 1]) + data[32:])
    add_p256(data[:32] + u256(r + P256_N) + data[64:])
    add_p256(data[:-1])
    add_p256(data[:128] + u256(pub.y + 1))
add_p256(bytes(160))

# --- alt_bn128 ----------------------------------------------------------------

BN_P = bn.field_modulus


def bn_g1(x, y):
    if x >= BN_P or y >= BN_P:
        raise ValueError
    if x == 0 and y == 0:
        return bn.Z1
    pt = (bn.FQ(x), bn.FQ(y), bn.FQ.one())
    if not bn.is_on_curve(pt, bn.b):
        raise ValueError
    return pt


def bn_enc(pt):
    if bn.is_inf(pt):
        return bytes(64)
    x, y = bn.normalize(pt)
    return u256(int(x)) + u256(int(y))


def bn_g1_bytes(pt):
    return bn_enc(pt)


def bn_g2_bytes(pt):
    if bn.is_inf(pt):
        return bytes(128)
    x, y = bn.normalize(pt)
    return u256(x.coeffs[1]) + u256(x.coeffs[0]) + u256(y.coeffs[1]) + u256(y.coeffs[0])


def bn_add(data):
    try:
        v = [int.from_bytes(data[i:i + 32], "big") for i in range(0, 128, 32)]
        return bn_enc(bn.add(bn_g1(v[0], v[1]), bn_g1(v[2], v[3])))
    except ValueError:
        return None


def bn_mul(data):
    try:
        v = [int.from_bytes(data[i:i + 32], "big") for i in range(0, 96, 32)]
        return bn_enc(bn.multiply(bn_g1(v[0], v[1]), v[2]))
    except ValueError:
        return None


def bn_pairing(data):
    if len(data) % 192:
        return None
    product = bn.FQ12.one()
    for i in range(0, len(data), 192):
        v = [int.from_bytes(data[i + j:i + j + 32], "big") for j in range(0, 192, 32)]
        if any(x >= BN_P for x in v):
            return None
        try:
            p = bn_g1(v[0], v[1])
        except ValueError:
            return None
        if v[2:] == [0, 0, 0, 0]:
            q = bn.Z2
        else:
            q = (bn.FQ2([v[3], v[2]]), bn.FQ2([v[5], v[4]]), bn.FQ2.one())
            if not bn.is_on_curve(q, bn.b2):
                return None
        if not bn.is_inf(bn.multiply(q, bn.curve_order)):
            return None
        if not bn.is_inf(p) and not bn.is_inf(q):
            product *= bn.pairing(q, p, final_exponentiate=False)
    return u256(1 if bn.final_exponentiate(product) == bn.FQ12.one() else 0)


for _ in range(4):
    a, b = rng.randrange(bn.curve_order), rng.randrange(bn.curve_order)
    pa, pb = bn.multiply(bn.G1, a), bn.multiply(bn.G1, b)
    for data in [bn_g1_bytes(pa) + bn_g1_bytes(pb), bn_g1_bytes(pa) + bn_g1_bytes(pa),
                 bn_g1_bytes(pa) + bn_g1_bytes(bn.neg(pa)), bytes(64) + bn_g1_bytes(pb)]:
        add("bn_add", data, bn_add(data))
    data = bn_g1_bytes(pa) + u256(b)
    add("bn_mul", data, bn_mul(data))
for data in [bytes(128), u256(1) + u256(2) + u256(1) + u256(3), u256(BN_P) + u256(0) + bytes(64)]:
    add("bn_add", data, bn_add(data))
for data in [u256(1) + u256(2) + u256(2**256 - 1), u256(1) + u256(2) + u256(bn.curve_order),
             u256(1) + u256(3) + u256(2), bytes(64) + u256(5)]:
    add("bn_mul", data, bn_mul(data))

a, b = rng.randrange(bn.curve_order), rng.randrange(bn.curve_order)
pairing_inputs = [
    b"",
    bn_g1_bytes(bn.multiply(bn.G1, a)) + bn_g2_bytes(bn.multiply(bn.G2, b))
    + bn_g1_bytes(bn.neg(bn.multiply(bn.G1, a * b))) + bn_g2_bytes(bn.G2),
    bn_g1_bytes(bn.multiply(bn.G1, a)) + bn_g2_bytes(bn.multiply(bn.G2, b))
    + bn_g1_bytes(bn.neg(bn.multiply(bn.G1, a * b + 1))) + bn_g2_bytes(bn.G2),
    bn_g1_bytes(bn.G1) + bn_g2_bytes(bn.G2),
    bytes(64) + bn_g2_bytes(bn.G2),
    bn_g1_bytes(bn.G1) + bytes(128),
    bn_g1_bytes(bn.G1) + bn_g2_bytes(bn.G2)[:-1] + b"\x00",
    bn_g1_bytes(bn.G1) + bn_g2_bytes(bn.G2)[:-1],
]
for data in pairing_inputs:
    add("bn_pairing", data, bn_pairing(data))

# --- BLS12-381 (EIP-2537) -----------------------------------------------------

BLS_P = bls.field_modulus


def fq(raw):
    if len(raw) != 64 or any(raw[:16]):
        raise ValueError
    value = int.from_bytes(raw, "big")
    if value >= BLS_P:
        raise ValueError
    return value


def g1(raw, subgroup=True):
    x, y = fq(raw[:64]), fq(raw[64:])
    if x == 0 and y == 0:
        return bls.Z1
    pt = (bls.FQ(x), bls.FQ(y), bls.FQ.one())
    if not bls.is_on_curve(pt, bls.b):
        raise ValueError
    if subgroup and not bls.is_inf(bls.multiply(pt, bls.curve_order)):
        raise ValueError
    return pt


def g2(raw, subgroup=True):
    xr, xi, yr, yi = (fq(raw[i:i + 64]) for i in range(0, 256, 64))
    if xr == xi == yr == yi == 0:
        return bls.Z2
    pt = (bls.FQ2([xr, xi]), bls.FQ2([yr, yi]), bls.FQ2.one())
    if not bls.is_on_curve(pt, bls.b2):
        raise ValueError
    if subgroup and not bls.is_inf(bls.multiply(pt, bls.curve_order)):
        raise ValueError
    return pt


def enc_fq(v):
    return int(v).to_bytes(64, "big")


def enc_g1(pt):
    if bls.is_inf(pt):
        return bytes(128)
    x, y = bls.normalize(pt)
    return enc_fq(x) + enc_fq(y)


def enc_g2(pt):
    if bls.is_inf(pt):
        return bytes(256)
    x, y = bls.normalize(pt)
    return enc_fq(x.coeffs[0]) + enc_fq(x.coeffs[1]) + enc_fq(y.coeffs[0]) + enc_fq(y.coeffs[1])


def bls_run(op, data):
    if op == 11 and len(data) == 256:
        return enc_g1(bls.add(g1(data[:128], False), g1(data[128:], False)))
    if op == 12 and len(data) and len(data) % 160 == 0:
        acc = bls.Z1
        for i in range(0, len(data), 160):
            acc = bls.add(acc, bls.multiply(g1(data[i:i + 128]),
                                            int.from_bytes(data[i + 128:i + 160], "big")))
        return enc_g1(acc)
    if op == 13 and len(data) == 512:
        return enc_g2(bls.add(g2(data[:256], False), g2(data[256:], False)))
    if op == 14 and len(data) and len(data) % 288 == 0:
        acc = bls.Z2
        for i in range(0, len(data), 288):
            acc = bls.add(acc, bls.multiply(g2(data[i:i + 256]),
                                            int.from_bytes(data[i + 256:i + 288], "big")))
        return enc_g2(acc)
    if op == 15 and len(data) and len(data) % 384 == 0:
        product = bls.FQ12.one()
        for i in range(0, len(data), 384):
            product *= bls.pairing(g2(data[i + 128:i + 384]), g1(data[i:i + 128]),
                                   final_exponentiate=False)
        return u256(1 if bls.final_exponentiate(product) == bls.FQ12.one() else 0)
    if op == 16 and len(data) == 64:
        return enc_g1(clear_cofactor_G1(map_to_curve_G1(bls.FQ(fq(data)))))
    if op == 17 and len(data) == 128:
        return enc_g2(clear_cofactor_G2(map_to_curve_G2(bls.FQ2([fq(data[:64]), fq(data[64:])]))))
    raise ValueError


def add_bls(op, data):
    try:
        expected = bls_run(op, data)
    except ValueError:
        expected = None
    add(f"bls_{op}", data, expected)


def rand_g1():
    return bls.multiply(bls.G1, rng.randrange(1, bls.curve_order))


def rand_g2():
    return bls.multiply(bls.G2, rng.randrange(1, bls.curve_order))


# A point on E but not in G₁: (x, y) for the smallest x with x³ + 4 a square.
def off_subgroup_g1():
    x = 1
    while True:
        rhs = (x ** 3 + 4) % BLS_P
        y = pow(rhs, (BLS_P + 1) // 4, BLS_P)
        if y * y % BLS_P == rhs:
            return enc_fq(x) + enc_fq(y)
        x += 1


for _ in range(3):
    p1, p2 = rand_g1(), rand_g1()
    add_bls(11, enc_g1(p1) + enc_g1(p2))
    add_bls(11, enc_g1(p1) + enc_g1(p1))
    add_bls(11, enc_g1(p1) + enc_g1(bls.neg(p1)))
    q1, q2 = rand_g2(), rand_g2()
    add_bls(13, enc_g2(q1) + enc_g2(q2))
    add_bls(13, enc_g2(q1) + bytes(256))
    add_bls(12, enc_g1(p1) + u256(rng.getrandbits(256)) + enc_g1(p2) + u256(rng.getrandbits(256)))
    add_bls(14, enc_g2(q1) + u256(rng.getrandbits(256)))
    add_bls(16, enc_fq(rng.randrange(BLS_P)))
    add_bls(17, enc_fq(rng.randrange(BLS_P)) + enc_fq(rng.randrange(BLS_P)))
add_bls(11, off_subgroup_g1() + enc_g1(bls.G1))
add_bls(12, off_subgroup_g1() + u256(1))
add_bls(11, enc_fq(1) + enc_fq(1) + bytes(128))
add_bls(11, enc_fq(BLS_P) + enc_fq(0) + bytes(128))
add_bls(11, b"\x01" + enc_g1(bls.G1)[1:] + bytes(128))
add_bls(12, enc_g1(bls.G1) + u256(bls.curve_order))
add_bls(16, enc_fq(0))
add_bls(16, enc_fq(1))
add_bls(16, enc_fq(BLS_P))
add_bls(17, enc_fq(0) + enc_fq(0))
add_bls(17, enc_fq(1) + enc_fq(0))
a, b = rng.randrange(bls.curve_order), rng.randrange(bls.curve_order)
add_bls(15, enc_g1(bls.multiply(bls.G1, a)) + enc_g2(bls.multiply(bls.G2, b))
        + enc_g1(bls.neg(bls.multiply(bls.G1, a * b))) + enc_g2(bls.G2))
add_bls(15, enc_g1(bls.multiply(bls.G1, a)) + enc_g2(bls.multiply(bls.G2, b))
        + enc_g1(bls.neg(bls.multiply(bls.G1, a * b + 1))) + enc_g2(bls.G2))
add_bls(15, enc_g1(bls.G1) + enc_g2(bls.G2))
add_bls(15, bytes(128) + enc_g2(bls.G2))
add_bls(15, off_subgroup_g1() + enc_g2(bls.G2))

# --- KZG point evaluation -----------------------------------------------------
# Without the G₁ setup we cannot build proofs of nonzero polynomials; the zero
# polynomial (commitment and proof at infinity) proves p(z) = 0 for every z.

BLS_R = bls.curve_order
INFINITY = b"\xc0" + bytes(47)
OUTPUT = u256(4096) + u256(BLS_R)


def versioned(commitment):
    return b"\x01" + hashlib.sha256(commitment).digest()[1:]


z = rng.randrange(BLS_R)
add("kzg", versioned(INFINITY) + u256(z) + u256(0) + INFINITY + INFINITY, OUTPUT)
add("kzg", versioned(INFINITY) + u256(z) + u256(1) + INFINITY + INFINITY, None)
add("kzg", versioned(INFINITY) + u256(BLS_R) + u256(0) + INFINITY + INFINITY, None)
add("kzg", b"\x02" + versioned(INFINITY)[1:] + u256(z) + u256(0) + INFINITY + INFINITY, None)
add("kzg", versioned(INFINITY) + u256(z) + u256(0) + INFINITY + INFINITY[:-1], None)
g1c = compress_G1(bls.G1).to_bytes(48, "big")
add("kzg", versioned(g1c) + u256(z) + u256(0) + g1c + INFINITY, None)
add("kzg", versioned(INFINITY) + u256(z) + u256(0) + INFINITY + b"\xe0" + bytes(47), None)

# --- Trie roots ---------------------------------------------------------------


def trie_bytes(s):
    if s is None:
        return None
    return bytes.fromhex(s[2:]) if s.startswith("0x") else s.encode()


def rlp_bytes(b):
    if len(b) == 1 and b[0] < 0x80:
        return b
    return rlp_len(len(b), 0x80) + b


def rlp_len(n, offset):
    if n < 56:
        return bytes([offset + n])
    nb = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([offset + 55 + len(nb)]) + nb


def rlp_list(items):
    payload = b"".join(items)
    return rlp_len(len(payload), 0xC0) + payload


def add_trie(entries, root):
    data = rlp_list([rlp_list([rlp_bytes(k), rlp_bytes(v)]) for k, v in entries.items()])
    add("trie", data, bytes.fromhex(root[2:]))


with open("EthereumTests/TrieTests/trieanyorder.json") as f:
    for test in json.load(f).values():
        add_trie({trie_bytes(k): trie_bytes(v) for k, v in test["in"].items()}, test["root"])
with open("EthereumTests/TrieTests/trietest.json") as f:
    for test in json.load(f).values():
        entries = {}
        for k, v in test["in"]:
            k, v = trie_bytes(k), trie_bytes(v)
            if v:
                entries[k] = v
            else:
                entries.pop(k, None)
        add_trie(entries, test["root"])

# --- Output -------------------------------------------------------------------

print("""/-!
Generated by `scripts/gen-crypto-vectors.py`; do not edit.

Each vector is `(primitive, input, expected output)` in hex, with `error`
for a failing call.
-/

namespace CryptoTests

def vectors : Array (String × String × String) := #[""")
print(",\n".join(f'  ("{n}", "{i}", "{o}")' for n, i, o in vectors))
print("]\n\nend CryptoTests")
