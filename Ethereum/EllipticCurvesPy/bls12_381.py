import sys

from py_ecc.optimized_bls12_381 import (
    FQ, FQ2, FQ12, Z1, Z2, add, b, b2, curve_order, field_modulus,
    final_exponentiate, is_inf, is_on_curve, multiply, normalize, pairing,
)
from py_ecc.bls.hash_to_curve import (
    clear_cofactor_G1,
    clear_cofactor_G2,
    map_to_curve_G1,
    map_to_curve_G2,
)


def fq(raw: bytes) -> int:
    if len(raw) != 64 or any(raw[:16]):
        raise ValueError("non-canonical field element")
    value = int.from_bytes(raw, "big")
    if value >= field_modulus:
        raise ValueError("field element out of range")
    return value


def g1(raw: bytes, subgroup=True):
    if len(raw) != 128:
        raise ValueError("bad G1 length")
    x, y = fq(raw[:64]), fq(raw[64:])
    if x == 0 and y == 0:
        return Z1
    point = (FQ(x), FQ(y), FQ.one())
    if not is_on_curve(point, b):
        raise ValueError("G1 point not on curve")
    if subgroup and not is_inf(multiply(point, curve_order)):
        raise ValueError("G1 point not in subgroup")
    return point


def g2(raw: bytes, subgroup=True):
    if len(raw) != 256:
        raise ValueError("bad G2 length")
    xr, xi, yr, yi = (fq(raw[i:i + 64]) for i in range(0, 256, 64))
    if xr == xi == yr == yi == 0:
        return Z2
    point = (FQ2([xr, xi]), FQ2([yr, yi]), FQ2.one())
    if not is_on_curve(point, b2):
        raise ValueError("G2 point not on curve")
    if subgroup and not is_inf(multiply(point, curve_order)):
        raise ValueError("G2 point not in subgroup")
    return point


def enc_fq(value) -> bytes:
    return int(value).to_bytes(64, "big")


def enc_g1(point) -> bytes:
    if is_inf(point):
        return bytes(128)
    x, y = normalize(point)
    return enc_fq(x) + enc_fq(y)


def enc_g2(point) -> bytes:
    if is_inf(point):
        return bytes(256)
    x, y = normalize(point)
    return enc_fq(x.coeffs[0]) + enc_fq(x.coeffs[1]) + enc_fq(y.coeffs[0]) + enc_fq(y.coeffs[1])


def run(operation: int, data: bytes) -> bytes:
    if operation == 11:
        if len(data) != 256:
            raise ValueError("bad G1ADD length")
        return enc_g1(add(g1(data[:128], False), g1(data[128:], False)))
    if operation == 12:
        if len(data) == 0 or len(data) % 160:
            raise ValueError("bad G1MSM length")
        result = Z1
        for i in range(0, len(data), 160):
            result = add(result, multiply(g1(data[i:i + 128]), int.from_bytes(data[i + 128:i + 160], "big")))
        return enc_g1(result)
    if operation == 13:
        if len(data) != 512:
            raise ValueError("bad G2ADD length")
        return enc_g2(add(g2(data[:256], False), g2(data[256:], False)))
    if operation == 14:
        if len(data) == 0 or len(data) % 288:
            raise ValueError("bad G2MSM length")
        result = Z2
        for i in range(0, len(data), 288):
            result = add(result, multiply(g2(data[i:i + 256]), int.from_bytes(data[i + 256:i + 288], "big")))
        return enc_g2(result)
    if operation == 15:
        if len(data) == 0 or len(data) % 384:
            raise ValueError("bad pairing length")
        product = FQ12.one()
        for i in range(0, len(data), 384):
            product *= pairing(g2(data[i + 128:i + 384]), g1(data[i:i + 128]), final_exponentiate=False)
        valid = final_exponentiate(product) == FQ12.one()
        return bytes(31) + bytes([1 if valid else 0])
    if operation == 16:
        if len(data) != 64:
            raise ValueError("bad MAP_FP_TO_G1 length")
        return enc_g1(clear_cofactor_G1(map_to_curve_G1(FQ(fq(data)))))
    if operation == 17:
        if len(data) != 128:
            raise ValueError("bad MAP_FP2_TO_G2 length")
        real, imaginary = fq(data[:64]), fq(data[64:])
        return enc_g2(clear_cofactor_G2(map_to_curve_G2(FQ2([real, imaginary]))))
    raise ValueError("unknown operation")


if __name__ == "__main__":
    try:
        encoded = sys.argv[2] if len(sys.argv) > 2 else sys.stdin.read().strip()
        print(run(int(sys.argv[1]), bytes.fromhex(encoded)).hex())
    except Exception:
        print("error")
