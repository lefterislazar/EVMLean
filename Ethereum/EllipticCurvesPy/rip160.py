import sys

from Crypto.Hash import RIPEMD160

data = bytes.fromhex(sys.argv[1])
digest = RIPEMD160.new(data=data).digest()
print(digest.rjust(32, b"\x00").hex(), end="")
