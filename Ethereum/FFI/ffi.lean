import Ethereum.PrecompileOutput

namespace ffi

@[extern "sha256"]
opaque sha256 (input : @& ByteArray) (len : USize) : ByteArray

def SHA256 (d : ByteArray) : Except String ByteArray :=
  Ethereum.checkedPrecompileOutput "SHA256" 32 <|
    .ok (sha256 d d.size.toUSize)

@[extern "blake2compressb64"]
opaque BLAKE2Compress (input : @& ByteArray) : ByteArray

def BLAKE2 (d : ByteArray) : Except String ByteArray := do
  if d.size != 213                    then throw "error"
  if d[212]! ∉ [0, 1].map Nat.toUInt8 then throw "error"
  Ethereum.checkedPrecompileOutput "BLAKE2" 64 <|
    .ok (BLAKE2Compress d)

/- Replaced with transparent version in Wheels
   Slight performance impact, but reduced trust surface -/
-- @[extern "memset_zero"]
-- opaque ByteArray.zeroes (n : USize) : ByteArray

end ffi
