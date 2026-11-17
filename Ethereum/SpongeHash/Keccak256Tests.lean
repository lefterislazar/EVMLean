import Ethereum.SpongeHash.Keccak256

namespace Ethereum.Keccak256Tests

private def hex (bytes : ByteArray) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList <| bytes.data.toList.flatMap fun byte =>
    [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!]

-- Expected digests use Ethereum Keccak-256, not SHA3-256.
-- Generated independently with Foundry cast keccak.

#guard hex (KEC ByteArray.empty) ==
  "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

#guard hex (KEC "abc".toUTF8) ==
  "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"

#guard hex (KEC "transfer(address,uint256)".toUTF8) ==
  "a9059cbb2ab09eb219583f4a59a5d0623ade346d962bcd4e46b11da047c9049b"

-- Check both sides of the 136-byte rate and the next full block.
private def input (size : Nat) : ByteArray :=
  ⟨(Array.range size).map Nat.toUInt8⟩

#guard hex (KEC (input 1)) ==
  "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a"

#guard hex (KEC (input 134)) ==
  "861e165162f806cd361c4421a48f205820ddf4deb02db9f041f48e179ddada97"

#guard hex (KEC (input 135)) ==
  "cbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62"

#guard hex (KEC (input 136)) ==
  "7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e"

#guard hex (KEC (input 137)) ==
  "ac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db"

#guard hex (KEC (input 271)) ==
  "7c974895b2a88303ff2dc6b58f438ceb0b298cac91099ac0539cc0f477506191"

#guard hex (KEC (input 272)) ==
  "fdf2ec49e749960d3c8521a0219af8d03e30e2b3bf19bd16150ee0eaf133d66e"

#guard hex (KEC (input 273)) ==
  "4f707289a9c3ccd0c4a51f2f17339f5dd171d371c04ff7783b735b5b22682eaf"

-- `KEC` also evaluates in the kernel, as proofs about concrete hashes require.

example : KEC ByteArray.empty = ⟨#[
    0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
    0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
    0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
    0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70]⟩ := by
  decide +kernel

example : (KEC "transfer(address,uint256)".toUTF8).extract 0 4 = ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ := by
  decide +kernel

-- The suffix and the final bit share the last byte of the block (`0x81`).
example : KEC ⟨Array.replicate 135 0x61⟩ = ⟨#[
    0x34, 0x36, 0x7d, 0xc2, 0x48, 0xbb, 0xd8, 0x32,
    0xf4, 0xe3, 0xe6, 0x9d, 0xfa, 0xac, 0x2f, 0x92,
    0x63, 0x8b, 0xd0, 0xbb, 0xd1, 0x8f, 0x29, 0x12,
    0xba, 0x4e, 0xf4, 0x54, 0x91, 0x9c, 0xf4, 0x46]⟩ := by
  decide +kernel

-- A full block is followed by a block of padding alone.
example : KEC ⟨Array.replicate 136 0x61⟩ = ⟨#[
    0xa6, 0xc4, 0xd4, 0x03, 0x27, 0x9f, 0xe3, 0xe0,
    0xaf, 0x03, 0x72, 0x9c, 0xaa, 0xda, 0x83, 0x74,
    0xb5, 0xca, 0x54, 0xd8, 0x06, 0x53, 0x29, 0xa3,
    0xeb, 0xca, 0xeb, 0x4b, 0x60, 0xaa, 0x38, 0x6e]⟩ := by
  decide +kernel

end Ethereum.Keccak256Tests
