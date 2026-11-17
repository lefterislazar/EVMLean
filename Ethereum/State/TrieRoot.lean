import Ethereum.Wheels

/-!
# Merkle Patricia trie roots

The root of the (unsecured) Merkle Patricia trie of a set of key/value pairs,
as in Appendix D of the Yellow Paper and `trie.py` of the execution specs.
Keys are used as given, so callers hash them first for secure tries.

The pairs are sorted by key; the keys below a node then form a contiguous
range, and each node is built from its range.
-/

namespace Ethereum.Trie

/-- A key as nibbles, with its value. -/
private abbrev Entry := Array UInt8 × ByteArray

private instance : Inhabited 𝕋 := ⟨.𝔹 .empty⟩

private def nibbles (key : ByteArray) : Array UInt8 :=
  key.foldl (fun acc b => acc.push (b >>> 4) |>.push (b &&& 0x0f)) (Array.mkEmpty (2 * key.size))

/-- The hex-prefix encoding of the nibbles `ns`, flagged as a leaf or an
    extension. -/
private def compact (ns : Array UInt8) (isLeaf : Bool) : ByteArray := Id.run do
  let flag : UInt8 := if isLeaf then 2 else 0
  let mut out := ByteArray.emptyWithCapacity (ns.size / 2 + 1)
  let mut i := 0
  if ns.size % 2 == 1 then
    out := out.push (((flag + 1) <<< 4) ||| ns[0]!)
    i := 1
  else
    out := out.push (flag <<< 4)
  while i + 1 < ns.size do
    out := out.push ((ns[i]! <<< 4) ||| ns[i + 1]!)
    i := i + 2
  return out

private def rlp (t : 𝕋) : ByteArray := (RLP t).getD .empty

/-- A node as it appears inside its parent: inline when its encoding is
    shorter than 32 bytes, and as the hash of its encoding otherwise. -/
private def reference (node : 𝕋) : 𝕋 :=
  let encoded := rlp node
  if encoded.size < 32 then node else .𝔹 (KEC encoded)

/-- The length of the common prefix of `a` and `b` from position `level`. -/
private def commonPrefix (a b : Array UInt8) (level : Nat) : Nat := Id.run do
  let mut n := 0
  while level + n < a.size && level + n < b.size && a[level + n]! == b[level + n]! do
    n := n + 1
  return n

/-- The node of the sorted entries `es[lo:hi]`, whose keys agree on their first
    `level` nibbles. -/
private partial def node (es : Array Entry) (lo hi level : Nat) : 𝕋 :=
  if hi ≤ lo then .𝔹 .empty
  else if hi = lo + 1 then
    let (key, value) := es[lo]!
    .𝕃 [.𝔹 (compact (key.extract level key.size) true), .𝔹 value]
  else
    let first := es[lo]!.1
    -- The keys are sorted, so the first and the last share the common prefix.
    let shared := commonPrefix first es[hi - 1]!.1 level
    if shared > 0 then
      .𝕃 [ .𝔹 (compact (first.extract level (level + shared)) false)
         , reference (node es lo hi (level + shared)) ]
    else Id.run do
      -- A key that ends here is the first, and is the branch's value.
      let (value, start) := if first.size == level then (es[lo]!.2, lo + 1) else (.empty, lo)
      let mut children : Array 𝕋 := #[]
      let mut i := start
      for nibble in [0:16] do
        let mut j := i
        while j < hi && es[j]!.1[level]! == nibble.toUInt8 do
          j := j + 1
        children := children.push (reference (node es i j (level + 1)))
        i := j
      return .𝕃 (children.toList ++ [.𝔹 value])

private def compareKeys (a b : Array UInt8) : Ordering := Id.run do
  for i in [0:min a.size b.size] do
    if a[i]! < b[i]! then return .lt
    if a[i]! > b[i]! then return .gt
  return compare a.size b.size

/-- The root of the trie of the key/value pairs `pairs`. When a key repeats,
    its last value counts. -/
def root (pairs : Array (ByteArray × ByteArray)) : ByteArray :=
  let indexed := pairs.mapIdx fun i (k, v) => (nibbles k, v, i)
  let sorted := indexed.qsort fun (k₁, _, i₁) (k₂, _, i₂) =>
    match compareKeys k₁ k₂ with
    | .lt => true
    | .gt => false
    | .eq => i₁ < i₂
  -- Keep the last value of each key.
  let entries : Array Entry := Id.run do
    let mut out : Array Entry := #[]
    for (k, v, _) in sorted do
      if out.size > 0 && compareKeys out.back!.1 k == .eq then
        out := out.pop
      out := out.push (k, v)
    return out
  KEC (rlp (node entries 0 entries.size 0))

end Ethereum.Trie
