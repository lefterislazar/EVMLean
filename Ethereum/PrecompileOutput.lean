/-!
Validation for outputs returned by external precompile implementations.

The external implementation remains responsible for computing the result.
This transparent Lean boundary ensures that malformed results cannot enter the
EVM semantics as successful precompile outputs.
-/

namespace Ethereum

/-- Accept an external result only when its output has the expected size. -/
def checkedPrecompileOutput
    (name : String) (expectedSize : Nat)
    (result : Except String ByteArray) : Except String ByteArray := do
  let output ← result
  if output.size = expectedSize then
    return output
  throw s!"{name} returned {output.size} bytes; expected {expectedSize}"

theorem checkedPrecompileOutput_ok_size
    {name : String} {expectedSize : Nat} {result : Except String ByteArray}
    {output : ByteArray}
    (h : checkedPrecompileOutput name expectedSize result = .ok output) :
    output.size = expectedSize := by
  unfold checkedPrecompileOutput at h
  cases hresult : result with
  | error error => simp [hresult, bind, Except.bind] at h
  | ok candidate =>
      simp only [hresult, bind, Except.bind] at h
      split at h
      · rename_i hsize
        simp [pure, Except.pure] at h
        subst output
        exact hsize
      · simp [pure, Except.pure] at h

end Ethereum
