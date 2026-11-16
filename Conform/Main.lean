import Conform.Suites

open Ethereum.Conform

def nproc : IO Nat := do
  let out ← IO.Process.output {cmd := "nproc", stdin := .null}
  return out.stdout.trimAscii.toString.toNat? |>.getD 1

/--
`lake test -- [THREADS]` runs the `execution-spec-tests` fixtures, or the
legacy suite when `CONFORM_SUITE=legacy` (see `Conform.Suites`), on `THREADS`
threads, by default one per processor.
-/
def main (args : List String) : IO UInt32 := do
  let threads : ℕ := args.head? <&> String.toNat! |>.getD (← nproc)
  if (← IO.getEnv "CONFORM_SUITE") == some "legacy" then runLegacy threads else runEEST threads
