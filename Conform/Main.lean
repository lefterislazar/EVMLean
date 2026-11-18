import Conform.Suites

/-!
The `conform` executable, which `lake test -- [OPTION]...` runs with the
fixtures that it fetches (see `lakefile.lean`).
-/

namespace Ethereum

namespace Conform

def usage : String :=
  "Usage: lake test -- [OPTION]...
Run the conformance tests: the execution-spec-tests fixtures, or the legacy suite.
`lake test` fetches the pinned fixtures of the suite, unless --fixtures is given.

  --legacy            run the legacy suite instead of the execution-spec-tests fixtures
  --fixtures PATH     run the fixtures in PATH instead of fetching the pinned ones
  --state-tests       run the execution-spec-tests state tests, not the blockchain tests
  --threads N         run on N threads (default: one per processor)
  --dirs D1,D2,...    run only these execution-spec-tests directories, such as for_osaka
  --filter S1|S2|...  run only the tests whose name contains one of these substrings
  --perf              include the performance tests of the legacy suite
  --timed             write the running time of every test to .cache/conform/timings.txt
  --progress          log each test as it starts and finishes to .cache/conform/progress.txt
  --help              show this help"

/-- Fails unless `value`, given to `option`, is a value rather than the next option. -/
def checkValue (option value : String) : Except String Unit :=
  if value.startsWith "--" then throw s!"{option} needs a value" else pure ()

/-- The options `args`, added to `options`. -/
def Options.parse (options : Options) : List String → Except String Options
  | [] => pure options
  | "--legacy" :: args => parse { options with legacy := true } args
  | "--fixtures" :: path :: args => do
    checkValue "--fixtures" path
    parse { options with fixtures := some path } args
  | "--threads" :: n :: args => do
    checkValue "--threads" n
    let some n := n.toNat? | throw s!"--threads: not a number: {n}"
    parse { options with threads := some n } args
  | "--dirs" :: dirs :: args => do
    checkValue "--dirs" dirs
    parse { options with dirs := some (dirs.splitOn ",") } args
  | "--filter" :: filter :: args => do
    checkValue "--filter" filter
    parse { options with filter := filter.splitOn "|" } args
  | "--state-tests" :: args => parse { options with stateTests := true } args
  | "--perf" :: args => parse { options with perf := true } args
  | "--timed" :: args => parse { options with timed := true } args
  | "--progress" :: args => parse { options with progress := true } args
  | "--help" :: args => parse { options with help := true } args
  | [option] =>
    if option ∈ ["--fixtures", "--threads", "--dirs", "--filter"] then
      throw s!"{option} needs a value"
    else
      throw s!"unknown option: {option}"
  | arg :: _ => throw s!"unknown option: {arg}"

/-- The options in `args`, checking that they fit the suite. -/
def parseOptions (args : List String) : Except String Options := do
  let options ← Options.parse {} args
  if options.legacy ∧ options.dirs.isSome then
    throw "--dirs selects execution-spec-tests directories; it does not apply to --legacy"
  if options.legacy ∧ options.stateTests then
    throw "--state-tests selects execution-spec-tests state tests; it does not apply to --legacy"
  if ¬options.legacy ∧ options.perf then
    throw "--perf includes the performance tests of the legacy suite; it needs --legacy"
  return options

end Conform

end Ethereum

open Ethereum.Conform in
def main (args : List String) : IO UInt32 := do
  match parseOptions args with
  | .error message =>
    IO.eprintln s!"{message}\nRun `lake test -- --help` for the options."
    return 2
  | .ok options =>
    if options.help then
      IO.println usage
      return 0
    if options.legacy then runLegacy options else runEEST options
