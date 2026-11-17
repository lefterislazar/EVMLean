import Conform.Fixture
import Conform.Network
import Conform.Run

/-!
# Running the tests of fixture files

Finds the fixture files in directories, runs their tests on several threads
and logs the results. A test whose network the model does not support is not
run, and is reported as such.
-/

namespace Ethereum

namespace Conform

abbrev TestId : Type := System.FilePath × String

inductive TestResult where
  | passed
  | failed (reason : String)
  /-- The model does not support the test's network, so the test did not run. -/
  | unsupportedNetwork (network : String)

instance : ToString TestResult where
  toString
    | .passed => "Success."
    | .failed reason => reason
    | .unsupportedNetwork network => s!"Skipped: unsupported network {network}"

/-- The directory of the logs of a run, which git ignores. Each run replaces them. -/
def logDirectory : System.FilePath := ".cache/conform"

/-- The result of every test. -/
def resultsLog : System.FilePath := logDirectory / "results.txt"

/-- The tests that failed, and why. -/
def failuresLog : System.FilePath := logDirectory / "failures.txt"

/-- With `CONFORM_TIMED`, the running time of every test that ran, slowest first. -/
def timingsLog : System.FilePath := logDirectory / "timings.txt"

/-- With `CONFORM_PROGRESS`, each test as it starts and finishes, to see which tests are running. -/
def progressLog : System.FilePath := logDirectory / "progress.txt"

/--
Run the tests of the fixture file `path` whose names `isSelected` selects,
parsing the file once. Every result comes with the test's running time in
milliseconds.
-/
def runFile (path : System.FilePath) (isSelected : String → Bool) :
    IO (Array (TestId × TestResult × ℕ)) := do
  let progress := (← IO.getEnv "CONFORM_PROGRESS").isSome
  let tests ← match (← readJsonFile path).getObj? with
    | .ok tests => pure tests
    | .error err => throw <| .userError s!"{path}: {err}"
  let mut results := #[]
  for (testName, test) in tests.toArray do
    unless isSelected testName do continue
    if let .ok network := test.getObjValAs? String "network" then
      if (parseNetwork? network).isNone then
        results := results.push ((path, testName), .unsupportedNetwork network, 0)
        continue
    let start ← IO.monoMsNow
    if progress then
      IO.FS.withFile progressLog .append (·.putStrLn s!"start {testName} FROM {path}")
    let result : TestResult :=
      match (Lean.fromJson? test : Except String BlockchainTest) with
      | .error err => .failed s!"Cannot decode: {err}"
      | .ok test =>
        match run test with
        | .error failure => .failed (toString failure)
        | .ok () => .passed
    let elapsed := (← IO.monoMsNow) - start
    if progress then
      IO.FS.withFile progressLog .append (·.putStrLn s!"done {elapsed}ms {testName}")
    results := results.push ((path, testName), result, elapsed)
  return results

/-- Whether `path` lies in the directory `dir`, comparing path components. -/
def isUnder (dir path : System.FilePath) : Bool :=
  let parts (p : System.FilePath) := p.components.filter (· ≠ "")
  (parts dir).isPrefixOf (parts path)

/--
Run the tests that `isSelected` selects of the fixture files `files` on
`threads` threads. Each thread repeatedly takes the next file from a shared
queue, in the order of `files`.
-/
def runFiles (files : Array System.FilePath) (isSelected : String → Bool) (threads : ℕ) :
    IO (Array (TestId × TestResult × ℕ)) := do
  let next ← IO.mkRef 0
  let worker : IO (Array (TestId × TestResult × ℕ)) := do
    let mut results := #[]
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      let some path := files[i]? | break
      results := results ++ (← runFile path isSelected)
    return results
  let mut tasks := #[]
  for _ in [0:max threads 1] do
    tasks := tasks.push (← IO.asTask worker .dedicated)
  let mut results := #[]
  for task in tasks do
    results := results ++ (← IO.ofExcept task.get)
  return results

/-- The outcome of `runTests`. -/
structure Summary where
  passed      : ℕ
  /-- The tests that failed, as `file[test]`. -/
  failed      : Array String
  /-- The number of tests of each network that the model does not support. -/
  unsupported : Std.HashMap String ℕ

/--
Run the tests of the fixture files in `roots` on `threads` threads, leaving
out the files that `skipFile` selects and the tests that `skipTest` selects.
The largest files start first, so that they do not finish last.
-/
def runTests (roots : Array System.FilePath) (threads : ℕ)
    (skipFile : System.FilePath → Bool := fun _ => false)
    (skipTest : String → Bool := fun _ => false) : IO Summary := do
  -- `CONFORM_FILTER` selects the tests whose name contains one of its
  -- `|`-separated substrings.
  let filter := (← IO.getEnv "CONFORM_FILTER").getD ""
  let isSelected (testName : String) : Bool :=
    ¬skipTest testName ∧
      (filter.isEmpty ∨ (filter.splitOn "|").any (fun f => (testName.splitOn f).length > 1))

  -- The `.meta` directories hold an index of the fixtures, not fixtures.
  let mut files := #[]
  for root in roots do
    for path in ← System.FilePath.walkDir root do
      if path.extension == some "json" ∧ ¬skipFile path ∧ path.components.all (· != ".meta") then
        files := files.push (path, (← path.metadata).byteSize)

  IO.FS.createDirAll logDirectory
  for log in [resultsLog, failuresLog, timingsLog, progressLog] do
    if ← log.pathExists then IO.FS.removeFile log

  -- The largest files start first, so that they do not finish last.
  let queue := (files.qsort (·.2 > ·.2)).map (·.1)
  IO.println s!"Running the tests of {queue.size} files on {threads} thread{if threads == 1 then "" else "s"}..."
  (← IO.getStdout).flush
  let results ← runFiles queue isSelected threads

  let mut summary : Summary := { passed := 0, failed := #[], unsupported := ∅ }
  let mut resultLines := #[]
  let mut failureLines := #[]
  for ((file, test), result, _) in results do
    let name := s!"{file.fileName.get!}[{test}]"
    resultLines := resultLines.push s!"{name} - {result}\n"
    match result with
    | .passed => summary := { summary with passed := summary.passed + 1 }
    | .failed reason =>
      summary := { summary with failed := summary.failed.push name }
      failureLines := failureLines.push s!"{name} {reason}"
    | .unsupportedNetwork network =>
      summary := { summary with unsupported := summary.unsupported.alter network (some <| ·.getD 0 + 1) }
  IO.FS.writeFile resultsLog (String.intercalate "\n" resultLines.toList ++ "\n")
  unless failureLines.isEmpty do
    IO.FS.writeFile failuresLog (String.intercalate "\n" failureLines.toList ++ "\n")

  if (← IO.getEnv "CONFORM_TIMED").isSome then
    let ran := results.filter fun (_, result, _) => !(result matches .unsupportedNetwork _)
    IO.FS.withFile timingsLog .write fun h =>
      for ((file, test), _, ms) in ran.qsort (·.2.2 > ·.2.2) do
        h.putStrLn s!"{ms.toFloat / 1000.0}s {file}[{test}]"
  return summary

/-- Print `summary`, and return the exit code: 0 when every test that ran passed. -/
def report (summary : Summary) : IO UInt32 := do
  let total := summary.passed + summary.failed.size
  IO.println s!"Total tests: {total}"
  IO.println s!"The post was NOT equal to the resulting state: {summary.failed.size}"
  IO.println s!"Succeeded: {summary.passed}"
  IO.println s!"Success rate of: {if total = 0 then 100.0 else (summary.passed.toFloat / total.toFloat) * 100.0}"
  let unsupported := summary.unsupported.toArray.qsort (·.1 < ·.1)
  let skipped := unsupported.foldl (· + ·.2) 0
  IO.println <| s!"Skipped, unsupported network: {skipped}" ++
    String.join (unsupported.toList.map fun (network, n) => s!"\n  {network}: {n}")
  IO.println s!"Failed tests:\n{summary.failed}"
  IO.println <| s!"Logs in {logDirectory}: results of every test in {resultsLog.fileName.get!}" ++
    (if summary.failed.isEmpty then "." else s!", failures in {failuresLog.fileName.get!}.")
  return if summary.failed.isEmpty then 0 else 1

end Conform

end Ethereum
