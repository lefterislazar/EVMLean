import Conform.TestRunner

def TestsSubdir : System.FilePath := "BlockchainTests"
def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

private def basicSuccess (name : System.FilePath)
                         (result : Batteries.RBMap String Ethereum.Conform.TestResult compare) : IO Bool := do
  if result.all (λ _ v ↦ v.isNone)
  then IO.println s!"SUCCESS! - {name}"; pure true
  else pure false

private def success (result : Batteries.RBMap String Ethereum.Conform.TestResult compare) : Array String × Array String :=
  let (succeeded, failed) := result.partition (λ _ v ↦ v.isNone)
  (succeeded.keys, failed.keys)

def logFile (phase : ℕ) : System.FilePath := s!"tests_{phase}.txt"

open Ethereum.Conform in
instance : ToString TestResult where
  toString tr := tr.elim "Success." id

open Ethereum.Conform in
def log (testFile : System.FilePath) (testName : String) (result : TestResult) (phase : ℕ := 0) : IO Unit :=
  IO.FS.withFile (logFile phase) .append λ h ↦ h.putStrLn s!"{testFile.fileName.get!}[{testName}] - {result}\n"

def directoryBlacklist : List System.FilePath := []

def fileBlacklist : List System.FilePath := []

def testFiles (root               : System.FilePath)
              (directoryBlacklist : Array System.FilePath := #[])
              (fileBlacklist      : Array System.FilePath := #[])
              (testBlacklist      : Array String := #[])
              (testWhitelist      : Array String := #[])
              (phase              : ℕ)
              (threads            : ℕ := 1)
              (timed              : Bool := false) : IO (Nat × Array String) := do
  let isToBeTested (testname : String) : Bool :=
    let whitelist := testWhitelist
    let blacklist := testBlacklist ++ Ethereum.Conform.GlobalBlacklist
    testname ∉ blacklist ∧ (whitelist.isEmpty ∨ testname ∈ whitelist)

  let testFiles ←
    Array.filter isTestFile <$>
      System.FilePath.walkDir root (pure <| · ∉ directoryBlacklist)

  let testFiles := testFiles.filter (· ∉ fileBlacklist)
  let testFiles := testFiles.filter fun p => p.components.all (· != ".meta")

  let mut testNames : Array (System.FilePath × Array String) := #[]
  for path in testFiles do
    let json ← Lean.Json.fromFile path
    match json.getObj? with
    | .error _ => panic! "Malformed test json."
    | .ok x =>
        let names := x.toArray.filterMap fun (name, val) =>
          let isCancun := match val.getObjVal? "network" >>= Lean.Json.getStr? with
            | .ok network => network.startsWith "Cancun"
            | .error _ => false
          if isCancun && isToBeTested name then some name else none
        testNames := testNames.push (path, names)

  let mut discardedFiles : Array Ethereum.Conform.TestId := #[]
  let mut numSuccess := 0

  if ←System.FilePath.pathExists (logFile phase) then IO.FS.removeFile (logFile phase)

  let mut tasks : Array (Task _) := .empty
  let mut thread := 0
  let mut tests : Array (Array (System.FilePath × String)) := .replicate threads #[]

  IO.println s!"Scheduling tests for parallel execution..."
  for (path, names) in testNames do
    for name in names do
      tests := tests.set! thread (tests[thread]! |>.push (path, name))
      thread := thread + 1; thread := thread % threads
  for i in [0:threads] do
    tasks := tasks.push (←IO.asTask <| Ethereum.Conform.processTests tests[i]! (if timed then .some i else .none))

  let mut failedTests : Array String := .empty

  IO.println s!"Scheduled {tests.foldl (· + ·.size) 0} tests on {threads} thread{if threads == 1 then "" else "s"}."
  IO.println s!"Running..."
  (← IO.getStdout).flush
  let mut testResults := #[]
  for task in tasks do
    testResults := testResults.push (← IO.wait task >>= IO.ofExcept)
  for (discarded, batch) in testResults do
    discardedFiles := discardedFiles.append discarded
    for ((file, test), res) in batch do
      log file test res phase
      if res.isNone
      then numSuccess := numSuccess + 1
      else failedTests := failedTests.push s!"{file.fileName.get!}[{test}]"
  return (numSuccess, failedTests)

def nproc : IO Nat := do
  let out ← IO.Process.output {cmd := "nproc", stdin := .null}
  return out.stdout.trimAscii.toString.toNat? |>.getD 1

def main (args : List String) : IO UInt32 := do

  let NumThreads : ℕ := args.head? <&> String.toNat! |>.getD (←nproc)

  let DelayFiles : Array String :=
    #["static_Call50000bytesContract50_2_d1g0v0_Cancun",
      "static_Call50000bytesContract50_2_d0g0v0_Cancun",
      "static_Call50000bytesContract50_3_d1g0v0_Cancun",
      "static_Call50000_sha256_d0g0v0_Cancun",
      "static_Call50000_sha256_d1g0v0_Cancun",
      "CALLBlake2f_MaxRounds_d0g0v0_Cancun",
      "SuicideIssue_Cancun"]

  let printResults (result : ℕ × Array String) : IO (Array String) := do
    let (success, failure) := result
    IO.println s!"Total tests: {success + failure.size}"
    IO.println s!"The post was NOT equal to the resulting state: {failure.size}"
    IO.println s!"Succeeded: {success}"
    let total := failure.size + success
    IO.println s!"Success rate of: {if total = 0 then 100.0 else (success.toFloat / total.toFloat) * 100.0}"
    IO.println s!"Failed tests:\n{failure}"
    return failure

  -- v17.2 keeps the refilled block tests in `BlockchainTests` and the
  -- Cancun general-state corpus in the `legacytests` submodule.
  let legacyRoot : System.FilePath :=
    "EthereumTests/LegacyTests/Cancun/BlockchainTests/"
  let perfDir : System.FilePath :=
    "EthereumTests/LegacyTests/Cancun/BlockchainTests/GeneralStateTests/VMTests/vmPerformance"

  IO.println s!"Phase 1/3 - No performance tests."
  (← IO.getStdout).flush
  let failed₁a ← testFiles (root := "EthereumTests/BlockchainTests/")
                          (testBlacklist := DelayFiles)
                          (phase := 1)
                          (threads := NumThreads) >>= printResults
  let failed₁b ← testFiles (root := legacyRoot)
                          (directoryBlacklist := #[perfDir])
                          (testBlacklist := DelayFiles)
                          (phase := 1)
                          (threads := NumThreads) >>= printResults
  let failed₁ := failed₁a ++ failed₁b

  IO.println s!"Phase 2/3 - Performance tests only."
  let failed₂ ← testFiles (root := perfDir)
                          (phase := 2)
                          (threads := NumThreads) >>= printResults

  IO.println s!"Phase 3/3 - Individually scheduled tests."
  let failed₃a ← testFiles (root := "EthereumTests/BlockchainTests/")
                          (testWhitelist := DelayFiles)
                          (phase := 3)
                          (threads := NumThreads) >>= printResults
  let failed₃b ← testFiles (root := legacyRoot)
                          (testWhitelist := DelayFiles)
                          (phase := 3)
                          (threads := NumThreads) >>= printResults
  let failed₃ := failed₃a ++ failed₃b

  return if (failed₁ ++ failed₂ ++ failed₃).isEmpty then 0 else 1
