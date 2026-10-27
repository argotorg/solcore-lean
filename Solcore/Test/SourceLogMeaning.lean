import Solcore.Synthesis.Source.EventLogCases
import Solcore.Synthesis.Source.ScalarMeaning.LogEmitter
import Solcore.Test.SourceScalarMeaning
import Solcore.ContractRuntime.CheckedContractRegistry

/-! Executable checks of the log source meaning on actual event-log emitter
output. Each emitted text is lexed, parsed with the log grammar and called
under the log source semantics with flags and an input, one transaction at a
time, from the storage of the account that the committed world holds and from a
dispatcher memory whose free-memory pointer word at 64 holds a buffer pointer.
Each call is compared with the original Core contract's top-level transaction:
a returned call with the returned ABI bytes, the committed slots and the
committed journal, which must be the framing of the source logs and decode to
them; a reverted call with the reverted bytes, an unchanged account storage
and an empty committed journal. Buffer pointers include 64, whose buffer
overlaps the pointer word, and the last pointer whose buffer lies below
`2^256`. `EventLog.emit_source_meaning` covers every successful emission,
every installed account and every such memory; these checks exercise the same
definitions on real texts and histories. Altered texts lose or change their
meaning. -/
set_option autoImplicit false

namespace Tests.SourceLogMeaning

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.EventLog (CheckedPlan Site)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def entry : Wire.Expr := call 1 (.var 0)
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def checkedPlan (label : String) (helpers : List Wire.Expr) (body : Wire.Expr)
    (sites : List Site) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError s!"log step failed the aggregate DAG checker: {label}")
  let some plan := CheckedPlan.ofParts? step sites |
    throw (IO.userError s!"log plan failed the host checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.EventLog.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"log emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the log grammar to a file whose printing is
that text, with the wrappers of the used topic counts before the raw aliases,
one function per helper and `sc_step`. The loop-free, storage, rollback and
keyed grammars reject it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseLogSource source |
    throw (IO.userError s!"emitted log source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed log source does not print back: {label}"
  ensure (file.opcodeAliases ==
        logAliases plan.sites ++ aggregateAliases (plan.step.helpers ++ [plan.step.entry]) &&
      file.functions.length == plan.step.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == Solcore.Synthesis.Source.EventLog.contractName &&
      file.method.body.length == plan.sites.length + 10)
    s!"log file has other aliases, functions, contract or body: {label}"
  ensure ((parseSource source).isNone && (parseStorageSource source).isNone &&
      (parseRollbackSource source).isNone && (parseKeyedSource source).isNone)
    s!"the loop-free, storage, rollback or keyed grammar accepted a log text: {label}"

private def target : Address := ⟨100, by decide⟩
private def caller : Address := ⟨200, by decide⟩

/-- Slots compared after each transaction. -/
private def comparedSlots : List Nat := [0, 1, 2, 5, high, maximum]

/-- Initial storages; the last fills slot zero with the maximum, so the first
step argument wraps. -/
private def initialStorages : List (List (Nat × Nat)) :=
  [[], [(0, 5), (1, 9), (5, 7)], [(0, maximum), (1, maximum), (maximum, 4)]]

/-- Buffer pointers the dispatcher may leave at 64: the usual 128, one whose
buffer overlaps the pointer word, and the last whose buffer lies below
`2^256`. -/
private def pointers : List Nat := [128, 64, 2 ^ 256 - 64]

/-- A dispatcher memory: only the free-memory pointer word is known. -/
private def dispatcherMemory (pointer : Nat) : Memory :=
  fun offset => if offset = 64 then some pointer else none

/-- The logs and the result the event-log recurrence gives from slot zero. -/
private def recurrence (step : Word → Word) (sites : List Site) (slot0 flags input : Nat) :
    Nat × List SourceLog :=
  let result := step ((Word.ofNatModulo input).add (Word.ofNatModulo slot0))
  let logs := sites.filterMap fun site =>
    if flags / 2 ^ site.guard % 2 = 1 then
      let value := step (result.add (Word.ofNatModulo site.guard))
      some ⟨(List.range site.topics).map fun index => (value.val + index + 1) % 2 ^ 256,
        [value.val, result.val].take site.dataWords⟩
    else none
  (result.val, logs)

/-- Runs one history of `(flags, input)` rows from an account holding
`initial`, with the dispatcher leaving `pointer`. Before each transaction the
source storage is read from the account that the committed world holds; the
source call must settle as the Core transaction with the framing of its logs.
When `step` is given, the outcome must also follow the event-log recurrence.
When `golden` is given, the rows must be those hand-known outcomes. Returns the
numbers of returned and reverted transactions and of committed logs. -/
private def checkHistory (label : String) (plan : CheckedPlan) (source : String)
    (initial : List (Nat × Nat)) (pointer : Nat) (rows : List (Nat × Nat))
    (step : Option (Word → Word) := none)
    (golden : List (Bool × Nat × List (List Nat × List Nat)) := []) :
    IO (Nat × Nat × Nat) := do
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == target then some plan.contract else none⟩
  let installedAccount := initial.foldl (fun account (slot, value) =>
    account.storageWrite (Word.ofNatModulo slot) (Word.ofNatModulo value))
    (Account.empty.withCode plan.code)
  let mut world := WorldState.empty.putAccount target installedAccount
  let mut returned := 0
  let mut reverted := 0
  let mut committed := 0
  let mut index := 0
  for (flags, input) in rows do
    let calldata := Solcore.Synthesis.Stateful.EventLogExecution.inputData
      (Word.ofNatModulo flags) (Word.ofNatModulo input)
    ensure (calldata.wordBE? (Word.ofNatModulo 4) == some (Word.ofNatModulo flags) &&
        calldata.wordBE? (Word.ofNatModulo 36) == some (Word.ofNatModulo input))
      s!"canonical calldata does not carry its flags and input words: {label}"
    let some ⟨contract, installed⟩ := registry.resolve? world target |
      throw (IO.userError s!"committed world no longer resolves the contract: {label}")
    let storage := accountStorage installed.account
    let invocation : TopLevelInvocation :=
      { target, caller, callValue := Word.zero, inputData := calldata }
    let some outcome := logSourceCall source storage (dispatcherMemory pointer) "run"
        [flags, input] |
      throw (IO.userError s!"log source call has no meaning: {label} at {flags}, {input}")
    match TopLevelExecution.run contract invocation installed 0 with
    | .outOfFuel _ _ _ _ _ _ => pure ()
    | .completed _ => throw (IO.userError s!"zero fuel completed a log transaction: {label}")
    let result ← match TopLevelExecution.run contract invocation installed 100000 with
      | .outOfFuel _ _ _ _ _ _ =>
          throw (IO.userError s!"log transaction exhausted its fuel: {label}")
      | .completed result => pure result
    let some account := result.finalWorld.account? target |
      throw (IO.userError s!"committed storage account disappeared: {label}")
    let expected := step.map fun stepResult =>
      recurrence stepResult plan.sites (storage 0) flags input
    let records := result.committedJournal.logList
    match outcome with
    | .returned value storage' logs =>
        ensure (flags % 2 == 0) s!"odd flags returned: {label} at {flags}, {input}"
        ensure (value < 2 ^ 256 &&
            result.outcome == .returned (encodeWordBytesBE (Word.ofNatModulo value)))
          s!"returned word differs from the Core transaction: {label} at {flags}, {input}"
        ensure (comparedSlots.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage' slot)
          s!"committed slots differ from the source storage: {label} at {flags}, {input}"
        ensure (records == logs.flatMap (logFrame target))
          s!"committed journal is not the framing of the source logs: {label} at {flags}"
        match Solcore.Synthesis.Stateful.EventLogExecution.decodeJournal records with
        | .ok events =>
            ensure (events.map (fun event =>
                (event.emitter, event.topics.map (·.val), event.data.map (·.val))) ==
              logs.map fun log => (target, log.topics, log.data))
              s!"decoded journal differs from the source logs: {label} at {flags}"
        | .error error => throw (IO.userError s!"committed journal did not decode: {error}")
        if let some (sum, expectedLogs) := expected then
          ensure (value == sum && logs == expectedLogs)
            s!"returned results differ from the log recurrence: {label} at {flags}, {input}"
        if let some (odd, payload, shapes) := golden[index]? then
          ensure (!odd && value == payload &&
              logs.map (fun log => (log.topics, log.data)) == shapes)
            s!"log golden row changed: {label} row {index}"
        returned := returned + 1
        committed := committed + logs.length
    | .reverted data =>
        ensure (flags % 2 == 1) s!"even flags reverted: {label} at {flags}, {input}"
        ensure (data < 2 ^ 256 &&
            result.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo data)))
          s!"reverted word differs from the Core transaction: {label} at {flags}, {input}"
        ensure (comparedSlots.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage slot)
          s!"a reverted transaction changed the committed slots: {label} at {flags}"
        ensure records.isEmpty s!"a reverted transaction committed logs: {label} at {flags}"
        if let some (sum, _) := expected then
          ensure (data == sum) s!"reverted word differs from the log recurrence: {label}"
        if let some (odd, payload, _) := golden[index]? then
          ensure (odd && data == payload) s!"log golden row changed: {label} row {index}"
        reverted := reverted + 1
    world := result.finalWorld
    index := index + 1
  let some ⟨_, installed⟩ := registry.resolve? world target |
    throw (IO.userError s!"committed world no longer resolves the contract: {label}")
  let storage := accountStorage installed.account
  ensure (logSourceCall source storage (dispatcherMemory pointer) "run" [2 ^ 256, 0]).isNone
    s!"log method accepted flags outside uint256: {label}"
  ensure (logSourceCall source storage (fun _ => none) "run" [0, 0]).isNone
    s!"log method ran without a free-memory pointer: {label}"
  return (returned, reverted, committed)

/-- Every history of a plan, from each initial storage and buffer pointer. -/
private def checkPlan (label : String) (plan : CheckedPlan) (rows : List (Nat × Nat))
    (step : Option (Word → Word) := none) : IO (String × Nat × Nat × Nat) := do
  let program ← emitted label plan
  checkReprint label plan program.source
  let mut returned := 0
  let mut reverted := 0
  let mut committed := 0
  for initial in initialStorages do
    for pointer in pointers do
      let (more, fewer, logs) ← checkHistory label plan program.source initial pointer rows step
      returned := returned + more
      reverted := reverted + fewer
      committed := committed + logs
  return (program.source, returned, reverted, committed)

/-- Flags enabling no site, each site, every site and high noise bits, with
both parities and boundary inputs. -/
private def regressionRows : List (Nat × Nat) :=
  [(0, 5), (2, 0), (4, maximum), (8, 1), (14, 7), (15, 2), (14 + high, maximum),
    (7, high), (2, maximum), (8, 3)]

private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

/-- Site layouts covering guards one to three, zero to four topics and zero to
two data Words. -/
private def layouts : List (List Site) :=
  [[⟨1, 2, 1⟩, ⟨3, 0, 2⟩], [⟨1, 0, 0⟩, ⟨2, 1, 1⟩, ⟨3, 4, 2⟩], [⟨2, 3, 2⟩],
    [⟨1, 4, 0⟩, ⟨3, 2, 1⟩], []]

/-- The golden histories of `SourceEventLogEmitter`, from empty storage. -/
private def goldenChecks : IO Unit := do
  let identity ← checkedPlan "identity" [.var 0] entry [⟨1, 2, 1⟩, ⟨3, 0, 2⟩]
  let identitySource := (← emitted "identity" identity).source
  let _ ← checkHistory "golden sites" identity identitySource [] 128
    [(2, 5), (9, 1), (8, 0)] (some id)
    [(false, 5, [([7, 8], [6])]), (true, 6, []), (false, 5, [([], [8, 5])])]
  let incremented ← checkedPlan "increment" [increment] entry [⟨2, 4, 0⟩]
  let _ ← checkHistory "golden wrapping" incremented (← emitted "increment" incremented).source
    [] 128 [(4, maximum), (5, 3), (high + 6, 2)]
    (some fun input => input.add (Word.ofNatModulo 1))
    [(false, 0, [([4, 5, 6, 7], [])]), (true, 4, []), (false, 3, [([7, 8, 9, 10], [])])]
  let bare ← checkedPlan "no site" [.var 0] entry []
  let _ ← checkHistory "golden completion" bare (← emitted "no site" bare).source [] 128
    [(14, 7), (15, 1)] (some id) [(false, 7, []), (true, 8, [])]

/-- The regression steps with their step functions, over every layout. -/
private def regressionChecks : IO (String × Nat × Nat × Nat) := do
  let plus (amount : Nat) (input : Word) : Word := input.add (Word.ofNatModulo amount)
  let mut returned := 0
  let mut reverted := 0
  let mut committed := 0
  let mut fixture := ""
  for sites in layouts do
    for (label, helpers, body, step) in [
        ("identity", [.var 0], entry, fun input : Word => input),
        ("increment", [increment], entry, plus 1),
        ("private cell", [privateStep], .binary .wordSub entry (word 1), plus 1),
        ("constant", [.var 0], word 0, fun _ => Word.zero),
        ("division", [.binary .wordDiv (.var 0) (word 1)], entry, id)] do
      let (source, more, fewer, logs) ← checkPlan s!"{label} {sites.length} sites"
        (← checkedPlan label helpers body sites) regressionRows (some step)
      if label == "identity" && sites.length == 3 then fixture := source
      returned := returned + more
      reverted := reverted + fewer
      committed := committed + logs
  return (fixture, returned, reverted, committed)

/-- Raw opcodes applied to a helper result as the step. -/
private def primitiveSteps : List (String × Wire.Expr) :=
  let c := call 1
  [("clz", .unary .wordClz (c (.var 0))),
    ("div", .binary .wordDiv (c (.var 0)) (c (word 2))),
    ("mod", .binary .wordMod (c (.var 0)) (c (word 0))),
    ("shl", .binary .wordShl (c (word 1)) (c (.var 0))),
    ("shr", .binary .wordShr (c (word maximum)) (c (.var 0))),
    ("sar", .binary .wordSar (c (word high)) (c (.var 0))),
    ("sdiv", .binary .wordSdiv (c (.var 0)) (c (word maximum))),
    ("smod", .binary .wordSmod (c (.var 0)) (c (word 2))),
    ("sgt", .ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0)),
    ("byte", .binary .wordByte (c (.var 0)) (c (word 0x1234))),
    ("pow", .binary .wordPow (c (word maximum)) (c (.var 0))),
    ("signextend", .binary .wordSignExtend (c (word 0)) (c (.var 0))),
    ("addmod", .ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum))),
    ("mulmod", .ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)))]

/-- Generated event-log scenarios at two budgets, with their generated rows and
two more. Seeds the generator rejects are skipped. -/
private def checkGenerated : IO (Nat × Nat × Nat × Nat) := do
  let mut plans := 0
  let mut returned := 0
  let mut reverted := 0
  let mut committed := 0
  for nodes in [256, 512] do
    for seed in List.range 12 do
      match Solcore.Synthesis.Source.EventLog.generatedScenario (Seed.ofNat seed) nodes with
      | .error _ => pure ()
      | .ok (scenario, _) =>
          let rows := scenario.transactions.map fun transaction =>
            (transaction.flags.val, transaction.input.val)
          let (_, more, fewer, logs) ← checkPlan s!"generated budget {nodes} seed {seed}"
            scenario.plan (rows ++ [(14, maximum), (15, 0)])
          plans := plans + 1
          returned := returned + more
          reverted := reverted + fewer
          committed := committed + logs
  ensure (plans ≥ 16) s!"the event-log generator produced only {plans} plans"
  return (plans, returned, reverted, committed)

/-- The outcome of one call from a nonempty storage and the usual buffer. -/
private def observed (source : String) (flags input : Nat) : Option String :=
  let storage : Storage := fun slot => if slot = 0 then 5 else if slot = 1 then 9 else 7
  (logSourceCall source storage (dispatcherMemory 128) "run" [flags, input]).map fun
    | .returned value storage' logs =>
        s!"returned {value} {storage' 0} {storage' 1} " ++
          toString (logs.map fun log => (log.topics, log.data))
    | .reverted data => s!"reverted {data}"

/-- Altered log programs lose their meaning or change their outcome. The
fixture has sites with guards one, two and three, the last with four topics and
two data Words. -/
private def checkAlterations (source : String) : IO Unit := do
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"log fixture has no {old}"
    pure changed
  let all := observed source 14 2
  ensure all.isSome "the log fixture has no meaning"
  let otherPointer ← replace "mload(64);" "mload(96);"
  ensure ((parseLogSource otherPointer).isSome && observed otherPointer 14 2 == none)
    "a pointer read from unknown memory kept a meaning"
  let farther ← replace "mstore(sc_ptr + 32, sc_result);" "mstore(sc_ptr + 64, sc_result);"
  ensure ((parseLogSource farther).isSome && observed farther 14 2 == none)
    "a second data Word stored past the buffer kept a meaning"
  let unstored ← replace "            mstore(sc_ptr, sc_value3);\n" ""
  ensure ((parseLogSource unstored).isSome && observed unstored 8 2 == none)
    "a log over a Word that no site stored kept a meaning"
  let shorter ← replace "sc_log4(sc_ptr, 64," "sc_log4(sc_ptr, 33,"
  ensure ((parseLogSource shorter).isSome && observed shorter 8 2 == none)
    "a log size that is no multiple of 32 kept a meaning"
  let wrongArity ← replace "sc_log4(sc_ptr, 64, sc_value3 + 1, sc_value3 + 2, sc_value3 + 3, "
    "sc_log4(sc_ptr, 64, sc_value3 + 1, sc_value3 + 2, "
  ensure ((parseLogSource wrongArity).isSome && observed wrongArity 8 2 == none)
    "a logger called with the wrong topic count kept a meaning"
  let reordered ← replace "sc_value3 + 1, sc_value3 + 2" "sc_value3 + 2, sc_value3 + 1"
  ensure ((parseLogSource reordered).isSome && observed reordered 8 2 != observed source 8 2 &&
      observed reordered 2 2 == observed source 2 2)
    "reordered topics kept the log or changed another site"
  let otherGuard ← replace "if ((sc_flags & 8) == 8) {" "if ((sc_flags & 4) == 4) {"
  ensure ((parseLogSource otherGuard).isSome && observed otherGuard 8 2 != observed source 8 2)
    "a site moved to another guard bit kept its outcome"
  let withElse ← replace "sc_value3 + 4);\n        }\n"
    "sc_value3 + 4);\n        } else {\n        }\n"
  ensure (parseLogSource withElse).isNone "a log block followed by else was accepted"

def testSourceLogMeaning : IO Unit := do
  goldenChecks
  let (fixture, regressionReturned, regressionReverted, regressionLogs) ← regressionChecks
  let mut primitivesReturned := 0
  let mut primitivesReverted := 0
  let mut primitivesLogs := 0
  for (label, body) in primitiveSteps do
    let (_, more, fewer, logs) ← checkPlan label
      (← checkedPlan label [.var 0] body [⟨1, 2, 2⟩, ⟨3, 4, 1⟩])
      [(0, 0), (2, 1), (10, maximum), (11, high)]
    primitivesReturned := primitivesReturned + more
    primitivesReverted := primitivesReverted + fewer
    primitivesLogs := primitivesLogs + logs
  let (generated, generatedReturned, generatedReverted, generatedLogs) ← checkGenerated
  checkAlterations fixture
  IO.println (s!"log source meaning: 3 golden histories, 25 regression plans " ++
    s!"({regressionReturned} returned, {regressionReverted} reverted, {regressionLogs} logs), " ++
    s!"14 raw primitive plans ({primitivesReturned} returned, {primitivesReverted} reverted, " ++
    s!"{primitivesLogs} logs) and {generated} generated plans ({generatedReturned} returned, " ++
    s!"{generatedReverted} reverted, {generatedLogs} logs) settle as Core from 3 initial " ++
    "storages and 3 buffer pointers")

end Tests.SourceLogMeaning
