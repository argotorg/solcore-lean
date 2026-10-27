import Solcore.Synthesis.Source.StorageRollbackCases
import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.ScalarMeaning.RollbackEmitter
import Solcore.Test.SourceScalarMeaning
import Solcore.ContractRuntime.CheckedContractRegistry

/-! Executable checks of the rollback source meaning on actual rollback emitter
output. Each emitted text is lexed, parsed with the rollback grammar and called
under the rollback source semantics, one transaction at a time, from the
storage of the account that the committed world holds. Each call is compared
with the original Core contract's top-level transaction: a returned call with
the returned ABI bytes and the committed slots, a reverted call with the
reverted bytes and an unchanged account storage. `StorageRollback.emit_source_meaning`
covers every successful emission and every installed account; these checks
exercise the same definitions on real texts and histories that mix even and
odd inputs. Altered texts lose or change their meaning. -/
set_option autoImplicit false

namespace Tests.SourceRollbackMeaning

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.StorageRollback (CheckedPlan)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def entry : Wire.Expr := call 1 (.var 0)
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def checkedPlan (label : String) (helpers : List Wire.Expr) (body : Wire.Expr) :
    IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError s!"rollback step failed the aggregate DAG checker: {label}")
  let some plan := CheckedPlan.ofParts? step |
    throw (IO.userError s!"rollback plan failed the host checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match StorageRollback.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"rollback emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the rollback grammar to a file whose printing
is that text, with one function per helper and `sc_step`, and the aliases
exactly when a step body uses one. The loop-free and storage grammars reject
it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseRollbackSource source |
    throw (IO.userError s!"emitted rollback source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed rollback source does not print back: {label}"
  ensure (file.opcodeAliases == aggregateAliases (plan.step.helpers ++ [plan.step.entry]) &&
      file.functions.length == plan.step.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == StorageRollback.contractName)
    s!"rollback file has other aliases, functions or contract: {label}"
  ensure ((parseSource source).isNone && (parseStorageSource source).isNone)
    s!"the loop-free or storage grammar accepted a rollback text: {label}"

private def target : Address := ⟨100, by decide⟩
private def caller : Address := ⟨200, by decide⟩

/-- The slots compared after each transaction. -/
private def comparedSlots : List Nat := [0, 1, 2, 3, high, maximum]

/-- Two nonempty initial storages; the second makes slot 1 wrap to zero. -/
private def initialStorages : List (List (Nat × Nat)) :=
  [[], [(0, 5), (1, 9), (2, 7), (high, 3)], [(0, maximum), (1, maximum), (3, 1)]]

/-- Runs one history from an account holding `initial`. Before each
transaction the source storage is read from the account that the committed
world holds; the source call must settle as the Core transaction. When `step`
is given, the outcome's word and the written slots must also follow the
two-slot recurrence. Returns the numbers of returned and reverted
transactions. -/
private def checkHistory (label : String) (plan : CheckedPlan) (source : String)
    (initial : List (Nat × Nat)) (inputs : List Nat)
    (step : Option (Word → Word) := none) : IO (Nat × Nat) := do
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == target then some plan.contract else none⟩
  let installedAccount := initial.foldl (fun account (slot, value) =>
    account.storageWrite (Word.ofNatModulo slot) (Word.ofNatModulo value))
    (Account.empty.withCode plan.code)
  let mut world := WorldState.empty.putAccount target installedAccount
  let mut returned := 0
  let mut reverted := 0
  for input in inputs do
    let calldata := Solcore.Synthesis.Stateful.StorageExecution.inputData (Word.ofNatModulo input)
    ensure (calldata.wordBE? (Word.ofNatModulo 4) == some (Word.ofNatModulo input))
      s!"canonical calldata does not carry its input word: {label}"
    let some ⟨contract, installed⟩ := registry.resolve? world target |
      throw (IO.userError s!"committed world no longer resolves the contract: {label}")
    let storage := accountStorage installed.account
    let invocation : TopLevelInvocation :=
      { target, caller, callValue := Word.zero, inputData := calldata }
    let some outcome := rollbackSourceCall source storage "run" [input] |
      throw (IO.userError s!"rollback source call has no meaning: {label} at {input}")
    match TopLevelExecution.run contract invocation installed 0 with
    | .outOfFuel _ _ _ _ _ _ => pure ()
    | .completed _ => throw (IO.userError s!"zero fuel completed a rollback transaction: {label}")
    let result ← match TopLevelExecution.run contract invocation installed 100000 with
      | .outOfFuel _ _ _ _ _ _ =>
          throw (IO.userError s!"rollback transaction exhausted its fuel: {label}")
      | .completed result => pure result
    let some account := result.finalWorld.account? target |
      throw (IO.userError s!"committed storage account disappeared: {label}")
    let expected : Option (Nat × Nat × Nat) := step.map fun stepResult =>
      let computed := stepResult ((Word.ofNatModulo input).add (Word.ofNatModulo (storage 0)))
      let second := (Word.ofNatModulo (storage 1)).add (Word.ofNatModulo 1)
      ((computed.add second).val, computed.val, second.val)
    match outcome with
    | .returned value storage' =>
        ensure (input % 2 == 0) s!"an odd input returned: {label} at {input}"
        ensure (value < 2 ^ 256 &&
            result.outcome == .returned (encodeWordBytesBE (Word.ofNatModulo value)))
          s!"returned word differs from the Core transaction: {label} at {input}"
        ensure (comparedSlots.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage' slot)
          s!"committed slots differ from the source storage: {label} at {input}"
        if let some (sum, first, second) := expected then
          ensure (value == sum && storage' 0 == first && storage' 1 == second)
            s!"returned results differ from the two-slot recurrence: {label} at {input}"
        returned := returned + 1
    | .reverted data =>
        ensure (input % 2 == 1) s!"an even input reverted: {label} at {input}"
        ensure (data < 2 ^ 256 &&
            result.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo data)))
          s!"reverted word differs from the Core transaction: {label} at {input}"
        ensure (comparedSlots.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage slot)
          s!"a reverted transaction changed the committed slots: {label} at {input}"
        if let some (sum, _, _) := expected then
          ensure (data == sum) s!"reverted word differs from the two-slot recurrence: {label}"
        reverted := reverted + 1
    world := result.finalWorld
  let some ⟨_, installed⟩ := registry.resolve? world target |
    throw (IO.userError s!"committed world no longer resolves the contract: {label}")
  ensure (rollbackSourceCall source (accountStorage installed.account) "run" [2 ^ 256]).isNone
    s!"rollback method accepted an argument outside uint256: {label}"
  return (returned, reverted)

/-- Every history of a plan, from each initial storage. -/
private def checkPlan (label : String) (plan : CheckedPlan) (inputs : List Nat)
    (step : Option (Word → Word) := none) : IO (String × Nat × Nat) := do
  let program ← emitted label plan
  checkReprint label plan program.source
  let mut returned := 0
  let mut reverted := 0
  for initial in initialStorages do
    let (more, fewer) ← checkHistory label plan program.source initial inputs step
    returned := returned + more
    reverted := reverted + fewer
  return (program.source, returned, reverted)

private def regressionInputs : List Nat := [2, 3, 4, 1, maximum, high, high + 1, 0, 7]

private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

private def pairStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.pair (.loadCell (.var 0))
      (.letE (.storeCell (.var 0) (word 2)) (.loadCell (.var 1))))
      (.binary .wordAdd (.first (.var 0)) (.second (.var 0))))

/-- The regression plans of `SourceStorageRollbackEmitter`, with their step
functions. Returns the identity plan's text and the transaction counts. -/
private def regressionChecks : IO (String × Nat × Nat) := do
  let plus (amount : Nat) (input : Word) : Word := input.add (Word.ofNatModulo amount)
  let clearOne (input : Word) : Word := if input == Word.ofNatModulo 1 then Word.zero else input
  let mut returned := 0
  let mut reverted := 0
  let (identitySource, more, fewer) ← checkPlan "identity"
    (← checkedPlan "identity" [.var 0] entry) regressionInputs (some id)
  returned := returned + more
  reverted := reverted + fewer
  for (label, helpers, body, step) in [
      ("clears", [.ifE (.binary .wordEq (.var 0) (word 1)) (word 0) (.var 0)], entry, clearOne),
      ("private cell", [privateStep], .binary .wordSub entry (word 1), plus 1),
      ("mixed", [increment, pairStep], call 1 (call 2 (.var 0)), plus 3),
      ("constant", [.var 0], word 0, fun _ => Word.zero),
      ("division", [.binary .wordDiv (.var 0) (word 1)], entry, id)] do
    let (_, more, fewer) ← checkPlan label (← checkedPlan label helpers body) regressionInputs
      (some step)
    returned := returned + more
    reverted := reverted + fewer
  return (identitySource, returned, reverted)

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

/-- Generated rollback scenarios at two budgets, with their generated inputs
and two more. Seeds the generator rejects are skipped. -/
private def checkGenerated : IO (Nat × Nat × Nat) := do
  let mut plans := 0
  let mut returned := 0
  let mut reverted := 0
  for nodes in [256, 512] do
    for seed in List.range 12 do
      match StorageRollback.generatedScenario (Seed.ofNat seed) nodes with
      | .error _ => pure ()
      | .ok (scenario, _) =>
          let inputs := scenario.transactions.map (·.input.val)
          let (_, more, fewer) ← checkPlan s!"generated budget {nodes} seed {seed}"
            scenario.plan (inputs ++ [1, maximum - 1])
          plans := plans + 1
          returned := returned + more
          reverted := reverted + fewer
  ensure (plans ≥ 16) s!"the rollback generator produced only {plans} plans"
  return (plans, returned, reverted)

/-- Storage texts are outside the rollback grammar. -/
private def checkStorageTexts : IO Nat := do
  let mut count := 0
  for (helpers, body) in [([privateStep], entry), ([.binary .wordDiv (.var 0) (word 1)], entry)] do
    let some step := Aggregates.CheckedDAG.ofParts? helpers body |
      throw (IO.userError "storage fixture failed the aggregate DAG checker")
    let some plan := Solcore.Synthesis.Core.StorageContract.CheckedPlan.ofParts? step |
      throw (IO.userError "storage fixture failed the host checker")
    let program ← match Storage.emit plan with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"storage emission failed: {reprStr error}")
    ensure ((parseStorageSource program.source).isSome &&
        (parseRollbackSource program.source).isNone)
      "the rollback grammar accepted a storage text"
    count := count + 1
  return count

/-- The outcome of one call from a nonempty storage. -/
private def observed (source : String) (input : Nat) : Option String :=
  let storage : Storage := fun slot => if slot = 0 then 5 else if slot = 1 then 9 else 7
  (rollbackSourceCall source storage "run" [input]).map fun
    | .returned value storage' => s!"returned {value} {storage' 0} {storage' 1}"
    | .reverted data => s!"reverted {data}"

/-- Altered rollback programs lose their meaning or change their outcome. -/
private def checkAlterations (source : String) : IO Unit := do
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"rollback fixture has no {old}"
    pure changed
  let even := observed source 2
  let odd := observed source 3
  ensure (even.isSome && odd.isSome) "the rollback fixture has no meaning"
  let longer ← replace "revert_(0, 32);" "revert_(0, 64);"
  ensure ((parseRollbackSource longer).isSome && observed longer 3 == none &&
      observed longer 2 == even)
    "a revert of other bytes received a meaning"
  let elsewhere ← replace "revert_(0, 32);" "revert_(32, 32);"
  ensure ((parseRollbackSource elsewhere).isSome && observed elsewhere 3 == none)
    "a revert from another offset received a meaning"
  let otherWord ← replace "mstore(0, sc_result);" "mstore(0, sc_final0);"
  ensure ((parseRollbackSource otherWord).isSome && observed otherWord 3 != odd &&
      observed otherWord 2 == even)
    "storing another word kept the reverted word"
  let flipped ← replace "if ((sc_input & 1) == 1) {" "if ((sc_input & 1) == 0) {"
  ensure ((parseRollbackSource flipped).isSome && observed flipped 2 != even &&
      observed flipped 3 != odd)
    "a flipped condition kept the outcomes"
  let noRevert ← replace
    "        if ((sc_input & 1) == 1) {\n            mstore(0, sc_result);\n            revert_(0, 32);\n        }\n" ""
  ensure ((parseRollbackSource noRevert).isSome && observed noRevert 3 != odd)
    "a program without its revert block kept the odd outcome"
  let doubled ← replace "if ((sc_input & 1) == 1) {" "if (((sc_input & 1) == 1)) {"
  ensure (parseRollbackSource doubled).isNone
    "a revert condition in two pairs of parentheses was accepted"
  let twoOperators ← replace "sc_final0 + sc_final1;" "sc_final0 + sc_final1 + 0;"
  ensure (parseRollbackSource twoOperators).isNone
    "two infix operations without parentheses were accepted"
  let booleanStore ← replace "mstore(0, sc_result);" "mstore(0, true);"
  ensure ((parseRollbackSource booleanStore).isSome && observed booleanStore 3 == none)
    "a Boolean was stored in memory"

def testSourceRollbackMeaning : IO Unit := do
  let (identitySource, regressionReturned, regressionReverted) ← regressionChecks
  let mut primitivesReturned := 0
  let mut primitivesReverted := 0
  for (label, body) in primitiveSteps do
    let (_, more, fewer) ← checkPlan label (← checkedPlan label [.var 0] body)
      [0, 1, maximum, high]
    primitivesReturned := primitivesReturned + more
    primitivesReverted := primitivesReverted + fewer
  let (generated, generatedReturned, generatedReverted) ← checkGenerated
  let storageTexts ← checkStorageTexts
  checkAlterations identitySource
  IO.println (s!"rollback source meaning: 6 regression plans " ++
    s!"({regressionReturned} returned, {regressionReverted} reverted), 14 raw primitive plans " ++
    s!"({primitivesReturned} returned, {primitivesReverted} reverted) and {generated} generated " ++
    s!"plans ({generatedReturned} returned, {generatedReverted} reverted) settle as Core from " ++
    s!"3 initial storages; {storageTexts} storage texts are outside the rollback grammar")

end Tests.SourceRollbackMeaning
