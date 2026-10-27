import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.ScalarMeaning.StorageEmitter
import Solcore.Test.SourceScalarMeaning
import Solcore.ContractRuntime.CheckedContractRegistry

/-! Executable checks of the storage source meaning on actual storage emitter
output. Each emitted text is lexed, parsed with the storage grammar and called
under the storage source semantics, one transaction at a time, from the storage
of the account that the committed world holds. Each call is compared with the
original Core contract's top-level transaction: the returned word, its ABI
bytes and the committed account storage. `Storage.emit_source_meaning` covers
every successful emission and every installed account; these checks exercise
the same definitions on real texts and histories, from empty and from nonempty
storage. Altered texts lose or change their meaning. -/
set_option autoImplicit false

namespace Tests.SourceStorageMeaning

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.StorageContract (CheckedPlan)

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
    throw (IO.userError s!"storage step failed the aggregate DAG checker: {label}")
  let some plan := CheckedPlan.ofParts? step |
    throw (IO.userError s!"storage plan failed the host checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match Storage.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"storage emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the storage grammar to a file whose printing is
that text, with one function per helper and `sc_step`, and the aliases exactly
when a step body uses one. The loop-free grammar rejects it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseStorageSource source |
    throw (IO.userError s!"emitted storage source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed storage source does not print back: {label}"
  ensure (file.opcodeAliases == aggregateAliases (plan.step.helpers ++ [plan.step.entry]) &&
      file.functions.length == plan.step.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == Storage.contractName)
    s!"storage file has other aliases, functions or contract: {label}"
  ensure (parseSource source).isNone s!"the loop-free grammar accepted a storage text: {label}"

private def target : Address := ⟨100, by decide⟩
private def caller : Address := ⟨200, by decide⟩

/-- The slots compared after each transaction: both written slots, untouched
ones and the highest. -/
private def comparedSlots : List Nat := [0, 1, 2, 3, high, maximum]

/-- Two nonempty initial storages; the second makes slot 1 wrap to zero. -/
private def initialStorages : List (List (Nat × Nat)) :=
  [[], [(0, 5), (1, 9), (2, 7), (high, 3)], [(0, maximum), (1, maximum), (3, 1)]]

/-- Runs one history from an account holding `initial`. Before each
transaction the source storage is read from the account that the committed
world holds; the source call must give the transaction's word and committed
slots. When `step` is given, the results must also follow the two-slot
recurrence. Returns the number of transactions. -/
private def checkHistory (label : String) (plan : CheckedPlan) (source : String)
    (initial : List (Nat × Nat)) (inputs : List Nat)
    (step : Option (Word → Word) := none) : IO Nat := do
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == target then some plan.contract else none⟩
  let installedAccount := initial.foldl (fun account (slot, value) =>
    account.storageWrite (Word.ofNatModulo slot) (Word.ofNatModulo value))
    (Account.empty.withCode plan.code)
  let mut world := WorldState.empty.putAccount target installedAccount
  let mut previous : Option Storage := none
  let mut count := 0
  for input in inputs do
    let calldata := Solcore.Synthesis.Stateful.StorageExecution.inputData (Word.ofNatModulo input)
    ensure (calldata.wordBE? (Word.ofNatModulo 4) == some (Word.ofNatModulo input))
      s!"canonical calldata does not carry its input word: {label}"
    let some ⟨contract, installed⟩ := registry.resolve? world target |
      throw (IO.userError s!"committed world no longer resolves the contract: {label}")
    let storage := accountStorage installed.account
    if let some committed := previous then
      ensure (comparedSlots.all fun slot => storage slot == committed slot)
        s!"committed account storage differs from the source storage: {label}"
    let invocation : TopLevelInvocation :=
      { target, caller, callValue := Word.zero, inputData := calldata }
    let some (value, storage') := storageSourceCall source storage "run" [input] |
      throw (IO.userError s!"storage source call has no meaning: {label} at {input}")
    match TopLevelExecution.run contract invocation installed 0 with
    | .outOfFuel _ _ _ _ _ _ => pure ()
    | .completed _ => throw (IO.userError s!"zero fuel completed a storage transaction: {label}")
    match TopLevelExecution.run contract invocation installed 100000 with
    | .outOfFuel _ _ _ _ _ _ =>
        throw (IO.userError s!"storage transaction exhausted its fuel: {label}")
    | .completed result =>
        ensure (value < 2 ^ 256 && result.coreValue == .word (Word.ofNatModulo value) &&
            result.outcome == .returned (encodeWordBytesBE (Word.ofNatModulo value)))
          s!"storage source result differs from the Core transaction: {label} at {input}"
        let some account := result.finalWorld.account? target |
          throw (IO.userError s!"committed storage account disappeared: {label}")
        ensure (comparedSlots.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage' slot)
          s!"committed slots differ from the source storage: {label} at {input}"
        if let some stepResult := step then
          let first := Word.ofNatModulo (storage 0)
          let second := (Word.ofNatModulo (storage 1)).add (Word.ofNatModulo 1)
          let computed := stepResult ((Word.ofNatModulo input).add first)
          ensure (storage' 0 == computed.val && storage' 1 == second.val &&
              value == (computed.add second).val)
            s!"storage results differ from the two-slot recurrence: {label} at {input}"
        world := result.finalWorld
        previous := some storage'
    count := count + 1
  let some ⟨_, installed⟩ := registry.resolve? world target |
    throw (IO.userError s!"committed world no longer resolves the contract: {label}")
  ensure (storageSourceCall source (accountStorage installed.account) "run" [2 ^ 256]).isNone
    s!"storage method accepted an argument outside uint256: {label}"
  return count

/-- Every history of a plan, from each initial storage. -/
private def checkPlan (label : String) (plan : CheckedPlan) (inputs : List Nat)
    (step : Option (Word → Word) := none) : IO (String × Nat) := do
  let program ← emitted label plan
  checkReprint label plan program.source
  let mut count := 0
  for initial in initialStorages do
    count := count + (← checkHistory label plan program.source initial inputs step)
  return (program.source, count)

private def regressionInputs : List Nat := [0, 1, 3, maximum, 0, high, 7]

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

/-- The regression plans of `SourceStorageEmitter`, with their step functions.
Returns the increment plan's text and the number of transactions. -/
private def regressionChecks : IO (String × Nat) := do
  let plus (amount : Nat) (input : Word) : Word := input.add (Word.ofNatModulo amount)
  let (incrementSource, first) ← checkPlan "increment" (← checkedPlan "increment" [increment] entry)
    regressionInputs (some (plus 1))
  let (_, second) ← checkPlan "private cell"
    (← checkedPlan "private cell" [privateStep] (.binary .wordSub entry (word 1)))
    regressionInputs (some (plus 1))
  let (_, third) ← checkPlan "mixed"
    (← checkedPlan "mixed" [increment, pairStep] (call 1 (call 2 (.var 0))))
    regressionInputs (some (plus 3))
  let (_, fourth) ← checkPlan "identity" (← checkedPlan "identity" [increment] (.var 0))
    [5, 2 ^ 256 - 5, 0] (some id)
  let (_, fifth) ← checkPlan "constant" (← checkedPlan "constant" [increment] (word 0))
    regressionInputs (some fun _ => Word.zero)
  let (_, sixth) ← checkPlan "division" (← checkedPlan "division"
    [.binary .wordDiv (.var 0) (word 1)] entry) regressionInputs (some id)
  return (incrementSource, first + second + third + fourth + fifth + sixth)

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

/-- Generated storage scenarios at two budgets, each with its own generated
inputs. Seeds the generator rejects are skipped. -/
private def checkGenerated : IO (Nat × Nat) := do
  let mut plans := 0
  let mut transactions := 0
  for nodes in [256, 512] do
    for seed in List.range 12 do
      match Storage.generatedScenario (Seed.ofNat seed) nodes with
      | .error _ => pure ()
      | .ok (scenario, _) =>
          let inputs := scenario.transactions.map (·.input.val)
          let (_, count) ← checkPlan s!"generated budget {nodes} seed {seed}" scenario.plan
            (inputs ++ [0, maximum])
          plans := plans + 1
          transactions := transactions + count
  ensure (plans ≥ 16) s!"the storage generator produced only {plans} plans"
  return (plans, transactions)

/-- Loop-free aggregate texts are outside the storage grammar. -/
private def checkLoopFree : IO Nat := do
  let mut count := 0
  for (helpers, body) in [([privateStep], entry), ([.binary .wordDiv (.var 0) (word 1)], entry)] do
    let some graph := Aggregates.CheckedDAG.ofParts? helpers body |
      throw (IO.userError "loop-free aggregate fixture failed its checker")
    let program ← match Aggregate.emit graph with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"aggregate emission failed: {reprStr error}")
    ensure ((parseSource program.source).isSome && (parseStorageSource program.source).isNone)
      "the storage grammar accepted a loop-free aggregate text"
    count := count + 1
  return count

/-- The result and the first slots after one call from a nonempty storage. -/
private def observed (source : String) : Option (Nat × Nat × Nat × Nat) :=
  let storage : Storage := fun slot => if slot = 0 then 5 else if slot = 1 then 9 else 7
  (storageSourceCall source storage "run" [1]).map fun (value, storage') =>
    (value, storage' 0, storage' 1, storage' 2)

/-- Altered storage programs lose their meaning or change their result. -/
private def checkAlterations (source : String) : IO Unit := do
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"storage fixture has no {old}"
    pure changed
  let expected := observed source
  ensure expected.isSome "the storage fixture has no meaning"
  let swappedSlot ← replace "        sstore(0, sc_computed);" "        sstore(2, sc_computed);"
  ensure ((parseStorageSource swappedSlot).isSome && observed swappedSlot != expected)
    "a store to another slot kept its result"
  let otherLoad ← replace "        let sc_old0: word = sload(0);"
    "        let sc_old0: word = sload(2);"
  ensure ((parseStorageSource otherLoad).isSome && observed otherLoad != expected)
    "a load of another slot kept its result"
  let dropped ← replace "        sstore(1, sc_old1 + 1);\n" ""
  ensure ((parseStorageSource dropped).isSome && observed dropped != expected)
    "a program without its second store kept its result"
  let parenthesized ← replace "sc_step(sc_input + sc_old0)" "sc_step((sc_input + sc_old0))"
  ensure ((parseStorageSource parenthesized).isSome && observed parenthesized == expected)
    "a parenthesized step argument changed the result"
  let twoOperators ← replace "sstore(1, sc_old1 + 1);" "sstore(1, sc_old1 + 1 + 1);"
  ensure (parseStorageSource twoOperators).isNone
    "two infix operations without parentheses were accepted"
  let helperLoad ← replace "    let sc_v0: word = 1;\n" "    let sc_v0: word = sload(1);\n"
  ensure ((parseStorageSource helperLoad).isSome && observed helperLoad == none)
    "a free function that reads storage received a meaning"
  let booleanStore ← replace "        sstore(0, sc_computed);" "        sstore(0, true);"
  ensure ((parseStorageSource booleanStore).isSome && observed booleanStore == none)
    "a Boolean was stored"
  let noStoreImport ← replace "import {sload, sstore} from std.opcodes;"
    "import {sload} from std.opcodes;"
  ensure (parseStorageSource noStoreImport).isNone "an import line without sstore was accepted"

def testSourceStorageMeaning : IO Unit := do
  let (incrementSource, regression) ← regressionChecks
  let mut primitives := 0
  for (label, body) in primitiveSteps do
    let (_, count) ← checkPlan label (← checkedPlan label [.var 0] body) [0, 1, maximum, high]
    primitives := primitives + count
  let (generated, generatedTransactions) ← checkGenerated
  let loopFree ← checkLoopFree
  checkAlterations incrementSource
  IO.println (s!"storage source meaning: 6 regression plans ({regression} transactions), " ++
    s!"14 raw primitive plans ({primitives} transactions) and {generated} generated plans " ++
    s!"({generatedTransactions} transactions) agree with Core from 3 initial storages; " ++
    s!"{loopFree} loop-free texts are outside the storage grammar")

end Tests.SourceStorageMeaning
