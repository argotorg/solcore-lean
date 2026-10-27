import Solcore.Synthesis.Source.KeyedStorageCases
import Solcore.Synthesis.Source.ScalarMeaning.KeyedEmitter
import Solcore.Test.SourceScalarMeaning
import Solcore.ContractRuntime.CheckedContractRegistry

/-! Executable checks of the keyed source meaning on actual keyed-storage
emitter output. Each emitted text is lexed, parsed with the keyed grammar and
called under the keyed source semantics with a key and an input, one
transaction at a time, from the storage of the account that the committed
world holds. Each call is compared with the original Core contract's top-level
transaction: a returned call with the returned ABI bytes and the committed
slots, a reverted call with the reverted bytes and an unchanged account
storage. Histories include the keys zero and `2^256 - 1`, whose writes alias the
counter slot. `KeyedStorage.emit_source_meaning` covers every successful
emission and every installed account; these checks exercise the same
definitions on real texts and histories. Altered texts lose or change their
meaning. -/
set_option autoImplicit false

namespace Tests.SourceKeyedMeaning

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.KeyedStorage (CheckedPlan)

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
    throw (IO.userError s!"keyed step failed the aggregate DAG checker: {label}")
  let some plan := CheckedPlan.ofParts? step |
    throw (IO.userError s!"keyed plan failed the host checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.KeyedStorage.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"keyed emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the keyed grammar to a file whose printing is
that text, with one function per helper and `sc_step`, and the aliases exactly
when a step body uses one. The loop-free, storage and rollback grammars reject
it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseKeyedSource source |
    throw (IO.userError s!"emitted keyed source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed keyed source does not print back: {label}"
  ensure (file.opcodeAliases == aggregateAliases (plan.step.helpers ++ [plan.step.entry]) &&
      file.functions.length == plan.step.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == Solcore.Synthesis.Source.KeyedStorage.contractName)
    s!"keyed file has other aliases, functions or contract: {label}"
  ensure ((parseSource source).isNone && (parseStorageSource source).isNone &&
      (parseRollbackSource source).isNone)
    s!"the loop-free, storage or rollback grammar accepted a keyed text: {label}"

private def target : Address := ⟨100, by decide⟩
private def caller : Address := ⟨200, by decide⟩

/-- Fixed slots compared after each transaction, besides the key and its
successor. -/
private def fixedSlots : List Nat := [0, 1, 2, 5, 6, high, high + 1, maximum - 1, maximum]

/-- Two nonempty initial storages; the second fills the slots around zero and
the maximum. -/
private def initialStorages : List (List (Nat × Nat)) :=
  [[], [(0, 5), (1, 9), (5, 7), (high, 3)], [(0, maximum), (1, maximum), (maximum, 4)]]

/-- The source storage written in the keyed order, for the recurrence. -/
private def write (storage : Nat → Nat) (slot value : Nat) : Nat → Nat :=
  fun other => if other = slot then value else storage other

/-- Runs one history of `(key, input)` rows from an account holding `initial`.
Before each transaction the source storage is read from the account that the
committed world holds; the source call must settle as the Core transaction.
When `step` is given, the outcome's word and the written slots must also follow
the keyed recurrence. When `golden` is given, the outcomes must be those
hand-known words. Returns the numbers of returned and reverted transactions. -/
private def checkHistory (label : String) (plan : CheckedPlan) (source : String)
    (initial : List (Nat × Nat)) (rows : List (Nat × Nat))
    (step : Option (Word → Word) := none) (golden : List (Bool × Nat) := []) :
    IO (Nat × Nat) := do
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == target then some plan.contract else none⟩
  let installedAccount := initial.foldl (fun account (slot, value) =>
    account.storageWrite (Word.ofNatModulo slot) (Word.ofNatModulo value))
    (Account.empty.withCode plan.code)
  let mut world := WorldState.empty.putAccount target installedAccount
  let mut returned := 0
  let mut reverted := 0
  let mut index := 0
  for (key, input) in rows do
    let calldata := Solcore.Synthesis.Stateful.KeyedStorageExecution.inputData
      (Word.ofNatModulo key) (Word.ofNatModulo input)
    ensure (calldata.wordBE? (Word.ofNatModulo 4) == some (Word.ofNatModulo key) &&
        calldata.wordBE? (Word.ofNatModulo 36) == some (Word.ofNatModulo input))
      s!"canonical calldata does not carry its key and input words: {label}"
    let some ⟨contract, installed⟩ := registry.resolve? world target |
      throw (IO.userError s!"committed world no longer resolves the contract: {label}")
    let storage := accountStorage installed.account
    let invocation : TopLevelInvocation :=
      { target, caller, callValue := Word.zero, inputData := calldata }
    let some outcome := keyedSourceCall source storage "run" [key, input] |
      throw (IO.userError s!"keyed source call has no meaning: {label} at {key}, {input}")
    match TopLevelExecution.run contract invocation installed 0 with
    | .outOfFuel _ _ _ _ _ _ => pure ()
    | .completed _ => throw (IO.userError s!"zero fuel completed a keyed transaction: {label}")
    let result ← match TopLevelExecution.run contract invocation installed 100000 with
      | .outOfFuel _ _ _ _ _ _ =>
          throw (IO.userError s!"keyed transaction exhausted its fuel: {label}")
      | .completed result => pure result
    let some account := result.finalWorld.account? target |
      throw (IO.userError s!"committed storage account disappeared: {label}")
    let successor := (key + 1) % 2 ^ 256
    let compared := key :: successor :: fixedSlots
    let expected : Option (Nat × (Nat → Nat)) := step.map fun stepResult =>
      let old := storage key
      let count := storage 0
      let computed := (stepResult ((Word.ofNatModulo input).add (Word.ofNatModulo old))).val
      let written := write (write (write storage key computed) successor old) 0
        ((count + 1) % 2 ^ 256)
      ((written key + written successor + written 0) % 2 ^ 256, written)
    match outcome with
    | .returned value storage' =>
        ensure (input % 2 == 0) s!"an odd input returned: {label} at {key}, {input}"
        ensure (value < 2 ^ 256 &&
            result.outcome == .returned (encodeWordBytesBE (Word.ofNatModulo value)))
          s!"returned word differs from the Core transaction: {label} at {key}, {input}"
        ensure (compared.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage' slot)
          s!"committed slots differ from the source storage: {label} at {key}, {input}"
        if let some (sum, written) := expected then
          ensure (value == sum && compared.all fun slot => storage' slot == written slot)
            s!"returned results differ from the keyed recurrence: {label} at {key}, {input}"
        if let some (odd, payload) := golden[index]? then
          ensure (!odd && value == payload) s!"keyed golden row changed: {label} row {index}"
        returned := returned + 1
    | .reverted data =>
        ensure (input % 2 == 1) s!"an even input reverted: {label} at {key}, {input}"
        ensure (data < 2 ^ 256 &&
            result.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo data)))
          s!"reverted word differs from the Core transaction: {label} at {key}, {input}"
        ensure (compared.all fun slot =>
            (account.storageRead (Word.ofNatModulo slot)).val == storage slot)
          s!"a reverted transaction changed the committed slots: {label} at {key}, {input}"
        if let some (sum, _) := expected then
          ensure (data == sum) s!"reverted word differs from the keyed recurrence: {label}"
        if let some (odd, payload) := golden[index]? then
          ensure (odd && data == payload) s!"keyed golden row changed: {label} row {index}"
        reverted := reverted + 1
    world := result.finalWorld
    index := index + 1
  let some ⟨_, installed⟩ := registry.resolve? world target |
    throw (IO.userError s!"committed world no longer resolves the contract: {label}")
  ensure (keyedSourceCall source (accountStorage installed.account) "run" [2 ^ 256, 0]).isNone
    s!"keyed method accepted a key outside uint256: {label}"
  ensure (keyedSourceCall source (accountStorage installed.account) "run" [0]).isNone
    s!"keyed method accepted a missing argument: {label}"
  return (returned, reverted)

/-- Every history of a plan, from each initial storage. -/
private def checkPlan (label : String) (plan : CheckedPlan) (rows : List (Nat × Nat))
    (step : Option (Word → Word) := none) : IO (String × Nat × Nat) := do
  let program ← emitted label plan
  checkReprint label plan program.source
  let mut returned := 0
  let mut reverted := 0
  for initial in initialStorages do
    let (more, fewer) ← checkHistory label plan program.source initial rows step
    returned := returned + more
    reverted := reverted + fewer
  return (program.source, returned, reverted)

/-- Keys around zero, the maximum and the middle, with inputs of both
parities. -/
private def regressionRows : List (Nat × Nat) :=
  [(5, 2), (0, 4), (maximum, 3), (maximum - 1, 0), (maximum, 2), (maximum - 1, 6),
    (high, 7), (high, 2), (1, 1), (0, 0), (2, maximum)]

private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

/-- The golden histories of `SourceKeyedStorageEmitter`, from empty storage. -/
private def goldenChecks : IO Unit := do
  let identity ← checkedPlan "identity" [.var 0] entry
  let identitySource := (← emitted "identity" identity).source
  let _ ← checkHistory "golden aliasing" identity identitySource []
    [(5, 2), (0, 4), (maximum, 3)] (some id) [(false, 3), (false, 5), (true, 9)]
  let _ ← checkHistory "golden wrapping" identity identitySource []
    [(maximum - 1, 0), (maximum, 2), (maximum - 1, 6)] (some id)
    [(false, 1), (false, 6), (false, 9)]
  let constant ← checkedPlan "constant" [.var 0] (word 0)
  let _ ← checkHistory "golden deletion" constant (← emitted "constant" constant).source []
    [(1, 0), (0, 0), (1, 1)] (some fun _ => Word.zero) [(false, 1), (false, 5), (true, 4)]
  let cell ← checkedPlan "private cell" [privateStep] (.binary .wordSub entry (word 1))
  let _ ← checkHistory "golden cell" cell (← emitted "private cell" cell).source []
    [(high, 7), (high, 2)] (some fun input => input.add (Word.ofNatModulo 1))
    [(true, 9), (false, 4)]

/-- The regression plans of `SourceKeyedStorageEmitter`, with their step
functions. Returns the identity plan's text and the transaction counts. -/
private def regressionChecks : IO (String × Nat × Nat) := do
  let plus (amount : Nat) (input : Word) : Word := input.add (Word.ofNatModulo amount)
  let mut returned := 0
  let mut reverted := 0
  let (identitySource, more, fewer) ← checkPlan "identity"
    (← checkedPlan "identity" [.var 0] entry) regressionRows (some id)
  returned := returned + more
  reverted := reverted + fewer
  for (label, helpers, body, step) in [
      ("increment", [increment], entry, plus 1),
      ("private cell", [privateStep], .binary .wordSub entry (word 1), plus 1),
      ("constant", [.var 0], word 0, fun _ => Word.zero),
      ("division", [.binary .wordDiv (.var 0) (word 1)], entry, id)] do
    let (_, more, fewer) ← checkPlan label (← checkedPlan label helpers body) regressionRows
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

/-- Generated keyed scenarios at two budgets, with their generated rows and
two more. Seeds the generator rejects are skipped. -/
private def checkGenerated : IO (Nat × Nat × Nat) := do
  let mut plans := 0
  let mut returned := 0
  let mut reverted := 0
  for nodes in [256, 512] do
    for seed in List.range 12 do
      match Solcore.Synthesis.Source.KeyedStorage.generatedScenario (Seed.ofNat seed) nodes with
      | .error _ => pure ()
      | .ok (scenario, _) =>
          let rows := scenario.transactions.map fun transaction =>
            (transaction.key.val, transaction.input.val)
          let (_, more, fewer) ← checkPlan s!"generated budget {nodes} seed {seed}"
            scenario.plan (rows ++ [(0, 1), (maximum, 2)])
          plans := plans + 1
          returned := returned + more
          reverted := reverted + fewer
  ensure (plans ≥ 16) s!"the keyed generator produced only {plans} plans"
  return (plans, returned, reverted)

/-- The outcome of one call from a nonempty storage. -/
private def observed (source : String) (key input : Nat) : Option String :=
  let storage : Storage := fun slot =>
    if slot = 0 then 5 else if slot = 1 then 9 else if slot = 2 then 11 else 7
  (keyedSourceCall source storage "run" [key, input]).map fun
    | .returned value storage' =>
        s!"returned {value} {storage' 0} {storage' 1} {storage' 2} {storage' 3}"
    | .reverted data => s!"reverted {data}"

/-- Altered keyed programs lose their meaning or change their outcome. -/
private def checkAlterations (source : String) : IO Unit := do
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"keyed fixture has no {old}"
    pure changed
  let atOne := observed source 1 2
  let atZero := observed source 0 2
  ensure (atOne.isSome && atZero.isSome) "the keyed fixture has no meaning"
  let farther ← replace "sstore(sc_key + 1, sc_old);" "sstore(sc_key + 2, sc_old);"
  ensure ((parseKeyedSource farther).isSome && observed farther 1 2 != atOne)
    "a write two slots on kept the result"
  let reordered ← replace
    "        sstore(sc_key, sc_computed);\n        sstore(sc_key + 1, sc_old);\n        sstore(0, sc_count + 1);\n"
    "        sstore(0, sc_count + 1);\n        sstore(sc_key, sc_computed);\n        sstore(sc_key + 1, sc_old);\n"
  ensure ((parseKeyedSource reordered).isSome && observed reordered 0 2 != atZero &&
      observed reordered 1 2 == atOne)
    "reordered writes kept the aliased result or changed an unaliased one"
  let swappedKey ← replace "let sc_key: word = Typedef.rep(key);"
    "let sc_key: word = Typedef.rep(input);"
  ensure ((parseKeyedSource swappedKey).isSome && observed swappedKey 1 2 != atOne)
    "a key read from the input kept the result"
  let nested ← replace "sc_final_key + sc_final_next + sc_final_count;"
    "(sc_final_key + sc_final_next) + sc_final_count;"
  ensure ((parseKeyedSource nested).isSome && observed nested 1 2 == atOne &&
      observed nested 0 2 == atZero)
    "a parenthesized sum changed the result"
  let wrapped ← replace "sload(sc_key + 1);" "sload((sc_key + 1));"
  ensure ((parseKeyedSource wrapped).isSome && observed wrapped 1 2 == atOne)
    "a parenthesized load argument changed the result"
  let fourTerms ← replace "sc_final_key + sc_final_next + sc_final_count;"
    "sc_final_key + sc_final_next + sc_final_count + 0;"
  ensure (parseKeyedSource fourTerms).isNone "a sum of four terms was accepted"
  let mixed ← replace "sc_final_key + sc_final_next + sc_final_count;"
    "sc_final_key + sc_final_next * sc_final_count;"
  ensure (parseKeyedSource mixed).isNone "a mixed chain without parentheses was accepted"

def testSourceKeyedMeaning : IO Unit := do
  goldenChecks
  let (identitySource, regressionReturned, regressionReverted) ← regressionChecks
  let mut primitivesReturned := 0
  let mut primitivesReverted := 0
  for (label, body) in primitiveSteps do
    let (_, more, fewer) ← checkPlan label (← checkedPlan label [.var 0] body)
      [(0, 0), (1, 1), (maximum, high), (high, maximum)]
    primitivesReturned := primitivesReturned + more
    primitivesReverted := primitivesReverted + fewer
  let (generated, generatedReturned, generatedReverted) ← checkGenerated
  checkAlterations identitySource
  IO.println (s!"keyed source meaning: 4 golden histories, 5 regression plans " ++
    s!"({regressionReturned} returned, {regressionReverted} reverted), 14 raw primitive plans " ++
    s!"({primitivesReturned} returned, {primitivesReverted} reverted) and {generated} generated " ++
    s!"plans ({generatedReturned} returned, {generatedReverted} reverted) settle as Core from " ++
    "3 initial storages")

end Tests.SourceKeyedMeaning
