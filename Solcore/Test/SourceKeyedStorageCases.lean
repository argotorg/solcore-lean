import Solcore.Synthesis.Source.KeyedStorageCases

/-! Keyed-storage case regressions: exact replay, bounded generation from an
independent sequence stream, canonical transaction/slot boundaries and typed
scenario reductions over steps, transactions, inputs and keys. Expected values
here are test goldens only; emitted cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceKeyedStorageCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.KeyedStorage (CheckedPlan)
open Solcore.Synthesis.Stateful.KeyedStorageExecution (Transaction Bindings)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def rows (value : Json) (name : String := "transactions") : IO (Array Json) :=
  get (value.getObjValAs? (Array Json) name)
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩⟩

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "keyed fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "keyed wrapper failed host admission")
  return plan
private def transactions (values : List (Nat × Nat)) : List Transaction :=
  values.zipIdx.map fun ((key, input), index) =>
    ⟨"call-" ++ toString index, Word.ofNatModulo key, Word.ofNatModulo input⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × Nat)) : IO KeyedStorage.CheckedScenario :=
  get (KeyedStorage.checkedScenario plan (transactions values))
private def imported (value : KeyedStorage.CheckedScenario) (fuel : Nat := 10000) : IO Json :=
  get (KeyedStorage.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(5, 2), (0, 4), (2 ^ 256 - 1, 3)]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson (["0", "1", "5", "6", toString (2 ^ 256 - 1)] : List String))
    "case did not declare the derived observed slots"
  ensure ((← get (KeyedStorage.replayCase saved 10000)) == saved) "imported keyed case did not replay"
  ensure ((← get (KeyedStorage.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 10000)) == saved)
    "keyed replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(1, 2), (2 ^ 255, 3)])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "keys or inputs were substituted into source or Core code"
  let observed := KeyedStorage.observe value bindings 10000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "returned", some "reverted"])
    "keyed scenario did not follow its input parities"
  ensure ((← rows (KeyedStorage.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 10000)) == (← rows observed))
    "address-independent keyed profile changed with bindings"
  -- The maximum key's wrapping successor is both the counter and another key.
  ensure (KeyedStorage.aliases value.transactions == ["key-counter", "successor-counter", "successor-key"] &&
    KeyedStorage.aliases (transactions [(7, 0), (8, 0), (7, 0)]) == ["repeated-key", "successor-key"] &&
    KeyedStorage.aliases (transactions [(3, 0)]) == [])
    "static alias inventory changed"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := KeyedStorage.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 7 && (choices.take 6).all (· < 6) && choices.getD 6 0 < 4)
      "sequence choices escaped their banks"
    match KeyedStorage.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 && Wire.programNodes value.program ≤ 384 &&
          value.plan.step.helpers.length == 1 + seed % 3) "keyed recipe lost node/transaction/helper bounds"
        ensure (value.transactions.all (fun tx => KeyedStorage.keyBank.contains tx.key)) "generated key escaped its bank"
        ensure ((value.transactions.map fun tx => tx.input.val % 2 == 1) == KeyedStorage.generatedParities (Seed.ofNat seed))
          "generated inputs lost their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (KeyedStorage.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (KeyedStorage.generatedScenario (Seed.ofNat 0) KeyedStorage.programOverhead) "undersized node budget accepted"
  let corpus := KeyedStorage.generateCases (Seed.ofNat 0) 384 4 512 10000
  ensure (corpus == KeyedStorage.generateCases (Seed.ofNat 0) 384 4 512 10000) "keyed generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "keyed count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (KeyedStorage.replayCase saved 10000)) == saved) "generated keyed provenance did not replay"
    let low ← get (KeyedStorage.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := KeyedStorage.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "keyed generation resource exhaustion was not distinguished"
  ensure ((← rows (KeyedStorage.generateCases (Seed.ofNat seed) 384 2 1 10000) "cases").size == 1 &&
    (← natural (KeyedStorage.generateCases (Seed.ofNat seed) 384 0 10 10000) "attempted") == 0 &&
    (← rows (KeyedStorage.generateCases (Seed.ofNat seed) 384 1 0 10000) "cases").isEmpty)
    "keyed generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("key", toJson "05"),
      ("key", toJson (toString (2 ^ 256))), ("key", toJson "6"), ("input", toJson "01"), ("input", toJson "7"),
      ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (KeyedStorage.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical keyed transaction accepted"
  rejected (KeyedStorage.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (KeyedStorage.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (KeyedStorage.decodeTransactions (toJson (List.replicate 4 first))) "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson (["0", "1"] : List String)),
      ("observedSlots", toJson (["1", "0", "5", "6", toString (2 ^ 256 - 1)] : List String)),
      ("executionFuel", toJson (10000001 : Nat)), ("keyedStoragePlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (KeyedStorage.caseProgram (saved.setObjVal! name bad)) "invalid keyed case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (KeyedStorage.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 10000)
      "tampered keyed provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (KeyedStorage.replayCase (withOrigin (origin.setObjVal! name bad)) 10000)
      "tampered generated keyed recipe accepted"
  let plan ← field saved "keyedStoragePlan"
  rejected (KeyedStorage.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical keyed plan accepted"
  rejected (KeyedStorage.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.storage-plan.v1")))
    "two-slot plan schema accepted as a keyed plan"
  rejected (KeyedStorage.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (KeyedStorage.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0xa444f5e9"))) 10000)
    "single-Word storage selector accepted for the keyed ABI"
  rejected (KeyedStorage.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-storage-case.v1")) 10000)
    "two-slot case schema accepted by the keyed tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [(2 ^ 256 - 1, 2), (2 ^ 255, 7), (2 ^ 256 - 1, 2 ^ 255)]
  let saved ← imported value
  let candidates ← get (KeyedStorage.shrinkCases saved 1000 10000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (KeyedStorage.shrinkCases saved 1000 10000)))
    "keyed reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredInput := false
  let mut loweredKey := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (KeyedStorage.caseProgram row)
    ensure (decide (KeyedStorage.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "keyed reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.program),
      ("transactions", KeyedStorage.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate keyed reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let sameCount := reduced.transactions.length == value.transactions.length
    loweredInput := loweredInput || (sameCount && (reduced.transactions.zip value.transactions).any
      fun (left, right) => left.input.val < right.input.val)
    loweredKey := loweredKey || (sameCount && (reduced.transactions.zip value.transactions).any
      fun (left, right) => left.key.val < right.key.val)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← field row "observedSlots") == KeyedStorage.observedSlotsJson reduced)
      "reduced case did not rederive its observed slots"
    ensure ((← get (KeyedStorage.replayCase row 10000)) == row) "reduced keyed case did not replay"
  ensure (removed && loweredInput && loweredKey && changedStep) "keyed shrink omitted sequence/input/key/step axes"
  ensure ((← rows (← get (KeyedStorage.shrinkCases saved 2 10000)) "cases") == result.extract 0 2 &&
    (← rows (← get (KeyedStorage.shrinkCases saved 0 10000)) "cases").isEmpty) "keyed shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (KeyedStorage.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", KeyedStorage.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", KeyedStorage.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (KeyedStorage.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 10000)
    "non-strict keyed reduction provenance accepted"

def testSourceKeyedStorageCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceKeyedStorageCases
