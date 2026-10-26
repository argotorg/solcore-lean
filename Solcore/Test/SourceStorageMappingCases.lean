import Solcore.Synthesis.Source.StorageMappingCases

/-! Keccak-mapping case regressions: exact replay, bounded generation from an
independent sequence stream, canonical transaction and declared-slot
boundaries, static alias kinds, and typed reductions over steps,
transactions, keys, inputs and flags. Expected values here are test goldens
only; cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceStorageMappingCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.StorageMapping (CheckedPlan)
open Solcore.Synthesis.Stateful.StorageMappingExecution (Transaction Bindings)

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
private def maximum : Nat := 2 ^ 256 - 1

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "mapping fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "mapping wrapper failed host admission")
  return plan
private def transactions (values : List (Nat × Nat × Nat)) : List Transaction :=
  values.zipIdx.map fun ((flags, key, input), index) =>
    ⟨"call-" ++ toString index, Word.ofNatModulo flags, Word.ofNatModulo key, Word.ofNatModulo input⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × Nat × Nat)) : IO StorageMapping.CheckedScenario :=
  get (StorageMapping.checkedScenario plan (transactions values))
private def imported (value : StorageMapping.CheckedScenario) (fuel : Nat := 1000000) : IO Json :=
  get (StorageMapping.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(0, 6, 1), (1, 7, 3), (2, maximum, 7)]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson ((value.observedSlots.map (·.val)).map toString) &&
    value.observedSlots.length == 6) "case did not declare the counter and six entry slots"
  ensure ((← get (StorageMapping.replayCase saved 1000000)) == saved) "imported mapping case did not replay"
  ensure ((← get (StorageMapping.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 1000000)) == saved)
    "mapping replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(5, 0, 2), (2, 1, 9)])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "keys, inputs or flags were substituted into source or Core code"
  let observed := StorageMapping.observe value bindings 1000000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "returned"])
    "mapping scenario did not follow its flags parities"
  ensure ((← get (StorageMapping.checkProtocol value observed)) == ["returned", "reverted", "returned"])
    "mapping history broke its counter or sum protocol"
  ensure ((← rows (StorageMapping.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 1000000)) == (← rows observed))
    "address-independent mapping profile changed with bindings"
  ensure (StorageMapping.aliases (transactions [(0, 6, 0), (0, 7, 0), (0, 6, 0)]) == ["repeated-key", "successor-key"] &&
    StorageMapping.aliases (transactions [(0, maximum, 0)]) == ["wrapped-successor"] &&
    StorageMapping.aliases (transactions [(0, 0, 0), (0, 2 ^ 255, 0)]) == [])
    "static mapping aliases changed"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := StorageMapping.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 7 && (choices.zip [6, 6, 6, 6, 6, 6, 4]).all (fun (value, bound) => value < bound))
      "sequence choices escaped their banks"
    match StorageMapping.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 &&
          Wire.programNodes value.program ≤ 384 + StorageMapping.hashNodes &&
          value.plan.step.helpers.length == 1 + seed % 3) "mapping recipe lost node/transaction/helper bounds"
        ensure (value.transactions.all fun tx => StorageMapping.keyBank.contains tx.key && StorageMapping.boundaryInputs.contains tx.input)
          "generated key or input escaped its bank"
        ensure ((value.transactions.map fun tx => tx.flags.val % 2 == 1) == StorageMapping.generatedParities (Seed.ofNat seed) &&
          value.transactions.all (fun tx => tx.flags.val < 2))
          "generated flags are not exactly their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (StorageMapping.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (StorageMapping.generatedScenario (Seed.ofNat 0) Solcore.Synthesis.Core.StorageMapping.programOverhead)
    "undersized node budget accepted"
  let corpus := StorageMapping.generateCases (Seed.ofNat 0) 384 2 64 1000000
  ensure (corpus == StorageMapping.generateCases (Seed.ofNat 0) 384 2 64 1000000) "mapping generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 2 && (← natural corpus "attempted") ≤ 64 && (← string corpus "status") == "complete")
    "mapping count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (StorageMapping.replayCase saved 1000000)) == saved) "generated mapping provenance did not replay"
    let low ← get (StorageMapping.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := StorageMapping.generateCases (Seed.ofNat seed) 384 1 1 1000
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "mapping generation resource exhaustion was not distinguished"
  ensure ((← natural (StorageMapping.generateCases (Seed.ofNat seed) 384 0 10 1000000) "attempted") == 0 &&
    (← rows (StorageMapping.generateCases (Seed.ofNat seed) 384 1 0 1000000) "cases").isEmpty)
    "mapping generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("flags", toJson "01"),
      ("key", toJson "06"), ("key", toJson (toString (2 ^ 256))), ("input", toJson "01"),
      ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (StorageMapping.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical mapping transaction accepted"
  rejected (StorageMapping.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (StorageMapping.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (StorageMapping.decodeTransactions (toJson (List.replicate 4 first))) "unbounded transaction count accepted"
  let slots ← get (saved.getObjValAs? (Array Json) "observedSlots")
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", .arr slots.pop), ("observedSlots", .arr (slots.push (toJson "1"))),
      ("observedSlots", .arr slots.reverse), ("executionFuel", toJson (10000001 : Nat)), ("mappingPlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (StorageMapping.caseProgram (saved.setObjVal! name bad)) "invalid mapping case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (StorageMapping.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 1000000)
      "tampered mapping provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (StorageMapping.replayCase (withOrigin (origin.setObjVal! name bad)) 1000000)
      "tampered generated mapping recipe accepted"
  let plan ← field saved "mappingPlan"
  rejected (StorageMapping.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical mapping plan accepted"
  rejected (StorageMapping.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.keyed-storage-plan.v1")))
    "keyed plan schema accepted as a mapping plan"
  rejected (StorageMapping.replayCase (saved.setObjVal! "source" (toJson "stale")) 1000000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (StorageMapping.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x7357f5d2"))) 1000000)
    "the keyed two-Word selector accepted for the mapping ABI"
  rejected (StorageMapping.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-keyed-storage-case.v1")) 1000000)
    "keyed case schema accepted by the mapping tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [(3, 7, 2 ^ 255), (1, maximum, 3), (2, 2 ^ 255, maximum)]
  let saved ← imported value
  let candidates ← get (StorageMapping.shrinkCases saved 2000 1000000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (StorageMapping.shrinkCases saved 2000 1000000)))
    "mapping reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredKey := false
  let mut loweredInput := false
  let mut loweredFlags := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (StorageMapping.caseProgram row)
    ensure (decide (StorageMapping.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "mapping reduction lost strict complexity, host typing or stable scope/IDs"
    ensure ((← field row "observedSlots") == toJson ((reduced.observedSlots.map (·.val)).map toString))
      "a reduced mapping case did not rederive its declared slots"
    let identity := (Json.mkObj [("plan", StorageMapping.planJson reduced.plan),
      ("transactions", StorageMapping.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate mapping reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    let sameCount := reduced.transactions.length == value.transactions.length
    loweredKey := loweredKey || (sameCount && pairs.any fun (left, right) => left.key.val < right.key.val)
    loweredInput := loweredInput || (sameCount && pairs.any fun (left, right) => left.input.val < right.input.val)
    loweredFlags := loweredFlags || (sameCount && pairs.any fun (left, right) => left.flags.val < right.flags.val)
    changedStep := changedStep || StorageMapping.planJson reduced.plan != StorageMapping.planJson value.plan
  ensure (removed && loweredKey && loweredInput && loweredFlags && changedStep)
    "mapping shrink omitted sequence/key/input/flags/step axes"
  for row in result.extract 0 3 do
    ensure ((← get (StorageMapping.replayCase row 1000000)) == row) "reduced mapping case did not replay"
  ensure ((← rows (← get (StorageMapping.shrinkCases saved 2 1000000)) "cases") == result.extract 0 2 &&
    (← rows (← get (StorageMapping.shrinkCases saved 0 1000000)) "cases").isEmpty) "mapping shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (StorageMapping.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", StorageMapping.planJson reduced.plan),
    ("parentTransactions", StorageMapping.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (StorageMapping.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 1000000)
    "non-strict mapping reduction provenance accepted"

def testSourceStorageMappingCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceStorageMappingCases
