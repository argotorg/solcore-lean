import Solcore.Synthesis.Source.DynamicArrayCases

/-! Dynamic-array case regressions: exact replay, bounded generation from an
independent sequence stream, canonical transaction and calldata boundaries, and
typed reductions over steps, transactions, array elements and flags. Expected
values here are test goldens only; cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceDynamicArrayCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.DynamicArray (CheckedPlan)
open Solcore.Synthesis.Stateful.DynamicArrayExecution (Transaction Bindings)

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
    throw (IO.userError "array fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "array wrapper failed host admission")
  return plan
private def transactions (values : List (Nat × List Nat)) : List Transaction :=
  values.zipIdx.map fun ((flags, elements), index) =>
    ⟨"call-" ++ toString index, Word.ofNatModulo flags, elements.map Word.ofNatModulo⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × List Nat)) : IO DynamicArray.CheckedScenario :=
  get (DynamicArray.checkedScenario plan (transactions values))
private def imported (value : DynamicArray.CheckedScenario) (fuel : Nat := 10000) : IO Json :=
  get (DynamicArray.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(0, [1, 3, 7]), (1, [2 ^ 256 - 1]), (2, [])]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson (["0", "1", "2", "3", "4"] : List String))
    "case did not declare slots zero through four"
  ensure ((← get (DynamicArray.replayCase saved 10000)) == saved) "imported array case did not replay"
  ensure ((← get (DynamicArray.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 10000)) == saved)
    "array replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(5, []), (2, [9, 9])])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "array elements or flags were substituted into source or Core code"
  let observed := DynamicArray.observe value bindings 10000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "returned"])
    "array scenario did not follow its flags parities"
  let rebound ← rows (DynamicArray.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 10000)
  ensure (rebound.map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows observed).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      rebound.all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "address-independent array profile changed with bindings"
  rejected (DynamicArray.checkedScenario identity (transactions [(0, [1, 2, 3, 4])])) "four-element array accepted"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := DynamicArray.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 16 && (choices.zip DynamicArray.sequenceBounds).all (fun (value, bound) => value < bound))
      "sequence choices escaped their banks"
    match DynamicArray.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 && Wire.programNodes value.program ≤ 384 &&
          value.plan.step.helpers.length == 1 + seed % 3) "array recipe lost node/transaction/helper bounds"
        ensure ((value.transactions.map (·.values.length)) == choices.take 3) "generated lengths escaped their draws"
        ensure (value.transactions.all (fun tx => tx.values.all DynamicArray.boundaryInputs.contains))
          "generated element escaped its bank"
        ensure ((value.transactions.map fun tx => tx.flags.val % 2 == 1) == DynamicArray.generatedParities (Seed.ofNat seed))
          "generated flags lost their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (DynamicArray.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (DynamicArray.generatedScenario (Seed.ofNat 0) DynamicArray.programOverhead) "undersized node budget accepted"
  let corpus := DynamicArray.generateCases (Seed.ofNat 0) 384 4 512 10000
  ensure (corpus == DynamicArray.generateCases (Seed.ofNat 0) 384 4 512 10000) "array generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "array count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (DynamicArray.replayCase saved 10000)) == saved) "generated array provenance did not replay"
    let low ← get (DynamicArray.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := DynamicArray.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "array generation resource exhaustion was not distinguished"
  ensure ((← rows (DynamicArray.generateCases (Seed.ofNat seed) 384 2 1 10000) "cases").size == 1 &&
    (← natural (DynamicArray.generateCases (Seed.ofNat seed) 384 0 10 10000) "attempted") == 0 &&
    (← rows (DynamicArray.generateCases (Seed.ofNat seed) 384 1 0 10000) "cases").isEmpty)
    "array generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("flags", toJson "01"),
      ("flags", toJson (toString (2 ^ 256))), ("flags", toJson "2"), ("values", toJson (["01"] : List String)),
      ("values", toJson (["1", "3"] : List String)), ("values", toJson (["1", "2", "3", "4"] : List String)),
      ("values", toJson "1"), ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (DynamicArray.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical array transaction accepted"
  rejected (DynamicArray.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (DynamicArray.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (DynamicArray.decodeTransactions (toJson (List.replicate 4 first))) "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson (["0", "1", "2", "3"] : List String)),
      ("observedSlots", toJson (["1", "0", "2", "3", "4"] : List String)),
      ("executionFuel", toJson (10000001 : Nat)), ("dynamicArrayPlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (DynamicArray.caseProgram (saved.setObjVal! name bad)) "invalid array case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (DynamicArray.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 10000)
      "tampered array provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (DynamicArray.replayCase (withOrigin (origin.setObjVal! name bad)) 10000)
      "tampered generated array recipe accepted"
  let plan ← field saved "dynamicArrayPlan"
  rejected (DynamicArray.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical array plan accepted"
  rejected (DynamicArray.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.keyed-storage-plan.v1")))
    "keyed plan schema accepted as an array plan"
  rejected (DynamicArray.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (DynamicArray.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x7357f5d2"))) 10000)
    "two-Word selector accepted for the array ABI"
  rejected (DynamicArray.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-keyed-storage-case.v1")) 10000)
    "keyed case schema accepted by the array tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [(2 ^ 256 - 2, [2 ^ 256 - 1, 7]), (2 ^ 255 + 1, [2 ^ 255]), (4, [3, 3, 3])]
  let saved ← imported value
  let candidates ← get (DynamicArray.shrinkCases saved 2000 10000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (DynamicArray.shrinkCases saved 2000 10000)))
    "array reductions were empty or nondeterministic"
  let mut removed := false
  let mut removedElement := false
  let mut loweredElement := false
  let mut loweredFlags := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (DynamicArray.caseProgram row)
    ensure (decide (DynamicArray.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "array reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.program),
      ("transactions", DynamicArray.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate array reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    let sameCount := reduced.transactions.length == value.transactions.length
    removedElement := removedElement || (sameCount && DynamicArray.elementCount reduced < DynamicArray.elementCount value)
    loweredElement := loweredElement || (sameCount && pairs.any fun (left, right) =>
      left.values.length == right.values.length && (left.values.zip right.values).any fun (a, b) => a.val < b.val)
    loweredFlags := loweredFlags || (sameCount && pairs.any fun (left, right) => left.flags.val < right.flags.val)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← get (DynamicArray.replayCase row 10000)) == row) "reduced array case did not replay"
  ensure (removed && removedElement && loweredElement && loweredFlags && changedStep)
    "array shrink omitted sequence/element/value/flags/step axes"
  ensure ((← rows (← get (DynamicArray.shrinkCases saved 2 10000)) "cases") == result.extract 0 2 &&
    (← rows (← get (DynamicArray.shrinkCases saved 0 10000)) "cases").isEmpty) "array shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (DynamicArray.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", DynamicArray.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", DynamicArray.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (DynamicArray.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 10000)
    "non-strict array reduction provenance accepted"

def testSourceDynamicArrayCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceDynamicArrayCases
