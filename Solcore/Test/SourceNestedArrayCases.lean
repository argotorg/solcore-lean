import Solcore.Synthesis.Source.NestedArrayCases

/-! Nested-array case regressions: exact replay, bounded generation from an
independent sequence stream, canonical values and nested calldata, and typed
reductions over steps, transactions, rows, elements and flags. Expected values
here are test goldens only; cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceNestedArrayCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.NestedArray (CheckedPlan)
open Solcore.Synthesis.Stateful.NestedArrayExecution (Transaction Bindings)

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
private def high : Nat := 2 ^ 255

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "nested-array fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "nested-array wrapper failed host admission")
  return plan
private def nested (rows : List (List Nat)) : List (List Word) := rows.map (·.map Word.ofNatModulo)
private def transactions (values : List (Nat × List (List Nat))) : List Transaction :=
  values.zipIdx.map fun ((flags, rows), index) => ⟨"call-" ++ toString index, Word.ofNatModulo flags, nested rows⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × List (List Nat))) : IO NestedArray.CheckedScenario :=
  get (NestedArray.checkedScenario plan (transactions values))
private def imported (value : NestedArray.CheckedScenario) (fuel : Nat := 1000000) : IO Json :=
  get (NestedArray.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(0, [[1, 3], [], [7]]), (1, [[maximum, high], [0]]), (2, [])]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson ((List.range 9).map toString))
    "case did not declare slots zero through eight"
  ensure ((← get (NestedArray.replayCase saved 1000000)) == saved) "imported nested-array case did not replay"
  ensure ((← get (NestedArray.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 1000000)) == saved)
    "nested-array replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(5, [[9]]), (2, [[], [], []])])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "values or flags were substituted into source or Core code"
  ensure (((← rows saved).map fun row => (row.getObjVal? "values").toOption) ==
      #[some (toJson [["1", "3"], [], ["7"]]), some (toJson [[toString maximum, toString high], ["0"]]),
        some (toJson ([] : List (List String)))])
    "values are not canonical decimal rows"
  let observed := NestedArray.observe value bindings 1000000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "returned"])
    "nested-array scenario did not follow its flags parities"
  ensure ((← get (NestedArray.checkProtocol value observed)) == ["returned", "reverted", "returned"])
    "nested-array history broke its row count, element count or sum protocol"
  let rebound ← rows (NestedArray.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 1000000)
  ensure (rebound.map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows observed).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      rebound.all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "address-independent nested-array profile changed with bindings"
  rejected (NestedArray.checkedScenario identity (transactions [(0, [[], [], [], []])])) "four rows accepted"
  rejected (NestedArray.checkedScenario identity (transactions [(0, [[1, 2, 3]])])) "three elements in a row accepted"
  ensure (NestedArray.elementCount ⟨"x", Word.zero, nested [[1, 2], [], [3]]⟩ == 3 &&
    NestedArray.validValue (nested [[1, 2], [3, 4], [5, 6]]) && !NestedArray.validValue (nested [[], [], [], []]))
    "element count or value bound changed"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := NestedArray.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 31 && (choices.zip NestedArray.sequenceBounds).all (fun (value, bound) => value < bound))
      "sequence choices escaped their banks"
    match NestedArray.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 &&
          Wire.programNodes value.program ≤ 384 + Solcore.Synthesis.Core.NestedArray.guardNodes &&
          value.plan.step.helpers.length == 1 + seed % 3) "nested-array recipe lost node/transaction/helper bounds"
        for (tx, index) in value.transactions.zipIdx do
          ensure (tx.values.length == choices.getD index 0) "generated outer length escaped its draw"
          for (cells, row) in tx.values.zipIdx do
            ensure (cells.length == choices.getD (3 + 3 * index + row) 0) "generated row length escaped its draw"
            for (cell, column) in cells.zipIdx do
              ensure (cell == NestedArray.boundaryInputs.getD (choices.getD (12 + 6 * index + 2 * row + column) 0) Word.zero)
                "generated element escaped its bank"
        ensure ((value.transactions.map fun tx => tx.flags.val % 2 == 1) == NestedArray.generatedParities (Seed.ofNat seed) &&
          value.transactions.all (fun tx => tx.flags.val < 2))
          "generated flags are not exactly their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (NestedArray.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (NestedArray.generatedScenario (Seed.ofNat 0) Solcore.Synthesis.Core.NestedArray.programOverhead)
    "undersized node budget accepted"
  let corpus := NestedArray.generateCases (Seed.ofNat 0) 384 4 512 1000000
  ensure (corpus == NestedArray.generateCases (Seed.ofNat 0) 384 4 512 1000000) "nested-array generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "nested-array count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (NestedArray.replayCase saved 1000000)) == saved) "generated nested-array provenance did not replay"
    let low ← get (NestedArray.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := NestedArray.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "nested-array generation resource exhaustion was not distinguished"
  ensure ((← rows (NestedArray.generateCases (Seed.ofNat seed) 384 2 1 1000000) "cases").size == 1 &&
    (← natural (NestedArray.generateCases (Seed.ofNat seed) 384 0 10 1000000) "attempted") == 0 &&
    (← rows (NestedArray.generateCases (Seed.ofNat seed) 384 1 0 1000000) "cases").isEmpty)
    "nested-array generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("flags", toJson "01"),
      ("flags", toJson (toString (2 ^ 256))), ("flags", toJson "2"), ("values", toJson [["1", "3"], [], ["07"]]),
      ("values", toJson [["1", "3"], [], [toString (2 ^ 256)]]), ("values", toJson [["1", "3"], ["7"]]),
      ("values", toJson [["1", "3", "0"], [], ["7"]]), ("values", toJson [["1", "3"], [], ["7"], []]),
      ("values", toJson ["1", "3", "7"]), ("values", toJson [[1, 3], [], [7]]),
      ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (NestedArray.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical nested-array transaction accepted"
  -- Calldata that names a different head offset or row offset is not canonical.
  let calldata ← string first "calldata"
  rejected (NestedArray.decodeTransactions (toJson [first.setObjVal! "calldata"
      (toJson (calldata.replace "0000000000000040" "0000000000000060"))]))
    "noncanonical head offset accepted"
  rejected (NestedArray.decodeTransactions (toJson [first.setObjVal! "calldata"
      (toJson (calldata.replace "00000000000000c0" "00000000000000e0"))]))
    "noncanonical row offset accepted"
  rejected (NestedArray.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (NestedArray.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (NestedArray.decodeTransactions (toJson (List.replicate 4 first))) "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson ((List.range 10).map toString)),
      ("observedSlots", toJson (["0", "1", "2", "3", "4"] : List String)),
      ("observedSlots", toJson (["1", "0"] ++ (List.range 7).map (toString ∘ (· + 2)))),
      ("executionFuel", toJson (10000001 : Nat)), ("nestedArrayPlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (NestedArray.caseProgram (saved.setObjVal! name bad)) "invalid nested-array case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (NestedArray.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 1000000)
      "tampered nested-array provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (NestedArray.replayCase (withOrigin (origin.setObjVal! name bad)) 1000000)
      "tampered generated nested-array recipe accepted"
  let generatedTransactions ← get (NestedArray.decodeTransactions (← field generated "transactions"))
  let some tx := generatedTransactions[0]? | throw (IO.userError "missing generated transaction")
  rejected (NestedArray.replayCase (generated.setObjVal! "transactions" (NestedArray.transactionsJson
      ({tx with values := tx.values ++ [[Word.ofNatModulo 1]]} :: generatedTransactions.drop 1))) 1000000)
    "generated value replaced without its seed"
  let plan ← field saved "nestedArrayPlan"
  rejected (NestedArray.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical nested-array plan accepted"
  rejected (NestedArray.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.dynamic-array-plan.v1")))
    "the flat array profile's plan schema accepted as a nested-array plan"
  rejected (NestedArray.replayCase (saved.setObjVal! "source" (toJson "stale")) 1000000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (NestedArray.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x9a94c44b"))) 1000000)
    "flat array selector accepted for the nested ABI"
  rejected (NestedArray.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-dynamic-array-case.v1")) 1000000)
    "the flat array profile's case schema accepted by the nested-array tool"

private def dropLastAt (values : List (List Word)) (row : Nat) : List (List Word) :=
  values.zipIdx.map fun (cells, current) => if current == row then cells.dropLast else cells

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [(1, [[7, 3], [1]]), (0, [[maximum], [], [high, 1]]), (3, [[0, 7]])]
  let saved ← imported value
  let candidates ← get (NestedArray.shrinkCases saved 2000 1000000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (NestedArray.shrinkCases saved 2000 1000000)))
    "nested-array reductions were empty or nondeterministic"
  let mut removed := false
  let mut removedRow := false
  let mut droppedElement := false
  let mut zeroed := false
  let mut loweredFlags := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (NestedArray.caseProgram row)
    ensure (decide (NestedArray.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "nested-array reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.program),
      ("transactions", NestedArray.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate nested-array reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    let sameCount := reduced.transactions.length == value.transactions.length
    removedRow := removedRow || (sameCount && pairs.any fun (left, right) =>
      (List.range right.values.length).any fun index => left.values == right.values.eraseIdx index)
    droppedElement := droppedElement || (sameCount && pairs.any fun (left, right) =>
      left.values != right.values &&
        (List.range right.values.length).any fun index => left.values == dropLastAt right.values index)
    zeroed := zeroed || (sameCount && pairs.any fun (left, right) =>
      left.values != right.values && left.values.map (·.length) == right.values.map (·.length) &&
        left.values.all (·.all (· == Word.zero)))
    loweredFlags := loweredFlags || (sameCount && pairs.any fun (left, right) => left.flags.val < right.flags.val)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← get (NestedArray.replayCase row 1000000)) == row) "reduced nested-array case did not replay"
  ensure (removed && removedRow && droppedElement && zeroed && loweredFlags && changedStep)
    "nested-array shrink omitted sequence/row/element/zero/flags/step axes"
  ensure ((← rows (← get (NestedArray.shrinkCases saved 2 1000000)) "cases") == result.extract 0 2 &&
    (← rows (← get (NestedArray.shrinkCases saved 0 1000000)) "cases").isEmpty) "nested-array shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (NestedArray.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", NestedArray.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", NestedArray.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (NestedArray.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 1000000)
    "non-strict nested-array reduction provenance accepted"

def testSourceNestedArrayCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceNestedArrayCases
