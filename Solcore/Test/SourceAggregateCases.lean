import Solcore.Synthesis.Source.AggregateCases

/-! Aggregate cases preserve payload scopes, mutable Word cells and the
independent applied Core program across generation, replay and reduction. -/
set_option autoImplicit false

namespace Tests.SourceAggregateCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.Aggregates (CheckedDAG)

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
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedDAG :=
  match CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "aggregate case fixture failed checked admission")
private def imported (graph : CheckedDAG) (input : Word) : IO Json :=
  get (Aggregate.emitCase graph input (Json.mkObj [("kind", toJson "imported")]) 3000)
private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

private def templateResult (pattern : Nat) (input scalar : Word) : Word :=
  let high := input.val ≥ 2 ^ 255
  if pattern = 0 then input.add scalar
  else if pattern = 1 then if high then input.bitXor scalar else input.add scalar
  else if pattern = 2 then input.add (if high then scalar.add scalar else scalar)
  else input.add (if high then input.bitXor scalar else input.add scalar)

private def unitCase : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.inLeft .word (.loadCell (.var 0)))
      (.letE (.caseE (.var 0)
        (.storeCell (.var 2) (.var 0)) (.storeCell (.var 2) (.var 0)))
        (.loadCell (.var 2))))

/-- Both the case payload and an unprinted Unit binding shift the helper index. -/
private def payloadCall : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.caseE (.inRight .word (.loadCell (.var 0)))
      (.apply (.var 3) (.var 0))
      (.letE .unit (.apply (.var 4) (.binary .wordAdd (.var 1) (.loadCell (.var 2))))))

private def boolCase : Wire.Expr :=
  .ifE (.caseE (.inRight .word (.var 0))
      (.binary .wordEq (.var 0) (word 0)) (.binary .wordGt (.var 0) (word 0)))
    (.var 0) (word 1)

private def fixtures : List (List Wire.Expr) :=
  (List.range 4).map (fun pattern => [Aggregate.template pattern (word 2)]) ++
    [[unitCase], [.binary .wordAdd (.var 0) (word 1), payloadCall], [boolCase]]

private def indexChecks : IO Unit := do
  for pattern in List.range 4 do
    for scalar in [Word.zero, Word.ofNatModulo 2, Word.maximum] do
      let graph ← checked [Aggregate.template pattern (.word scalar)]
      ensure (graph.features.count "newCell" == 1) "template changed its private cell allocation"
      ensure ((Aggregate.bindingInventory graph).count .leftPayload ==
        (Aggregate.bindingInventory graph).count .rightPayload) "template omitted a case branch scope"
      for input in Input.boundaryInputs do
        ensure (Aggregate.observe graph input 3000 == returned (templateResult pattern input scalar))
          s!"aggregate index mismatch: pattern {pattern}, scalar {scalar.val}, input {input.val}"
  let snapshot ← checked [Aggregate.template 0 (word 2)]
  ensure (Aggregate.observe snapshot (Word.ofNatModulo 1) 3000 == returned (Word.ofNatModulo 3))
    "pair construction reread the overwritten left operand"
  let called ← checked [.binary .wordAdd (.var 0) (word 1), payloadCall]
  for input in Input.boundaryInputs do
    ensure (Aggregate.observe called input 3000 == returned (input.add input |>.add (Word.ofNatModulo 1)))
      "case/Unit payload context selected the wrong helper or cell"
  for helpers in fixtures do
    let graph ← checked helpers
    let mut source : Option String := none
    for input in Input.boundaryInputs do
      let saved ← imported graph input
      let current ← string saved "source"
      if let some previous := source then ensure (previous == current) "aggregate source depends on input"
      source := some current
      let admitted ← get (Aggregate.caseProgram saved)
      ensure (admitted.program.check && admitted.input == input) "aggregate case changed its original Core"
      ensure ((← get (Aggregate.replayCase saved 3000)) == saved) "imported aggregate case did not replay"
      ensure ((← get (Aggregate.replayCase (saved.setObjVal! "directCore" (returned Word.zero)) 3000)) == saved)
        "aggregate replay trusted a saved result"
      let low ← get (Aggregate.replayCase saved 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "zero fuel was confused with aggregate completion"

private def minimumBudget (seed : Nat) : IO Nat := do
  for nodes in List.range 513 do
    if (Aggregate.generatedFunction (Seed.ofNat seed) nodes).isOk then return nodes
  throw (IO.userError "aggregate skeleton did not fit the case node limit")

private def generationChecks : IO Json := do
  let mut saved := Json.null
  for seed in [0, 1, 2, 3, 6, 9] do
    let budget ← minimumBudget seed
    let corpus := Aggregate.generateCases (Seed.ofNat seed) budget 4 1 3000
    ensure (corpus == Aggregate.generateCases (Seed.ofNat seed) budget 4 1 3000)
      "aggregate generation is nondeterministic"
    ensure ((← string corpus "status") == "complete" && (← natural corpus "attempted") == 1)
      "minimal measured skeleton did not generate one four-input case group"
    let rows ← cases corpus
    ensure (rows.size == 4) "generated aggregate group omitted boundary inputs"
    for index in List.range 4 do
      let row := rows[index]!
      let graph ← get (Aggregate.caseProgram row)
      ensure (graph.program.check && graph.function.helpers.length == 1 + seed % 3 &&
        Wire.programNodes graph.program ≤ budget) "aggregate generation escaped helper/type/node budget"
      ensure (some graph.input == Input.boundaryInputs[index]?) "aggregate boundary input order changed"
      ensure ((← get (Aggregate.replayCase row 3000)) == row) "generated aggregate provenance did not replay"
      let low ← get (Aggregate.replayCase row 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "fresh replay fuel changed original validation fuel"
      saved := row
    ensure ((← cases (Aggregate.generateCases (Seed.ofNat seed) (budget - 1) 1 1 3000)).isEmpty)
      "insufficient skeleton budget silently changed the selected template"
  let corpus := Aggregate.generateCases (Seed.ofNat 0) 256 8 256 3000
  ensure ((← cases corpus).size == 8 && (← natural corpus "attempted") ≤ 256)
    "bounded mixed aggregate corpus did not complete"
  for row in ← cases corpus do
    let graph ← get (Aggregate.caseProgram row)
    ensure (Wire.programNodes graph.program ≤ 256) "closed G0 embedding exceeded the full program budget"
    ensure ((← get (Aggregate.replayCase row 3000)) == row) "mixed aggregate metadata failed replay"
  let budget ← minimumBudget 0
  let low := Aggregate.generateCases (Seed.ofNat 0) budget 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource") "generation fuel was a semantic exclusion"
  ensure ((← cases (Aggregate.generateCases (Seed.ofNat 0) budget 3 1 3000)).size == 3)
    "case count did not truncate a boundary group"
  ensure ((← string (Aggregate.generateCases (Seed.ofNat 0) budget 5 1 3000) "status") == "generation-exhausted")
    "aggregate attempt limit counted inputs instead of function candidates"
  ensure ((← natural (Aggregate.generateCases (Seed.ofNat 0) 256 0 100 3000) "attempted") == 0 &&
    (← cases (Aggregate.generateCases (Seed.ofNat 0) 256 1 0 3000)).isEmpty)
    "empty generation budgets consumed work"
  return saved

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for version in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Aggregate.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! version (toJson "forged"))) 3000) "tampered aggregate version accepted"
  for (name, value) in [("seed", toJson "02"), ("finalSeed", toJson "0"),
      ("maxProgramNodes", toJson (513 : Nat)), ("helpers", Json.arr #[]),
      ("helperCount", toJson (0 : Nat)), ("inputIndex", toJson (10 : Nat)),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Aggregate.replayCase (withOrigin (origin.setObjVal! name value)) 3000)
      s!"tampered aggregate {name} accepted"
  let metadata ← get (origin.getObjValAs? (Array Json) "helpers")
  for name in ["seed", "finalSeed", "maxProgramNodes", "template"] do
    let changed := metadata[0]!.setObjVal! name (toJson "forged")
    rejected (Aggregate.replayCase (withOrigin (origin.setObjVal! "helpers" (.arr (metadata.set! 0 changed)))) 3000)
      "tampered helper template metadata accepted"
  rejected (Aggregate.replayCase (saved.setObjVal! "source" (toJson "stale")) 3000) "stale aggregate source accepted"
  rejected (Aggregate.replayCase (saved.setObjVal! "input" (toJson "0")) 3000) "input/application mismatch accepted"
  let contract ← field saved "contract"
  rejected (Aggregate.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "calldata" (toJson "0x"))) 3000)
    "wrong aggregate ABI input accepted"
  let bad : Wire.Expr := .letE (.newCell .word (.var 0))
    (.caseE (.inLeft .word (word 1)) (.loadCell (.var 0)) (.loadCell (.var 0)))
  rejected (Aggregate.checkedFunction (Wire.encodeProgram (functionDAGProgram [bad] entry)))
    "case payload was incorrectly treated as the outer cell"
  rejected (Aggregate.caseProgram (saved.setObjVal! "input" (toJson "01")))
    "noncanonical aggregate input accepted"

private def shrinkChecks : IO Unit := do
  for helpers in fixtures do
    let graph ← checked helpers
    let saved ← imported graph Word.maximum
    let original ← get (Aggregate.caseProgram saved)
    let shrunk ← get (Aggregate.shrinkCases saved 1000 3000)
    let rows ← cases shrunk
    ensure (!rows.isEmpty && shrunk == (← get (Aggregate.shrinkCases saved 1000 3000)))
      "aggregate shrinking was empty or nondeterministic"
    let mut seen : List String := []
    let mut inputReduced := false
    let mut storesReduced := false
    for row in rows do
      let candidate ← get (Aggregate.caseProgram row)
      ensure (candidate.program.check && candidate.function.helpers.length == graph.helpers.length &&
        Aggregate.bindingInventory candidate.function == Aggregate.bindingInventory graph &&
        candidate.function.features.count "newCell" == graph.features.count "newCell" &&
        candidate.function.features.count "case" == graph.features.count "case")
        "shrink erased/retyped a cell, aggregate, Unit or case payload binder"
      ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
        "aggregate reduction did not strictly decrease the original Core program"
      let key := (Wire.encodeProgram candidate.program).compress
      ensure (!seen.contains key) "aggregate reduction duplicated a candidate"
      seen := key :: seen
      ensure ((← get (Aggregate.replayCase row 3000)) == row) "aggregate reduction did not replay"
      inputReduced := inputReduced || candidate.input != original.input
      storesReduced := storesReduced || candidate.function.features.count "storeCell" < graph.features.count "storeCell"
    ensure inputReduced "aggregate shrinking omitted input candidates"
    if graph.features.contains "storeCell" then
      ensure storesReduced "aggregate shrinking omitted store-to-Unit candidates"
    ensure ((← cases (← get (Aggregate.shrinkCases saved 2 3000))) == rows.extract 0 2 &&
      (← cases (← get (Aggregate.shrinkCases saved 0 3000))).isEmpty) "aggregate shrink limit changed ordering"

def testSourceAggregateCases : IO Unit := do
  indexChecks
  let saved ← generationChecks
  tamperingChecks saved
  shrinkChecks

end Tests.SourceAggregateCases
