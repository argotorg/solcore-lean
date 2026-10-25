import Solcore.Synthesis.Source.MutationCases
import Solcore.Test.SourceMutationEmitter

/-! Case-level mutation replay and reduction checks. Concrete index goldens
cover reads before writes, Unit binders, two cells and private helper cells. -/
set_option autoImplicit false

namespace Tests.SourceMutationCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.LocalMutation (CheckedDAG)

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
  | none => throw (IO.userError "mutation case fixture failed checked admission")
private def imported (graph : CheckedDAG) (input : Word) : IO Json :=
  get (Mutation.emitCase graph input (Json.mkObj [("kind", toJson "imported")]) 3000)
private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

private def templateResult (pattern count : Nat) (input : Word) : Word :=
  let constant := Word.ofNatModulo 2
  if pattern = 0 then input.add (Word.ofNatModulo (2 * count))
  else if pattern = 1 then
    (List.range count).foldl (fun value _ =>
      if value.val > 2 then value.add constant else value.sub constant) input
  else if pattern = 2 then
    let pair := (List.range count).foldl (fun (pair : Word × Word) index =>
      if index % 2 = 0 then (pair.1.add pair.2 |>.add constant, pair.2)
      else (pair.1, pair.2.add pair.1 |>.add constant)) (input, input)
    pair.1.add pair.2
  else input.add (Word.ofNatModulo (2 + count - 1))

private def indexChecks : IO Unit := do
  for pattern in List.range 4 do
    for count in [1, 2, 3, 4] do
      let graph ← checked [Mutation.template pattern count (word 2)]
      ensure ((Mutation.bindingInventory graph).count .unit == count)
        "template did not retain all update Unit binders"
      ensure (graph.features.count "newCell" == if pattern = 2 then 2 else 1)
        "template allocated the wrong number of private cells"
      for input in Input.boundaryInputs do
        ensure (Mutation.observe graph input 3000 == returned (templateResult pattern count input))
          s!"template index mismatch: pattern {pattern}, count {count}, input {input.val}"
  let snapshot ← checked [SourceMutationEmitter.snapshotBody]
  ensure (Mutation.observe snapshot (Word.ofNatModulo 1) 3000 == returned (Word.ofNatModulo 3))
    "load-before-store returned the overwritten value instead of the original snapshot"
  for (_, helpers, body) in SourceMutationEmitter.fixtures do
    let graph ← checked helpers body
    let mut source : Option String := none
    for input in Input.boundaryInputs do
      let saved ← imported graph input
      let current ← string saved "source"
      if let some previous := source then ensure (previous == current) "mutation source depends on input"
      source := some current
      let admitted ← get (Mutation.caseProgram saved)
      ensure (admitted.program.check && admitted.input == input) "mutation case changed its original Core"
      ensure ((← get (Mutation.replayCase saved 3000)) == saved) "imported mutation case did not replay"
      ensure ((← get (Mutation.replayCase (saved.setObjVal! "directCore" (returned Word.zero)) 3000)) == saved)
        "mutation replay trusted a saved result"
      let low ← get (Mutation.replayCase saved 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "zero fuel was confused with mutation completion"

private def minimumBudget (seed : Nat) : IO Nat := do
  for nodes in List.range 513 do
    if (Mutation.generatedFunction (Seed.ofNat seed) nodes).isOk then return nodes
  throw (IO.userError "mutation skeleton did not fit the case node limit")

private def generationChecks : IO Json := do
  let mut saved := Json.null
  for seed in List.range 3 do
    let budget ← minimumBudget seed
    let corpus := Mutation.generateCases (Seed.ofNat seed) budget 4 1 3000
    ensure (corpus == Mutation.generateCases (Seed.ofNat seed) budget 4 1 3000)
      "mutation generation is nondeterministic"
    ensure ((← string corpus "status") == "complete" && (← natural corpus "attempted") == 1)
      "minimal measured skeleton did not generate one four-input case group"
    let rows ← cases corpus
    ensure (rows.size == 4) "generated mutation group omitted boundary inputs"
    for index in List.range 4 do
      let row := rows[index]!
      let graph ← get (Mutation.caseProgram row)
      ensure (graph.program.check && graph.function.helpers.length == seed + 1 &&
        Wire.programNodes graph.program ≤ budget) "mutation generation escaped helper/type/node budget"
      ensure (some graph.input == Input.boundaryInputs[index]?) "mutation boundary input order changed"
      ensure ((← get (Mutation.replayCase row 3000)) == row) "generated mutation provenance did not replay"
      let low ← get (Mutation.replayCase row 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "fresh replay fuel changed original validation fuel"
      saved := row
    ensure ((← cases (Mutation.generateCases (Seed.ofNat seed) (budget - 1) 1 1 3000)).isEmpty)
      "insufficient skeleton budget silently changed the selected template"
  let corpus := Mutation.generateCases (Seed.ofNat 0) 192 8 256 3000
  ensure ((← cases corpus).size == 8 && (← natural corpus "attempted") ≤ 256)
    "bounded mixed mutation corpus did not complete"
  for row in ← cases corpus do
    let graph ← get (Mutation.caseProgram row)
    ensure (Wire.programNodes graph.program ≤ 192) "closed G0 embedding exceeded the full program budget"
    ensure ((← get (Mutation.replayCase row 3000)) == row) "mixed mutation metadata failed replay"
  let budget ← minimumBudget 0
  let low := Mutation.generateCases (Seed.ofNat 0) budget 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource") "generation fuel was a semantic exclusion"
  ensure ((← cases (Mutation.generateCases (Seed.ofNat 0) budget 3 1 3000)).size == 3)
    "case count did not truncate a boundary group"
  ensure ((← string (Mutation.generateCases (Seed.ofNat 0) budget 5 1 3000) "status") == "generation-exhausted")
    "mutation attempt limit counted inputs instead of function candidates"
  ensure ((← natural (Mutation.generateCases (Seed.ofNat 0) 192 0 100 3000) "attempted") == 0 &&
    (← cases (Mutation.generateCases (Seed.ofNat 0) 192 1 0 3000)).isEmpty)
    "empty generation budgets consumed work"
  return saved

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for version in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Mutation.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! version (toJson "forged"))) 3000) "tampered mutation version accepted"
  for (name, value) in [("seed", toJson "02"), ("finalSeed", toJson "0"),
      ("maxProgramNodes", toJson (513 : Nat)), ("helpers", Json.arr #[]),
      ("helperCount", toJson (0 : Nat)), ("inputIndex", toJson (10 : Nat)),
      ("validationFuel", toJson (10000001 : Nat))] do
    rejected (Mutation.replayCase (withOrigin (origin.setObjVal! name value)) 3000)
      s!"tampered mutation {name} accepted"
  let metadata ← get (origin.getObjValAs? (Array Json) "helpers")
  for name in ["seed", "finalSeed", "maxProgramNodes", "template", "updates"] do
    let changed := metadata[0]!.setObjVal! name (toJson "forged")
    rejected (Mutation.replayCase (withOrigin (origin.setObjVal! "helpers" (.arr (metadata.set! 0 changed)))) 3000)
      "tampered helper template metadata accepted"
  rejected (Mutation.replayCase (saved.setObjVal! "source" (toJson "stale")) 3000) "stale mutation source accepted"
  rejected (Mutation.replayCase (saved.setObjVal! "input" (toJson "0")) 3000) "input/application mismatch accepted"
  let contract ← field saved "contract"
  rejected (Mutation.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "calldata" (toJson "0x"))) 3000)
    "wrong mutation ABI input accepted"
  let bad : Wire.Expr := .letE (.newCell .word (.var 0)) (.letE .unit (.loadCell (.var 0)))
  rejected (Mutation.checkedFunction (Wire.encodeProgram (functionDAGProgram [bad] entry)))
    "eliding a Unit binder changed the referenced cell without rejection"

private def shrinkChecks : IO Unit := do
  for body in [SourceMutationEmitter.snapshotBody, SourceMutationEmitter.boolAndUnitBody,
      SourceMutationEmitter.nestedStoreBody] do
    let graph ← checked [body]
    let saved ← imported graph Word.maximum
    let original ← get (Mutation.caseProgram saved)
    let shrunk ← get (Mutation.shrinkCases saved 1000 3000)
    let rows ← cases shrunk
    ensure (!rows.isEmpty && shrunk == (← get (Mutation.shrinkCases saved 1000 3000)))
      "mutation shrinking was empty or nondeterministic"
    let mut seen : List String := []
    let mut inputReduced := false
    let mut storesReduced := false
    for row in rows do
      let candidate ← get (Mutation.caseProgram row)
      ensure (candidate.program.check && candidate.function.helpers.length == graph.helpers.length &&
        Mutation.bindingInventory candidate.function == Mutation.bindingInventory graph &&
        candidate.function.features.count "newCell" == graph.features.count "newCell")
        "shrink erased/retyped a cell, Unit or scalar binder"
      ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
        "mutation reduction did not strictly decrease the original Core program"
      let key := (Wire.encodeProgram candidate.program).compress
      ensure (!seen.contains key) "mutation reduction duplicated a candidate"
      seen := key :: seen
      ensure ((← get (Mutation.replayCase row 3000)) == row) "mutation reduction did not replay"
      inputReduced := inputReduced || candidate.input != original.input
      storesReduced := storesReduced || candidate.function.features.count "storeCell" < graph.features.count "storeCell"
    ensure (inputReduced && storesReduced) "mutation shrinking omitted input or store-to-Unit candidates"
    ensure ((← cases (← get (Mutation.shrinkCases saved 2 3000))) == rows.extract 0 2 &&
      (← cases (← get (Mutation.shrinkCases saved 0 3000))).isEmpty) "mutation shrink limit changed ordering"

def testSourceMutationCases : IO Unit := do
  indexChecks
  let saved ← generationChecks
  tamperingChecks saved
  shrinkChecks

end Tests.SourceMutationCases
