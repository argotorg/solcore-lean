import Solcore.Synthesis.Source.TupleReturnCases

/-! Generated tuple-return cases. The Core contract must equal the source model,
a slot map, on every transaction of the generated sequences; each case must
replay to itself; the shell node counts must be those the definitions fix; and
every reduction must be a strictly smaller sealed case that replays. -/
set_option autoImplicit false

namespace Tests.SourceTupleReturnCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.TupleReturnExecution (Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def slots (values : List Word) : Json :=
  toJson ((values.zipIdx).map fun (value, slot) => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString value.val))])

/-- The Core rows of a scenario equal the model's, transaction by transaction. -/
private def sameAsModel (scenario : Solcore.Synthesis.Source.TupleReturn.CheckedScenario) (fuel : Nat) (name : String) :
    IO Unit := do
  let history := Solcore.Synthesis.Source.TupleReturn.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := TupleReturnExecution.model scenario.plan.step fuel scenario.plan.arity scenario.transactions
    | throw (IO.userError s!"{name}: the source model failed")
  ensure (rows.size == modelled.length) s!"{name}: a row is missing"
  for (row, model) in rows.toList.zip modelled do
    ensure ((row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
        (row.getObjValAs? String "output").toOption == some (encodeBytesText (TupleReturnExecution.outputBytes model)) &&
        (row.getObjVal? "committedStorage").toOption == some (slots model.slots))
      s!"{name}: the Core row differs from the source model: {row.compress}"
    -- A return carries the arity's Words and a revert one Word.
    ensure (model.output.length == if model.reverted then 1 else scenario.plan.arity)
      s!"{name}: the output has the wrong number of Words"

def testSourceTupleReturnCases : IO Unit := do
  let fuel := 1000000
  ensure ([2, 3, 4].map TupleReturn.shellNodes == [79, 85, 91])
    s!"the shells have {[2, 3, 4].map TupleReturn.shellNodes} nodes"
  ensure (Solcore.Synthesis.Source.TupleReturn.maxProgramNodes == 512) "the case limit changed"
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three.
  let mut arities : List Nat := []
  let mut cases : Array Json := #[]
  for (revision, transactions, count) in [(GeneratorRevision.v3, 8, 40), (GeneratorRevision.v1, 3, 24)] do
    let corpus := Solcore.Synthesis.Source.TupleReturn.generateCases (Seed.ofNat 1) 384 count 512 fuel revision transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} case {index}"
      ensure ((Solcore.Synthesis.Source.TupleReturn.replayCase json fuel).toOption == some json) s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.TupleReturn.caseProgram json)
      ensure (scenario.transactions.length == transactions) s!"{name}: wrong sequence length"
      sameAsModel scenario fuel name
      let source ← get (json.getObjValAs? String "source")
      ensure ((source.splitOn s!"public returns {Solcore.Synthesis.Source.TupleReturn.returnType scenario.plan.arity} \{").length == 2)
        s!"{name}: the emitted return type differs"
      arities := scenario.plan.arity :: arities
      cases := cases.push json
  for arity in [2, 3, 4] do
    ensure (arities.contains arity) s!"generation never drew arity {arity}"
  -- Reductions: lower arities come with every arity above two, and every
  -- emitted candidate replays as a strictly smaller sealed case.
  for json in cases.toList.take 6 do
    let source ← get (Solcore.Synthesis.Source.TupleReturn.caseProgram json)
    let reduced := Solcore.Synthesis.Source.TupleReturn.reductions source
    ensure (!reduced.isEmpty) "a case has no reduction"
    ensure (source.plan.arity == 2 || reduced.any (fun candidate => candidate.candidate.plan.arity < source.plan.arity))
      "no lower arity"
    let shrunk ← get (Solcore.Synthesis.Source.TupleReturn.shrinkCases json 64 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.TupleReturn.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      sameAsModel (← get (Solcore.Synthesis.Source.TupleReturn.caseProgram candidate)) fuel "reduction"
  -- A plan whose arity is not admitted is refused, and so is a forged arity.
  let some json := cases[0]? | throw (IO.userError "no case")
  let plan ← get (json.getObjVal? "tupleReturnPlan")
  ensure (Solcore.Synthesis.Source.TupleReturn.checkedPlan (plan.setObjVal! "arity" (toJson 5))).toOption.isNone
    "arity five was admitted"
  let scenario ← get (Solcore.Synthesis.Source.TupleReturn.caseProgram json)
  let other := if scenario.plan.arity == 2 then 3 else 2
  ensure (Solcore.Synthesis.Source.TupleReturn.caseProgram
      (json.setObjVal! "tupleReturnPlan" (plan.setObjVal! "arity" (toJson other)))).toOption.isNone
    "a case whose program differs from its plan's arity was admitted"

end Tests.SourceTupleReturnCases
