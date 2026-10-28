import Solcore.Synthesis.Source.StorageLoopCases

/-! Generated storage-loop cases. The guarded Core contract must equal the
source-loop model, a counter over a slot map, on every transaction of the
generated sequences; each case must replay to itself; the shell and guard
node counts must be those the definitions fix; and every reduction must be a
strictly smaller sealed case that replays. -/
set_option autoImplicit false

namespace Tests.SourceStorageLoopCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.StorageLoopExecution (Transaction)

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
private def sameAsModel (scenario : Solcore.Synthesis.Source.StorageLoop.CheckedScenario) (fuel : Nat) (name : String) :
    IO Unit := do
  let history := Solcore.Synthesis.Source.StorageLoop.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := StorageLoopExecution.model scenario.plan.step fuel scenario.plan.mask scenario.transactions
    | throw (IO.userError s!"{name}: the source-loop model failed")
  ensure (rows.size == modelled.length) s!"{name}: a row is missing"
  for (row, model) in rows.toList.zip modelled do
    ensure ((row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
        (row.getObjValAs? String "output").toOption == some (encodeBytesText (encodeWordBytesBE model.result)) &&
        (row.getObjVal? "committedStorage").toOption == some (slots model.slots))
      s!"{name}: the guarded Core row differs from the source-loop model: {row.compress}"

def testSourceStorageLoopCases : IO Unit := do
  let fuel := 1000000
  ensure (StorageLoop.shellNodes == 57) s!"the shell has {StorageLoop.shellNodes} nodes"
  ensure ([0, 1, 3, 7].map StorageLoop.guardNodes == [0, 45, 135, 315]) "the guards changed size"
  ensure (Solcore.Synthesis.Source.StorageLoop.maxProgramNodes == 827) "the case limit changed"
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three.
  let mut masks : List Nat := []
  let mut counts : List Nat := []
  let mut cases : Array Json := #[]
  for (revision, transactions, count) in [(GeneratorRevision.v3, 8, 40), (GeneratorRevision.v1, 3, 24)] do
    let corpus := Solcore.Synthesis.Source.StorageLoop.generateCases (Seed.ofNat 1) 384 count 512 fuel revision transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} case {index}"
      ensure ((Solcore.Synthesis.Source.StorageLoop.replayCase json fuel).toOption == some json) s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.StorageLoop.caseProgram json)
      ensure (scenario.transactions.length == transactions) s!"{name}: wrong sequence length"
      sameAsModel scenario fuel name
      let source ← get (json.getObjValAs? String "source")
      ensure ((source.splitOn "while (sc_limit > sc_counter) {").length == 2 &&
          (source.splitOn s!"let sc_limit: word = (sc_input & {scenario.plan.mask});").length == 2)
        s!"{name}: the emitted loop differs"
      masks := scenario.plan.mask :: masks
      counts := counts ++ scenario.transactions.map (StorageLoopExecution.iterations scenario.plan.mask ·.input)
      cases := cases.push json
  for mask in [1, 3, 7] do
    ensure (masks.contains mask) s!"generation never drew mask {mask}"
  ensure (!masks.contains 0) "generation drew mask zero"
  for iterations in List.range 8 do
    ensure (counts.contains iterations) s!"no generated transaction runs {iterations} iterations"
  -- Reductions: lower masks come with every positive mask, and every
  -- emitted candidate replays as a strictly smaller sealed case.
  for json in cases.toList.take 6 do
    let source ← get (Solcore.Synthesis.Source.StorageLoop.caseProgram json)
    let reduced := Solcore.Synthesis.Source.StorageLoop.reductions source
    ensure (!reduced.isEmpty) "a case has no reduction"
    ensure (reduced.any (fun candidate => candidate.candidate.plan.mask < source.plan.mask)) "no lower mask"
    let shrunk ← get (Solcore.Synthesis.Source.StorageLoop.shrinkCases json 64 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.StorageLoop.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      sameAsModel (← get (Solcore.Synthesis.Source.StorageLoop.caseProgram candidate)) fuel "reduction"
  -- A recorded iteration count must be the input's bits under the mask.
  let some json := cases[0]? | throw (IO.userError "no case")
  let scenario ← get (Solcore.Synthesis.Source.StorageLoop.caseProgram json)
  let wrong := json.setObjVal! "transactions" (toJson ((← get (json.getObjValAs? (Array Json) "transactions")).toList.map
    fun row => row.setObjVal! "iterations" (toJson (StorageLoopExecution.iterations scenario.plan.mask
      ((row.getObjValAs? String "input").toOption.bind String.toNat? |>.map Word.ofNatModulo |>.getD Word.zero) + 8))))
  ensure (Solcore.Synthesis.Source.StorageLoop.caseProgram wrong).toOption.isNone "a wrong iteration count was admitted"
  -- A plan whose mask is not admitted is refused.
  let plan ← get (json.getObjVal? "storageLoopPlan")
  ensure (Solcore.Synthesis.Source.StorageLoop.checkedPlan (plan.setObjVal! "mask" (toJson 5))).toOption.isNone
    "mask five was admitted"

end Tests.SourceStorageLoopCases
