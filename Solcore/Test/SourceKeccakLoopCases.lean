import Solcore.Synthesis.Source.KeccakLoopCases

/-! Generated Keccak-loop cases. The guarded Core contract must equal the
source-loop model, a counter over a slot map with Keccak slots and a log list,
on every transaction of the generated sequences: status, output, the observed
slots and every committed log. Each case must replay to itself; the shell and
guard node counts must be those the definitions fix; the recorded iteration
counts and observed slots are checked on decode; and every reduction must be a
strictly smaller sealed case that replays. -/
set_option autoImplicit false

namespace Tests.SourceKeccakLoopCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def storageJson (slots values : List Word) : Json :=
  toJson ((slots.zip values).map fun (slot, value) => Json.mkObj [
    ("slot", toJson (toString slot.val)), ("value", toJson (toString value.val))])

private def logsJson (logs : List KeccakLoopExecution.ModelLog) : Json :=
  toJson (logs.map fun log => Json.mkObj [
    ("address", toJson (toString StorageExecution.fixtureBindings.address.val)),
    ("topics", toJson [toString log.ordinal, toString log.key.val]),
    ("data", toJson (encodeBytesText (encodeWordBytesBE log.value)))])

/-- The Core rows of a scenario equal the model's, transaction by transaction. -/
private def sameAsModel (scenario : Solcore.Synthesis.Source.KeccakLoop.CheckedScenario) (fuel : Nat) (name : String) :
    IO Unit := do
  let history := Solcore.Synthesis.Source.KeccakLoop.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let slots := scenario.observedSlots
  let some modelled := KeccakLoopExecution.model scenario.plan.step fuel scenario.plan.mask scenario.plan.keyMask
      scenario.transactions
    | throw (IO.userError s!"{name}: the source-loop model failed")
  ensure (rows.size == modelled.length) s!"{name}: a row is missing"
  for (row, model) in rows.toList.zip modelled do
    ensure ((row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
        (row.getObjValAs? String "output").toOption == some (encodeBytesText (encodeWordBytesBE model.result)) &&
        (row.getObjVal? "committedStorage").toOption == some (storageJson slots (KeccakLoopExecution.modelSlots model slots)) &&
        (row.getObjVal? "logs").toOption == some (logsJson model.logs))
      s!"{name}: the guarded Core row differs from the source-loop model: {row.compress}"

def testSourceKeccakLoopCases : IO Unit := do
  let fuel := 1000000
  ensure (KeccakLoop.hashNodes == 2654) s!"the Keccak closure has {KeccakLoop.hashNodes} nodes"
  ensure (KeccakLoop.shellNodes == 38) s!"the shell has {KeccakLoop.shellNodes} nodes"
  ensure ([0, 1, 3, 7].map KeccakLoop.guardNodes == [0, 69, 207, 483]) "the guards changed size"
  ensure (Solcore.Synthesis.Source.KeccakLoop.maxProgramNodes == 3649) "the case limit changed"
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three.
  let mut masks : List Nat := []
  let mut keyMasks : List Nat := []
  let mut counts : List Nat := []
  let mut cases : Array Json := #[]
  for (revision, transactions, count) in [(GeneratorRevision.v3, 8, 24), (GeneratorRevision.v1, 3, 16)] do
    let corpus := Solcore.Synthesis.Source.KeccakLoop.generateCases (Seed.ofNat 1) 384 count 512 fuel revision transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} case {index}"
      ensure ((Solcore.Synthesis.Source.KeccakLoop.replayCase json fuel).toOption == some json) s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.KeccakLoop.caseProgram json)
      ensure (scenario.transactions.length == transactions) s!"{name}: wrong sequence length"
      sameAsModel scenario fuel name
      let source ← get (json.getObjValAs? String "source")
      ensure ((source.splitOn "while (sc_limit > sc_counter) {").length == 2 &&
          (source.splitOn s!"let sc_limit: word = (sc_input & {scenario.plan.mask});").length == 2 &&
          (source.splitOn s!"sc_key = (sc_base | (sc_counter & {scenario.plan.keyMask}));").length == 2 &&
          (source.splitOn "sc_log2(sc_ptr, 32, sc_counter, sc_key);").length == 2)
        s!"{name}: the emitted loop differs"
      masks := scenario.plan.mask :: masks
      keyMasks := scenario.plan.keyMask :: keyMasks
      counts := counts ++ scenario.transactions.map (KeccakLoopExecution.iterations scenario.plan.mask ·.input)
      cases := cases.push json
  for mask in [1, 3, 7] do
    ensure (masks.contains mask) s!"generation never drew loop mask {mask}"
  ensure (!masks.contains 0) "generation drew loop mask zero"
  for keyMask in [0, 1, 3, 7] do
    ensure (keyMasks.contains keyMask) s!"generation never drew key mask {keyMask}"
  for iterations in List.range 8 do
    ensure (counts.contains iterations) s!"no generated transaction runs {iterations} iterations"
  -- Reductions: lower loop and key masks come with every positive mask, and
  -- every emitted candidate replays as a strictly smaller sealed case. Each
  -- candidate runs every Keccak iteration again, so two cases of each
  -- revision are reduced.
  for json in cases.toList.take 2 ++ (cases.toList.drop 24).take 2 do
    let source ← get (Solcore.Synthesis.Source.KeccakLoop.caseProgram json)
    let reduced := Solcore.Synthesis.Source.KeccakLoop.reductions source
    ensure (!reduced.isEmpty) "a case has no reduction"
    ensure (reduced.any (fun candidate => candidate.candidate.plan.mask < source.plan.mask)) "no lower loop mask"
    ensure (source.plan.keyMask == 0 ||
        reduced.any (fun candidate => candidate.candidate.plan.keyMask < source.plan.keyMask)) "no lower key mask"
    let shrunk ← get (Solcore.Synthesis.Source.KeccakLoop.shrinkCases json 32 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.KeccakLoop.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      sameAsModel (← get (Solcore.Synthesis.Source.KeccakLoop.caseProgram candidate)) fuel "reduction"
  -- A recorded iteration count must be the input's bits under the mask.
  let some json := cases[0]? | throw (IO.userError "no case")
  let scenario ← get (Solcore.Synthesis.Source.KeccakLoop.caseProgram json)
  let wrong := json.setObjVal! "transactions" (toJson ((← get (json.getObjValAs? (Array Json) "transactions")).toList.map
    fun row => row.setObjVal! "iterations" (toJson (KeccakLoopExecution.iterations scenario.plan.mask
      ((row.getObjValAs? String "input").toOption.bind String.toNat? |>.map Word.ofNatModulo |>.getD Word.zero) + 8))))
  ensure (Solcore.Synthesis.Source.KeccakLoop.caseProgram wrong).toOption.isNone "a wrong iteration count was admitted"
  -- The observed slots must be exactly slot zero and every addressed entry slot.
  let slots ← get (json.getObjValAs? (List String) "observedSlots")
  ensure (slots.length == (scenario.observedSlots).length && slots.head? == some "0") "unexpected observed slots"
  for changed in [slots.dropLast, slots ++ ["1"], slots.reverse, slots.map fun slot => if slot == "0" then "1" else slot] do
    ensure (changed == slots ||
        (Solcore.Synthesis.Source.KeccakLoop.caseProgram (json.setObjVal! "observedSlots" (toJson changed))).toOption.isNone)
      "changed observed slots were admitted"
  -- A plan whose loop mask or key mask is not admitted is refused.
  let plan ← get (json.getObjVal? "keccakLoopPlan")
  ensure (Solcore.Synthesis.Source.KeccakLoop.checkedPlan (plan.setObjVal! "mask" (toJson 5))).toOption.isNone
    "loop mask five was admitted"
  ensure (Solcore.Synthesis.Source.KeccakLoop.checkedPlan (plan.setObjVal! "keyMask" (toJson 2))).toOption.isNone
    "key mask two was admitted"

end Tests.SourceKeccakLoopCases
