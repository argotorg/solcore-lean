import Solcore.Synthesis.Source.CallSequenceCases

/-! Generated call-sequence cases. Original Core through the call chain must
equal the Lean model, the child's data and the parent's reads around each call,
on every transaction of the generated sequences, with each transaction's
prescribed outcomes; every chain must make one call per window; each case must
replay to itself; the contracts' node counts must be the ones the definitions
fix; generation must draw both call counts, every bank offset, width and
length, uniform ones beside them, both statuses and both parent outcomes; and
every reduction must be a strictly smaller sealed case that replays. -/
set_option autoImplicit false

namespace Tests.SourceCallSequenceCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallSequence (CheckedPlan Window)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.CallSequenceExecution (Transaction)

private abbrev Cases := Solcore.Synthesis.Source.CallSequence.CheckedScenario

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

private def slotValues (account : Json) : List String :=
  match account.getObjValAs? (List Json) "storage" with
  | .ok entries => entries.filterMap fun entry => (entry.getObjValAs? String "value").toOption
  | .error _ => []

private def sameRow (row : Json) (model : CallSequenceExecution.ModelRow) : Bool :=
  let accounts := (row.getObjValAs? (List Json) "committedAccounts").toOption.getD []
  (row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
    (row.getObjValAs? String "output").toOption == some (encodeBytesText model.output) &&
    accounts.map slotValues == [model.parent.map (toString ·.val), model.child.map (toString ·.val)]

/-- The Core rows of a scenario equal the model's, each transaction records
the model's prescribed outcomes, and each chain makes one call per window. -/
private def sameAsModel (scenario : Cases) (json : Json) (fuel : Nat) (name : String) : IO (List String) := do
  let history := Solcore.Synthesis.Source.CallSequence.observe scenario NestedCallExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := CallSequenceExecution.model scenario.plan fuel scenario.transactions
    | throw (IO.userError s!"{name}: the Lean model failed")
  ensure (rows.size == modelled.length) s!"{name}: a row is missing"
  for (row, model) in rows.toList.zip modelled do
    ensure (sameRow row model) s!"{name}: the Core row differs from the Lean model: {row.compress}"
  let saved ← get (json.getObjValAs? (List Json) "transactions")
  ensure (saved.map (fun tx => ((tx.getObjVal? "calls").toOption, (tx.getObjVal? "parentReverts").toOption)) ==
      modelled.map (fun row => (some (toJson (row.calls.map Solcore.Synthesis.Source.CallSequence.callRowJson)),
        some (toJson row.reverted))))
    s!"{name}: a prescribed outcome differs from the model"
  -- Every transaction's chain makes one call per window, the last child's
  -- data being the last call's.
  let bindings := NestedCallExecution.fixtureBindings
  let mut world := CallSequenceExecution.initialWorld scenario.plan bindings
  for (transaction, model) in scenario.transactions.zip modelled do
    match CallChainExecution.run (CallSequenceExecution.registry scenario.plan bindings) scenario.plan.parent world
        bindings.parent bindings.caller (CallSequenceExecution.inputData bindings transaction.input) fuel with
    | .completed _ finalWorld calls =>
        ensure (calls.length == scenario.plan.calls &&
            calls.map (fun call => (call.child.status == .returned, call.child.data.size)) ==
              model.calls.map (fun call => (call.returned, call.length)))
          s!"{name}: a chain's calls differ from the model's"
        world := finalWorld
    | _ => throw (IO.userError s!"{name}: a chain did not complete")
  return modelled.flatMap fun row =>
    (if row.reverted then ["parent-reverted"] else ["parent-returned"]) ++
      row.calls.map fun call => if call.returned then "returned" else "reverted"

def testSourceCallSequenceCases : IO Unit := do
  let fuel := 1000000
  -- The contracts' sizes, as the definitions fix them.
  ensure (CallSequence.callNodes == 91 && CallSequence.childShellNodes == 129) "the call phase or the child's shell changed size"
  for window in [(⟨0, 0⟩ : Window), ⟨0, 32⟩, ⟨96, 32⟩, ⟨33, 31⟩] do
    ensure (Solcore.Core.Wire.programNodes (CallSequence.middleProgram 1 window) == 235 &&
        Solcore.Core.Wire.programNodes (CallSequence.middleProgram 2 window) == 230 &&
        Solcore.Core.Wire.programNodes (CallSequence.lastProgram 2 window) == 192 &&
        Solcore.Core.Wire.programNodes (CallSequence.lastProgram 3 window) == 192)
      "a middle or last phase changed size"
  ensure (CallSequence.maxContractNodes == 1024 && Solcore.Synthesis.Source.CallSequence.maxStepNodes == 512 &&
      CallSequence.base == 256) "the case limits or the data's base changed"
  -- The draws alone, over enough seeds to reach every bank entry.
  let mut counts : List Nat := []
  let mut offsets : List Nat := []
  let mut widths : List Nat := []
  let mut lengths : List Nat := []
  let mut statuses : List Bool := []
  let mut parents : List Bool := []
  for index in List.range 256 do
    let seed := Seed.ofNat (1 + index)
    let windows := Solcore.Synthesis.Source.CallSequence.generatedWindows seed
    ensure (CallSequence.validWindows windows) s!"seed {1 + index}: the drawn windows are not valid"
    counts := (counts ++ [windows.length]).eraseDups
    offsets := (offsets ++ windows.map (·.offset)).eraseDups
    widths := (widths ++ windows.map (·.width)).eraseDups
    for transaction in Solcore.Synthesis.Source.CallSequence.generatedTransactions windows.length seed 3 do
      let input := transaction.input.val
      for call in List.range windows.length do
        let byte := input / 2 ^ (8 * call) % 256
        lengths := (lengths ++ [byte / 2]).eraseDups
        statuses := (statuses ++ [byte % 2 == 1]).eraseDups
      ensure (windows.length == 3 || input / 2 ^ 16 % 256 == 0) s!"seed {1 + index}: an unused class byte is not zero"
      ensure (input / 2 ^ 25 % 2 ^ 7 == 0) s!"seed {1 + index}: the input's bits 25 to 31 are not zero"
      parents := (parents ++ [input / 2 ^ 24 % 2 == 1]).eraseDups
  ensure (counts.length == 2 && [2, 3].all counts.contains) s!"the draws chose the call counts {counts}"
  ensure (Solcore.Synthesis.Source.CallSequence.offsetBank.all offsets.contains &&
      offsets.any (fun offset => !Solcore.Synthesis.Source.CallSequence.offsetBank.contains offset) &&
      offsets.all (· ≤ 96)) "the draws missed a bank offset or a uniform one"
  ensure (Solcore.Synthesis.Source.CallSequence.widthBank.all widths.contains &&
      widths.any (fun width => !Solcore.Synthesis.Source.CallSequence.widthBank.contains width) &&
      widths.all (· ≤ 32)) "the draws missed a bank width or a uniform one"
  ensure (Solcore.Synthesis.Source.CallSequence.lengthBank.all lengths.contains &&
      lengths.any (fun length => !Solcore.Synthesis.Source.CallSequence.lengthBank.contains length) &&
      lengths.all (· ≤ 96)) "the draws missed a bank length or a uniform one"
  ensure (statuses.length == 2 && parents.length == 2) "the draws missed a call or parent outcome"
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three.
  let mut outcomes : List String := []
  let mut cases : Array Json := #[]
  for (revision, transactions, count, nodes) in
      [(GeneratorRevision.v3, 8, 40, 384), (GeneratorRevision.v1, 3, 24, 384), (GeneratorRevision.v3, 4, 12, 512)] do
    let corpus := Solcore.Synthesis.Source.CallSequence.generateCases (Seed.ofNat 1) nodes count 512 fuel
      revision transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} at {nodes} case {index}"
      ensure ((Solcore.Synthesis.Source.CallSequence.replayCase json fuel).toOption == some json)
        s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.CallSequence.caseProgram json)
      ensure (scenario.transactions.length == transactions) s!"{name}: wrong sequence length"
      ensure (Solcore.Synthesis.Source.CallSequence.budgetNodes scenario.plan ≤ nodes) s!"{name}: over its node budget"
      outcomes := (outcomes ++ (← sameAsModel scenario json fuel name)).eraseDups
      let sources ← get (json.getObjVal? "sources")
      ensure (((← get (sources.getObjValAs? String "parent")).splitOn "contract SynthesizedReturnCaller {").length == 2 &&
          ((← get (sources.getObjValAs? String "child")).splitOn "contract SynthesizedReturnCallee {").length == 2 &&
          ((← get (sources.getObjValAs? String "parent")).splitOn "contract ").length == 2 &&
          ((← get (sources.getObjValAs? String "child")).splitOn "contract ").length == 2 &&
          ((← get (sources.getObjValAs? String "parent")).splitOn "raw_call(").length == scenario.plan.calls + 1)
        s!"{name}: a source does not hold exactly its one contract and one raw_call per call"
      cases := cases.push json
  ensure (["parent-returned", "parent-reverted", "returned", "reverted"].all outcomes.contains)
    s!"generation reached the outcomes {outcomes}"
  -- Reductions: a dropped call, an earlier or narrower window and smaller
  -- inputs come with every case that has one, and every emitted candidate
  -- replays as a strictly smaller sealed case.
  for json in cases.toList.take 12 do
    let source ← get (Solcore.Synthesis.Source.CallSequence.caseProgram json)
    let reduced := Solcore.Synthesis.Source.CallSequence.reductions source
    ensure (!reduced.isEmpty) "a case has no reduction"
    ensure (source.plan.calls == 2 || reduced.any (fun candidate => candidate.candidate.plan.calls == 2))
      "no reduction drops the last call"
    ensure (Solcore.Synthesis.Source.CallSequence.windowWeight source.plan == 0 || reduced.any (fun candidate =>
        Solcore.Synthesis.Source.CallSequence.windowWeight candidate.candidate.plan <
          Solcore.Synthesis.Source.CallSequence.windowWeight source.plan))
      "no reduction narrows a window"
    ensure (reduced.any (fun candidate => Solcore.Synthesis.Source.CallSequence.inputWeight candidate.candidate <
        Solcore.Synthesis.Source.CallSequence.inputWeight source)) "no reduction makes an input smaller"
    let shrunk ← get (Solcore.Synthesis.Source.CallSequence.shrinkCases json 64 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.CallSequence.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      let _ ← sameAsModel (← get (Solcore.Synthesis.Source.CallSequence.caseProgram candidate)) candidate fuel "reduction"
  -- Refusals: windows outside the bounds, call counts outside two and three,
  -- and saved fields that differ from the plan or the model.
  let some first := cases[0]? | throw (IO.userError "no case")
  let template ← get (Solcore.Synthesis.Source.CallSequence.caseProgram first)
  let step := template.plan.step
  let admitted (windows : List Window) : Bool := (CheckedPlan.ofParts? step windows).isSome
  ensure (admitted [⟨0, 0⟩, ⟨96, 32⟩] && admitted [⟨33, 31⟩, ⟨0, 1⟩, ⟨95, 0⟩]) "admissible windows were refused"
  for (windows, label) in [(([⟨0, 0⟩] : List Window), "one call"), ([⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], "four calls"),
      ([⟨97, 0⟩, ⟨0, 0⟩], "an offset above 96"), ([⟨0, 33⟩, ⟨0, 0⟩], "a width above 32")] do
    ensure (!admitted windows) s!"{label} was admitted"
  let some plan := CheckedPlan.ofParts? step [⟨31, 1⟩, ⟨32, 32⟩] | throw (IO.userError "the plan failed admission")
  let scenario ← get (Solcore.Synthesis.Source.CallSequence.checkedScenario plan [⟨"tx-0", w 64⟩, ⟨"tx-1", w (2 ^ 24 + 1)⟩])
  let pairCase ← get (Solcore.Synthesis.Source.CallSequence.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel)
  let refused (json : Json) : Bool := (Solcore.Synthesis.Source.CallSequence.caseProgram json).toOption.isNone
  ensure (!refused pairCase) "an admissible case was refused"
  let saved ← get (pairCase.getObjValAs? (Array Json) "transactions")
  ensure (refused (pairCase.setObjVal! "transactions" (toJson (saved.modify 0 (·.setObjVal! "parentReverts" (toJson true))))))
    "a parent revert that differs from the model was admitted"
  ensure (refused (pairCase.setObjVal! "transactions" (toJson (saved.modify 1 (·.setObjVal! "calls" (toJson ([] : List Json)))))))
    "calls that differ from the model were admitted"
  let programs ← get (pairCase.getObjVal? "programs")
  ensure (refused (pairCase.setObjVal! "programs" (programs.setObjVal! "parentLast" (← get (programs.getObjVal? "parentCall")))))
    "a last phase from another role was admitted"
  ensure (refused (pairCase.setObjVal! "programs" (programs.setObjVal! "parentMiddles" (toJson ([] : List Json)))))
    "a chain without its middle phase was admitted"
  ensure (refused (pairCase.setObjVal! "observedSlots" (Solcore.Synthesis.Source.CallReturn.observedSlotsJson)))
    "the call-return profile's observed slots were admitted"
  ensure ((Solcore.Synthesis.Source.CallSequence.replayCase (pairCase.setObjVal! "sources"
      ((← get (pairCase.getObjVal? "sources")).setObjVal! "parent" (toJson "contract X {}"))) fuel).toOption.isNone)
    "a changed parent source was admitted"
  let saved ← get (pairCase.getObjVal? "callSequencePlan")
  for (changed, label) in [(saved.setObjVal! "calls" (toJson 3), "a call count without its window"),
      (saved.setObjVal! "windows" (toJson ([] : List Json)), "no windows"),
      (saved.setObjVal! "extra" (toJson 1), "an extra field")] do
    ensure (Solcore.Synthesis.Source.CallSequence.checkedPlan changed).toOption.isNone s!"a plan with {label} was admitted"

end Tests.SourceCallSequenceCases
