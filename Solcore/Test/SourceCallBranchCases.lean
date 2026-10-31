import Solcore.Synthesis.Source.CallBranchCases

/-! Generated call-branch cases. Original Core through the choice chain must
equal the Lean model, the child's data and the parent's reads before and after
each site and after each call, on every transaction of the generated sequences,
with each transaction's prescribed outcomes; every chain must make exactly the
model's calls; each case must replay to itself; the phases must stay within
their bounds, at the sizes measured here; generation must draw every site
count, both kinds, every loop bound, every bank offset, width and length beside
uniform ones, both statuses, every control outcome and both parent outcomes;
and every reduction must be a strictly smaller sealed case that replays. -/
set_option autoImplicit false

namespace Tests.SourceCallBranchCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallBranch (CheckedPlan Site Kind)
open Solcore.Synthesis.Core.CallSequence (Window)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.CallBranchExecution (Transaction)

private abbrev Cases := Solcore.Synthesis.Source.CallBranch.CheckedScenario

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

private def sameRow (row : Json) (model : CallBranchExecution.ModelRow) : Bool :=
  let accounts := (row.getObjValAs? (List Json) "committedAccounts").toOption.getD []
  (row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
    (row.getObjValAs? String "output").toOption == some (encodeBytesText model.output) &&
    accounts.map slotValues == [model.parent.map (toString ·.val), model.child.map (toString ·.val)]

/-- The Core rows of a scenario equal the model's, each transaction records
the model's prescribed outcomes, and each chain makes exactly the model's
calls. Returns the outcomes reached. -/
private def sameAsModel (scenario : Cases) (json : Json) (fuel : Nat) (name : String) : IO (List String) := do
  let history := Solcore.Synthesis.Source.CallBranch.observe scenario NestedCallExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := CallBranchExecution.model scenario.plan fuel scenario.transactions
    | throw (IO.userError s!"{name}: the Lean model failed")
  ensure (rows.size == modelled.length) s!"{name}: a row is missing"
  for (row, model) in rows.toList.zip modelled do
    ensure (sameRow row model) s!"{name}: the Core row differs from the Lean model: {row.compress}"
  let saved ← get (json.getObjValAs? (List Json) "transactions")
  ensure (saved.map (fun tx => ((tx.getObjVal? "calls").toOption, (tx.getObjVal? "parentReverts").toOption)) ==
      modelled.map (fun row => (some (toJson (row.calls.map Solcore.Synthesis.Source.CallBranch.callRowJson)),
        some (toJson row.reverted))))
    s!"{name}: a prescribed outcome differs from the model"
  let bindings := NestedCallExecution.fixtureBindings
  let mut world := CallBranchExecution.initialWorld scenario.plan bindings
  for (transaction, model) in scenario.transactions.zip modelled do
    match CallChoiceExecution.run (CallBranchExecution.registry scenario.plan bindings) scenario.plan.parent world
        bindings.parent bindings.caller (CallBranchExecution.inputData bindings transaction.input) fuel with
    | .completed _ finalWorld calls =>
        ensure (calls.map (fun call => (call.child.status == .returned, call.child.data.size)) ==
            model.calls.map (fun call => (call.returned, call.length)))
          s!"{name}: a chain's calls differ from the model's"
        world := finalWorld
    | _ => throw (IO.userError s!"{name}: a chain did not complete")
  return modelled.flatMap fun row =>
    (if row.reverted then ["parent-reverted"] else ["parent-returned"]) ++ ["calls-" ++ toString row.calls.length] ++
      row.calls.map fun call => if call.returned then "returned" else "reverted"

private def branchSite (spot : Window) : Site := ⟨.branch, 1, 0, spot, spot⟩
private def loopSite (bound stop : Nat) (spot : Window) : Site := ⟨.loop, bound, stop, spot, spot⟩

def testSourceCallBranchCases : IO Unit := do
  let fuel := 1000000
  -- The phases' sizes, measured for one plan of each shape, and the bounds.
  for (sites, call, resume) in [([branchSite ⟨0, 32⟩], 399, 502), ([loopSite 3 33 ⟨31, 2⟩], 574, 877),
      ([branchSite ⟨1, 31⟩, loopSite 2 96 ⟨64, 32⟩], 763, 1066),
      ([branchSite ⟨0, 0⟩, branchSite ⟨96, 0⟩, branchSite ⟨33, 31⟩], 867, 1170),
      ([loopSite 1 64 ⟨0, 32⟩, branchSite ⟨63, 1⟩, loopSite 1 1 ⟨95, 1⟩], 1037, 1340)] do
    ensure (CallBranch.validSites sites) "a measured plan is not valid"
    ensure (Solcore.Core.Wire.programNodes (CallBranch.callProgram sites) == call &&
        Solcore.Core.Wire.programNodes (CallBranch.resumeProgram sites) == resume)
      s!"a phase changed size: {Solcore.Core.Wire.programNodes (CallBranch.callProgram sites)}, {Solcore.Core.Wire.programNodes (CallBranch.resumeProgram sites)}"
    ensure ((CallBranch.callProgram sites).check && (CallBranch.resumeProgram sites).check) "a phase is not admitted"
  ensure (CallSequence.childShellNodes == 129 && CallBranch.maxChildNodes == 1024 && CallBranch.maxPhaseNodes == 2048 &&
      Solcore.Synthesis.Source.CallBranch.maxStepNodes == 512 && CallBranch.base == 192 && CallBranch.keptWords == 5)
    "the case limits, the kept Words or the data's base changed"
  -- The draws alone, over enough seeds to reach every bank entry.
  let mut counts : List Nat := []
  let mut kinds : List String := []
  let mut bounds : List Nat := []
  let mut stops : List Nat := []
  let mut offsets : List Nat := []
  let mut widths : List Nat := []
  let mut lengths : List Nat := []
  let mut statuses : List Bool := []
  let mut controls : List String := []
  let mut parents : List Bool := []
  for index in List.range 256 do
    let seed := Seed.ofNat (1 + index)
    let sites := Solcore.Synthesis.Source.CallBranch.generatedSites seed
    ensure (CallBranch.validSites sites) s!"seed {1 + index}: the drawn sites are not valid"
    counts := (counts ++ [sites.length]).eraseDups
    for site in sites do
      kinds := (kinds ++ [Solcore.Synthesis.Source.CallBranch.kindName site.kind]).eraseDups
      if site.kind == .loop then
        bounds := (bounds ++ [site.bound]).eraseDups
        stops := (stops ++ [site.stop]).eraseDups
      offsets := (offsets ++ [site.callWindow.offset, site.exitWindow.offset]).eraseDups
      widths := (widths ++ [site.callWindow.width, site.exitWindow.width]).eraseDups
    let positions := CallBranch.positions sites
    for transaction in Solcore.Synthesis.Source.CallBranch.generatedTransactions sites seed 3 do
      let input := transaction.input.val
      for position in List.range 3 do
        let byte := input / 2 ^ (8 * position) % 256
        if position < positions then
          lengths := (lengths ++ [byte / 2]).eraseDups
          statuses := (statuses ++ [byte % 2 == 1]).eraseDups
        else ensure (byte == 0) s!"seed {1 + index}: an unused class byte is not zero"
      for slot in List.range 3 do
        let bits := input / 2 ^ CallBranch.controlBit slot % 4
        match sites[slot]? with
        | some site =>
            match site.kind with
            | .branch =>
                ensure (bits < 2) s!"seed {1 + index}: a branch's second control bit is set"
                controls := (controls ++ ["branch-" ++ toString bits]).eraseDups
            | .loop => controls := (controls ++ ["loop-" ++ toString bits]).eraseDups
        | none => ensure (bits == 0) s!"seed {1 + index}: an unused site's control bits are set"
      ensure (input / 2 ^ 31 % 2 == 0) s!"seed {1 + index}: the input's bit 31 is set"
      parents := (parents ++ [input / 2 ^ CallBranch.revertBit % 2 == 1]).eraseDups
  ensure ([1, 2, 3].all counts.contains) s!"the draws chose the site counts {counts}"
  ensure (["branch", "loop"].all kinds.contains && [1, 2, 3].all bounds.contains) "the draws missed a kind or a loop bound"
  ensure (Solcore.Synthesis.Source.CallBranch.offsetBank.all offsets.contains &&
      offsets.any (fun offset => !Solcore.Synthesis.Source.CallBranch.offsetBank.contains offset) &&
      offsets.all (· ≤ 96)) "the draws missed a bank offset or a uniform one"
  ensure (Solcore.Synthesis.Source.CallBranch.widthBank.all widths.contains &&
      widths.any (fun width => !Solcore.Synthesis.Source.CallBranch.widthBank.contains width) &&
      widths.all (· ≤ 32)) "the draws missed a bank width or a uniform one"
  ensure (Solcore.Synthesis.Source.CallBranch.lengthBank.all lengths.contains &&
      lengths.any (fun length => !Solcore.Synthesis.Source.CallBranch.lengthBank.contains length) &&
      lengths.all (· ≤ 96)) "the draws missed a bank length or a uniform one"
  ensure (Solcore.Synthesis.Source.CallBranch.lengthBank.all stops.contains &&
      stops.any (fun stop => !Solcore.Synthesis.Source.CallBranch.lengthBank.contains stop) && stops.all (· ≤ 96))
    "the draws missed a bank stop length or a uniform one"
  ensure (statuses.length == 2 && parents.length == 2) "the draws missed a call or parent outcome"
  ensure (["branch-0", "branch-1", "loop-0", "loop-1", "loop-2", "loop-3"].all controls.contains)
    s!"the draws chose the control outcomes {controls}"
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three.
  let mut outcomes : List String := []
  let mut cases : Array Json := #[]
  for (revision, transactions, count, nodes) in
      [(GeneratorRevision.v3, 8, 40, 384), (GeneratorRevision.v1, 3, 24, 384), (GeneratorRevision.v3, 4, 12, 512)] do
    let corpus := Solcore.Synthesis.Source.CallBranch.generateCases (Seed.ofNat 1) nodes count 512 fuel
      revision transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} at {nodes} case {index}"
      ensure ((Solcore.Synthesis.Source.CallBranch.replayCase json fuel).toOption == some json)
        s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.CallBranch.caseProgram json)
      ensure (scenario.transactions.length == transactions) s!"{name}: wrong sequence length"
      ensure (Solcore.Synthesis.Source.CallBranch.budgetNodes scenario.plan ≤ nodes) s!"{name}: over its node budget"
      outcomes := (outcomes ++ (← sameAsModel scenario json fuel name)).eraseDups
      let sources ← get (json.getObjVal? "sources")
      ensure (((← get (sources.getObjValAs? String "parent")).splitOn "contract SynthesizedReturnCaller {").length == 2 &&
          ((← get (sources.getObjValAs? String "child")).splitOn "contract SynthesizedReturnCallee {").length == 2 &&
          ((← get (sources.getObjValAs? String "parent")).splitOn "contract ").length == 2 &&
          ((← get (sources.getObjValAs? String "child")).splitOn "contract ").length == 2 &&
          ((← get (sources.getObjValAs? String "parent")).splitOn "raw_call(").length == scenario.plan.sites.length + 1)
        s!"{name}: a source does not hold exactly its one contract and one raw_call per site"
      cases := cases.push json
  ensure (["parent-returned", "parent-reverted", "returned", "reverted", "calls-0", "calls-1", "calls-2", "calls-3"].all
      outcomes.contains)
    s!"generation reached the outcomes {outcomes}"
  -- Reductions: a dropped site, a lowered loop bound, an earlier or narrower
  -- window and smaller inputs come with every case that has one, and every
  -- emitted candidate replays as a strictly smaller sealed case.
  for json in cases.toList.take 12 do
    let source ← get (Solcore.Synthesis.Source.CallBranch.caseProgram json)
    let reduced := Solcore.Synthesis.Source.CallBranch.reductions source
    ensure (!reduced.isEmpty) "a case has no reduction"
    ensure (source.plan.sites.length == 1 || reduced.any (fun candidate =>
        candidate.candidate.plan.sites.length < source.plan.sites.length))
      "no reduction drops the last site"
    ensure (!source.plan.sites.any (fun site => site.kind == .loop && site.bound > 1) || reduced.any (fun candidate =>
        candidate.candidate.plan.sites.length == source.plan.sites.length &&
          candidate.candidate.plan.positions < source.plan.positions))
      "no reduction lowers a loop's bound"
    ensure (Solcore.Synthesis.Source.CallBranch.siteWeight source.plan == 0 || reduced.any (fun candidate =>
        Solcore.Synthesis.Source.CallBranch.siteWeight candidate.candidate.plan <
          Solcore.Synthesis.Source.CallBranch.siteWeight source.plan))
      "no reduction narrows a window or an earlier stop"
    ensure (reduced.any (fun candidate => Solcore.Synthesis.Source.CallBranch.inputWeight candidate.candidate <
        Solcore.Synthesis.Source.CallBranch.inputWeight source)) "no reduction makes an input smaller"
    let shrunk ← get (Solcore.Synthesis.Source.CallBranch.shrinkCases json 64 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.CallBranch.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      let _ ← sameAsModel (← get (Solcore.Synthesis.Source.CallBranch.caseProgram candidate)) candidate fuel "reduction"
  -- Refusals: sites outside the bounds, and saved fields that differ from the
  -- plan or the model.
  let some first := cases[0]? | throw (IO.userError "no case")
  let template ← get (Solcore.Synthesis.Source.CallBranch.caseProgram first)
  let step := template.plan.step
  let admitted (sites : List Site) : Bool := (CheckedPlan.ofParts? step sites).isSome
  ensure (admitted [branchSite ⟨0, 0⟩] && admitted [loopSite 3 96 ⟨96, 0⟩] &&
      admitted [branchSite ⟨33, 31⟩, loopSite 1 0 ⟨0, 32⟩, branchSite ⟨95, 1⟩]) "admissible sites were refused"
  for (sites, label) in [(([] : List Site), "no site"),
      ([branchSite ⟨0, 0⟩, branchSite ⟨0, 0⟩, branchSite ⟨0, 0⟩, branchSite ⟨0, 0⟩], "four sites"),
      ([loopSite 3 0 ⟨0, 0⟩, branchSite ⟨0, 0⟩], "four positions"), ([⟨.branch, 2, 0, ⟨0, 0⟩, ⟨0, 0⟩⟩], "a branch of bound two"),
      ([⟨.branch, 1, 5, ⟨0, 0⟩, ⟨0, 0⟩⟩], "a branch with a stop length"), ([loopSite 4 0 ⟨0, 0⟩], "a loop of bound four"),
      ([loopSite 0 0 ⟨0, 0⟩], "a loop of bound zero"), ([loopSite 1 97 ⟨0, 0⟩], "a stop length above 96"),
      ([branchSite ⟨97, 0⟩], "an offset above 96"), ([branchSite ⟨0, 33⟩], "a width above 32")] do
    ensure (!admitted sites) s!"{label} was admitted"
  let some plan := CheckedPlan.ofParts? step [branchSite ⟨31, 1⟩, loopSite 2 33 ⟨32, 32⟩]
    | throw (IO.userError "the plan failed admission")
  let scenario ← get (Solcore.Synthesis.Source.CallBranch.checkedScenario plan
    [⟨"tx-0", w (64 + 2 ^ 24 + 2 * 2 ^ 26)⟩, ⟨"tx-1", w (2 ^ 30 + 1)⟩])
  let pairCase ← get (Solcore.Synthesis.Source.CallBranch.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel)
  let refused (json : Json) : Bool := (Solcore.Synthesis.Source.CallBranch.caseProgram json).toOption.isNone
  ensure (!refused pairCase) "an admissible case was refused"
  let saved ← get (pairCase.getObjValAs? (Array Json) "transactions")
  ensure (refused (pairCase.setObjVal! "transactions" (toJson (saved.modify 0 (·.setObjVal! "parentReverts" (toJson true))))))
    "a parent revert that differs from the model was admitted"
  ensure (refused (pairCase.setObjVal! "transactions" (toJson (saved.modify 0 (·.setObjVal! "calls" (toJson ([] : List Json)))))))
    "calls that differ from the model were admitted"
  let programs ← get (pairCase.getObjVal? "programs")
  ensure (refused (pairCase.setObjVal! "programs" (programs.setObjVal! "parentResume" (← get (programs.getObjVal? "parentCall")))))
    "a resume phase from another role was admitted"
  ensure (refused (pairCase.setObjVal! "observedSlots" (Solcore.Synthesis.Source.CallReturn.observedSlotsJson)))
    "the call-return profile's observed slots were admitted"
  ensure ((Solcore.Synthesis.Source.CallBranch.replayCase (pairCase.setObjVal! "sources"
      ((← get (pairCase.getObjVal? "sources")).setObjVal! "parent" (toJson "contract X {}"))) fuel).toOption.isNone)
    "a changed parent source was admitted"
  let savedPlan ← get (pairCase.getObjVal? "callBranchPlan")
  for (changed, label) in [(savedPlan.setObjVal! "sites" (toJson ([] : List Json)), "no sites"),
      (savedPlan.setObjVal! "extra" (toJson 1), "an extra field")] do
    ensure (Solcore.Synthesis.Source.CallBranch.checkedPlan changed).toOption.isNone s!"a plan with {label} was admitted"

end Tests.SourceCallBranchCases
