import Solcore.Synthesis.Internal.CallReturns
import Solcore.Synthesis.Internal.Calls
import Solcore.Synthesis.Internal.ConstructorArguments

/-!
# Call profile tests

Call branches, returns, sequences and values, forwarded calls and constructor arguments.
-/

section
-- leanmerge: from Solcore.Test.SourceCallBranchCases
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
end

section
-- leanmerge: from Solcore.Test.SourceCallBranchCorpus
/-! The fixed call-branch corpus checks actual original Core histories, run
through the choice chain, against each entry's expected history, which must
also equal the byte-level model's rows: the child's data cut to its class
byte's length and the parent's reads of the return-data buffer before and
after each site and after each call, in which each step runs alone in Core.
Coverage describes the checked steps' AST, the inputs, one to three sites,
every loop bound, zero to three calls, the buffer at every position passed
without a call, every loop exit, the bank's lengths for returned and reverted
data, windows inside, past the end and of width zero, the three rollback
patterns, the call modes, the node budgets of generated entries and both
outcomes. Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceCallBranchCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.CallBranch (Site Kind)
open Solcore.Synthesis.Core.CallSequence (Window)
open Solcore.Synthesis.Stateful.CallBranchExecution (CallRow)
open Solcore.ContractRuntime (encodeBytesText)

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers {α : Type} [BEq α] (left right : List α) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", CallBranch.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.CallSequence.childVersion),
  ("templateVersion", CallBranch.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", CallBranch.emitterVersion), ("wrapperVersion", CallBranch.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

def skipStates : List String := ["none", "returned-data", "returned-empty", "reverted-data", "reverted-empty"]
def loopExits : List String := ["stop-at-entry", "stop-after-call", "limit"]
def lengthNames : List String := ["returned", "reverted"].flatMap fun status =>
  CallBranch.lengthBank.map fun length => status ++ ":" ++ toString length
def windowKinds : List String := ["empty", "inside", "outside"]
def rollbacks : List String := ["child-reverted-parent-returned", "child-reverted-parent-reverted",
  "children-returned-parent-reverted"]

private def windowKind (window : Window) (size : Nat) : String :=
  if window.offset + window.width > size then "outside" else if window.width == 0 then "empty" else "inside"

/-- One transaction's branch values: the buffer at each position passed
without a call, each loop's exit and every window's place. -/
def transactionValues (sites : List Site) (input : Word) (calls : List CallRow) :
    List String × List String × List String := Id.run do
  let latest := fun (before : Nat) => (calls.filter (·.position < before)).getLast?
  let stateOf := fun (call : Option CallRow) => match call with
    | none => "none"
    | some call => (if call.returned then "returned" else "reverted") ++ (if call.length == 0 then "-empty" else "-data")
  let mut skips : List String := []
  let mut exits : List String := []
  let mut windows : List String := []
  for (site, index) in sites.zipIdx do
    let first := CallBranch.firstPosition sites index
    let positions := (List.range site.bound).map (first + ·)
    for position in positions do
      unless calls.any (·.position == position) do
        skips := skips ++ [stateOf (latest position)]
    if site.kind == .loop then
      let limit := Solcore.Synthesis.Stateful.CallBranchExecution.limitOf input index site.bound
      let made := (calls.filter fun call => positions.contains call.position).length
      exits := exits ++ [if made == limit then "limit" else if made == 0 then "stop-at-entry" else "stop-after-call"]
    windows := windows ++ [windowKind site.exitWindow ((latest (first + site.bound)).map (·.length) |>.getD 0)]
  for call in calls do
    let site := sites.getD (CallBranch.siteOf sites call.position) ⟨.branch, 1, 0, ⟨0, 0⟩, ⟨0, 0⟩⟩
    windows := windows ++ [windowKind site.callWindow call.length]
  return (skips, exits, windows)

/-- Imported entries are emitted from their saved plan and sequence;
generated entries are regenerated from their seed. Both are checked by full
replay. -/
def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := CallBranch.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← CallBranch.checkedPlan (← entry.getObjVal? "callBranchPlan")
  let scenario ← CallBranch.checkedScenario plan (← CallReturn.decodeImportedSequence (← entry.getObjVal? "transactions"))
  CallBranch.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "call-branch-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- The source model's rows of a scenario, in the corpus's expected-row form:
the status, the output, every call's prescribed outcome, and the parent's and
child's committed slots. -/
def modelRows (scenario : CallBranch.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.CallBranchExecution.model scenario.plan fuel scenario.transactions
    | throw "the source model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (encodeBytesText row.output)), ("calls", toJson (row.calls.map CallBranch.callRowJson)),
    ("parent", toJson (words row.parent)), ("child", toJson (words row.child))]

private def slotValues (account : Json) : Except String (List String) := do
  (← account.getObjValAs? (List Json) "storage").mapM fun entry => entry.getObjValAs? String "value"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-call-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-call-branches" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected call-branch manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("call-branch manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words NestedCall.boundaryInputs))
    "call-branch corpus must require every boundary input"
  require ((← manifest.getObjValAs? (List Nat) "requiredBranchSites") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredBranchLoops") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredBranchCalls") == [0, 1, 2, 3] &&
    (← strings manifest "requiredBranchSkips") == skipStates &&
    (← strings manifest "requiredBranchLoopExits") == loopExits &&
    sameMembers (← strings manifest "requiredBranchLengths") lengthNames &&
    (← strings manifest "requiredBranchWindows") == windowKinds &&
    (← strings manifest "requiredBranchRollbacks") == rollbacks &&
    (← manifest.getObjValAs? (List Nat) "requiredBranchNodeBudgets") == [384, 512])
    "call-branch corpus must require every site count, loop bound, call count, skip, loop exit, bank length, window, rollback and both node budgets"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredCallModes") == [0, 1])
    "call-branch corpus must require one to three helpers and transactions and both call modes"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "call-branch corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "call-branch corpus must require both transaction outcomes"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "call-branch corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut siteCounts : List Nat := []
  let mut loopBounds : List Nat := []
  let mut callCounts : List Nat := []
  let mut seenSkips : List String := []
  let mut seenExits : List String := []
  let mut seenLengths : List String := []
  let mut seenWindows : List String := []
  let mut rolled : List String := []
  let mut modes : List Nat := []
  let mut budgets : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut statusesSeen : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate call-branch corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← CallBranch.replayCase saved fuel) == saved) ("call-branch corpus entry did not replay: " ++ identifier)
    let scenario ← CallBranch.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "callBranchPlan") == (← entry.getObjVal? "callBranchPlan"))
        ("imported call-branch entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("call-branch corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel)) ("the expected history differs from the source model: " ++ identifier)
    let savedTransactions ← saved.getObjValAs? (List Json) "transactions"
    require (savedTransactions.map (·.getObjVal? "calls" |>.toOption) == expected.map (·.getObjVal? "calls" |>.toOption))
      ("a prescribed outcome differs from the expected history: " ++ identifier)
    let history := CallBranch.observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("call-branch corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("call-branch expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let accounts ← row.getObjValAs? (List Json) "committedAccounts"
      let some parent := accounts[0]? | throw "missing parent account"
      let some child := accounts[1]? | throw "missing child account"
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("calls", ← golden.getObjVal? "calls"),
        ("parent", toJson (← slotValues parent)), ("child", toJson (← slotValues child))]
      require (actual == golden) ("original Core differs from the source model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    let sites := scenario.plan.sites
    siteCounts := (siteCounts ++ [sites.length]).eraseDups
    loopBounds := (loopBounds ++ (sites.filter (·.kind == .loop)).map (·.bound)).eraseDups
    let some rows := Solcore.Synthesis.Stateful.CallBranchExecution.model scenario.plan fuel scenario.transactions
      | throw "the source model failed"
    for (transaction, row) in scenario.transactions.zip rows do
      modes := (modes ++ [transaction.input.val % 2]).eraseDups
      callCounts := (callCounts ++ [row.calls.length]).eraseDups
      let (skips, exits, windows) := transactionValues sites transaction.input row.calls
      seenSkips := (seenSkips ++ skips).eraseDups
      seenExits := (seenExits ++ exits).eraseDups
      seenWindows := (seenWindows ++ windows).eraseDups
      seenLengths := (seenLengths ++ row.calls.map fun call =>
        (if call.returned then "returned:" else "reverted:") ++ toString call.length).eraseDups
      let reverted := row.calls.any (!·.returned)
      if row.reverted then
        if reverted then rolled := (rolled ++ ["child-reverted-parent-reverted"]).eraseDups
        if row.calls.any (·.returned) then rolled := (rolled ++ ["children-returned-parent-reverted"]).eraseDups
      else if reverted then rolled := (rolled ++ ["child-reverted-parent-returned"]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    statusesSeen := (statusesSeen ++ statuses).eraseDups
  require (requiredFeatures.all features.contains) "call-branch corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "call-branch corpus misses a boundary input"
  require ([1, 2, 3].all siteCounts.contains && [1, 2, 3].all loopBounds.contains && [0, 1, 2, 3].all callCounts.contains)
    "call-branch corpus misses a site count, a loop bound or a call count"
  require (skipStates.all seenSkips.contains && loopExits.all seenExits.contains && lengthNames.all seenLengths.contains)
    "call-branch corpus misses a skip, a loop exit or a bank length"
  require (windowKinds.all seenWindows.contains && rollbacks.all rolled.contains && [0, 1].all modes.contains &&
      [384, 512].all budgets.contains)
    "call-branch corpus misses a window, a rollback, a call mode or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "call-branch corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "call-branch corpus misses a generated template"
  require (["returned", "reverted"].all statusesSeen.contains) "call-branch corpus misses an observed outcome"
  return Json.mkObj [("profile", toJson "stateful-call-branches"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("sites", toJson siteCounts), ("loops", toJson loopBounds),
    ("calls", toJson callCounts), ("skips", toJson seenSkips), ("exits", toJson seenExits),
    ("lengths", toJson seenLengths.length), ("windows", toJson seenWindows), ("rollbacks", toJson rolled),
    ("nodeBudgets", toJson budgets)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid call-branch corpus unexpectedly passed")

def testSourceCallBranchCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-call-branch-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated call-branch case")
  let some first := entries.find? (fun entry => (entry.getObjValAs? String "id").toOption == some "skips") |
    throw (IO.userError "missing the skips entry")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  -- A row's output, slots and prescribed calls, and a missing row, are all
  -- checked.
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let output ← checked (row.getObjValAs? String "output")
  let changedOutput := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 1)) ++
    (if output.endsWith "1" then "2" else "1")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let parent ← checked (row.getObjValAs? (Array String) "parent")
  let changedSlot := row.setObjVal! "parent" (toJson (parent.set! 5 (if parent[5]! == "7" then "8" else "7")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory"
    (.arr (history.set! 0 (row.setObjVal! "calls" (toJson ([] : List Json))))))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  if let some head := generatedHistory[0]? then
    let flipped := if (head.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
    rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
      (.arr (generatedHistory.set! 0 (head.setObjVal! "status" (toJson flipped)))))))
  -- The plan, the features, a duplicate entry and the requirements are checked.
  let plan ← checked (first.getObjVal? "callBranchPlan")
  rejects (validateManifest (replace first (first.setObjVal! "callBranchPlan" (plan.setObjVal! "sites" (toJson ([] : List Json))))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-call-sequences"), ("functionVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredBranchSites", toJson [1]), ("requiredBranchLoops", toJson [3]), ("requiredBranchCalls", toJson [1]),
      ("requiredBranchSkips", toJson (["none"] : List String)),
      ("requiredBranchLoopExits", toJson (["limit"] : List String)),
      ("requiredBranchLengths", toJson (["returned:0"] : List String)),
      ("requiredBranchWindows", toJson (["inside"] : List String)),
      ("requiredBranchRollbacks", toJson (["child-reverted-parent-returned"] : List String)),
      ("requiredBranchNodeBudgets", toJson [384]),
      ("requiredHelperCounts", toJson [1, 2]), ("requiredTransactionCounts", toJson [1, 2]),
      ("requiredCallModes", toJson [0])] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceCallBranchCorpus
end

section
-- leanmerge: from Solcore.Test.SourceCallBranchGolden
/-! Golden rows of whole transactions for the call-branch profile. Every
expected row is written out by an independent Python model of the two sources
over the EVM's return-data buffer, not by either Lean model: the child's
identity step `r = x + o`, its data cut to its class byte's length, and the
parent's reads before and after each site and after each call, through six
plans of branches and loops. A row is the transaction's status and output, the
parent's and the child's committed slots, and the calls it makes as their
positions, statuses and data lengths. The byte-level model gives each row
exactly, and so does original Core through the choice chain, the call phase,
each child and each resume phase run through the public top-level runner.
Changed rows fail. -/
set_option autoImplicit false

namespace Tests.SourceCallBranchGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallBranch (CheckedPlan Site Kind)
open Solcore.Synthesis.Core.CallSequence (Window)
open Solcore.Synthesis.Stateful

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The identity step, `let h = fun x => x in fun y => h y`, an imported step of
the call corpora. -/
def identityStep : String := "{\"body\":{\"body\":{\"body\":{\"argument\":{\"index\":0,\"tag\":\"var\"},\"function\":{\"index\":1,\"tag\":\"var\"},\"tag\":\"apply\"},\"parameterType\":\"word\",\"resultType\":\"word\",\"tag\":\"lambda\"},\"initializer\":{\"body\":{\"index\":0,\"tag\":\"var\"},\"parameterType\":\"word\",\"resultType\":\"word\",\"tag\":\"lambda\"},\"tag\":\"let\"},\"dataDefinitions\":[],\"resultType\":{\"parameter\":\"word\",\"result\":\"word\",\"tag\":\"function\"},\"schema\":\"solcore-semantic-core\"}"

private def branch (call exit : Window) : Site := ⟨.branch, 1, 0, call, exit⟩
private def loop (bound stop : Nat) (call exit : Window) : Site := ⟨.loop, bound, stop, call, exit⟩

/-- The six plans the rows name. -/
def plans : List (String × List Site) := [
  ("branch", [branch ⟨0, 32⟩ ⟨64, 32⟩]),
  ("loop", [loop 3 33 ⟨31, 2⟩ ⟨64, 32⟩]),
  ("branch-loop", [branch ⟨1, 31⟩ ⟨33, 31⟩, loop 2 32 ⟨32, 32⟩ ⟨0, 0⟩]),
  ("three-branches", [branch ⟨0, 0⟩ ⟨96, 0⟩, branch ⟨95, 1⟩ ⟨0, 32⟩, branch ⟨33, 31⟩ ⟨63, 1⟩]),
  ("loops-around", [loop 1 0 ⟨0, 32⟩ ⟨1, 1⟩, branch ⟨63, 1⟩ ⟨64, 32⟩, loop 1 64 ⟨95, 1⟩ ⟨32, 32⟩]),
  ("loop-branch", [loop 2 1 ⟨0, 1⟩ ⟨95, 1⟩, branch ⟨96, 0⟩ ⟨31, 2⟩])]

/-- The name, the plan, the transaction's index, its input and the expected row. -/
def rows : List (String × String × String × String × String) := [
  ("branch-0", "branch", "0", "66", "status:returned output:0000000000000000000000000000000000000000000000000000000000000042 parent:66,0,0,0,0,0,0,0,0,0 child:0,0 calls:"),
  ("branch-1", "branch", "1", "4311744578", "status:returned output:038e36a437602738d653f269c62ba2f9876b2b90e4a79634f0bad4d227eaafde parent:4311744644,0,0,33,0,67,804103975257020510786665636818339584693665539641618581323552313294261147498,33,804103975257020510786665636818339584693665539641618581323552313294261147498,1 child:322,1 calls:0:returned:33"),
  ("branch-2", "branch", "2", "8606712001", "status:returned output:f5fe46aea8facc5c469dc77e10060a728f68b4ea4d55b823a0105c4fccfbe298 parent:12918456645,0,0,96,60107477038876802831507568021578656920676872543997416836352194236029517815892,192,83475263543432000108327258496792590125671245524785929167382747290477206110143,96,83475263543432000108327258496792590125671245524785929167382747290477206110143,1 child:322,1 calls:0:reverted:96"),
  ("branch-3", "branch", "3", "12901679104", "status:returned output:0000000000000000000000000000000000000000000000000000000603000147 parent:25820135749,0,0,0,0,1,0,0,0,1 child:1090,2 calls:0:returned:0"),
  ("branch-4", "branch", "4", "17179869187", "status:returned output:0000000000000000000000000000000000000000000000000000000a03000148 parent:43000004936,0,0,0,0,0,0,0,0,0 child:1090,2 calls:"),
  ("branch-5", "branch", "5", "22565355648", "status:reverted output:b2a38818299d9c663f1a5895907718122c0956beae3f07b423c603bd4562969e parent:43000004936,0,0,0,0,0,0,0,0,0 child:1090,2 calls:0:returned:64"),
  ("branch-6", "branch", "6", "25786581184", "status:returned output:81635e9db00a7129c0a72f1dcaa82fbcfa9f68abfd261146a2f1d6766a2e3533 parent:68786586120,0,0,96,30784706616699849062070126906922486313828505751928585213070755224244034414933,193,71765655481339127253539133745707777525637722765606778538112222174806184002602,96,71765655481339127253539133745707777525637722765606778538112222174806184002602,1 child:2818,3 calls:0:returned:96"),
  ("branch-7", "branch", "7", "6901746346790563787434755862277025452451108972170386555162524240576577", "status:returned output:69a34a8c24d0d66cfc94fa6d13ab44abd383e9717cdae24159dd0d53ec9172c8 parent:6901746346790563787434755862277025452451108972170386555162593027162697,0,0,32,0,64,23890676389277424921538839942096715463631220817657872355510684435528748152831,32,23890676389277424921538839942096715463631220817657872355510684435528748152831,1 child:2818,3 calls:0:reverted:32"),
  ("loop-0", "loop", "0", "657930", "status:returned output:00000000000000000000000000000000000000000000000000000000000a0a0a parent:657930,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 child:0,0 calls:"),
  ("loop-1", "loop", "1", "4312402512", "status:returned output:396dc37711c2dccfbdbc7e79f816c455aad3bdafc5360b960e4b3762ff1f388c parent:4313060442,0,0,40,0,81,76355644955039627113584554365824294253552075779826404632331696332076487484304,40,65412212032225344649832840072504329292965108830129165067578104784255369347072,0,0,0,0,0,0,0,0,1 child:336,1 calls:0:returned:40"),
  ("loop-2", "loop", "2", "8640545538", "status:returned output:1cfe31f2d542bc7c76be3a43a916beb0a8ad798a9c3a7588219627460e17d29f parent:12953605980,0,0,33,0,3,0,1,0,66,44842923236412452309127493490747316110647002178613388341580411927934825102009,33,84063049648025969632914128490346577146040028845548198789509779845100263702528,0,0,0,0,2 child:850,2 calls:0:returned:1;1:reverted:33"),
  ("loop-3", "loop", "3", "12947930752", "status:returned output:28d8f5d863f80a61abe5c048d93ee20f898ce1db62f3daf3bc4416b5c125fd7a parent:25901536732,0,0,96,53285903240311716342392281254662973395652900446800351164742766927063140451853,129,10113785616757195461523770068396979628967266418833897725534918270616118129722,64,26619317877951138309501960146192810359456872390328075223060119028674609545216,191,109268932733003173291862966752716945926819019764472937662578911002672593700816,95,94218886576372122759358922524616872775016406284789256560792772290130242174976,192,55583213235054893154320687485511392788158533469961445192302804601252076167717,96,16762078103552532134756743389548067959655339729658997055699678031663083814912,3 child:24515266422721616073337149231265700921710777228579387644265243977462783968400,4 calls:0:returned:64;1:returned:95;2:reverted:96"),
  ("loop-4", "loop", "4", "17213439489", "status:returned output:0000000000000000000000000000000000000000000000000000000a09da545c parent:43114976221,0,0,31,0,0,0,0,0,63,0,31,0,0,0,0,0,2 child:24515266422721616073337149231265700921710777228579387644265243977462783969486,5 calls:0:reverted:0;1:returned:31"),
  ("loop-5", "loop", "5", "21526089282", "status:returned output:514d686efcb4ef0413b2b9ff9d9aea278b27c73fa4a80de76ca742c9879bf1f5 parent:64641065503,0,0,33,0,67,269281527673643312640779255704745171938893986222738585412613932484524216144,33,36504827205386198633520509662849439455511644793347163293750505724906817191936,0,0,0,0,0,0,0,0,1 child:24515266422721616073337149231265700921710777228579387644265243977462783970832,6 calls:0:returned:33"),
  ("loop-6", "loop", "6", "26898088000", "status:reverted output:a8886d292dcf549261bd99de3ce45a6a95056ff33625981f0261d67f435c2515 parent:64641065503,0,0,33,0,67,269281527673643312640779255704745171938893986222738585412613932484524216144,33,36504827205386198633520509662849439455511644793347163293750505724906817191936,0,0,0,0,0,0,0,0,1 child:24515266422721616073337149231265700921710777228579387644265243977462783970832,6 calls:0:returned:32;1:returned:32;2:returned:32"),
  ("loop-7", "loop", "7", "57896044618658097711785492504343953926634992332820282019728792003952303439491", "status:returned output:b3cbcdb98b53853a10a5e1dcb34c7cfb8c93dc53b9acfead10ef640ef30c0a99 parent:57896044618658097711785492504343953926634992332820282019728792004016944504994,0,0,63,0,130,14603455883220766524269191551058896679086552560139320588221877911095696486543,65,64827385653783699436740768599758423264226211660263335192439853131627512201216,127,100131711822557169023060042691328146305586552110618587759376256473408193312678,63,75449670207231346026195553174224849381381044848279556368666949613798742294528,0,0,0,0,2 child:95195086816403876362246465037493663226043827390115046673784467111068632964494,7 calls:0:reverted:65;1:returned:63"),
  ("branch-loop-0", "branch-loop", "0", "151126592", "status:returned output:6c4cce3271a4826417482f52ad7f1124aa64d7e585311299359ef8a49d0ae842 parent:151126592,0,0,32,0,32,32,0,65,64169113474095441298403670597213730842554198338574794994497382923786862699840,32,100608466906849417667830786661720088382806936819827989027810683373685571928064,0,0,0,0,0,0,0,0,1 child:64,1 calls:0:returned:32"),
  ("branch-loop-1", "branch-loop", "1", "4429594624", "status:returned output:5336963eefba20ed6b20908b64ac4e18c33b21ed73ab7af4a29f1aba335e2242 parent:4580721216,0,0,0,0,0,32,0,0,0,0,0,65,37638413132624061519709068557218661495515236034527077848611545518981787279232,32,0,0,0,0,0,1 child:384,2 calls:1:returned:32"),
  ("branch-loop-2", "branch-loop", "2", "8673852993", "status:returned output:2e31482d726a35e6ed97e6957527fd6a8e9239d263f4db4489270d8a54de5397 parent:13254574209,0,0,32,0,32,32,0,64,107763434989924353944013305231453358204654404008162362485133558656504136482133,32,28922118939380098857511707184337631313271075667110554803286022181734085121280,0,0,0,0,0,0,0,0,1 child:384,2 calls:0:reverted:32"),
  ("branch-loop-3", "branch-loop", "3", "13086425344", "status:returned output:00000000000000000000000000000000000000000000000000000006220bc187 parent:26340999553,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,2,0,1,0,2 child:384,2 calls:1:reverted:0;2:reverted:1"),
  ("branch-loop-4", "branch-loop", "4", "17335238656", "status:returned output:2831f5b7f33b65625dffa6a731a01890d3102df71c2bfa95cbd6c05c8c450aa9 parent:43676238209,0,0,0,0,0,33,0,1,0,0,0,193,83507689216956793915988824294628991772782469237474185906325851701172518614848,96,54669608633456800578962535353626817863465255687378671454418779436198673137300,67,111587665960864117481851326540960981572329529131240167479268923321393295839658,33,0,3 child:56801032324440586518397642303675371632072257741959452316062448753520548397698,5 calls:0:returned:0;1:returned:96;2:returned:33"),
  ("branch-loop-5", "branch-loop", "5", "21491613826", "status:returned output:f1ec5276eac679f52f12cb68ee8fa385255b800108069240689a11aaebd1f5df parent:65167852035,0,0,65,34761563293180050655265289220186738128790959472467747354988598068014019181568,65,65,0,131,45345806622581685829790542243533666947744719770247660572472145259932926485076,65,29317571649292030069280313475827953295649794619344702607110785751516216185856,0,0,0,0,0,0,0,0,1 child:56801032324440586518397642303675371632072257741959452316062448753520548399108,6 calls:0:returned:65"),
  ("three-branches-0", "three-branches", "0", "297861248", "status:returned output:a6f1b2a463fa5594322b892e1b1ae354bb7d461de3f6a06872c1bcfb7a8a0c98 parent:297861248,0,0,64,0,64,64,12546137710874687173236356185739553831838412011509025949537181839660595759744,64,96,106293519417067601267731177644693977912181431236037236520595829069764005724160,129,12546137710874687173236356185739553831838412011509025949537181839660595759744,64,0,0,0,0,0,192,78214348535409267502382711367266952388552303608552843235503619510853997201621,96,97495011050649839387010565686878620687017891423129334870985635221225259002624,2 child:128,1 calls:0:returned:64;2:reverted:96"),
  ("three-branches-1", "three-branches", "1", "4362093312", "status:returned output:7776e396807135585a4dd3876dcf67722a96e65c6e5eccd14dfdbac69fbda545 parent:4659954560,0,0,0,0,0,33,84913688463154005540549148165308551809033383805815594414194221015961090011263,33,33,0,0,0,0,0,66,84913688463154005540549148165308551809033383805815594414194221015961090011263,33,0,0,0,0,0,1 child:128,1 calls:1:reverted:33"),
  ("three-branches-2", "three-branches", "2", "8954839296", "status:returned output:c8ac3a5a267fb519cd331afea9b3ad8831c53a99fc2f24417e6b12fd68575345 parent:13614793856,0,0,0,0,0,0,0,0,96,57443731770074831323412168344153766786583156455220123566449660816425654157312,1,0,0,0,0,0,0,0,193,73838401345526117607196247445921361307668333788024490450411617312479690657344,96,75276826265248123039418137114437322991030472069054155697223091037963574411008,3 child:1344,3 calls:0:returned:0;1:reverted:0;2:returned:96"),
  ("three-branches-3", "three-branches", "3", "13153468416", "status:returned output:000000000000000000000000000000000000000000000000000000063b834486 parent:26768262272,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,3,0,1,0,1 child:2114,4 calls:2:returned:1"),
  ("three-branches-4", "three-branches", "4", "17196646463", "status:returned output:0000000000000000000000000000000000000000000000000000000a3c8345b8 parent:43964908735,0,0,31,0,31,31,0,31,31,0,62,0,31,0,0,0,0,0,0,0,0,0,1 child:2114,4 calls:0:reverted:31"),
  ("three-branches-5", "three-branches", "5", "21474836480", "status:returned output:0000000000000000000000000000000000000000000000000000000f3c8344bf parent:65439745215,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 child:2114,4 calls:"),
  ("three-branches-6", "three-branches", "6", "26927480512", "status:reverted output:d10c4d1728232ed75e4b98b08b402cf790e3a8537c63973122cc9b8d14349547 parent:65439745215,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 child:2114,4 calls:0:returned:96;1:returned:95"),
  ("three-branches-7", "three-branches", "7", "30408785920", "status:returned output:94f16639ff898c41227b2e78518303501e27146f2590807c593e5e8c0dc6fd75 parent:95848531135,0,0,0,0,0,32,68888805641895116389095354408675854158913446203547448044489274723838416200362,32,64,115339776388732929035197660848497720713218148788040405586178452820382218977280,0,0,0,0,65,68888805641895116389095354408675854158913446203547448044489274723838416200362,32,0,128,37901838121876563103479250131164244105863867207284334748813317476517776405183,64,7933769954923232984802306261182702840814033553172111683812049390938354417408,2 child:3970,5 calls:1:returned:32;2:reverted:64"),
  ("loops-around-0", "loops-around", "0", "353533962", "status:returned output:cef456792488870fc1fcf08ed3d1e23c5195dd65c4db9b4e2ea172fa469b5a21 parent:353533962,0,0,0,0,0,64,0,64,64,71563446777022297856526126342750658392501306254664949883333486863006233103893,0,0,0,0,129,12546137710874687173236356185739553831838412011509025949537181839660595759744,64,9498569820248594155839807363993929941088553429603327518861754938149123915776,0,0,0,0,1 child:128,1 calls:1:returned:64"),
  ("loops-around-1", "loops-around", "1", "4655682058", "status:returned output:878933a88d49fac8d7a3af8720edb1a007e916d74fb41a1a459829972b258afe parent:5009216020,0,0,0,0,0,9,0,9,64,98898251093750698146007394019564067324233934098354285610542876581105569675327,0,0,0,0,19,0,9,0,129,78198487283395291339832458840254494203187047082739727188700640681160273182586,64,0,2 child:5394,3 calls:1:returned:9;2:returned:64"),
  ("loops-around-2", "loops-around", "2", "8938062080", "status:returned output:ec4f6b801969b33cba5178e70bc209017e57a7214210edd7682844a924ef2665 parent:13947278100,0,0,0,0,0,0,0,0,96,54669608633456800578962535353626817863465255687378671454418779436198673135764,0,0,0,0,0,0,0,0,193,89306200074547973080846925357478086351663320813219087891426348795336985041210,96,78702435653488351576958403873092562369019442702427570870568826630378455302144,2 child:6098,4 calls:1:reverted:0;2:returned:96"),
  ("loops-around-3", "loops-around", "3", "13178568704", "status:returned output:3ce868309cb0f83d462c4aed05da4fa366e5efcde1e5f160d474572a7d6650cc parent:27125846804,0,0,0,0,0,0,0,0,64,10440966173162903011917676687689568402696577276403057298294682291291776600936,0,0,0,0,0,0,0,0,128,17108432353060690302885574983029805860493541817166091342604940520141129183567,64,0,1 child:6098,4 calls:2:reverted:64"),
  ("loops-around-4", "loops-around", "4", "17263788032", "status:returned output:3f2aa7f667e2921aef4feae996b4bb7fd88b345590b5d1074871feed7333d8b9 parent:44389634836,0,0,0,0,0,64,0,64,64,10440966173162903011917676687689568402696577276403057298294682291291776601193,0,0,0,0,129,86429350235103962216403146020446162984939044251159757397803401344369217238970,64,47492849101242970779199036819969649705442767148016637594308774690745619578880,0,0,0,0,1 child:7250,5 calls:1:returned:64"),
  ("loop-branch-0", "loop-branch", "0", "101059074", "status:returned output:3c00000000000000000000000000000000000000000000000000000006060a17 parent:101059074,0,0,1,0,1,3,0,3,0,1,27138770914995983302399449611411228403110152656009507196747871251854639759360,0,0,0,0,7,0,3,0,2 child:520,2 calls:0:returned:1;2:returned:3"),
  ("loop-branch-1", "loop-branch", "1", "4395958792", "status:returned output:640000000000000000000000000000000000000000000000000000010c0b0c28 parent:4497017866,0,0,1,0,1,2,0,9,0,4,61966860255907495207145409946055638187101515231221708099240972691734760783872,3,0,1,99056513839735339053757991081650983671352057194434701268129730069269435121664,4,0,2,0,3 child:2066,4 calls:0:returned:4;1:returned:1;2:reverted:2"),
  ("loop-branch-2", "loop-branch", "2", "8606712001", "status:returned output:da9192dcd33d219be9b6530de1ce0b8eb0d0b57e275b6d43fd801ed9ac2565db parent:13103729867,0,0,96,104484268022734535714237881003933229351974087725636602707479304319640363073536,96,96,93669397139226045232858517001885825116594058792860939064816952761528237424640,192,66254244843460795280369760888376160822905884099930491165708275842993987671759,96,66037675893156892702505327387767322447568038129623134178753153379512956747776,0,0,0,0,0,0,0,0,1 child:2066,4 calls:0:reverted:96"),
  ("loop-branch-3", "loop-branch", "3", "13002342403", "status:returned output:5c000000000000000000000000000000000000000000000000000006140b0cd6 parent:26106072270,0,0,1,0,1,0,0,2,0,1,41612782069660507730345822737497216884768900739214577701680069252843780964352,0,0,0,0,1,0,0,0,2 child:3346,5 calls:0:reverted:1;2:returned:0")
]

private def hex64 (word : Word) : String :=
  let digits := String.ofList (Nat.toDigits 16 word.val)
  String.ofList (List.replicate (64 - digits.length) '0') ++ digits

private def commas (values : List Word) : String := String.intercalate "," (values.map fun value => toString value.val)

private def callsText (calls : List (Nat × Bool × Nat)) : String :=
  String.intercalate ";" (calls.map fun (position, returned, length) =>
    s!"{position}:{if returned then "returned" else "reverted"}:{length}")

private def rowText (status : String) (output : Word) (parent child : List Word) (calls : List (Nat × Bool × Nat)) :
    String :=
  s!"status:{status} output:{hex64 output} parent:{commas parent} child:{commas child} calls:{callsText calls}"

private def outputWord (bytes : ByteArray) : Word :=
  (decodeWordBytesBE? bytes).getD Word.zero

private def slotWords (account : Json) : List Word :=
  match account.getObjValAs? (List Json) "storage" with
  | .ok entries => entries.filterMap fun entry =>
      ((entry.getObjValAs? String "value").toOption.bind String.toNat?).map Word.ofNatModulo
  | .error _ => []

def testSourceCallBranchGolden : IO Unit := do
  let fuel := 1000000
  let step ← get (Solcore.Synthesis.Source.Aggregate.checkedFunction (← get (Json.parse identityStep)))
  let mut checked := 0
  for (name, sites) in plans do
    let some plan := CheckedPlan.ofParts? step sites | throw (IO.userError s!"{name}: the plan failed admission")
    let planRows := rows.filter fun (_, planName, _, _, _) => planName == name
    let transactions : List CallBranchExecution.Transaction := planRows.map fun (_, _, index, input, _) =>
      ⟨"tx-" ++ index, Word.ofNatModulo (input.toNat?.getD 0)⟩
    let scenario ← get (Solcore.Synthesis.Source.CallBranch.checkedScenario plan transactions)
    let some modelled := CallBranchExecution.model plan fuel transactions
      | throw (IO.userError s!"{name}: the Lean model failed")
    -- Original Core through the choice chain, with each chain's calls.
    let bindings := NestedCallExecution.fixtureBindings
    let mut world := CallBranchExecution.initialWorld plan bindings
    let mut coreCalls : Array (List (Nat × Bool × Nat)) := #[]
    for transaction in transactions do
      match CallChoiceExecution.run (CallBranchExecution.registry plan bindings) plan.parent world bindings.parent
          bindings.caller (CallBranchExecution.inputData bindings transaction.input) fuel with
      | .completed _ finalWorld calls =>
          coreCalls := coreCalls.push (calls.map fun call =>
            ((call.request.kept.getD 3 Word.zero).val, call.child.status == .returned, call.child.data.size))
          world := finalWorld
      | _ => throw (IO.userError s!"{name}: a chain did not complete")
    let history := Solcore.Synthesis.Source.CallBranch.observe scenario bindings fuel
    let coreRows ← get (history.getObjValAs? (Array Json) "transactions")
    ensure (coreRows.size == planRows.length && modelled.length == planRows.length) s!"{name}: a row is missing"
    for (((rowName, _, _, _, expected), model), (coreRow, calls)) in
        (planRows.zip modelled).zip (coreRows.toList.zip coreCalls.toList) do
      let modelText := rowText (if model.reverted then "reverted" else "returned") (outputWord model.output)
        model.parent model.child (model.calls.map fun call => (call.position, call.returned, call.length))
      ensure (modelText == expected) s!"{rowName}: the Lean model gave {modelText}"
      let accounts ← get (coreRow.getObjValAs? (List Json) "committedAccounts")
      let output ← get (coreRow.getObjValAs? String "output")
      let some bytes := Solcore.ContractRuntime.decodeBytesText? output
        | throw (IO.userError s!"{rowName}: Core's output is not hexadecimal text")
      let coreText := rowText (← get (coreRow.getObjValAs? String "status")) (outputWord bytes)
        (slotWords (accounts.getD 0 Json.null)) (slotWords (accounts.getD 1 Json.null)) calls
      ensure (coreText == expected) s!"{rowName}: original Core gave {coreText}"
      -- A changed row fails.
      ensure (modelText != expected ++ "0" && coreText != expected.replace "status:" "status:x") s!"{rowName}: a changed row passed"
      checked := checked + 1
  ensure (checked == rows.length) s!"only {checked} of {rows.length} rows were checked"

end Tests.SourceCallBranchGolden
end

section
-- leanmerge: from Solcore.Test.SourceCallReturnCases
/-! Generated call-return cases. Original Core through the call-and-resume
convention must equal the Lean model, the child's bytes and std's decision on
them, on every transaction of the generated sequences, with each transaction's
prescribed rejection; a typed child must deliver exactly the bytes the model
builds for its canonical encoding; each case must replay to itself; the
contracts' node counts must be the ones the definitions fix; generation must
draw every kind, static and dynamic enums apart, every malformation kind that
applies to each, every std decision of each and every bank length; and every
reduction must be a strictly smaller sealed case that replays. -/
set_option autoImplicit false

namespace Tests.SourceCallReturnCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallReturn (CheckedPlan Kind Returned Delivery Malformation)
open Solcore.Synthesis.Core.EnumReturn (Constructor Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.CallReturnExecution (Transaction)

private abbrev Cases := Solcore.Synthesis.Source.CallReturn.CheckedScenario

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

private def sameRow (row : Json) (model : CallReturnExecution.ModelRow) : Bool :=
  let accounts := (row.getObjValAs? (List Json) "committedAccounts").toOption.getD []
  (row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
    (row.getObjValAs? String "output").toOption == some (encodeBytesText model.output) &&
    accounts.map slotValues == [model.parent.map (toString ·.val), model.child.map (toString ·.val)]

/-- The Core rows of a scenario equal the model's, and each transaction
records the model's prescribed rejection. -/
private def sameAsModel (scenario : Cases) (json : Json) (fuel : Nat) (name : String) : IO (List String) := do
  let history := Solcore.Synthesis.Source.CallReturn.observe scenario NestedCallExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := CallReturnExecution.model scenario.plan fuel scenario.transactions
    | throw (IO.userError s!"{name}: the Lean model failed")
  ensure (rows.size == modelled.length) s!"{name}: a row is missing"
  for (row, model) in rows.toList.zip modelled do
    ensure (sameRow row model) s!"{name}: the Core row differs from the Lean model: {row.compress}"
  let saved ← get (json.getObjValAs? (List Json) "transactions")
  ensure (saved.map (fun tx => (tx.getObjVal? "stdRejection").toOption) ==
      modelled.map (fun row => some (Solcore.Synthesis.Source.CallReturn.rejectionJson row.rejection)))
    s!"{name}: a prescribed rejection differs from the model"
  return modelled.map fun row => match row.rejection with
    | some data => encodeBytesText data
    | none => if row.reverted then "reverted" else "returned"

/-- A typed child delivers exactly the model's canonical bytes. -/
private def typedBytes (scenario : Cases) (fuel : Nat) (name : String) : IO Unit := do
  if scenario.plan.returned.delivery == .typed then
    let bindings := NestedCallExecution.fixtureBindings
    let world := CallReturnExecution.initialWorld scenario.plan bindings
    for transaction in scenario.transactions do
      if transaction.input.val % 2 == 0 then
        match CallResumeExecution.run (CallReturnExecution.registry scenario.plan bindings) scenario.plan.parent world
            bindings.parent bindings.caller (CallReturnExecution.inputData bindings transaction.input) fuel with
        | .completed _ _ _ (some child) =>
            let some r := CallReturnExecution.stepResult scenario.plan.step fuel transaction.input
              | throw (IO.userError s!"{name}: the step failed")
            ensure (child.status == .returned && child.data ==
                CallReturnExecution.returnBytes scenario.plan.returned
                  (CallReturnExecution.valuesOf r (w 1) transaction.input Word.zero))
              s!"{name}: a typed child's bytes differ from the model's canonical encoding"
        | _ => throw (IO.userError s!"{name}: the first call did not complete")

/-- The kinds, an enum by its class. -/
private def classOf : Kind → String
  | .tuple _ => "tuple"
  | .bytes => "bytes"
  | .enum shape => if shape.dynamic then "dynamic" else "static"

private def payloads : List EnumPayload := [.noWords, .oneWord, .twoWords, .boundedBytes]

/-- Every field list of `count` constructors. -/
private def fieldLists : Nat → List (List EnumPayload)
  | 0 => [[]]
  | count + 1 => (fieldLists count).flatMap fun rest => payloads.map (· :: rest)

private def shapeOf (constructors : List Constructor) : IO Shape := do
  let some shape := Solcore.Synthesis.Source.EnumReturn.Shape.ofList? constructors
    | throw (IO.userError "the shape has fewer than two constructors")
  return shape

/-- std's decision on a drawn value's bytes, which no Word of the value
decides. -/
private def decision (returned : Returned) : String :=
  match CallReturnExecution.decide returned.kind
      (CallReturnExecution.returnBytes returned (CallReturnExecution.valuesOf (w 3) (w 5) (w 8) (w 13))) with
  | .ok _ => "accepted"
  | .error data => encodeBytesText data

def testSourceCallReturnCases : IO Unit := do
  let fuel := 1000000
  -- The contracts' sizes, as the definitions fix them.
  ensure (CallReturn.callNodes == 49) "the call phase is not 49 nodes"
  ensure ([0, 1, 2].map (fun extra => CallReturn.childShellNodes ⟨.tuple extra, 0, 0, .typed⟩) == [58, 62, 66] &&
      [0, 1, 2].map (fun extra => CallReturn.resumeNodes (.tuple extra)) == [198, 203, 208])
    "a tuple's shell or resume phase changed size"
  ensure (CallReturn.childShellNodes ⟨.bytes, 0, 0, .typed⟩ == 66 && CallReturn.resumeNodes .bytes == 351)
    "the bytes shell or resume phase changed size"
  let names := ["Idle", "Ready", "Pair", "Blob"]
  for (count, staticRange, dynamicRange) in [(2, (227, 285), (446, 622)), (3, (242, 329), (461, 666)),
      (4, (257, 373), (476, 710))] do
    let shapes := (fieldLists count).filterMap fun fields =>
      if (fields.filter (· == .boundedBytes)).length ≤ 2 then
        Solcore.Synthesis.Source.EnumReturn.Shape.ofList? ((names.zip fields).map fun (name, payload) => ⟨name, payload⟩)
      else none
    for (dynamic, (low, high)) in [(false, staticRange), (true, dynamicRange)] do
      let sizes := (shapes.filter (·.dynamic == dynamic)).map (CallReturn.resumeNodes ∘ .enum)
      ensure (sizes.foldl min 1000000 == low && sizes.foldl max 0 == high)
        s!"the resume phases of {count} constructors (dynamic {dynamic}) take {sizes.foldl min 1000000} to {sizes.foldl max 0} nodes"
  ensure (CallReturn.maxContractNodes == 1024 && Solcore.Synthesis.Source.CallReturn.maxStepNodes == 512)
    "the case limits changed"
  -- The draws alone, over enough seeds to reach every malformation that
  -- applies to each kind and every std decision of each.
  let mut pairs : List String := []
  let mut decisions : List String := []
  let mut lengths : List Nat := []
  let mut shells : List Nat := []
  for index in List.range 256 do
    let seed := Seed.ofNat (1 + index)
    let returned := Solcore.Synthesis.Source.CallReturn.generatedReturned seed
    ensure (returned.valid) s!"seed {1 + index}: the drawn value is not valid"
    let malformation := match returned.delivery with
      | .typed => "typed"
      | .raw malformation => Solcore.Synthesis.Source.CallReturn.kindOf malformation
    pairs := (pairs ++ [classOf returned.kind ++ ":" ++ malformation]).eraseDups
    decisions := (decisions ++ [classOf returned.kind ++ ":" ++ decision returned]).eraseDups
    if returned.carriesBytes then lengths := (lengths ++ [returned.length]).eraseDups
    shells := shells ++ [CallReturn.childShellNodes returned]
  let applicable := [("tuple", ["typed", "truncate", "trailing"]),
    ("bytes", ["typed", "truncate", "trailing", "offset", "length"]),
    ("static", ["typed", "truncate", "trailing", "tag", "tagCut", "narrow"]),
    ("dynamic", ["typed", "truncate", "trailing", "offset", "length", "tag", "tagCut", "tail"])]
  let expectedPairs := applicable.flatMap fun (kind, kinds) => kinds.map (kind ++ ":" ++ ·)
  ensure (pairs.length == expectedPairs.length && expectedPairs.all pairs.contains)
    s!"the draws reached the malformations {pairs}"
  let expectedDecisions := ["tuple:accepted", "tuple:0x08638556", "bytes:accepted", "bytes:0x08638556",
    "static:accepted", "static:0x08638556", "static:0x", "dynamic:accepted", "dynamic:0x08638556", "dynamic:0x"]
  ensure (decisions.length == expectedDecisions.length && expectedDecisions.all decisions.contains)
    s!"the draws reached the decisions {decisions}"
  for length in Solcore.Synthesis.Source.CallReturn.lengthBank do
    ensure (lengths.contains length) s!"the draws never chose length {length}"
  ensure (lengths.all (· ≤ 64) && lengths.any (fun length => length % 32 != 0 &&
      !Solcore.Synthesis.Source.CallReturn.lengthBank.contains length))
    "the draws chose a length above 64 or no uniform partial-Word length"
  ensure (shells.all (fun shell => 58 ≤ shell && shell ≤ 114)) "a drawn child's shell lies outside 58 to 114 nodes"
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three.
  let mut classes : List String := []
  let mut outcomes : List String := []
  let mut cases : Array Json := #[]
  for (revision, transactions, count, nodes) in
      [(GeneratorRevision.v3, 8, 40, 384), (GeneratorRevision.v1, 3, 24, 384), (GeneratorRevision.v3, 4, 12, 512)] do
    let corpus := Solcore.Synthesis.Source.CallReturn.generateCases (Seed.ofNat 1) nodes count 512 fuel
      revision transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} at {nodes} case {index}"
      ensure ((Solcore.Synthesis.Source.CallReturn.replayCase json fuel).toOption == some json)
        s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.CallReturn.caseProgram json)
      ensure (scenario.transactions.length == transactions) s!"{name}: wrong sequence length"
      ensure (Solcore.Synthesis.Source.CallReturn.budgetNodes scenario.plan ≤ nodes) s!"{name}: over its node budget"
      outcomes := (outcomes ++ (← sameAsModel scenario json fuel name)).eraseDups
      typedBytes scenario fuel name
      let sources ← get (json.getObjVal? "sources")
      ensure (((← get (sources.getObjValAs? String "parent")).splitOn "contract SynthesizedReturnCaller {").length == 2 &&
          ((← get (sources.getObjValAs? String "child")).splitOn "contract SynthesizedReturnCallee {").length == 2 &&
          ((← get (sources.getObjValAs? String "parent")).splitOn "contract ").length == 2 &&
          ((← get (sources.getObjValAs? String "child")).splitOn "contract ").length == 2)
        s!"{name}: a source does not hold exactly its one contract"
      classes := (classes ++ [classOf scenario.plan.returned.kind]).eraseDups
      cases := cases.push json
  ensure (classes.length == 4) s!"generation drew the kinds {classes}"
  ensure (["returned", "reverted", "0x08638556", "0x"].all outcomes.contains) s!"generation reached the outcomes {outcomes}"
  -- Reductions: a dropped malformation, a shorter length and a simpler kind
  -- come with every case that has one, and every emitted candidate replays as
  -- a strictly smaller sealed case.
  for json in cases.toList.take 12 do
    let source ← get (Solcore.Synthesis.Source.CallReturn.caseProgram json)
    let reduced := Solcore.Synthesis.Source.CallReturn.reductions source
    ensure (!reduced.isEmpty) "a case has no reduction"
    ensure (source.plan.returned.delivery == .typed || reduced.any (fun candidate =>
        candidate.candidate.plan.returned.delivery == .typed))
      "no reduction drops the malformation"
    ensure (source.plan.returned.length == 0 || reduced.any (fun candidate =>
        candidate.candidate.plan.returned.length < source.plan.returned.length))
      "no reduction shortens the bytes"
    ensure (source.plan.returned.kind == .tuple 0 || reduced.any (fun candidate =>
        Solcore.Synthesis.Source.CallReturn.kindWeight candidate.candidate.plan.returned.kind <
          Solcore.Synthesis.Source.CallReturn.kindWeight source.plan.returned.kind))
      "no reduction simplifies the kind"
    let shrunk ← get (Solcore.Synthesis.Source.CallReturn.shrinkCases json 64 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.CallReturn.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      let _ ← sameAsModel (← get (Solcore.Synthesis.Source.CallReturn.caseProgram candidate)) candidate fuel "reduction"
  -- Refusals: values that do not fit their kind, malformations that do not
  -- apply, and saved fields that differ from the plan or the model.
  let some first := cases[0]? | throw (IO.userError "no case")
  let template ← get (Solcore.Synthesis.Source.CallReturn.caseProgram first)
  let step := template.plan.step
  let caseOf (returned : Returned) (transactions : List Transaction) : IO Json := do
    let some plan := CheckedPlan.ofParts? step returned | throw (IO.userError "the plan failed admission")
    let scenario ← get (Solcore.Synthesis.Source.CallReturn.checkedScenario plan transactions)
    get (Solcore.Synthesis.Source.CallReturn.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel)
  let txs : List Transaction := [⟨"tx-0", w 0⟩, ⟨"tx-1", w 1⟩]
  let dynamic : Shape ← shapeOf [⟨"Blob", .boundedBytes⟩, ⟨"Idle", .noWords⟩]
  let static : Shape ← shapeOf [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩]
  let admitted (returned : Returned) : Bool := (CheckedPlan.ofParts? step returned).isSome
  ensure (admitted ⟨.bytes, 33, 0, .typed⟩ && admitted ⟨.bytes, 64, 0, .raw (.length (w 0))⟩ &&
      admitted ⟨.enum dynamic, 17, 0, .raw (.tail (w 0))⟩ && admitted ⟨.enum static, 0, 1, .raw .narrow⟩ &&
      admitted ⟨.tuple 2, 0, 0, .raw (.trailing 33 2)⟩)
    "an admissible value was refused"
  for (returned, label) in [(⟨.bytes, 65, 0, .typed⟩, "a length above 64"),
      (⟨.bytes, 3, 1, .typed⟩, "a choice without an enum"),
      (⟨.tuple 3, 0, 0, .typed⟩, "a tuple of five Words"),
      (⟨.tuple 0, 1, 0, .typed⟩, "a length for a tuple"),
      (⟨.bytes, 3, 0, .raw (.offset (w 32))⟩, "the canonical offset as a malformation"),
      (⟨.bytes, 3, 0, .raw (.length (w 3))⟩, "the canonical length as a malformation"),
      (⟨.bytes, 3, 0, .raw .narrow⟩, "a narrowed bytes value"),
      (⟨.tuple 0, 0, 0, .raw (.tag (w 0))⟩, "a tag without an enum"),
      (⟨.tuple 0, 0, 0, .raw (.truncate 64)⟩, "a cut at the canonical size"),
      (⟨.tuple 0, 0, 0, .raw (.trailing 65 0)⟩, "65 trailing bytes"),
      (⟨.enum static, 0, 2, .typed⟩, "a choice beyond the constructors"),
      (⟨.enum static, 3, 1, .typed⟩, "a length for a constructor without bytes"),
      (⟨.enum static, 0, 0, .raw .narrow⟩, "a narrowed widest constructor"),
      (⟨.enum static, 0, 1, .raw (.offset (w 0))⟩, "an offset into a static enum"),
      (⟨.enum static, 0, 1, .raw (.tag (EnumReturn.tag ⟨"Pair", .twoWords⟩))⟩, "a known tag as unknown"),
      (⟨.enum dynamic, 17, 0, .raw .narrow⟩, "a narrowed dynamic enum"),
      (⟨.enum dynamic, 17, 0, .raw (.tail (w 64))⟩, "the canonical tail offset as a malformation"),
      (⟨.enum dynamic, 0, 1, .raw (.tail (w 0))⟩, "a tail offset without bytes")] do
    ensure (!admitted returned) s!"{label} was admitted"
  let bytesCase ← caseOf ⟨.bytes, 33, 0, .raw (.length (w 100))⟩ txs
  let refused (json : Json) : Bool := (Solcore.Synthesis.Source.CallReturn.caseProgram json).toOption.isNone
  ensure (!refused bytesCase) "an admissible case was refused"
  let saved ← get (bytesCase.getObjValAs? (Array Json) "transactions")
  ensure (refused (bytesCase.setObjVal! "transactions"
      (toJson (saved.modify 0 (·.setObjVal! "stdRejection" Json.null)))))
    "a prescribed rejection that differs from the model was admitted"
  ensure (refused (bytesCase.setObjVal! "transactions"
      (toJson (saved.modify 1 (·.setObjVal! "stdRejection" (toJson "0x08638556"))))))
    "a rejection after a child revert was admitted"
  let nine := (List.range 9).map fun index => (⟨"tx-" ++ toString index, w index⟩ : Transaction)
  ensure (refused (bytesCase.setObjVal! "transactions"
      (toJson (nine.map fun tx => Solcore.Synthesis.Source.CallReturn.transactionJson tx none))))
    "nine transactions were admitted"
  let programs ← get (bytesCase.getObjVal? "programs")
  ensure (refused (bytesCase.setObjVal! "programs" (programs.setObjVal! "child" (← get (programs.getObjVal? "parentResume")))))
    "a child program from another role was admitted"
  ensure ((Solcore.Synthesis.Source.CallReturn.replayCase (bytesCase.setObjVal! "sources"
      ((← get (bytesCase.getObjVal? "sources")).setObjVal! "child" (toJson "contract X {}"))) fuel).toOption.isNone)
    "a changed child source was admitted"
  -- Plans: an unknown kind, an arity outside two to four, and an extra field
  -- are refused.
  let plan ← get (bytesCase.getObjVal? "callReturnPlan")
  ensure (Solcore.Synthesis.Source.CallReturn.checkedPlan plan).toOption.isSome "the plan was refused"
  for (changed, label) in [(plan.setObjVal! "kind" (toJson "array"), "an unknown kind"),
      ((plan.setObjVal! "kind" (toJson "tuple")).setObjVal! "arity" (toJson 5), "a tuple of five Words"),
      (plan.setObjVal! "arity" (toJson 2), "an extra field")] do
    ensure (Solcore.Synthesis.Source.CallReturn.checkedPlan changed).toOption.isNone s!"a plan with {label} was admitted"

end Tests.SourceCallReturnCases
end

section
-- leanmerge: from Solcore.Test.SourceCallReturnCorpus
/-! The fixed call-return corpus checks actual original Core histories, run
through the call-and-resume convention, against expectations computed without
the Core contracts: the child's bytes, std's decision on them and the source
model, in which each step runs alone in Core. Coverage describes the checked
steps' AST, the inputs, every kind with static and dynamic enums apart, both
deliveries, every malformation kind, std's three decisions, the malformations
std accepted, the bank's `bytes` lengths, every decoded enum field kind, the
four rollback patterns, the call modes, the node budgets of generated entries
and both outcomes. Source/Rust/EVM agreement is a separate external
validation. -/
set_option autoImplicit false

namespace Tests.SourceCallReturnCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.CallReturn (Kind Returned)
open Solcore.ContractRuntime (EnumPayload encodeBytesText)

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers {α : Type} [BEq α] (left right : List α) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", CallReturn.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.CallReturn.childVersion),
  ("templateVersion", CallReturn.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", CallReturn.emitterVersion), ("wrapperVersion", CallReturn.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- The kinds, a tuple by its arity and an enum by its class. -/
def kindName : Kind → String
  | .tuple extra => "tuple-" ++ toString (extra + 2)
  | .bytes => "bytes"
  | .enum shape => if shape.dynamic then "dynamic-enum" else "static-enum"

def kindNames : List String := ["bytes", "dynamic-enum", "static-enum", "tuple-2", "tuple-3", "tuple-4"]
def decisions : List String := ["0x", "0x08638556", "accepted"]

/-- The malformations std can accept; an unknown tag is never accepted. -/
def acceptedKinds : List String := ["length", "narrow", "offset", "tail", "trailing", "truncate"]

def fieldName : EnumPayload → String
  | .noWords => "none"
  | .oneWord => "uint256"
  | .twoWords => "uint256,uint256"
  | .boundedBytes => "bytes"

def fieldKinds : List String := ["bytes", "none", "uint256", "uint256,uint256"]
def rollbacks : List String := ["child-returned-parent-reverted", "child-reverted-parent-returned",
  "child-reverted-parent-reverted", "rejected"]

/-- Imported entries are emitted from their saved plan and sequence;
generated entries are regenerated from their seed. Both are checked by full
replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := CallReturn.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← CallReturn.checkedPlan (← entry.getObjVal? "callReturnPlan")
  let scenario ← CallReturn.checkedScenario plan (← CallReturn.decodeImportedSequence (← entry.getObjVal? "transactions"))
  CallReturn.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "call-return-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- The source model's rows of a scenario, in the corpus's expected-row form:
the status, original Core's output, the prescribed rejection, and the
parent's and child's committed slots. -/
def modelRows (scenario : CallReturn.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.CallReturnExecution.model scenario.plan fuel scenario.transactions
    | throw "the source model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (encodeBytesText row.output)), ("stdRejection", CallReturn.rejectionJson row.rejection),
    ("parent", toJson (words row.parent)), ("child", toJson (words row.child))]

private def slotValues (account : Json) : Except String (List String) := do
  (← account.getObjValAs? (List Json) "storage").mapM fun entry => entry.getObjValAs? String "value"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-call-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-call-returns" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected call-return manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("call-return manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words CallReturn.boundaryInputs))
    "call-return corpus must require every boundary input"
  require ((← strings manifest "requiredReturnKinds") == kindNames &&
    (← strings manifest "requiredReturnDeliveries") == ["raw", "typed"] &&
    sameMembers (← strings manifest "requiredReturnMalformations") CallReturn.malformationKinds &&
    (← strings manifest "requiredReturnDecisions") == decisions &&
    (← strings manifest "requiredReturnAccepted") == acceptedKinds)
    "call-return corpus must require every kind, delivery, malformation, decision and accepted malformation"
  let lengths ← manifest.getObjValAs? (List Nat) "requiredReturnBytesLengths"
  require (CallReturn.lengthBank.all lengths.contains && lengths.all (· ≤ 64) &&
    (← strings manifest "requiredReturnEnumFields") == fieldKinds &&
    (← strings manifest "requiredReturnRollbacks") == rollbacks &&
    (← manifest.getObjValAs? (List Nat) "requiredReturnNodeBudgets") == [384, 512])
    "call-return corpus must require the bank's bytes lengths, every enum field kind, every rollback and both node budgets"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredCallModes") == [0, 1, 2, 3])
    "call-return corpus must require one to three helpers and transactions and every call mode"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "call-return corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "call-return corpus must require both transaction outcomes"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "call-return corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut kinds : List String := []
  let mut deliveries : List String := []
  let mut malformations : List String := []
  let mut decided : List String := []
  let mut accepted : List String := []
  let mut bytesLengths : List Nat := []
  let mut fields : List String := []
  let mut rolled : List String := []
  let mut modes : List Nat := []
  let mut budgets : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut statusesSeen : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate call-return corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← CallReturn.replayCase saved fuel) == saved) ("call-return corpus entry did not replay: " ++ identifier)
    let scenario ← CallReturn.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "callReturnPlan") == (← entry.getObjVal? "callReturnPlan"))
        ("imported call-return entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("call-return corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel)) ("the expected history differs from the source model: " ++ identifier)
    let savedTransactions ← saved.getObjValAs? (List Json) "transactions"
    require (savedTransactions.map (·.getObjVal? "stdRejection" |>.toOption) ==
        expected.map (·.getObjVal? "stdRejection" |>.toOption))
      ("a prescribed rejection differs from the expected history: " ++ identifier)
    let history := CallReturn.observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("call-return corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("call-return expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let accounts ← row.getObjValAs? (List Json) "committedAccounts"
      let some parent := accounts[0]? | throw "missing parent account"
      let some child := accounts[1]? | throw "missing child account"
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("stdRejection", ← golden.getObjVal? "stdRejection"),
        ("parent", toJson (← slotValues parent)), ("child", toJson (← slotValues child))]
      require (actual == golden) ("original Core differs from the source model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    let returned := scenario.plan.returned
    kinds := (kinds ++ [kindName returned.kind]).eraseDups
    deliveries := (deliveries ++ [match returned.delivery with | .typed => "typed" | .raw _ => "raw"]).eraseDups
    if let .raw malformation := returned.delivery then
      malformations := (malformations ++ [CallReturn.kindOf malformation]).eraseDups
    for (transaction, golden) in scenario.transactions.zip expected do
      let x := transaction.input.val
      modes := (modes ++ [x % 4]).eraseDups
      if x % 2 == 1 then
        rolled := (rolled ++ [if x / 2 % 2 == 1 then "child-reverted-parent-reverted" else "child-reverted-parent-returned"]).eraseDups
      else
        match ← golden.getObjVal? "stdRejection" with
        | .null =>
            decided := (decided ++ ["accepted"]).eraseDups
            if let .raw malformation := returned.delivery then
              accepted := (accepted ++ [CallReturn.kindOf malformation]).eraseDups
            if returned.carriesBytes then bytesLengths := (bytesLengths ++ [returned.length]).eraseDups
            if let .enum shape := returned.kind then
              fields := (fields ++ [fieldName (Solcore.Synthesis.Core.CallReturn.chosen shape returned.choice).payload]).eraseDups
            if x / 2 % 2 == 1 then rolled := (rolled ++ ["child-returned-parent-reverted"]).eraseDups
        | rejection =>
            decided := (decided ++ [← rejection.getStr?]).eraseDups
            rolled := (rolled ++ ["rejected"]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    statusesSeen := (statusesSeen ++ statuses).eraseDups
  require (requiredFeatures.all features.contains) "call-return corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "call-return corpus misses a boundary input"
  require (kindNames.all kinds.contains && ["raw", "typed"].all deliveries.contains &&
      CallReturn.malformationKinds.all malformations.contains) "call-return corpus misses a kind, delivery or malformation"
  require (decisions.all decided.contains && acceptedKinds.all accepted.contains)
    "call-return corpus misses a decision or an accepted malformation"
  require (CallReturn.lengthBank.all bytesLengths.contains && fieldKinds.all fields.contains)
    "call-return corpus misses an accepted bytes length or enum field kind"
  require (rollbacks.all rolled.contains && [0, 1, 2, 3].all modes.contains && [384, 512].all budgets.contains)
    "call-return corpus misses a rollback, a call mode or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "call-return corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "call-return corpus misses a generated template"
  require (["returned", "reverted"].all statusesSeen.contains) "call-return corpus misses an observed outcome"
  return Json.mkObj [("profile", toJson "stateful-call-returns"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("kinds", toJson kinds), ("malformations", toJson malformations),
    ("decisions", toJson decided), ("accepted", toJson accepted), ("bytesLengths", toJson bytesLengths),
    ("fields", toJson fields), ("rollbacks", toJson rolled), ("nodeBudgets", toJson budgets)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid call-return corpus unexpectedly passed")

def testSourceCallReturnCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-call-return-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated call-return case")
  -- An imported entry whose first transaction returns, and one whose first is
  -- rejected.
  let firstStatus (entry : Json) : Option String :=
    (entry.getObjValAs? (Array Json) "expectedHistory").toOption.bind fun history =>
      history[0]?.bind fun row => (row.getObjValAs? String "status").toOption
  let some first := entries.find? (fun entry => (entry.getObjVal? "callReturnPlan").isOk &&
      firstStatus entry == some "returned") |
    throw (IO.userError "missing imported returned case")
  let some rejected := entries.find? (fun entry => (entry.getObjVal? "callReturnPlan").isOk &&
      (entry.getObjValAs? (Array Json) "expectedHistory").toOption.any (fun history =>
        history[0]?.any (fun row => (row.getObjValAs? String "stdRejection").toOption == some "0x08638556"))) |
    throw (IO.userError "missing rejected case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  -- A row's output, slots, status and prescribed rejection, and a missing row,
  -- are all checked.
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let output ← checked (row.getObjValAs? String "output")
  let changedOutput := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 1)) ++
    (if output.endsWith "1" then "2" else "1")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let parent ← checked (row.getObjValAs? (Array String) "parent")
  let changedSlot := row.setObjVal! "parent" (toJson (parent.set! 3 (if parent[3]! == "7" then "8" else "7")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let rejection ← checked (rejected.getObjValAs? (Array Json) "expectedHistory")
  rejects (validateManifest (replace rejected (rejected.setObjVal! "expectedHistory"
    (.arr (rejection.set! 0 (rejection[0]!.setObjVal! "stdRejection" (toJson "0x")))))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  if let some head := generatedHistory[0]? then
    let flipped := if (head.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
    rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
      (.arr (generatedHistory.set! 0 (head.setObjVal! "status" (toJson flipped)))))))
  -- The plan, the features, a duplicate entry and the requirements are checked.
  let plan ← checked (first.getObjVal? "callReturnPlan")
  rejects (validateManifest (replace first (first.setObjVal! "callReturnPlan" (plan.setObjVal! "choice" (toJson 9)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-calls"), ("functionVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredReturnKinds", toJson (["bytes"] : List String)),
      ("requiredReturnDeliveries", toJson (["typed"] : List String)),
      ("requiredReturnMalformations", toJson (["truncate"] : List String)),
      ("requiredReturnDecisions", toJson (["accepted"] : List String)),
      ("requiredReturnAccepted", toJson (["trailing"] : List String)),
      ("requiredReturnBytesLengths", toJson [0, 1, 32]),
      ("requiredReturnEnumFields", toJson (["none"] : List String)),
      ("requiredReturnRollbacks", toJson (["rejected"] : List String)),
      ("requiredReturnNodeBudgets", toJson [384]),
      ("requiredHelperCounts", toJson [1, 2]), ("requiredTransactionCounts", toJson [1, 2]),
      ("requiredCallModes", toJson [0, 1])] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceCallReturnCorpus
end

section
-- leanmerge: from Solcore.Test.SourceCallSequenceCases
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
end

section
-- leanmerge: from Solcore.Test.SourceCallSequenceCorpus
/-! The fixed call-sequence corpus checks actual original Core histories, run
through the call chain, against expectations computed without the Core
contracts: the child's data cut to its class byte's length and the parent's
reads of the return-data buffer around each call, in which each step runs alone
in Core. Coverage describes the checked steps' AST, the inputs, both call
counts, every pair of consecutive call states, the bank's lengths for returned
and reverted data, windows inside, past the end and of width zero, the three
rollback patterns, the call modes, the node budgets of generated entries and
both outcomes. Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceCallSequenceCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.ContractRuntime (encodeBytesText)

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers {α : Type} [BEq α] (left right : List α) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", CallSequence.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.CallSequence.childVersion),
  ("templateVersion", CallSequence.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", CallSequence.emitterVersion), ("wrapperVersion", CallSequence.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- A call's state: its status and whether its data are empty. -/
def stateOf (row : Solcore.Synthesis.Stateful.CallSequenceExecution.CallRow) : String :=
  (if row.returned then "returned" else "reverted") ++ (if row.length == 0 then "-empty" else "-data")

def states : List String := ["returned-data", "returned-empty", "reverted-data", "reverted-empty"]
def transitions : List String := states.flatMap fun first => states.map (first ++ ":" ++ ·)
def lengthNames : List String := ["returned", "reverted"].flatMap fun status =>
  CallSequence.lengthBank.map fun length => status ++ ":" ++ toString length
def windowKinds : List String := ["empty", "inside", "outside"]
def rollbacks : List String := ["child-reverted-parent-returned", "child-reverted-parent-reverted",
  "children-returned-parent-reverted"]

/-- Imported entries are emitted from their saved plan and sequence;
generated entries are regenerated from their seed. Both are checked by full
replay. -/
def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := CallSequence.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← CallSequence.checkedPlan (← entry.getObjVal? "callSequencePlan")
  let scenario ← CallSequence.checkedScenario plan (← CallReturn.decodeImportedSequence (← entry.getObjVal? "transactions"))
  CallSequence.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "call-sequence-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- The source model's rows of a scenario, in the corpus's expected-row form:
the status, the output, every call's prescribed outcome, and the parent's and
child's committed slots. -/
def modelRows (scenario : CallSequence.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.CallSequenceExecution.model scenario.plan fuel scenario.transactions
    | throw "the source model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (encodeBytesText row.output)), ("calls", toJson (row.calls.map CallSequence.callRowJson)),
    ("parent", toJson (words row.parent)), ("child", toJson (words row.child))]

private def slotValues (account : Json) : Except String (List String) := do
  (← account.getObjValAs? (List Json) "storage").mapM fun entry => entry.getObjValAs? String "value"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-call-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-call-sequences" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected call-sequence manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("call-sequence manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words CallSequence.boundaryInputs))
    "call-sequence corpus must require every boundary input"
  require ((← manifest.getObjValAs? (List Nat) "requiredSequenceCalls") == [2, 3] &&
    sameMembers (← strings manifest "requiredSequenceTransitions") transitions &&
    sameMembers (← strings manifest "requiredSequenceLengths") lengthNames &&
    (← strings manifest "requiredSequenceWindows") == windowKinds &&
    (← strings manifest "requiredSequenceRollbacks") == rollbacks &&
    (← manifest.getObjValAs? (List Nat) "requiredSequenceNodeBudgets") == [384, 512])
    "call-sequence corpus must require both call counts, every transition, the bank's lengths, every window, every rollback and both node budgets"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredCallModes") == [0, 1])
    "call-sequence corpus must require one to three helpers and transactions and both call modes"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "call-sequence corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "call-sequence corpus must require both transaction outcomes"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "call-sequence corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut counts : List Nat := []
  let mut seenTransitions : List String := []
  let mut seenLengths : List String := []
  let mut seenWindows : List String := []
  let mut rolled : List String := []
  let mut modes : List Nat := []
  let mut budgets : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut statusesSeen : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate call-sequence corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← CallSequence.replayCase saved fuel) == saved) ("call-sequence corpus entry did not replay: " ++ identifier)
    let scenario ← CallSequence.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "callSequencePlan") == (← entry.getObjVal? "callSequencePlan"))
        ("imported call-sequence entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("call-sequence corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel)) ("the expected history differs from the source model: " ++ identifier)
    let savedTransactions ← saved.getObjValAs? (List Json) "transactions"
    require (savedTransactions.map (·.getObjVal? "calls" |>.toOption) == expected.map (·.getObjVal? "calls" |>.toOption))
      ("a prescribed outcome differs from the expected history: " ++ identifier)
    let history := CallSequence.observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("call-sequence corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("call-sequence expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let accounts ← row.getObjValAs? (List Json) "committedAccounts"
      let some parent := accounts[0]? | throw "missing parent account"
      let some child := accounts[1]? | throw "missing child account"
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("calls", ← golden.getObjVal? "calls"),
        ("parent", toJson (← slotValues parent)), ("child", toJson (← slotValues child))]
      require (actual == golden) ("original Core differs from the source model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    counts := (counts ++ [scenario.plan.calls]).eraseDups
    let some rows := Solcore.Synthesis.Stateful.CallSequenceExecution.model scenario.plan fuel scenario.transactions
      | throw "the source model failed"
    for (transaction, row) in scenario.transactions.zip rows do
      modes := (modes ++ [transaction.input.val % 2]).eraseDups
      let callStates := row.calls.map stateOf
      seenTransitions := (seenTransitions ++ (callStates.zip callStates.tail).map fun (a, b) => a ++ ":" ++ b).eraseDups
      seenLengths := (seenLengths ++ row.calls.map fun call =>
        (if call.returned then "returned:" else "reverted:") ++ toString call.length).eraseDups
      seenWindows := (seenWindows ++ (row.calls.zip scenario.plan.windows).map
        fun ((call, window) : Solcore.Synthesis.Stateful.CallSequenceExecution.CallRow × Solcore.Synthesis.Core.CallSequence.Window) =>
          if window.offset + window.width > call.length then "outside" else if window.width == 0 then "empty" else "inside").eraseDups
      let reverted := row.calls.any (!·.returned)
      if row.reverted then
        if reverted then rolled := (rolled ++ ["child-reverted-parent-reverted"]).eraseDups
        if row.calls.any (·.returned) then rolled := (rolled ++ ["children-returned-parent-reverted"]).eraseDups
      else if reverted then rolled := (rolled ++ ["child-reverted-parent-returned"]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    statusesSeen := (statusesSeen ++ statuses).eraseDups
  require (requiredFeatures.all features.contains) "call-sequence corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "call-sequence corpus misses a boundary input"
  require ([2, 3].all counts.contains && transitions.all seenTransitions.contains && lengthNames.all seenLengths.contains)
    "call-sequence corpus misses a call count, a transition or a bank length"
  require (windowKinds.all seenWindows.contains && rollbacks.all rolled.contains && [0, 1].all modes.contains &&
      [384, 512].all budgets.contains)
    "call-sequence corpus misses a window, a rollback, a call mode or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "call-sequence corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "call-sequence corpus misses a generated template"
  require (["returned", "reverted"].all statusesSeen.contains) "call-sequence corpus misses an observed outcome"
  return Json.mkObj [("profile", toJson "stateful-call-sequences"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("calls", toJson counts), ("transitions", toJson seenTransitions.length),
    ("lengths", toJson seenLengths.length), ("windows", toJson seenWindows), ("rollbacks", toJson rolled),
    ("nodeBudgets", toJson budgets)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid call-sequence corpus unexpectedly passed")

def testSourceCallSequenceCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-call-sequence-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated call-sequence case")
  let firstStatus (entry : Json) : Option String :=
    (entry.getObjValAs? (Array Json) "expectedHistory").toOption.bind fun history =>
      history[0]?.bind fun row => (row.getObjValAs? String "status").toOption
  let some first := entries.find? (fun entry => (entry.getObjVal? "callSequencePlan").isOk &&
      firstStatus entry == some "returned") |
    throw (IO.userError "missing imported returned case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  -- A row's output, slots and prescribed calls, and a missing row, are all
  -- checked.
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let output ← checked (row.getObjValAs? String "output")
  let changedOutput := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 1)) ++
    (if output.endsWith "1" then "2" else "1")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let parent ← checked (row.getObjValAs? (Array String) "parent")
  let changedSlot := row.setObjVal! "parent" (toJson (parent.set! 5 (if parent[5]! == "7" then "8" else "7")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory"
    (.arr (history.set! 0 (row.setObjVal! "calls" (toJson ([] : List Json))))))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  if let some head := generatedHistory[0]? then
    let flipped := if (head.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
    rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
      (.arr (generatedHistory.set! 0 (head.setObjVal! "status" (toJson flipped)))))))
  -- The plan, the features, a duplicate entry and the requirements are checked.
  let plan ← checked (first.getObjVal? "callSequencePlan")
  rejects (validateManifest (replace first (first.setObjVal! "callSequencePlan" (plan.setObjVal! "calls" (toJson 9)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-call-returns"), ("functionVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredSequenceCalls", toJson [2]),
      ("requiredSequenceTransitions", toJson (["returned-data:returned-data"] : List String)),
      ("requiredSequenceLengths", toJson (["returned:0"] : List String)),
      ("requiredSequenceWindows", toJson (["inside"] : List String)),
      ("requiredSequenceRollbacks", toJson (["child-reverted-parent-returned"] : List String)),
      ("requiredSequenceNodeBudgets", toJson [384]),
      ("requiredHelperCounts", toJson [1, 2]), ("requiredTransactionCounts", toJson [1, 2]),
      ("requiredCallModes", toJson [0])] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceCallSequenceCorpus
end

section
-- leanmerge: from Solcore.Test.SourceCallSequenceGolden
/-! Golden rows of the parent's reads on a call's data for the call-sequence
profile. Every expected row is written out as hexadecimal text by the probe's
independent Python model of the return-data buffer, not by either Lean model:
the ramp data of each bank length, 0 to 96 bytes, with windows at the start, at
each Word boundary, at the last byte and past the end, of widths 0, 1, 31 and
32. A row is the data's size, its first Word when it has one, and the window's
bytes left-aligned in a zero Word when they lie inside the data, as
`returndatacopy` into a zeroed Word leaves them, otherwise zero. The byte-level
model gives each row exactly. Original Core's phases, run through the public
top-level runner on seven kept Words, the status Word and the data, give it
too: the last phase of two calls writes the size, first Word and window to its
call's slots and returns their sum, and the middle phase after call 1 writes
them, keeps the first Word and whether the data have a whole Word, and grows
`mix` by the first Word, the size and the window. Changed rows fail. -/
set_option autoImplicit false

namespace Tests.SourceCallSequenceGolden

open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallSequence (Window)
open Solcore.Synthesis.Stateful

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The name, the data, the window's offset and width, and the expected reads. -/
def rows : List (String × String × Nat × Nat × String) := [
  ("ramp-0-0-0", "0x", 0, 0, "size:0 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-0-0-32", "0x", 0, 32, "size:0 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-0-31-1", "0x", 31, 1, "size:0 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-0-33-31", "0x", 33, 31, "size:0 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-0-64-32", "0x", 64, 32, "size:0 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-0-95-1", "0x", 95, 1, "size:0 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-0-96-0", "0x", 96, 0, "size:0 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-1-0-0", "0x01", 0, 0, "size:1 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-1-0-32", "0x01", 0, 32, "size:1 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-1-31-1", "0x01", 31, 1, "size:1 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-1-33-31", "0x01", 33, 31, "size:1 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-1-64-32", "0x01", 64, 32, "size:1 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-1-95-1", "0x01", 95, 1, "size:1 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-1-96-0", "0x01", 96, 0, "size:1 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-31-0-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f", 0, 0, "size:31 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-31-0-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f", 0, 32, "size:31 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-31-31-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f", 31, 1, "size:31 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-31-33-31", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f", 33, 31, "size:31 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-31-64-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f", 64, 32, "size:31 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-31-95-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f", 95, 1, "size:31 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-31-96-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f", 96, 0, "size:31 first:0000000000000000000000000000000000000000000000000000000000000000 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-32-0-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20", 0, 0, "size:32 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-32-0-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20", 0, 32, "size:32 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"),
  ("ramp-32-31-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20", 31, 1, "size:32 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:2000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-32-33-31", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20", 33, 31, "size:32 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-32-64-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20", 64, 32, "size:32 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-32-95-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20", 95, 1, "size:32 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-32-96-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20", 96, 0, "size:32 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-33-0-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021", 0, 0, "size:33 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-33-0-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021", 0, 32, "size:33 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"),
  ("ramp-33-31-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021", 31, 1, "size:33 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:2000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-33-33-31", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021", 33, 31, "size:33 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-33-64-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021", 64, 32, "size:33 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-33-95-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021", 95, 1, "size:33 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-33-96-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021", 96, 0, "size:33 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-63-0-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f", 0, 0, "size:63 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-63-0-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f", 0, 32, "size:63 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"),
  ("ramp-63-31-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f", 31, 1, "size:63 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:2000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-63-33-31", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f", 33, 31, "size:63 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-63-64-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f", 64, 32, "size:63 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-63-95-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f", 95, 1, "size:63 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-63-96-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f", 96, 0, "size:63 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-64-0-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40", 0, 0, "size:64 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-64-0-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40", 0, 32, "size:64 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"),
  ("ramp-64-31-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40", 31, 1, "size:64 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:2000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-64-33-31", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40", 33, 31, "size:64 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:22232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f4000"),
  ("ramp-64-64-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40", 64, 32, "size:64 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-64-95-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40", 95, 1, "size:64 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-64-96-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40", 96, 0, "size:64 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-65-0-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f4041", 0, 0, "size:65 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-65-0-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f4041", 0, 32, "size:65 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"),
  ("ramp-65-31-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f4041", 31, 1, "size:65 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:2000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-65-33-31", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f4041", 33, 31, "size:65 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:22232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f4000"),
  ("ramp-65-64-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f4041", 64, 32, "size:65 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-65-95-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f4041", 95, 1, "size:65 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-65-96-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f4041", 96, 0, "size:65 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-95-0-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f", 0, 0, "size:95 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-95-0-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f", 0, 32, "size:95 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"),
  ("ramp-95-31-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f", 31, 1, "size:95 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:2000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-95-33-31", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f", 33, 31, "size:95 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:22232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f4000"),
  ("ramp-95-64-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f", 64, 32, "size:95 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-95-95-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f", 95, 1, "size:95 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-95-96-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f", 96, 0, "size:95 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-96-0-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60", 0, 0, "size:96 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-96-0-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60", 0, 32, "size:96 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"),
  ("ramp-96-31-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60", 31, 1, "size:96 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:2000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-96-33-31", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60", 33, 31, "size:96 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:22232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f4000"),
  ("ramp-96-64-32", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60", 64, 32, "size:96 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:4142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60"),
  ("ramp-96-95-1", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60", 95, 1, "size:96 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:6000000000000000000000000000000000000000000000000000000000000000"),
  ("ramp-96-96-0", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60", 96, 0, "size:96 first:0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 window:0000000000000000000000000000000000000000000000000000000000000000")
]

private def wordHex (value : Word) : String :=
  let digits := Nat.toDigits 16 value.val
  String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

private def readsText (size : Nat) (first copied : Word) : String :=
  "size:" ++ toString size ++ " first:" ++ wordHex first ++ " window:" ++ wordHex copied

private def parentAddress : Address := ⟨0x20, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩

private def wordAt (bytes : ByteArray) (index : Nat) : Word :=
  CallResumeExecution.wordAt bytes index

/-- Run one phase on the kept Words, the status Word and the data, returning
its outcome bytes and the parent's slots 0 to 17. -/
private def runPhase (contract : CheckedCoreContract) (kept : List Word) (status : Word) (data : ByteArray) :
    Except String (FrameOutcome Word × List Word) := do
  let world := WorldState.empty.putAccount parentAddress (Account.empty.withCode contract.code)
  let input := kept.foldl (fun bytes word => bytes ++ encodeWordBytesBE word) ByteArray.empty ++ encodeWordBytesBE status ++ data
  if bounded : input.size < Solcore.Core.wordModulus then
    let invocation : TopLevelInvocation := {
      target := parentAddress, caller := callerAddress, callValue := Word.zero, inputData := ⟨input, bounded⟩ }
    match CallResumeExecution.phase? contract world invocation 1000000 with
    | some (.completed result) =>
        let slots := (List.range 18).map fun slot =>
          ((result.finalWorld.account? parentAddress).map fun account => account.storageRead (w slot)).getD Word.zero
        return (result.outcome, slots)
    | _ => throw "the phase did not complete"
  else throw "the input exceeds a Word's size"

/-- The last phase of two calls on a returned call's data: its call's slots 7
to 11, checked against the flag, the kept preceding size and the returned sum. -/
private def lastText (window : Window) (data : ByteArray) : Except String String := do
  let program := CallSequence.lastProgram 2 window
  if checked : program.check = true then
    let contract := CheckedCoreContract.wordOutcomeV1
      ⟨program.toCore, Solcore.Core.Wire.Program.check_promotes_current checked⟩ rfl
    let kept := [Word.zero, Word.zero, Word.zero, w 5, w 7, Word.zero, Word.zero]
    let (outcome, slots) ← runPhase contract kept (w 1) data
    let get := fun slot => slots.getD slot Word.zero
    unless get 7 == w (1 + 2 * data.size) do throw "slot 7 is not the flag and twice the size"
    unless get 9 == w 7 && get 12 == Word.zero do throw "the preceding size or the re-read changed"
    let sum := [w 5, get 7, get 8, get 9, get 10, get 11].foldl (· + ·) Word.zero
    unless outcome == .returned (encodeWordBytesBE sum) do throw "the returned Word is not the sum"
    return readsText (get 10).val (get 8) (get 11)
  else throw "the last phase failed admission"

/-- The middle phase after call 1 on a reverted call's data: its slots 2 to 6
and its request, which keeps the first Word and whether the data have a whole
Word and grows `mix` by the reads. -/
private def middleText (window : Window) (data : ByteArray) : Except String String := do
  let program := CallSequence.middleProgram 1 window
  if checked : program.check = true then
    let contract := CallSequence.CheckedPlan.requestContract program checked rfl
    let input := w (2 ^ 33 + 3 * 256)
    let kept := [w 0x30, input, w 2, w 11, Word.zero, Word.zero, Word.zero]
    let (outcome, slots) ← runPhase contract kept Word.zero data
    let get := fun slot => slots.getD slot Word.zero
    unless get 2 == w (2 * data.size) && get 4 == Word.zero do throw "slot 2 or the preceding size differs"
    let .returned request := outcome | throw "the middle phase did not request a call"
    let mix := w 2 + get 3 + get 5 + get 6
    let expected := [w 0x30, w CallSequence.getSelector, mix * w 256 + w 3, w 0x30, input, mix,
      [w 11, get 2, get 3, get 4, get 5, get 6].foldl (· + ·) Word.zero, get 5, get 3,
      if data.size ≥ 32 then w 1 else Word.zero]
    unless (List.range 10).map (wordAt request) == expected do throw "the request differs from the reads"
    return readsText (get 5).val (get 3) (get 6)
  else throw "the middle phase failed admission"

def testSourceCallSequenceGolden : IO Unit := do
  ensure (rows.length == 70) "the golden rows changed"
  for (name, data, offset, width, expected) in rows do
    let some bytes := decodeBytesText? data | throw (IO.userError s!"{name}: invalid row data")
    let window : Window := ⟨offset, width⟩
    ensure (readsText bytes.size (CallSequenceExecution.firstWord bytes) (CallSequenceExecution.windowWord bytes window) ==
        expected) s!"{name}: the byte-level model differs from its golden reads"
    ensure ((← get (lastText window bytes)) == expected) s!"{name}: original Core's last phase differs from its golden reads"
    ensure ((← get (middleText window bytes)) == expected)
      s!"{name}: original Core's middle phase differs from its golden reads"
  -- A changed row fails: a window moved by one byte, and a size off by one.
  let (name, data, offset, width, expected) := rows.getD 43 ("", "", 0, 0, "")
  let some bytes := decodeBytesText? data | throw (IO.userError "invalid row data")
  ensure (readsText bytes.size (CallSequenceExecution.firstWord bytes)
      (CallSequenceExecution.windowWord bytes ⟨offset + 1, width⟩) != expected)
    s!"{name}: a moved window still matched"
  ensure ((← get (lastText ⟨offset, width⟩ (bytes.extract 0 (bytes.size - 1)))) != expected)
    s!"{name}: a shorter data still matched"

end Tests.SourceCallSequenceGolden
end

section
-- leanmerge: from Solcore.Test.SourceCallValueCases
/-! Call-value case regressions: exact replay, bounded generation from an
independent sequence stream, canonical transaction, value and plan boundaries,
the funding bounds and typed scenario reductions over steps, transactions,
inputs, values, flags and the deployment value. Expected values here are test
goldens only; emitted cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceCallValueCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.CallValue (CheckedPlan)
open Solcore.Synthesis.Stateful.CallValueExecution (Transaction Bindings)

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

private def makePlan (body : Wire.Expr) (deployment : Nat) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] entry |
    throw (IO.userError "call-value fixture failed step admission")
  let some plan := CheckedPlan.ofParts? graph (Word.ofNatModulo deployment) |
    throw (IO.userError "call-value wrapper failed host admission")
  return plan
private def transactions (values : List (Nat × Nat × Nat)) : List Transaction :=
  values.zipIdx.map fun ((flags, input, value), index) =>
    ⟨"call-" ++ toString index, Word.ofNatModulo flags, Word.ofNatModulo input, Word.ofNatModulo value⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × Nat × Nat)) : IO CallValue.CheckedScenario :=
  get (CallValue.checkedScenario plan (transactions values))
private def imported (value : CallValue.CheckedScenario) (fuel : Nat := 10000) : IO Json :=
  get (CallValue.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0) 5
  let value ← scenario identity [(0, 5, 2 ^ 64), (3, 1, 7), (2, 2 ^ 255, 0)]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson (["0", "1"] : List String)) "call-value case changed its observed slots"
  ensure ((← field saved "callValuePlan") == CallValue.planJson identity) "call-value case lost its deployment value"
  ensure ((← get (CallValue.replayCase saved 10000)) == saved) "imported call-value case did not replay"
  ensure ((← get (CallValue.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 10000)) == saved)
    "call-value replay consumed a stored expected result"
  let changed ← imported (← scenario (← makePlan (.var 0) 0) [(1, 3, 2 ^ 70)])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "flags, inputs, values or the deployment value were substituted into source or Core code"
  let observed := CallValue.observe value bindings 10000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "returned"])
    "call-value scenario did not follow its flags parities"
  ensure (((← rows observed).map fun row => (row.getObjValAs? String "committedBalance").toOption) ==
      #[some (toString (2 ^ 64 + 5)), some (toString (2 ^ 64 + 5)), some (toString (2 ^ 64 + 5))])
    "committed balances did not accept, refund and accept zero"
  ensure ((← get (CallValue.checkBalances value observed)) == ["returned", "reverted", "returned"])
    "the balance self-check rejected a correct history"
  let rebound ← rows (CallValue.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 10000)
  ensure (rebound.map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows observed).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      rebound.all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "address-independent call-value profile changed with bindings"
  let forged := observed.setObjVal! "transactions" (toJson ((← rows observed).set! 1
    ((← rows observed)[1]!.setObjVal! "committedBalance" (toJson (toString (2 ^ 64 + 12))))))
  rejected (CallValue.checkBalances value forged) "the balance self-check accepted a committed refund"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 12 do
    let choices := CallValue.sequenceChoices (Seed.ofNat seed)
    let bounds := [6, 6, 6, 6, 6, 6, 2, 4]
    ensure (choices.length == bounds.length && (choices.zip bounds).all fun (value, bound) => value < bound)
      "sequence choices escaped their banks"
    match CallValue.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 && Wire.programNodes value.program ≤ 384 &&
          value.plan.step.helpers.length == 1 + seed % 3 &&
          CallValue.deploymentBank.contains value.plan.deploymentValue)
          "call-value recipe lost node/transaction/helper/deployment bounds"
        ensure (value.transactions.all fun tx => CallValue.boundaryInputs.contains tx.input &&
          CallValue.valueBank.contains tx.value && tx.flags.val < 2) "generated input, value or flags escaped its bank"
        ensure ((value.transactions.map CallValue.reverts) == CallValue.generatedParities (Seed.ofNat seed))
          "generated flags lost their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (CallValue.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (CallValue.generatedScenario (Seed.ofNat 0) CallValue.programOverhead) "undersized node budget accepted"
  let corpus := CallValue.generateCases (Seed.ofNat 0) 384 4 512 10000
  ensure (corpus == CallValue.generateCases (Seed.ofNat 0) 384 4 512 10000) "call-value generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "call-value count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (CallValue.replayCase saved 10000)) == saved) "generated call-value provenance did not replay"
    let low ← get (CallValue.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := CallValue.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "call-value generation resource exhaustion was not distinguished"
  ensure ((← rows (CallValue.generateCases (Seed.ofNat seed) 384 2 1 10000) "cases").size == 1 &&
    (← natural (CallValue.generateCases (Seed.ofNat seed) 384 0 10 10000) "attempted") == 0 &&
    (← rows (CallValue.generateCases (Seed.ofNat seed) 384 1 0 10000) "cases").isEmpty)
    "call-value generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("flags", toJson "02"),
      ("flags", toJson (toString (2 ^ 256))), ("input", toJson "05"), ("input", toJson "7"),
      ("value", toJson "07"), ("value", toJson (toString (2 ^ 256))), ("calldata", toJson "0x"), ("extra", toJson true)] do
    rejected (CallValue.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical call-value transaction accepted"
  rejected (CallValue.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (CallValue.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  let plan ← makePlan (.var 0) 5
  rejected (CallValue.checkedScenario plan (transactions [(0, 0, 1), (0, 0, 1)] |>.map fun tx => {tx with id := "same"}))
    "duplicate transaction IDs accepted"
  rejected (CallValue.checkedScenario plan (transactions [(0, 0, 2 ^ 70 + 1)])) "a value above 2^70 accepted"
  rejected (CallValue.checkedScenario plan (transactions [(0, 0, 2 ^ 70), (0, 0, 2 ^ 70), (0, 0, 2 ^ 70), (0, 0, 2 ^ 70)]))
    "more than three transactions accepted"
  -- Four values of at most 2^70 reach the 2^72 total exactly; the bound is attainable.
  let atBound ← get (CallValue.checkedScenario (← makePlan (.var 0) (2 ^ 70))
    (transactions [(0, 0, 2 ^ 70), (0, 0, 2 ^ 70), (0, 0, 2 ^ 70)]))
  ensure (CallValue.totalValue atBound.plan.deploymentValue atBound.transactions == CallValue.maxTotal)
    "the funding total at the value bounds changed"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson (["0"] : List String)), ("executionFuel", toJson (10000001 : Nat)),
      ("callValuePlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (CallValue.caseProgram (saved.setObjVal! name bad)) "invalid call-value case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (CallValue.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 10000)
      "tampered call-value provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (CallValue.replayCase (withOrigin (origin.setObjVal! name bad)) 10000)
      "tampered generated call-value recipe accepted"
  let planJson ← field saved "callValuePlan"
  rejected (CallValue.checkedPlan (planJson.setObjVal! "extra" Json.null)) "noncanonical call-value plan accepted"
  rejected (CallValue.checkedPlan (planJson.setObjVal! "schema" (toJson "solcore-lean.log-plan.v1")))
    "log plan schema accepted as a call-value plan"
  for bad in [toJson "05", toJson (toString (2 ^ 70 + 1)), toJson (5 : Nat), Json.null] do
    rejected (CallValue.checkedPlan (planJson.setObjVal! "deploymentValue" bad)) "invalid deployment value accepted"
  rejected (CallValue.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (CallValue.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "name" (toJson "SynthesizedLogs"))) 10000)
    "log wrapper metadata accepted for the call-value profile"
  rejected (CallValue.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-log-case.v1")) 10000)
    "log case schema accepted by the call-value tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2)) 5
  let value ← scenario plan [(2 ^ 255 + 3, 2 ^ 256 - 1, 2 ^ 70), (6, 7, 2 ^ 64), (1, 2 ^ 255, 7)]
  let saved ← imported value
  let candidates ← get (CallValue.shrinkCases saved 1000 10000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (CallValue.shrinkCases saved 1000 10000)))
    "call-value reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredInput := false
  let mut loweredValue := false
  let mut reducedFlags := false
  let mut zeroDeployment := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (CallValue.caseProgram row)
    ensure (decide (CallValue.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "call-value reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("plan", CallValue.planJson reduced.plan),
      ("transactions", CallValue.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate call-value reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let sameCount := reduced.transactions.length == value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    loweredInput := loweredInput || (sameCount && pairs.any fun (left, right) => left.input.val < right.input.val)
    loweredValue := loweredValue || (sameCount && pairs.any fun (left, right) =>
      left.value.val < right.value.val && CallValue.valueBank.contains left.value)
    reducedFlags := reducedFlags || (sameCount && pairs.any fun (left, right) =>
      left.flags.val < right.flags.val && left.flags.bitAnd right.flags == left.flags)
    zeroDeployment := zeroDeployment || (reduced.plan.deploymentValue == Word.zero)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← get (CallValue.replayCase row 10000)) == row) "reduced call-value case did not replay"
  ensure (removed && loweredInput && loweredValue && reducedFlags && zeroDeployment && changedStep)
    "call-value shrink omitted sequence/input/value/flags/deployment/step axes"
  ensure ((← rows (← get (CallValue.shrinkCases saved 2 10000)) "cases") == result.extract 0 2 &&
    (← rows (← get (CallValue.shrinkCases saved 0 10000)) "cases").isEmpty) "call-value shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (CallValue.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", CallValue.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", CallValue.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (CallValue.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 10000)
    "non-strict call-value reduction provenance accepted"

def testSourceCallValueCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceCallValueCases
end

section
-- leanmerge: from Solcore.Test.SourceCallValueCorpus
/-! The fixed call-value corpus checks actual original Core histories against
independently computed expectations: status, payload, slots zero and one, and
the contract's committed balance after every transaction. Coverage describes
the checked step AST, the inputs and completions, the call values, the values
reverted transactions refund and the deployment values. Source/Rust/EVM
agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceCallValueCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers (left right : List String) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", CallValue.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.CallValue.version),
  ("templateVersion", CallValue.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", CallValue.emitterVersion), ("wrapperVersion", CallValue.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := CallValue.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← CallValue.checkedPlan (← entry.getObjVal? "callValuePlan")
  let scenario ← CallValue.checkedScenario plan (← CallValue.decodeTransactions (← entry.getObjVal? "transactions"))
  CallValue.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "call-value-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-call-value" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected call-value manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("call-value manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words CallValue.boundaryInputs))
    "call-value corpus must require all six boundary inputs"
  require (sameMembers (← strings manifest "requiredValues") (words CallValue.valueBank))
    "call-value corpus must require the whole value bank"
  require (sameMembers (← strings manifest "requiredDeploymentValues") (words CallValue.deploymentBank))
    "call-value corpus must require both deployment values"
  let requiredReverted ← strings manifest "requiredRevertedValues"
  require (requiredReverted.length ≥ 3 && requiredReverted.contains "0" && requiredReverted.any (· != "0"))
    "call-value corpus must require refunds of zero and of nonzero values"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "call-value corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "call-value corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "call-value corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "call-value corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "call-value corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut values : List String := []
  let mut reverted : List String := []
  let mut deployments : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate call-value corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← CallValue.replayCase saved fuel) == saved) ("call-value corpus entry did not replay: " ++ identifier)
    let scenario ← CallValue.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "callValuePlan") == (← entry.getObjVal? "callValuePlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported call-value entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("call-value corpus features changed: " ++ identifier)
    let history := CallValue.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    let statuses ← CallValue.checkBalances scenario history
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("call-value expected history length changed: " ++ identifier)
    for ((row, golden), tx) in (observed.zip expected).zip scenario.transactions do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage"),
        ("committedBalance", ← row.getObjVal? "committedBalance")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
      values := (values ++ [toString tx.value.val]).eraseDups
      if (← string row "status") == "reverted" then
        reverted := (reverted ++ [toString tx.value.val]).eraseDups
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.map fun tx => toString tx.input.val).eraseDups
    deployments := (deployments ++ [toString scenario.plan.deploymentValue.val]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "call-value corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "call-value corpus misses an input"
  require ((words CallValue.valueBank).all values.contains && requiredReverted.all reverted.contains &&
    (words CallValue.deploymentBank).all deployments.contains)
    "call-value corpus misses a value, a refunded value or a deployment value"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "call-value corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "call-value corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "call-value corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-call-value"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("refunded", toJson reverted), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid call-value corpus unexpectedly passed: " ++ message))

def testSourceCallValueCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-call-value-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first call-value case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated call-value case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let withRow := fun (index : Nat) (row : Json) =>
    replace first (first.setObjVal! "expectedHistory" (.arr (history.set! index row)))
  let row := history[0]!
  rejects (validateManifest (withRow 0 (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr (storage.set! 1 (storage[1]!.setObjVal! "value" (toJson "8")))))))
    "changed accepted value"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedBalance" (toJson "13")))) "changed balance"
  -- The first scenario's second transaction reverts: a committed refund is wrong.
  let refund := history[1]!
  rejects (validateManifest (withRow 1 (refund.setObjVal! "committedBalance"
    (toJson (toString (12 + 2 ^ 64)))))) "a reverted value committed"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let generatedStatus ← checked (generatedHistory[0]!.getObjValAs? String "status")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status"
      (toJson (if generatedStatus == "returned" then "reverted" else "returned")))))))) "flipped status"
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "value" (toJson "8"))))))) "changed value"
  let plan ← checked (first.getObjVal? "callValuePlan")
  rejects (validateManifest (replace first (first.setObjVal! "callValuePlan" (plan.setObjVal! "deploymentValue" (toJson "0")))))
    "changed deployment value"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String))))) "features"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))])))) "changed seed"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first)))) "duplicate entry"
  for (key, value) in [
      ("profile", toJson "stateful-logs"), ("wrapperVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredValues", toJson (["0", "1"] : List String)), ("requiredDeploymentValues", toJson (["0"] : List String)),
      ("requiredRevertedValues", toJson (["1"] : List String)),
      ("requiredRevertedValues", toJson (["0", "1", "5"] : List String)),
      ("requiredCompletionPatterns", toJson (["reverted,reverted,reverted"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "zero fuel"
  IO.println summary.compress

end Tests.SourceCallValueCorpus
end

section
-- leanmerge: from Solcore.Test.SourceCallValueEmitter
/-! Call-value protocol regressions through actual installed ContractRuntime
code. Golden histories are hand-computed: they cover a funded deployment, value
folded into the step input, the accepted-value slot, wrapping arithmetic,
values on both sides of the 64-bit boundary, refunds on revert and a transfer
the caller cannot fund. -/
set_option autoImplicit false

namespace Tests.SourceCallValueEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallValue (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (deployment : Nat) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "call-value step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofParts? step (Word.ofNatModulo deployment) |
    throw (IO.userError "call-value wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.CallValue.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"call-value source emission failed: {reprStr error}")

private def transactions (rows : List (Nat × Nat × Nat)) : List CallValueExecution.Transaction :=
  rows.zipIdx.map fun ((flags, input, value), index) =>
    ⟨"tx-" ++ toString index, Word.ofNatModulo flags, Word.ofNatModulo input, Word.ofNatModulo value⟩

private def slotRows (slot0 slot1 : Nat) : Json := toJson [
  Json.mkObj [("slot", toJson "0"), ("value", toJson (toString slot0))],
  Json.mkObj [("slot", toJson "1"), ("value", toJson (toString slot1))]]

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexWord (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  "0x" ++ String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

/-- One hand-computed row: status, payload, slots zero and one, and balance. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × Nat × Nat))
    (expected : List (String × Nat × (Nat × Nat) × Nat)) : IO Unit := do
  let history := CallValueExecution.observe plan (transactions rows) StorageExecution.fixtureBindings 10000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length &&
    (history.getObjValAs? String "initialBalance").toOption == some (toString plan.deploymentValue.val))
    "call-value golden history did not complete from its deployment value"
  for (row, (status, payload, (slot0, slot1), balance)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (hexWord payload) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows slot0 slot1) &&
      (row.getObjValAs? String "committedBalance").toOption == some (toString balance))
      s!"call-value golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x: the result is input + value + slot 0; a revert refunds.
  historyCheck (← checked [.var 0] 5) [(0, 2, 7), (1, 1, 3), (0, 0, 0)] [
    ("returned", 9, (9, 7), 12),
    ("reverted", 13, (9, 7), 12),
    ("returned", 9, (9, 7), 12)]
  -- step(x) = x + 1 wraps at the maximum; values cross the 64-bit boundary.
  historyCheck (← checked [increment] 0) [(0, maximum, 1), (2, 0, 2 ^ 64), (3, 5, 2 ^ 70)] [
    ("returned", 1, (1, 1), 1),
    ("returned", 2 ^ 64 + 2, (2 ^ 64 + 2, 2 ^ 64 + 1), 2 ^ 64 + 1),
    ("reverted", 2 ^ 70 + 2 ^ 64 + 8, (2 ^ 64 + 2, 2 ^ 64 + 1), 2 ^ 64 + 1)]

/-- The reverted call's working world holds the transferred value and both
writes; the public runtime commits the pre-transfer world. -/
private def refundChecks : IO Unit := do
  let plan ← checked [.var 0] 5
  let bindings := StorageExecution.fixtureBindings
  let world := CallValueExecution.initialWorldForContract plan.contract plan.deploymentValue bindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
    throw (IO.userError "call-value contract did not resolve")
  let invocation : TopLevelInvocation := {
    target := bindings.address, caller := bindings.caller, callValue := Word.ofNatModulo 7,
    inputData := CallValueExecution.inputData (Word.ofNatModulo 1) (Word.ofNatModulo 3) }
  match (BalancedTopLevelExecution.run contract invocation installed registry 10000).view with
  | .rejected _ => throw (IO.userError "a funded call value was rejected")
  | .execution execution =>
      match execution.view with
      | .outOfFuel _ _ _ => throw (IO.userError "call-value golden call exhausted fuel")
      | .completed terminal =>
          ensure (terminal.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo 10)))
            "odd flags did not revert with input + value + slot 0"
          let some working := terminal.terminalContext.context.values.working.1.account? bindings.address |
            throw (IO.userError "working account missing")
          ensure (working.balance == Word.ofNatModulo 12 && working.storageRead Word.zero == Word.ofNatModulo 10 &&
            working.storageRead (Word.ofNatModulo 1) == Word.ofNatModulo 7)
            "the working world lost the transferred value or a write"
          let some committed := terminal.finalWorld.account? bindings.address |
            throw (IO.userError "committed account missing")
          let some caller := terminal.finalWorld.account? bindings.caller |
            throw (IO.userError "committed caller missing")
          ensure (committed.balance == Word.ofNatModulo 5 && (committed.storageValue? Word.zero).isNone &&
            caller.balance == Word.ofNatModulo CallValueExecution.callerFunds)
            "the reverted value or writes were committed"
  -- A caller that cannot fund the value is rejected before any execution.
  let poor := (WorldState.empty.putAccount bindings.caller (Account.empty.withBalance (Word.ofNatModulo 6))).putAccount
    bindings.address ((Account.empty.withCode plan.contract.code).withBalance (Word.ofNatModulo 5))
  let some ⟨poorContract, poorInstalled⟩ := registry.resolve? poor bindings.address |
    throw (IO.userError "call-value contract did not resolve in the unfunded world")
  match (BalancedTopLevelExecution.run poorContract invocation poorInstalled registry 10000).view with
  | .rejected rejected => ensure (rejected.failure == .insufficientBalance) "unfunded value was not an insufficient balance"
  | .execution _ => throw (IO.userError "an unfunded call value executed")

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment] 0, ← checked [.var 0] 5] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "call-value plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (CallValue.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program == Wire.programNodes plan.step.program + CallValue.programOverhead)
      "call-value wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "call-value wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "call-value wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "call-value emission is nondeterministic"
  ensure (Wire.encodeProgram (← checked [increment] 0).program == Wire.encodeProgram (← checked [increment] 5).program)
    "the deployment value changed the original Core program"

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mstore, revert_, callvalue as sc_callvalue} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedCallValue {",
  "    constructor() payable {}",
  "    function run(flags: uint256, input: uint256) public payable returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_value: word = sc_callvalue();",
  "        let sc_old: word = sload(0);", "        let sc_total: word = sload(1);",
  "        let sc_result: word = sc_step(sc_input + sc_value + sc_old);",
  "        sstore(0, sc_result);", "        sstore(1, sc_total + sc_value);",
  "        if ((sc_flags & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment] 5)
  ensure (source.source == expectedBasic) "call-value protocol source changed"
  ensure (source.contractName == "SynthesizedCallValue" && source.methodSignature == "run(uint256,uint256)" &&
    source.deployPath == ["SynthesizedCallValueDeploy"] &&
    source.runtimePath == ["SynthesizedCallValueDeploy", "SynthesizedCallValue"])
    "call-value wrapper metadata changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)] 0)
  ensure ((divided.source.splitOn "import {sload, sstore, mstore, revert_, callvalue as sc_callvalue, div as sc_div, ").length == 2)
    "call-value emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.CallValue.emitterVersion == "solcore-source-call-value-v1" &&
    Solcore.Synthesis.Source.CallValue.wrapperVersion == "solcore-word-call-value-contract-v1" &&
    Solcore.Synthesis.Source.CallValue.selector == "0x7357f5d2" && CallValue.version == "core-call-value-contract-v1")
    "call-value provenance changed"

private def observerChecks : IO Unit := do
  ensure (CallValueExecution.calldata (Word.ofNatModulo 2) Word.maximum ==
    "0x7357f5d2" ++ String.ofList (List.replicate 63 '0') ++ "2" ++ String.ofList (List.replicate 64 'f'))
    "call-value calldata is not selector, flags and input Words"
  let plan ← checked [.var 0] 5
  let calls := transactions [(0, 2, 7), (1, 1, 1), (0, 0, 0)]
  let exhausted := CallValueExecution.observe plan calls StorageExecution.fixtureBindings 0
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] && rows.length == 1 &&
    (rows[0]!.getObjValAs? String "committedBalance").toOption == some "5" &&
    (exhausted.getObjVal? "finalBalance").toOption == (exhausted.getObjVal? "initialBalance").toOption)
    "call-value observer conflated fuel exhaustion with completion or committed its value"
  let complete := CallValueExecution.observe plan calls StorageExecution.fixtureBindings 10000
  ensure ((complete.getObjVal? "observedSlots").toOption == some (toJson (["0", "1"] : List String)) &&
    (complete.getObjValAs? String "deploymentValue").toOption == some "5" &&
    (complete.getObjVal? "initialLogs").toOption == some (toJson ([] : List Json)) &&
    (complete.getObjValAs? String "finalBalance").toOption == some "12")
    "history did not declare its slots, deployment value, deployment logs or final balance"

def testSourceCallValueEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  refundChecks
  formattingChecks
  observerChecks

end Tests.SourceCallValueEmitter
end

section
-- leanmerge: from Solcore.Test.SourceConstructorArgumentCases
/-! Generated constructor-argument cases. Original Core's deployment and
runtime must equal the Lean model, std's decision on the argument bytes and the
protocol, on the deployment and every transaction of the generated sequences,
under the selector and empty-revert rules; each case must replay to itself;
the contracts' node counts must be the ones the definitions fix; generation
must draw every parameter kind, static and dynamic enums, every malformation
kind that applies to each, every std outcome of each, every bank length and a
uniform partial-Word length, and no transaction after a rejected deployment;
and every reduction must be a strictly smaller sealed case that replays. -/
set_option autoImplicit false

namespace Tests.SourceConstructorArgumentCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ConstructorArguments (CheckedPlan Parameters)
open Solcore.Synthesis.Core.EnumArgument (Constructor Payload Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.ConstructorArgumentsExecution (Deployment Malformation Transaction)

private abbrev Cases := Solcore.Synthesis.Source.ConstructorArguments.CheckedScenario

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def slots (values : List Word) : Json :=
  toJson ((values.zipIdx).map fun (value, slot) => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString value.val))])

/-- Original Core's revert Word for std's revert data: the selector Word for
four bytes, the Word zero for none; a Word stays itself. -/
private def coreOutput (output : ByteArray) : String :=
  if output.size == 4 then
    encodeBytesText (encodeWordBytesBE (Word.ofNatModulo (StdCalldata.bigEndian output 0 4)))
  else if output.size == 0 then encodeBytesText (encodeWordBytesBE Word.zero)
  else encodeBytesText output

private def sameRow (row : Json) (model : ConstructorArgumentsExecution.ModelRow) : Bool :=
  (row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
    (row.getObjValAs? String "output").toOption == some (coreOutput model.output) &&
    (row.getObjVal? "committedStorage").toOption == some (slots model.slots)

/-- The Core rows of a scenario equal the model's, the deployment first, and
the model's deployment is std's prescribed outcome, which it returns. -/
private def sameAsModel (scenario : Cases) (fuel : Nat) (name : String) : IO String := do
  let history := Solcore.Synthesis.Source.ConstructorArguments.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let deployment ← get (history.getObjVal? "deployment")
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some (modelled, transactions) := ConstructorArgumentsExecution.model scenario.plan.step fuel
      scenario.plan.parameters scenario.deployment scenario.transactions
    | throw (IO.userError s!"{name}: the Lean model failed")
  ensure (sameRow deployment modelled) s!"{name}: the Core deployment differs from the Lean model: {deployment.compress}"
  ensure (rows.size == transactions.length) s!"{name}: a row is missing"
  for (row, model) in rows.toList.zip transactions do
    ensure (sameRow row model) s!"{name}: the Core row differs from the Lean model: {row.compress}"
  let prescribed := Solcore.Synthesis.Source.ConstructorArguments.prescribed scenario.plan.parameters scenario.deployment
  ensure (prescribed == (if modelled.reverted then some (encodeBytesText modelled.output) else none))
    s!"{name}: the prescribed std outcome differs from the model"
  return prescribed.getD "deployed"

/-- The parameter kinds, an enum by its class. -/
private def classOf : Parameters → String
  | .enum shape => if shape.dynamic then "dynamic" else "static"
  | parameters => parameters.name

private def payloads : List Payload := [.noWords, .oneWord, .twoWords, .pair, .bytes]

/-- Every field list of `count` constructors. -/
private def fieldLists : Nat → List (List Payload)
  | 0 => [[]]
  | count + 1 => (fieldLists count).flatMap fun rest => payloads.map (· :: rest)

private def shapeOf (constructors : List Constructor) : IO Shape := do
  let some shape := Solcore.Synthesis.Source.EnumArgument.Shape.ofList? constructors
    | throw (IO.userError "the shape has fewer than two constructors")
  return shape

def testSourceConstructorArgumentCases : IO Unit := do
  let fuel := 1000000
  -- The runtime's shell and every parameter kind's initializer, as the
  -- definitions fix them.
  ensure (ConstructorArguments.shellNodes == 69) "the runtime's shell is not 69 nodes"
  ensure ([Parameters.none, .word, .words, .bytes].map ConstructorArguments.initializerNodes == [76, 96, 101, 237])
    "an initializer without an enum changed size"
  let names := ["Idle", "Ready", "Pair", "Blob"]
  for (count, staticRange, dynamicRange) in [(2, (138, 188), (343, 509)), (3, (158, 233), (363, 560)),
      (4, (178, 278), (383, 611))] do
    let shapes := (fieldLists count).filterMap fun fields =>
      if (fields.filter (· == .bytes)).length ≤ 2 then
        Solcore.Synthesis.Source.EnumArgument.Shape.ofList? ((names.zip fields).map fun (name, payload) => ⟨name, payload⟩)
      else none
    for (dynamic, (low, high)) in [(false, staticRange), (true, dynamicRange)] do
      let sizes := (shapes.filter (·.dynamic == dynamic)).map (ConstructorArguments.initializerNodes ∘ .enum)
      ensure (sizes.foldl min 1000000 == low && sizes.foldl max 0 == high)
        s!"the initializers of {count} constructors (dynamic {dynamic}) take {sizes.foldl min 1000000} to {sizes.foldl max 0} nodes"
  ensure (Solcore.Synthesis.Source.ConstructorArguments.maxProgramNodes == 512 &&
      Solcore.Synthesis.Source.ConstructorArguments.maxInitializerNodes == 1024) "the case limits changed"
  -- The draws alone, over enough seeds to reach every malformation that
  -- applies to each parameter kind and every std outcome of each.
  let mut pairs : List String := []
  let mut outcomes : List String := []
  let mut lengths : List Nat := []
  for index in List.range 256 do
    let seed := Seed.ofNat (1 + index)
    let parameters := Solcore.Synthesis.Source.ConstructorArguments.generatedParameters seed
    let deployment := Solcore.Synthesis.Source.ConstructorArguments.generatedDeployment seed parameters
    ensure (Solcore.Synthesis.Source.ConstructorArguments.admitsRecord parameters deployment)
      s!"seed {1 + index}: the drawn record is not admitted"
    pairs := (pairs ++ [classOf parameters ++ ":" ++
      Solcore.Synthesis.Source.ConstructorArguments.kindOf deployment.malformation]).eraseDups
    outcomes := (outcomes ++ [classOf parameters ++ ":" ++
      ((Solcore.Synthesis.Source.ConstructorArguments.prescribed parameters deployment).getD "deployed")]).eraseDups
    if ConstructorArgumentsExecution.carriesBytes parameters deployment then
      lengths := (lengths ++ [deployment.length]).eraseDups
  let applicable := [("none", ["none", "trailing"]), ("uint256", ["none", "truncate", "trailing"]),
    ("uint256,uint256", ["none", "truncate", "trailing"]),
    ("uint256,bytes", ["none", "truncate", "trailing", "offset", "length"]),
    ("static", ["none", "truncate", "trailing", "tag", "tagCut", "narrow"]),
    ("dynamic", ["none", "truncate", "trailing", "offset", "length", "tag", "tagCut", "tail"])]
  let expectedPairs := applicable.flatMap fun (kind, kinds) => kinds.map (kind ++ ":" ++ ·)
  ensure (pairs.length == expectedPairs.length && expectedPairs.all pairs.contains)
    s!"the draws reached the malformations {pairs}"
  let expectedOutcomes := ["none:deployed"] ++ (["uint256", "uint256,uint256", "uint256,bytes"].flatMap fun kind =>
      [kind ++ ":deployed", kind ++ ":0x08638556"]) ++
    (["static", "dynamic"].flatMap fun kind => [kind ++ ":deployed", kind ++ ":0x08638556", kind ++ ":0x"])
  ensure (outcomes.length == expectedOutcomes.length && expectedOutcomes.all outcomes.contains)
    s!"the draws reached the outcomes {outcomes}"
  for length in Solcore.Synthesis.Source.ConstructorArguments.lengthBank do
    ensure (lengths.contains length) s!"the draws never chose length {length}"
  ensure (lengths.all (· ≤ 64) && lengths.any (fun length => length % 32 != 0 &&
      !Solcore.Synthesis.Source.ConstructorArguments.lengthBank.contains length))
    "the draws chose a length above 64 or no uniform partial-Word length"
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three.
  let mut classes : List String := []
  let mut generatedOutcomes : List String := []
  let mut cases : Array Json := #[]
  for (revision, transactions, count, nodes) in
      [(GeneratorRevision.v3, 8, 40, 384), (GeneratorRevision.v1, 3, 24, 384), (GeneratorRevision.v3, 4, 12, 512)] do
    let corpus := Solcore.Synthesis.Source.ConstructorArguments.generateCases (Seed.ofNat 1) nodes count 512 fuel
      revision transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} at {nodes} case {index}"
      ensure ((Solcore.Synthesis.Source.ConstructorArguments.replayCase json fuel).toOption == some json)
        s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.ConstructorArguments.caseProgram json)
      let outcome ← sameAsModel scenario fuel name
      ensure (scenario.transactions.length == if outcome == "deployed" then transactions else 0)
        s!"{name}: wrong sequence length"
      let source ← get (json.getObjValAs? String "source")
      ensure ((source.splitOn "    constructor(").length == 2 &&
          (source.splitOn "function run(flags: uint256, input: uint256) public returns (uint256) {").length == 2)
        s!"{name}: the emitted contract differs"
      ensure ((json.getObjVal? "initializerProgram").toOption ==
            some (Solcore.Core.Wire.encodeProgram scenario.plan.initializerProgram) &&
          ((← get (json.getObjVal? "contract")).getObjValAs? String "constructorCalldata").toOption ==
            some (ConstructorArgumentsExecution.arguments scenario.plan.parameters scenario.deployment))
        s!"{name}: the case does not carry its arguments"
      classes := (classes ++ [classOf scenario.plan.parameters]).eraseDups
      generatedOutcomes := (generatedOutcomes ++ [outcome]).eraseDups
      cases := cases.push json
  ensure (classes.length == 6) s!"generation drew the parameters {classes}"
  ensure (generatedOutcomes.length == 3) s!"generation reached the outcomes {generatedOutcomes}"
  -- Reductions: a dropped malformation, a shorter length and simpler
  -- parameters come with every case that has one, and every emitted candidate
  -- replays as a strictly smaller sealed case.
  for json in cases.toList.take 12 do
    let source ← get (Solcore.Synthesis.Source.ConstructorArguments.caseProgram json)
    let reduced := Solcore.Synthesis.Source.ConstructorArguments.reductions source
    ensure (!reduced.isEmpty) "a case has no reduction"
    ensure (source.deployment.malformation == .none || reduced.any (fun candidate =>
        candidate.candidate.deployment.malformation == .none))
      "no reduction drops the malformation"
    ensure (source.deployment.length == 0 || reduced.any (fun candidate =>
        candidate.candidate.deployment.length < source.deployment.length))
      "no reduction shortens the bytes"
    ensure (source.plan.parameters == .none || classOf source.plan.parameters == "dynamic" || reduced.any (fun candidate =>
        Solcore.Synthesis.Source.ConstructorArguments.parametersWeight candidate.candidate.plan.parameters <
          Solcore.Synthesis.Source.ConstructorArguments.parametersWeight source.plan.parameters))
      "no reduction simplifies the parameters"
    let shrunk ← get (Solcore.Synthesis.Source.ConstructorArguments.shrinkCases json 64 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.ConstructorArguments.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      let _ ← sameAsModel (← get (Solcore.Synthesis.Source.ConstructorArguments.caseProgram candidate)) fuel "reduction"
  -- Refusals: a record the parameters do not send, a malformation that does
  -- not apply, transactions after a rejected deployment, and metadata that
  -- differs from the argument bytes or std's decision.
  let some first := cases[0]? | throw (IO.userError "no case")
  let template ← get (Solcore.Synthesis.Source.ConstructorArguments.caseProgram first)
  let step := template.plan.step
  let caseOf (parameters : Parameters) (deployment : Deployment) (transactions : List Transaction) : IO Json := do
    let some plan := CheckedPlan.ofParts? step parameters | throw (IO.userError "the plan failed admission")
    let scenario ← get (Solcore.Synthesis.Source.ConstructorArguments.checkedScenario plan deployment transactions)
    get (Solcore.Synthesis.Source.ConstructorArguments.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel)
  let w := Word.ofNatModulo
  let record : Deployment := ⟨w 5, 0, w 7, w 9, 33, .none⟩
  let txs : List Transaction := [⟨"tx-0", w 0, w 1⟩]
  let bytesCase ← caseOf .bytes record txs
  let dynamic : Parameters := .enum (← shapeOf [⟨"Blob", .bytes⟩, ⟨"Idle", .noWords⟩])
  let static : Parameters := .enum (← shapeOf [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩])
  let refused (json : Json) : Bool := (Solcore.Synthesis.Source.ConstructorArguments.caseProgram json).toOption.isNone
  let withDeployment (json : Json) (parameters : Parameters) (deployment : Deployment) : Json :=
    json.setObjVal! "deployment" (Solcore.Synthesis.Source.ConstructorArguments.deploymentJson parameters deployment)
  ensure (!refused bytesCase && !refused (withDeployment bytesCase .bytes {record with length := 64}))
    "an admissible bytes case was refused"
  for (deployment, label) in [({record with length := 65}, "a length above 64"),
      ({record with choice := 1}, "a choice without an enum"),
      ({record with malformation := .offset (w 64)}, "the canonical offset as a malformation"),
      ({record with malformation := .length (w 33)}, "the canonical length as a malformation"),
      ({record with malformation := .narrow}, "a narrowed bytes value"),
      ({record with malformation := .tag (w 0)}, "a tag without an enum"),
      ({record with malformation := .tail (w 0)}, "a tail offset without an enum"),
      ({record with malformation := .truncate 160}, "a cut at the canonical size"),
      ({record with malformation := .trailing 65 0}, "65 trailing bytes")] do
    ensure (refused (withDeployment bytesCase .bytes deployment)) s!"{label} was admitted"
  let wordCase ← caseOf .word ⟨w 5, 0, Word.zero, Word.zero, 0, .none⟩ txs
  for (deployment, label) in [(⟨w 5, 0, w 1, Word.zero, 0, .none⟩, "a second Word for one Word"),
      (⟨w 5, 0, Word.zero, Word.zero, 1, .none⟩, "a length without bytes"),
      (⟨w 5, 0, Word.zero, Word.zero, 0, .offset (w 0)⟩, "an offset without one"),
      (⟨w 5, 0, Word.zero, Word.zero, 0, .length (w 0)⟩, "a length Word without bytes")] do
    ensure (refused (withDeployment wordCase .word deployment)) s!"{label} was admitted"
  let noneCase ← caseOf .none ⟨Word.zero, 0, Word.zero, Word.zero, 0, .trailing 3 1⟩ txs
  ensure (refused (withDeployment noneCase .none ⟨w 1, 0, Word.zero, Word.zero, 0, .none⟩))
    "a leading Word without parameters was admitted"
  ensure (refused (withDeployment noneCase .none ⟨Word.zero, 0, Word.zero, Word.zero, 0, .truncate 0⟩))
    "a cut of no arguments was admitted"
  let staticCase ← caseOf static ⟨w 1, 1, Word.zero, Word.zero, 0, .narrow⟩ txs
  for (deployment, label) in [(⟨w 1, 2, Word.zero, Word.zero, 0, .none⟩, "a choice beyond the constructors"),
      (⟨w 1, 1, w 3, Word.zero, 0, .none⟩, "a field Word for a constructor without one"),
      (⟨w 1, 0, w 3, w 4, 0, .narrow⟩, "a narrowed widest constructor"),
      (⟨w 1, 1, Word.zero, Word.zero, 0, .offset (w 0)⟩, "an offset into a static enum"),
      (⟨w 1, 1, Word.zero, Word.zero, 0, .tag (EnumArgument.tag ⟨"Pair", .twoWords⟩)⟩, "a known tag as unknown")] do
    ensure (refused (withDeployment staticCase static deployment)) s!"{label} was admitted"
  let dynamicCase ← caseOf dynamic ⟨w 1, 0, w 2, w 3, 17, .tail (w 32)⟩ txs
  for (deployment, label) in [(⟨w 1, 0, w 2, w 3, 17, .narrow⟩, "a narrowed dynamic enum"),
      (⟨w 1, 0, w 2, w 3, 17, .tail (w 64)⟩, "the canonical tail offset as a malformation"),
      (⟨w 1, 1, Word.zero, Word.zero, 0, .tail (w 0)⟩, "a tail offset without bytes")] do
    ensure (refused (withDeployment dynamicCase dynamic deployment)) s!"{label} was admitted"
  -- A rejected deployment keeps no transactions; at most eight follow an
  -- accepted one.
  let rejectedCase ← caseOf .bytes {record with malformation := .truncate 64} []
  ensure (refused (rejectedCase.setObjVal! "transactions"
      (Solcore.Synthesis.Source.ConstructorArguments.transactionsJson txs)))
    "a transaction after a rejected deployment was admitted"
  let nine := (List.range 9).map fun index => (⟨"tx-" ++ toString index, w 0, w index⟩ : Transaction)
  ensure (refused (bytesCase.setObjVal! "transactions" (Solcore.Synthesis.Source.ConstructorArguments.transactionsJson nine)))
    "nine transactions were admitted"
  let deployment ← get (bytesCase.getObjVal? "deployment")
  for (key, value, label) in [("arguments", toJson "0x00", "arguments that differ from their encoding"),
      ("stdRejection", toJson "0x08638556", "a std outcome that differs from std's decision"),
      ("length", toJson 32, "a length that differs from its arguments")] do
    ensure (refused (bytesCase.setObjVal! "deployment" (deployment.setObjVal! key value))) s!"{label} was admitted"
  ensure ((Solcore.Synthesis.Source.ConstructorArguments.replayCase (bytesCase.setObjVal! "contract"
      ((← get (bytesCase.getObjVal? "contract")).setObjVal! "constructorCalldata" (toJson "0x")))
      fuel).toOption.isNone) "a contract without its arguments was admitted"
  -- Plans: every parameter kind is admitted with the enum's constructors only
  -- for an enum; an unknown kind, constructors elsewhere, one constructor,
  -- three bytes constructors and an extra field are refused.
  let plan ← get (bytesCase.getObjVal? "constructorArgumentsPlan")
  let stepProgram ← get (plan.getObjVal? "stepProgram")
  let planOf (kind : String) (constructors : List (String × String)) : Json := Json.mkObj [
    ("schema", toJson Solcore.Synthesis.Source.ConstructorArguments.planSchema), ("parameters", toJson kind),
    ("constructors", toJson (constructors.map fun (name, fields) =>
      Json.mkObj [("name", toJson name), ("fields", toJson fields)])),
    ("stepProgram", stepProgram)]
  for (kind, constructors) in [("none", []), ("uint256", []), ("uint256,uint256", []), ("uint256,bytes", []),
      ("uint256,enum", [("Idle", ""), ("Ready", "ScPair")])] do
    ensure (Solcore.Synthesis.Source.ConstructorArguments.checkedPlan (planOf kind constructors)).toOption.isSome
      s!"a plan with {kind} was refused"
  for (kind, constructors, label) in [
      ("bytes", [], "an unknown kind"), ("uint256", [("Idle", ""), ("Ready", "")], "constructors without an enum"),
      ("uint256,enum", [], "an enum without constructors"), ("uint256,enum", [("Idle", "")], "one constructor"),
      ("uint256,enum", [("Idle", "bytes"), ("Ready", "bytes"), ("Pair", "bytes")], "three bytes constructors"),
      ("uint256,enum", [("Idle", ""), ("Other", "uint256")], "a name outside the bank")] do
    ensure (Solcore.Synthesis.Source.ConstructorArguments.checkedPlan (planOf kind constructors)).toOption.isNone
      s!"a plan with {label} was admitted"
  ensure (Solcore.Synthesis.Source.ConstructorArguments.checkedPlan (plan.setObjVal! "arity" (toJson 2))).toOption.isNone
    "a plan with an extra field was admitted"

end Tests.SourceConstructorArgumentCases
end

section
-- leanmerge: from Solcore.Test.SourceConstructorArgumentCorpus
/-! The fixed constructor-argument corpus checks actual original Core histories
against expectations computed without the Core contracts: std's decision on
the argument bytes, the constructor's writes and the source model, in which
each step runs alone in Core. Coverage describes the checked steps' AST, the
inputs, every parameter kind with static and dynamic enums apart, every
malformation kind, the three deployment outcomes, the malformations std
accepted, the bank's `bytes` lengths and every decoded enum field kind of
accepted deployments, the runtime carries after a committed transaction and
past a revert, the node budgets of generated entries and the completions.
Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceConstructorArgumentCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.ConstructorArguments (Parameters)
open Solcore.Synthesis.Core.EnumArgument (Payload)

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers {α : Type} [BEq α] (left right : List α) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", ConstructorArguments.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.ConstructorArguments.runtimeVersion),
  ("initializerVersion", Solcore.Synthesis.Core.ConstructorArguments.initializerVersion),
  ("templateVersion", ConstructorArguments.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", ConstructorArguments.emitterVersion), ("wrapperVersion", ConstructorArguments.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- The parameter kinds, an enum by its class. -/
def parameterClass : Parameters → String
  | .enum shape => if shape.dynamic then "dynamic" else "static"
  | parameters => parameters.name

def parameterClasses : List String := ["none", "uint256", "uint256,uint256", "uint256,bytes", "static", "dynamic"]

/-- std's three deployment outcomes. -/
def outcomes : List String := ["deployed", "0x08638556", "0x"]

/-- The malformations std can accept; an unknown tag never deploys. -/
def acceptedKinds : List String := ["truncate", "trailing", "offset", "length", "tail", "narrow"]

def fieldName : Payload → String
  | .noWords => "none"
  | .oneWord => "one"
  | .twoWords => "two"
  | .pair => "pair"
  | .bytes => "bytes"

/-- Static enums decode Word fields and the struct, dynamic ones any field. -/
def fieldKinds : List String :=
  ["static:none", "static:one", "static:two", "static:pair", "dynamic:none", "dynamic:one", "dynamic:two",
    "dynamic:pair", "dynamic:bytes"]

/-- Imported entries are emitted from their saved plan, deployment and
sequence; generated entries are regenerated from their seed. Both are checked
by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := ConstructorArguments.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← ConstructorArguments.checkedPlan (← entry.getObjVal? "constructorArgumentsPlan")
  let scenario ← ConstructorArguments.checkedScenario plan
    (← ConstructorArguments.decodeDeployment plan.parameters (← entry.getObjVal? "deployment"))
    (← ConstructorArguments.decodeTransactions (← entry.getObjVal? "transactions"))
  ConstructorArguments.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "constructor-argument-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

private def slotsJson (values : List Word) : Json :=
  toJson (values.zipIdx.map fun (value, slot) => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString value.val))])

/-- The source model's rows of a scenario, in the corpus's expected-row form:
the deployment's status, std's revert data or null, and slots zero to five,
then each transaction's row. -/
def modelRows (scenario : ConstructorArguments.CheckedScenario) (fuel : Nat) : Except String (Json × List Json) := do
  let some (deployment, rows) := Solcore.Synthesis.Stateful.ConstructorArgumentsExecution.model scenario.plan.step fuel
      scenario.plan.parameters scenario.deployment scenario.transactions | throw "the source model failed"
  return (Json.mkObj [
      ("status", toJson (if deployment.reverted then "reverted" else "returned")),
      ("revertData", if deployment.reverted then toJson (Solcore.ContractRuntime.encodeBytesText deployment.output)
        else Json.null),
      ("committedStorage", slotsJson deployment.slots)],
    (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
      ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
      ("output", toJson (Solcore.ContractRuntime.encodeBytesText row.output)),
      ("committedStorage", slotsJson row.slots)])

/-- Original Core's output for an expected deployment row: the Word zero on
return, and on a revert the selector Word for std's four bytes or the Word
zero for none. -/
private def coreDeploymentOutput (expected : Json) : Except String String := do
  let zero := Solcore.ContractRuntime.encodeBytesText (Solcore.ContractRuntime.encodeWordBytesBE Word.zero)
  match ← expected.getObjVal? "revertData" with
  | .null => return zero
  | data => do
      let text ← data.getStr?
      if text == "0x" then return zero
      require (text.length == 10) "unexpected std revert data"
      return "0x" ++ String.ofList (List.replicate 56 '0') ++ text.drop 2

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-constructor-arguments" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected constructor-argument manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("constructor-argument manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words ConstructorArguments.boundaryInputs))
    "constructor-argument corpus must require all six boundary inputs"
  require ((← strings manifest "requiredConstructorParameters") == parameterClasses &&
    (← strings manifest "requiredConstructorMalformations") == ConstructorArguments.malformationKinds &&
    (← strings manifest "requiredConstructorOutcomes") == outcomes &&
    (← strings manifest "requiredConstructorAccepted") == acceptedKinds)
    "constructor-argument corpus must require every parameter kind, malformation, outcome and accepted malformation"
  require ((← manifest.getObjValAs? (List Nat) "requiredConstructorBytesLengths") == ConstructorArguments.lengthBank &&
    (← strings manifest "requiredConstructorEnumFields") == fieldKinds &&
    (← manifest.getObjValAs? (List Nat) "requiredConstructorNodeBudgets") == [384, 512])
    "constructor-argument corpus must require the bank's bytes lengths, every enum field kind and both node budgets"
  require ((← strings manifest "requiredConstructorCarries") == ["committed", "rollback"])
    "constructor-argument corpus must require carries from a committed transaction and past a revert"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [0, 1, 2, 3])
    "constructor-argument corpus must require one to three helpers and zero to three transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "constructor-argument corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "constructor-argument corpus must require both transaction outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "constructor-argument corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "constructor-argument corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut classes : List String := []
  let mut kinds : List String := []
  let mut deploymentOutcomes : List String := []
  let mut accepted : List String := []
  let mut bytesLengths : List Nat := []
  let mut fields : List String := []
  let mut carries : List String := []
  let mut budgets : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut statusesSeen : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate constructor-argument corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← ConstructorArguments.replayCase saved fuel) == saved)
      ("constructor-argument corpus entry did not replay: " ++ identifier)
    let scenario ← ConstructorArguments.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "constructorArgumentsPlan") == (← entry.getObjVal? "constructorArgumentsPlan") &&
        (← saved.getObjVal? "deployment") == (← entry.getObjVal? "deployment") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported constructor-argument entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("constructor-argument corpus features changed: " ++ identifier)
    let expectedDeployment ← entry.getObjVal? "expectedDeployment"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require ((expectedDeployment, expected) == (← modelRows scenario fuel))
      ("the expected history differs from the source model: " ++ identifier)
    let history := ConstructorArguments.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("constructor-argument corpus history incomplete: " ++ identifier)
    let deployment ← history.getObjVal? "deployment"
    require ((← deployment.getObjVal? "status") == (← expectedDeployment.getObjVal? "status") &&
      (← string deployment "output") == (← coreDeploymentOutput expectedDeployment) &&
      (← deployment.getObjVal? "committedStorage") == (← expectedDeployment.getObjVal? "committedStorage"))
      ("original Core's deployment differs from std's decision: " ++ identifier ++ " " ++ deployment.compress)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length)
      ("constructor-argument expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the source model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    let parameters := scenario.plan.parameters
    let record := scenario.deployment
    let outcome := (ConstructorArguments.prescribed parameters record).getD "deployed"
    let kind := ConstructorArguments.kindOf record.malformation
    classes := (classes ++ [parameterClass parameters]).eraseDups
    kinds := (kinds ++ [kind]).eraseDups
    deploymentOutcomes := (deploymentOutcomes ++ [outcome]).eraseDups
    if outcome == "deployed" then
      if kind != "none" then accepted := (accepted ++ [kind]).eraseDups
      if Solcore.Synthesis.Stateful.ConstructorArgumentsExecution.carriesBytes parameters record then
        bytesLengths := (bytesLengths ++ [record.length]).eraseDups
      if let .enum shape := parameters then
        let chosen := Solcore.Synthesis.Stateful.ConstructorArgumentsExecution.chosen shape record
        fields := (fields ++ [parameterClass parameters ++ ":" ++ fieldName chosen.payload]).eraseDups
    for (status, index) in statuses.zipIdx do
      if status == "returned" && (statuses.take index).contains "returned" then
        carries := (carries ++ ["committed"]).eraseDups
      if status == "returned" && (statuses.take index).contains "reverted" then
        carries := (carries ++ ["rollback"]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    statusesSeen := (statusesSeen ++ statuses).eraseDups
    if !statuses.isEmpty then patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "constructor-argument corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "constructor-argument corpus misses a boundary input"
  require (parameterClasses.all classes.contains && ConstructorArguments.malformationKinds.all kinds.contains)
    "constructor-argument corpus misses a parameter kind or a malformation"
  require (outcomes.all deploymentOutcomes.contains && acceptedKinds.all accepted.contains)
    "constructor-argument corpus misses a deployment outcome or an accepted malformation"
  require (ConstructorArguments.lengthBank.all bytesLengths.contains && fieldKinds.all fields.contains)
    "constructor-argument corpus misses a deployed bytes length or enum field kind"
  require (["committed", "rollback"].all carries.contains && [384, 512].all budgets.contains)
    "constructor-argument corpus misses a carry or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [0, 1, 2, 3].all transactionCounts.contains)
    "constructor-argument corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "constructor-argument corpus misses a generated template"
  require (["returned", "reverted"].all statusesSeen.contains && requiredPatterns.all patterns.contains)
    "constructor-argument corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-constructor-arguments"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("parameters", toJson classes),
    ("malformations", toJson kinds), ("outcomes", toJson deploymentOutcomes), ("accepted", toJson accepted),
    ("bytesLengths", toJson bytesLengths), ("fields", toJson fields), ("carries", toJson carries),
    ("nodeBudgets", toJson budgets), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid constructor-argument corpus unexpectedly passed")

def testSourceConstructorArgumentCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-constructor-argument-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated constructor-argument case")
  -- An imported deployed `bytes` entry whose first transaction returns, and a
  -- rejected one.
  let some first := entries.find? (fun entry => (entry.getObjVal? "constructorArgumentsPlan").toOption.any (fun plan =>
      (plan.getObjValAs? String "parameters").toOption == some "uint256,bytes") &&
      (entry.getObjVal? "expectedDeployment").toOption.any (fun row =>
        (row.getObjValAs? String "status").toOption == some "returned") &&
      (entry.getObjValAs? (Array Json) "expectedHistory").toOption.any (fun history =>
        history[0]?.any (fun row => (row.getObjValAs? String "status").toOption == some "returned"))) |
    throw (IO.userError "missing imported deployed bytes case")
  let some rejected := entries.find? (fun entry => (entry.getObjVal? "constructorArgumentsPlan").isOk &&
      (entry.getObjVal? "expectedDeployment").toOption.any (fun row =>
        (row.getObjValAs? String "revertData").toOption == some "0x08638556")) |
    throw (IO.userError "missing rejected case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  -- A deployment's status, revert data and slots, a transaction's output, slot
  -- and status, and a missing row are all checked.
  let deployment ← checked (first.getObjVal? "expectedDeployment")
  rejects (validateManifest (replace first (first.setObjVal! "expectedDeployment"
    (deployment.setObjVal! "status" (toJson "reverted")))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedDeployment"
    (deployment.setObjVal! "revertData" (toJson "0x08638556")))))
  let storage ← checked (deployment.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (replace first (first.setObjVal! "expectedDeployment"
    (deployment.setObjVal! "committedStorage" (.arr (storage.set! 1 (storage[1]!.setObjVal! "value" (toJson "12345"))))))))
  let rejection ← checked (rejected.getObjVal? "expectedDeployment")
  rejects (validateManifest (replace rejected (rejected.setObjVal! "expectedDeployment"
    (rejection.setObjVal! "revertData" (toJson "0x")))))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let output ← checked (row.getObjValAs? String "output")
  let changedOutput := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 1)) ++
    (if output.endsWith "1" then "2" else "1")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let rowStorage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let slotTwo := (rowStorage[2]!.getObjValAs? String "value").toOption
  let changedSlot := row.setObjVal! "committedStorage" (.arr (rowStorage.set! 2
    (rowStorage[2]!.setObjVal! "value" (toJson (if slotTwo == some "7" then "8" else "7")))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  if let some head := generatedHistory[0]? then
    let flipped := if (head.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
    rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
      (.arr (generatedHistory.set! 0 (head.setObjVal! "status" (toJson flipped)))))))
  -- The record is checked against its arguments, and a rejected deployment
  -- against any transaction after it.
  let record ← checked (first.getObjVal? "deployment")
  rejects (validateManifest (replace first (first.setObjVal! "deployment" (record.setObjVal! "a" (toJson "12345")))))
  rejects (validateManifest (replace rejected (rejected.setObjVal! "transactions" (first.getObjValD "transactions"))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("initializerVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredConstructorParameters", toJson (["none"] : List String)),
      ("requiredConstructorMalformations", toJson (["none"] : List String)),
      ("requiredConstructorOutcomes", toJson (["deployed"] : List String)),
      ("requiredConstructorAccepted", toJson (["trailing"] : List String)),
      ("requiredConstructorBytesLengths", toJson [0, 1, 32]),
      ("requiredConstructorEnumFields", toJson (["static:none"] : List String)),
      ("requiredConstructorNodeBudgets", toJson [384]),
      ("requiredConstructorCarries", toJson (["committed"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]), ("requiredTransactionCounts", toJson [1, 2, 3]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceConstructorArgumentCorpus
end

section
-- leanmerge: from Solcore.Test.SourceConstructorArgumentGolden
/-! Golden cases for the constructor-argument profile: std's exact acceptance
and refusals of the constructor's argument bytes. Every expected row is written
out as hexadecimal text computed outside Lean from the definitions and the
feasibility probe's reading of std's memory reader, not by either model, with
tags from `cast keccak`. The steps add a known constant `c`. A deployment
writes the marker 1 or the leading Word, then the second Word, a `bytes`
value's length and chunks, or an enum's one-based index and decoded Words, to
slots 1 to 5; each runtime transaction computes `r = slot 0 + input + slot 1 +
... + slot 5 + c`, writes `r` to slot 0 and returns it, and odd flags revert
with `r` and keep the prior slots. A rejected deployment is std's revert data,
an error selector or nothing for an unknown tag, and installs nothing. The
scenarios cover every parameter kind, static, dynamic and struct enums,
`bytes` lengths 0, 1, 17, 31, 32, 33 and 64, every malformation kind with
accepted and rejected entries, and the order of the checks. Original Core
gives each row under the selector and empty-revert rules, and the Lean model
gives it exactly. -/
set_option autoImplicit false

namespace Tests.SourceConstructorArgumentGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ConstructorArguments (CheckedPlan Parameters)
open Solcore.Synthesis.Core.EnumArgument (Constructor)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.ConstructorArgumentsExecution (Deployment Malformation Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
private def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- The expected row: the argument bytes as hexadecimal text, the deployment's
status, std's revert data, empty for an unknown tag, and slots zero to five,
then each runtime transaction's status, Word and slots. -/
private structure Expected where
  arguments : String
  status : String
  output : String
  values : List Nat
  transactions : List (String × Nat × List Nat)

private def slots (values : List Nat) : Json :=
  toJson ((List.range ConstructorArguments.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def dep (a choice first second length : Nat) (malformation : Malformation) : Deployment :=
  ⟨w a, choice, w first, w second, length, malformation⟩

/-- Two runtime transactions after an accepted deployment: one that returns and
one with odd flags. -/
private def runtimeTransactions : List Transaction := [⟨"tx-0", w 0, w 3⟩, ⟨"tx-1", w 1, w 5⟩]

-- The tags `keccak256("Name(fields)")`, as `cast keccak` writes them.
-- Blob(bytes): d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e45164
-- Idle(): ae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f
-- Pair(uint256,uint256): 2d3b57dedfada8371bdae932a6881ace0dec34c90dd19fd49b2164124e699e2d
-- Q(uint256): 5dcad53f88dc9d20c351c1bb58593dde38a673b5308c8751aaeb91edd8c97952
-- Ready(uint256): 0b217ad5c70346c7cd952bd2463c6684a56f9ed229f5780947586625781b4770
-- Ready(uint256,uint256): 1ee0fddb687f7d726adbdd32a0b3afe38d0593fe9dc00a18a5f4acd116e8b7c9
-- Rejected(): efde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e3
-- Settled(uint256,uint256): f5b268a3ff315cc44ccceeef86259c9e8eef81ceecb14001543809115380dd62

private def noneRows : List (Deployment × Expected) := [
  (dep 0 0 0 0 0 .none,
    ⟨"",
      "returned", "", [0, 1, 0, 0, 0, 0],
      [("returned", 5, [5, 1, 0, 0, 0, 0]),
       ("reverted", 12, [5, 1, 0, 0, 0, 0])]⟩),
  (dep 0 0 0 0 0 (.trailing 33 2),
    ⟨"0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021",
      "returned", "", [0, 1, 0, 0, 0, 0],
      [("returned", 5, [5, 1, 0, 0, 0, 0]),
       ("reverted", 12, [5, 1, 0, 0, 0, 0])]⟩),
  (dep 0 0 0 0 0 (.trailing 1 0),
    ⟨"00",
      "returned", "", [0, 1, 0, 0, 0, 0],
      [("returned", 5, [5, 1, 0, 0, 0, 0]),
       ("reverted", 12, [5, 1, 0, 0, 0, 0])]⟩)]

private def wordRows : List (Deployment × Expected) := [
  (dep 5 0 0 0 0 .none,
    ⟨"0000000000000000000000000000000000000000000000000000000000000005",
      "returned", "", [0, 5, 0, 0, 0, 0],
      [("returned", 10, [10, 5, 0, 0, 0, 0]),
       ("reverted", 22, [10, 5, 0, 0, 0, 0])]⟩),
  (dep (2 ^ 256 - 1) 0 0 0 0 .none,
    ⟨"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
      "returned", "", [0, (2 ^ 256 - 1), 0, 0, 0, 0],
      [("returned", 4, [4, (2 ^ 256 - 1), 0, 0, 0, 0]),
       ("reverted", 10, [4, (2 ^ 256 - 1), 0, 0, 0, 0])]⟩),
  (dep 7 0 0 0 0 (.truncate 31),
    ⟨"00000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 7 0 0 0 0 (.truncate 0),
    ⟨"",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 9 0 0 0 0 (.trailing 32 1),
    ⟨"0000000000000000000000000000000000000000000000000000000000000009ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
      "returned", "", [0, 9, 0, 0, 0, 0],
      [("returned", 14, [14, 9, 0, 0, 0, 0]),
       ("reverted", 30, [14, 9, 0, 0, 0, 0])]⟩)]

private def wordsRows : List (Deployment × Expected) := [
  (dep 7 0 9 0 0 .none,
    ⟨"00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000009",
      "returned", "", [0, 7, 9, 0, 0, 0],
      [("returned", 22, [22, 7, 9, 0, 0, 0]),
       ("reverted", 46, [22, 7, 9, 0, 0, 0])]⟩),
  (dep 1 0 (2 ^ 256 - 1) 0 0 (.truncate 63),
    ⟨"0000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 4 0 6 0 0 (.truncate 32),
    ⟨"0000000000000000000000000000000000000000000000000000000000000004",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 2 0 3 0 0 (.trailing 31 2),
    ⟨"000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000030102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "returned", "", [0, 2, 3, 0, 0, 0],
      [("returned", 11, [11, 2, 3, 0, 0, 0]),
       ("reverted", 24, [11, 2, 3, 0, 0, 0])]⟩)]

private def bytesRows : List (Deployment × Expected) := [
  (dep 1 0 0 0 0 .none,
    ⟨"000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 1, 0, 0, 0, 0],
      [("returned", 8, [8, 1, 0, 0, 0, 0]),
       ("reverted", 18, [8, 1, 0, 0, 0, 0])]⟩),
  (dep 2 0 1 2 1 .none,
    ⟨"0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000019e00000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 2, 1, 0x9e00000000000000000000000000000000000000000000000000000000000000, 0, 0],
      [("returned", 0x9e0000000000000000000000000000000000000000000000000000000000000a, [0x9e0000000000000000000000000000000000000000000000000000000000000a, 2, 1, 0x9e00000000000000000000000000000000000000000000000000000000000000, 0, 0]),
       ("reverted", 0x3c00000000000000000000000000000000000000000000000000000000000016, [0x9e0000000000000000000000000000000000000000000000000000000000000a, 2, 1, 0x9e00000000000000000000000000000000000000000000000000000000000000, 0, 0])]⟩),
  (dep 3 0 2 3 31 .none,
    ⟨"00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001f3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d00",
      "returned", "", [0, 3, 31, 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d00, 0, 0],
      [("returned", 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d29, [0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d29, 3, 31, 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d00, 0, 0]),
       ("reverted", 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54, [0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d29, 3, 31, 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d00, 0, 0])]⟩),
  (dep 4 0 3 4 32 .none,
    ⟨"000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000020daa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf",
      "returned", "", [0, 4, 32, 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf, 0, 0],
      [("returned", 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abea, [0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abea, 4, 32, 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf, 0, 0]),
       ("reverted", 0xb54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae48957d6, [0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abea, 4, 32, 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf, 0, 0])]⟩),
  (dep 5 0 4 5 33 .none,
    ⟨"00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002178dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a541700000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 5, 33, 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54, 0x1700000000000000000000000000000000000000000000000000000000000000, 0],
      [("returned", 0x8fdde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a81, [0x8fdde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a81, 5, 33, 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54, 0x1700000000000000000000000000000000000000000000000000000000000000, 0]),
       ("reverted", 0x1fbbcdcbfa53e0af9ce60302e76e41a084113b5f9d13928fc363508e860c7504, [0x8fdde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a81, 5, 33, 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54, 0x1700000000000000000000000000000000000000000000000000000000000000, 0])]⟩),
  (dep 6 0 5 6 64 .none,
    ⟨"0000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000401715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e9b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577e",
      "returned", "", [0, 6, 64, 0x1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e9, 0xb54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577e, 0],
      [("returned", 0xcc623af8783354f177bc4423fe379a3cb597b1a377fae985aca88ec3f85120b4, [0xcc623af8783354f177bc4423fe379a3cb597b1a377fae985aca88ec3f85120b4, 6, 64, 0x1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e9, 0xb54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577e, 0]),
       ("reverted", 0x98c475f0f066a9e2ef788847fc6f34796b2f6346eff5d30b59511d87f0a2416a, [0xcc623af8783354f177bc4423fe379a3cb597b1a377fae985aca88ec3f85120b4, 6, 64, 0x1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e9, 0xb54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577e, 0])]⟩),
  (dep 1 0 6 7 33 (.offset (w 0)),
    ⟨"000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577e5300000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 1, 1, 0, 0, 0],
      [("returned", 9, [9, 1, 1, 0, 0, 0]),
       ("reverted", 20, [9, 1, 1, 0, 0, 0])]⟩),
  (dep 7 0 7 8 33 (.offset (w 32)),
    ⟨"000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000021538454127b096499a94942a28a80796c738f13f3a971203dcaf6e67cb54ae613f100000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 7, 32, 33, 0, 0],
      [("returned", 79, [79, 7, 32, 33, 0, 0]),
       ("reverted", 160, [79, 7, 32, 33, 0, 0])]⟩),
  (dep 8 0 8 9 33 (.offset (w 129)),
    ⟨"000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000810000000000000000000000000000000000000000000000000000000000000021f1bbcdcbfa53e0af9ce60302e76e41a084113b5f9d13928fc363508e860c74a88f00000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 9 0 9 1 33 (.offset (w 160)),
    ⟨"000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000218ff34785799e5cc59082c363445c09d4949362cb90b604e1bbcfbaa056ce033d9e00000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 1 0 1 1 1 (.offset (w (2 ^ 255))),
    ⟨"0000000000000000000000000000000000000000000000000000000000000001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000019e00000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 2 0 2 2 17 (.offset (w 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0)),
    ⟨"0000000000000000000000000000000000000000000000000000000000000002ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000000000000000000113c6ef372fe94f82be73980c0b9db906821000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 3 0 3 3 17 (.length (w 18)),
    ⟨"000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000012daa66d2c7ddf7441dad6412116c9589c31000000000000000000000000000000",
      "returned", "", [0, 3, 18, 0xdaa66d2c7ddf7441dad6412116c9589c31000000000000000000000000000000, 0, 0],
      [("returned", 0xdaa66d2c7ddf7441dad6412116c9589c3100000000000000000000000000001c, [0xdaa66d2c7ddf7441dad6412116c9589c3100000000000000000000000000001c, 3, 18, 0xdaa66d2c7ddf7441dad6412116c9589c31000000000000000000000000000000, 0, 0]),
       ("reverted", 0xb54cda58fbbee883b5ac82422d92b1386200000000000000000000000000003a, [0xdaa66d2c7ddf7441dad6412116c9589c3100000000000000000000000000001c, 3, 18, 0xdaa66d2c7ddf7441dad6412116c9589c31000000000000000000000000000000, 0, 0])]⟩),
  (dep 4 0 4 4 17 (.length (w 16)),
    ⟨"00000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001078dde6e5fd29f057ce73018173b720d042000000000000000000000000000000",
      "returned", "", [0, 4, 16, 0x78dde6e5fd29f057ce73018173b720d000000000000000000000000000000000, 0, 0],
      [("returned", 0x78dde6e5fd29f057ce73018173b720d00000000000000000000000000000001b, [0x78dde6e5fd29f057ce73018173b720d00000000000000000000000000000001b, 4, 16, 0x78dde6e5fd29f057ce73018173b720d000000000000000000000000000000000, 0, 0]),
       ("reverted", 0xf1bbcdcbfa53e0af9ce60302e76e41a000000000000000000000000000000038, [0x78dde6e5fd29f057ce73018173b720d00000000000000000000000000000001b, 4, 16, 0x78dde6e5fd29f057ce73018173b720d000000000000000000000000000000000, 0, 0])]⟩),
  (dep 5 0 5 5 17 (.length (w 32)),
    ⟨"0000000000000000000000000000000000000000000000000000000000000005000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000201715609f7c746c6dc20fc1e1d0a4e90452000000000000000000000000000000",
      "returned", "", [0, 5, 32, 0x1715609f7c746c6dc20fc1e1d0a4e90452000000000000000000000000000000, 0, 0],
      [("returned", 0x1715609f7c746c6dc20fc1e1d0a4e9045200000000000000000000000000002c, [0x1715609f7c746c6dc20fc1e1d0a4e9045200000000000000000000000000002c, 5, 32, 0x1715609f7c746c6dc20fc1e1d0a4e90452000000000000000000000000000000, 0, 0]),
       ("reverted", 0x2e2ac13ef8e8d8db841f83c3a149d208a400000000000000000000000000005a, [0x1715609f7c746c6dc20fc1e1d0a4e9045200000000000000000000000000002c, 5, 32, 0x1715609f7c746c6dc20fc1e1d0a4e90452000000000000000000000000000000, 0, 0])]⟩),
  (dep 6 0 6 6 17 (.length (w 33)),
    ⟨"000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000021b54cda58fbbee883b5ac82422d92b13863000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 7 0 7 7 17 (.length (w (2 ^ 256 - 1))),
    ⟨"00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000040ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff538454127b096499a94942a28a80796c73000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 8 0 8 8 33 (.truncate 64),
    ⟨"00000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000040",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 9 0 9 9 33 (.truncate 128),
    ⟨"0000000000000000000000000000000000000000000000000000000000000009000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000218ff34785799e5cc59082c363445c09d4949362cb90b604e1bbcfbaa056ce033d",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 1 0 2 3 33 (.truncate 159),
    ⟨"0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000213c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2ada000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 1, 33, 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a, 0xda00000000000000000000000000000000000000000000000000000000000000, 0],
      [("returned", 0x166ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d53, [0x166ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d53, 1, 33, 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a, 0xda00000000000000000000000000000000000000000000000000000000000000, 0]),
       ("reverted", 0x2cdde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063aa8, [0x166ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d53, 1, 33, 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a, 0xda00000000000000000000000000000000000000000000000000000000000000, 0])]⟩),
  (dep 2 0 3 4 33 (.truncate 95),
    ⟨"0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 3 0 4 5 1 (.trailing 33 1),
    ⟨"0000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000017800000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
      "returned", "", [0, 3, 1, 0x7800000000000000000000000000000000000000000000000000000000000000, 0, 0],
      [("returned", 0x780000000000000000000000000000000000000000000000000000000000000b, [0x780000000000000000000000000000000000000000000000000000000000000b, 3, 1, 0x7800000000000000000000000000000000000000000000000000000000000000, 0, 0]),
       ("reverted", 0xf000000000000000000000000000000000000000000000000000000000000018, [0x780000000000000000000000000000000000000000000000000000000000000b, 3, 1, 0x7800000000000000000000000000000000000000000000000000000000000000, 0, 0])]⟩)]

private def staticRows : List (Deployment × Expected) := [
  (dep 1 0 7 9 0 .none,
    ⟨"00000000000000000000000000000000000000000000000000000000000000012d3b57dedfada8371bdae932a6881ace0dec34c90dd19fd49b2164124e699e2d00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000009",
      "returned", "", [0, 1, 1, 7, 9, 0],
      [("returned", 26, [26, 1, 1, 7, 9, 0]),
       ("reverted", 54, [26, 1, 1, 7, 9, 0])]⟩),
  (dep 2 1 0 0 0 .none,
    ⟨"0000000000000000000000000000000000000000000000000000000000000002ae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 2, 2, 0, 0, 0],
      [("returned", 12, [12, 2, 2, 0, 0, 0]),
       ("reverted", 26, [12, 2, 2, 0, 0, 0])]⟩),
  (dep 3 2 11 0 0 .none,
    ⟨"00000000000000000000000000000000000000000000000000000000000000035dcad53f88dc9d20c351c1bb58593dde38a673b5308c8751aaeb91edd8c97952000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 3, 3, 11, 0, 0],
      [("returned", 25, [25, 3, 3, 11, 0, 0]),
       ("reverted", 52, [25, 3, 3, 11, 0, 0])]⟩),
  (dep 4 1 0 0 0 .narrow,
    ⟨"0000000000000000000000000000000000000000000000000000000000000004ae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f",
      "returned", "", [0, 4, 2, 0, 0, 0],
      [("returned", 14, [14, 4, 2, 0, 0, 0]),
       ("reverted", 30, [14, 4, 2, 0, 0, 0])]⟩),
  (dep 5 2 12 0 0 .narrow,
    ⟨"00000000000000000000000000000000000000000000000000000000000000055dcad53f88dc9d20c351c1bb58593dde38a673b5308c8751aaeb91edd8c97952000000000000000000000000000000000000000000000000000000000000000c",
      "returned", "", [0, 5, 3, 12, 0, 0],
      [("returned", 28, [28, 5, 3, 12, 0, 0]),
       ("reverted", 58, [28, 5, 3, 12, 0, 0])]⟩),
  (dep 6 0 1 2 0 (.tag (w 0)),
    ⟨"0000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002",
      "reverted", "", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 7 1 0 0 0 (.tagCut (w 0xae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d50)),
    ⟨"0000000000000000000000000000000000000000000000000000000000000007ae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d50",
      "reverted", "", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 8 0 3 4 0 (.truncate 64),
    ⟨"00000000000000000000000000000000000000000000000000000000000000082d3b57dedfada8371bdae932a6881ace0dec34c90dd19fd49b2164124e699e2d",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 9 0 3 4 0 (.truncate 95),
    ⟨"00000000000000000000000000000000000000000000000000000000000000092d3b57dedfada8371bdae932a6881ace0dec34c90dd19fd49b2164124e699e2d00000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 1 2 5 0 0 (.truncate 32),
    ⟨"0000000000000000000000000000000000000000000000000000000000000001",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 2 2 6 0 0 (.truncate 96),
    ⟨"00000000000000000000000000000000000000000000000000000000000000025dcad53f88dc9d20c351c1bb58593dde38a673b5308c8751aaeb91edd8c979520000000000000000000000000000000000000000000000000000000000000006",
      "returned", "", [0, 2, 3, 6, 0, 0],
      [("returned", 19, [19, 2, 3, 6, 0, 0]),
       ("reverted", 40, [19, 2, 3, 6, 0, 0])]⟩),
  (dep 3 1 0 0 0 (.trailing 1 2),
    ⟨"0000000000000000000000000000000000000000000000000000000000000003ae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
      "returned", "", [0, 3, 2, 0, 0, 0],
      [("returned", 13, [13, 3, 2, 0, 0, 0]),
       ("reverted", 28, [13, 3, 2, 0, 0, 0])]⟩)]

private def dynamicRows : List (Deployment × Expected) := [
  (dep 1 0 1 2 33 .none,
    ⟨"00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000040d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e451640000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000219e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e953c00000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 1, 1, 33, 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95, 0x3c00000000000000000000000000000000000000000000000000000000000000],
      [("returned", 0xda3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ec1, [0xda3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ec1, 1, 1, 33, 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95, 0x3c00000000000000000000000000000000000000000000000000000000000000]),
       ("reverted", 0xb46ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d84, [0xda3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ec1, 1, 1, 33, 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95, 0x3c00000000000000000000000000000000000000000000000000000000000000])]⟩),
  (dep 2 1 5 0 0 .none,
    ⟨"000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000400b217ad5c70346c7cd952bd2463c6684a56f9ed229f5780947586625781b477000000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 2, 2, 5, 0, 0],
      [("returned", 18, [18, 2, 2, 5, 0, 0]),
       ("reverted", 38, [18, 2, 2, 5, 0, 0])]⟩),
  (dep 3 2 3 7 0 .none,
    ⟨"00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000040f5b268a3ff315cc44ccceeef86259c9e8eef81ceecb14001543809115380dd6200000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000007",
      "returned", "", [0, 3, 3, 3, 7, 0],
      [("returned", 25, [25, 3, 3, 3, 7, 0]),
       ("reverted", 52, [25, 3, 3, 3, 7, 0])]⟩),
  (dep 4 3 0 0 0 .none,
    ⟨"00000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000040efde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 4, 4, 0, 0, 0],
      [("returned", 17, [17, 4, 4, 0, 0, 0]),
       ("reverted", 36, [17, 4, 4, 0, 0, 0])]⟩),
  (dep 5 0 3 4 0 .none,
    ⟨"00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000040d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e45164000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 5, 1, 0, 0, 0],
      [("returned", 15, [15, 5, 1, 0, 0, 0]),
       ("reverted", 32, [15, 5, 1, 0, 0, 0])]⟩),
  (dep 6 1 8 0 0 (.offset (w 0)),
    ⟨"000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000000b217ad5c70346c7cd952bd2463c6684a56f9ed229f5780947586625781b477000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000",
      "reverted", "", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 0xefde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e3 3 0 0 0 (.offset (w 0)),
    ⟨"efde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e30000000000000000000000000000000000000000000000000000000000000000efde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 0xefde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e3, 4, 0, 0, 0],
      [("returned", 0xefde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1f0, [0xefde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1f0, 0xefde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e3, 4, 0, 0, 0]),
       ("reverted", 0xdfbcdb9e78432d8ae0bd091813e0cb3a67bc79404917c756810a5a375f81e3e2, [0xefde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1f0, 0xefde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e3, 4, 0, 0, 0])]⟩),
  (dep 7 2 1 1 0 (.offset (w 32)),
    ⟨"00000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000020f5b268a3ff315cc44ccceeef86259c9e8eef81ceecb14001543809115380dd6200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001",
      "reverted", "", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 8 3 0 0 0 (.offset (w 160)),
    ⟨"000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000a0efde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 9 1 2 0 0 (.offset (w (2 ^ 255))),
    ⟨"000000000000000000000000000000000000000000000000000000000000000980000000000000000000000000000000000000000000000000000000000000000b217ad5c70346c7cd952bd2463c6684a56f9ed229f5780947586625781b477000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 1 0 1 1 1 (.tail (w 0)),
    ⟨"00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000040d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e451640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000019e00000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 2 0 2 2 33 (.tail (w 32)),
    ⟨"00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000040d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e451640000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000213c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a3c00000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 2, 1, 32, 0, 0],
      [("returned", 44, [44, 2, 1, 32, 0, 0]),
       ("reverted", 90, [44, 2, 1, 32, 0, 0])]⟩),
  (dep 3 0 3 3 33 (.tail (w 193)),
    ⟨"00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000040d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e4516400000000000000000000000000000000000000000000000000000000000000c100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021daa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbfda00000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 4 0 4 4 33 (.length (w 34)),
    ⟨"00000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000040d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e4516400000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002278dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a547800000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 4, 1, 34, 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54, 0x7800000000000000000000000000000000000000000000000000000000000000],
      [("returned", 0xf0dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a84, [0xf0dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a84, 4, 1, 34, 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54, 0x7800000000000000000000000000000000000000000000000000000000000000]),
       ("reverted", 0xe1bbcdcbfa53e0af9ce60302e76e41a084113b5f9d13928fc363508e860c750a, [0xf0dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a84, 4, 1, 34, 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54, 0x7800000000000000000000000000000000000000000000000000000000000000])]⟩),
  (dep 5 0 5 5 33 (.length (w 65)),
    ⟨"00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000040d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e451640000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000411715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e91700000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 6 3 0 0 0 (.truncate 96),
    ⟨"00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000040efde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e3",
      "returned", "", [0, 6, 4, 0, 0, 0],
      [("returned", 19, [19, 6, 4, 0, 0, 0]),
       ("reverted", 40, [19, 6, 4, 0, 0, 0])]⟩),
  (dep 7 1 9 0 0 (.truncate 127),
    ⟨"000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000400b217ad5c70346c7cd952bd2463c6684a56f9ed229f5780947586625781b477000000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 8 2 1 2 0 (.tag (w (2 ^ 256 - 1))),
    ⟨"00000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000040ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002",
      "reverted", "", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 9 1 3 0 0 (.tagCut (w 0)),
    ⟨"000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000",
      "reverted", "", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 1 0 1 2 2 (.truncate 63),
    ⟨"000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩)]

private def structRows : List (Deployment × Expected) := [
  (dep 1 0 11 12 0 .none,
    ⟨"00000000000000000000000000000000000000000000000000000000000000011ee0fddb687f7d726adbdd32a0b3afe38d0593fe9dc00a18a5f4acd116e8b7c9000000000000000000000000000000000000000000000000000000000000000b000000000000000000000000000000000000000000000000000000000000000c",
      "returned", "", [0, 1, 1, 11, 12, 0],
      [("returned", 35, [35, 1, 1, 11, 12, 0]),
       ("reverted", 72, [35, 1, 1, 11, 12, 0])]⟩),
  (dep 2 1 0 0 0 .none,
    ⟨"0000000000000000000000000000000000000000000000000000000000000002ae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "returned", "", [0, 2, 2, 0, 0, 0],
      [("returned", 14, [14, 2, 2, 0, 0, 0]),
       ("reverted", 30, [14, 2, 2, 0, 0, 0])]⟩),
  (dep 3 1 0 0 0 .narrow,
    ⟨"0000000000000000000000000000000000000000000000000000000000000003ae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f",
      "returned", "", [0, 3, 2, 0, 0, 0],
      [("returned", 15, [15, 3, 2, 0, 0, 0]),
       ("reverted", 32, [15, 3, 2, 0, 0, 0])]⟩),
  (dep 4 0 1 2 0 (.truncate 96),
    ⟨"00000000000000000000000000000000000000000000000000000000000000041ee0fddb687f7d726adbdd32a0b3afe38d0593fe9dc00a18a5f4acd116e8b7c90000000000000000000000000000000000000000000000000000000000000001",
      "reverted", "08638556", [0, 0, 0, 0, 0, 0],
      []⟩),
  (dep 5 1 0 0 0 (.tag (w 0x2e897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f)),
    ⟨"00000000000000000000000000000000000000000000000000000000000000052e897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "reverted", "", [0, 0, 0, 0, 0, 0],
      []⟩)]

private def scenarios : List (String × Nat × String × List Constructor × List (Deployment × Expected)) := [
    ("none", 1, "none", [], noneRows),
    ("word", 2, "uint256", [], wordRows),
    ("words", 3, "uint256,uint256", [], wordsRows),
    ("bytes", 4, "uint256,bytes", [], bytesRows),
    ("static-enum", 5, "uint256,enum", [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩, ⟨"Q", .oneWord⟩], staticRows),
    ("dynamic-enum", 6, "uint256,enum", [⟨"Blob", .bytes⟩, ⟨"Ready", .oneWord⟩, ⟨"Settled", .twoWords⟩, ⟨"Rejected", .noWords⟩], dynamicRows),
    ("struct-enum", 7, "uint256,enum", [⟨"Ready", .pair⟩, ⟨"Idle", .noWords⟩], structRows)]

/-- Original Core reverts with one Word: an error selector stands for std's
four bytes and the Word zero for its empty revert data. Its accepted
initializer returns the Word zero, which has no EVM counterpart. -/
private def coreOutput (output : String) : String :=
  "0x" ++ if output.length == 8 then String.ofList (List.replicate 56 '0') ++ output
    else if output.isEmpty then String.ofList (List.replicate 64 '0') else output

private def wordText (value : Nat) : String := encodeBytesText (encodeWordBytesBE (w value))

private def words (values : List Nat) : List Word :=
  (List.range ConstructorArguments.slotCount).map fun slot => w (values.getD slot 0)

private def checkRow (name : String) (row : Json) (status output : String) (values : List Nat) : IO Unit :=
  ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some output &&
      (row.getObjVal? "committedStorage").toOption == some (slots values))
    s!"{name}: original Core differs from the expected row {row.compress}"

private def parameters (kind : String) (constructors : List Constructor) : IO Parameters := do
  let some parameters := Solcore.Synthesis.Source.ConstructorArguments.parametersOf? kind constructors
    | throw (IO.userError s!"{kind}: unsupported parameters")
  return parameters

/-- std's decisions that one malformation cannot reach, on raw arguments of
the dynamic enum's `Settled(3, 7)` and the static enum's `Idle`: the enum's
offset is checked before its tag, the tag is read wherever the offset points,
and the leading Word comes first. -/
private def orderRows (dynamic static : Parameters) : List (String × Parameters × ByteArray × String) :=
  let settled := ConstructorArgumentsExecution.argumentBytes dynamic (dep 3 2 3 7 0 .none)
  let unknown := StdCalldata.replaceWord settled 64 (w 7)
  let idle := ConstructorArgumentsExecution.argumentBytes static (dep 1 1 0 0 0 .none)
  [("unknown tag", dynamic, unknown, ""),
    ("unknown tag behind an offset that leaves no tag", dynamic,
      StdCalldata.replaceWord unknown 32 (w (unknown.size - 3)), "08638556"),
    ("an offset onto the first field", dynamic, StdCalldata.replaceWord settled 32 (w 96), ""),
    ("the leading Word cut before the tag", static, idle.extract 0 16, "08638556"),
    ("an unknown tag under a cut head", static, (StdCalldata.replaceWord idle 32 (w 5)).extract 0 64, "")]

def testSourceConstructorArgumentGolden : IO Unit := do
  let fuel := 1000000
  let bindings := StorageExecution.fixtureBindings
  let mut deployed := 0
  let mut rejected := 0
  for (name, constant, kind, constructors, rows) in scenarios do
    let step ← step constant
    let parameters ← parameters kind constructors
    let some plan := CheckedPlan.ofParts? step parameters
      | throw (IO.userError s!"{name}: the constructor-argument contracts failed admission")
    for (deployment, expected) in rows do
      let label := s!"{name} {(Solcore.Synthesis.Source.ConstructorArguments.malformationJson deployment.malformation).compress}"
      ensure (ConstructorArgumentsExecution.arguments parameters deployment == "0x" ++ expected.arguments)
        s!"{label}: the argument bytes differ from the expected encoding"
      let accepted := expected.status == "returned"
      ensure (Solcore.Synthesis.Source.ConstructorArguments.prescribed parameters deployment ==
          (if accepted then none else some ("0x" ++ expected.output)))
        s!"{label}: the prescribed std outcome differs from the expected row"
      let transactions := if accepted then runtimeTransactions else []
      let _ ← get (Solcore.Synthesis.Source.ConstructorArguments.checkedScenario plan deployment transactions)
      let history := ConstructorArgumentsExecution.observe plan deployment transactions bindings fuel
      ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{label}: the history is incomplete"
      checkRow label (← get (history.getObjVal? "deployment")) expected.status
        (if accepted then coreOutput "" else coreOutput expected.output) expected.values
      let observed ← get (history.getObjValAs? (Array Json) "transactions")
      ensure (observed.size == expected.transactions.length) s!"{label}: a transaction row is missing"
      for (row, (status, result, values)) in observed.toList.zip expected.transactions do
        checkRow label row status (wordText result) values
      let some (modelDeployment, modelled) := ConstructorArgumentsExecution.model step fuel parameters deployment transactions
        | throw (IO.userError s!"{label}: the Lean model failed")
      ensure (modelDeployment.reverted == !accepted && modelDeployment.slots == words expected.values &&
          (accepted || encodeBytesText modelDeployment.output == "0x" ++ expected.output))
        s!"{label}: the Lean model's deployment differs from the expected row"
      ensure (modelled.length == expected.transactions.length &&
          (modelled.zip expected.transactions).all fun (model, (status, result, values)) =>
            model.reverted == (status == "reverted") && model.output == encodeWordBytesBE (w result) &&
              model.slots == words values)
        s!"{label}: the Lean model's transactions differ from the expected rows"
      if accepted then deployed := deployed + 1 else rejected := rejected + 1
  ensure (deployed == 40 && rejected == 31) s!"the golden rows changed: {deployed} deployed, {rejected} rejected"
  -- The order of std's checks, on raw arguments, for Core and the Lean model alike.
  let dynamic ← parameters "uint256,enum" [⟨"Blob", .bytes⟩, ⟨"Ready", .oneWord⟩, ⟨"Settled", .twoWords⟩, ⟨"Rejected", .noWords⟩]
  let static ← parameters "uint256,enum" [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩, ⟨"Q", .oneWord⟩]
  for (label, parameters, bytes, expected) in orderRows dynamic static do
    let some plan := CheckedPlan.ofParts? (← step 1) parameters | throw (IO.userError "no plan")
    let history := ConstructorArgumentsExecution.observeContracts plan.initializer plan.runtime bytes [] bindings fuel
    checkRow label (← get (history.getObjVal? "deployment")) "reverted" (coreOutput expected) []
    let decided := match ConstructorArgumentsExecution.stdDecide parameters bytes with
      | .error data => some (encodeBytesText data)
      | .ok _ => none
    ensure (decided == some ("0x" ++ expected)) s!"{label}: std's order of checks differs in the Lean model"
  -- A changed expectation fails: the first accepted bytes row read as a rejection.
  let some (deployment, expected) := bytesRows.head? | throw (IO.userError "no bytes row")
  ensure (Solcore.Synthesis.Source.ConstructorArguments.prescribed .bytes deployment == none &&
      expected.status == "returned" && coreOutput expected.output != coreOutput "08638556")
    "a changed expectation is not detected"

end Tests.SourceConstructorArgumentGolden
end

section
-- leanmerge: from Solcore.Test.SourceForwardedCallCases
/-! Forwarded-value case regressions: exact replay, bounded generation from an
independent sequence stream, canonical transaction boundaries, the forwarding
protocol check and typed reductions over steps, transactions, inputs, revert
bits, call values and amounts. Expected values here are test goldens only;
cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceForwardedCallCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.ForwardedCall (CheckedPlan)
open Solcore.Synthesis.Stateful.ForwardedCallExecution (Transaction Bindings)

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
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩⟩

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "forwarded-value fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "forwarded-value wrappers failed host admission")
  return plan
private def transactions (values : List (Nat × Nat × Nat)) : List Transaction :=
  values.zipIdx.map fun ((input, value, amount), index) =>
    ⟨"call-" ++ toString index, Word.ofNatModulo input, Word.ofNatModulo value, Word.ofNatModulo amount⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × Nat × Nat)) : IO ForwardedCall.CheckedScenario :=
  get (ForwardedCall.checkedScenario plan (transactions values))
private def imported (value : ForwardedCall.CheckedScenario) (fuel : Nat := 100000) : IO Json :=
  get (ForwardedCall.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(0, 7, 5), (1, 0, 2 ^ 70), (2, 1, 1)]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson (["0", "1"] : List String)) "case did not declare slots zero and one"
  ensure ((← get (ForwardedCall.replayCase saved 100000)) == saved) "imported forwarded-value case did not replay"
  ensure ((← get (ForwardedCall.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 100000)) == saved)
    "forwarded-value replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(5, 2 ^ 64, 0), (2, 0, 7)])
  ensure ((← field saved "programs") == (← field changed "programs") &&
    (← string saved "source") == (← string changed "source"))
    "inputs, values or amounts were substituted into source or Core code"
  let observed := ForwardedCall.observe value bindings 100000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "returned", some "reverted"])
    "forwarded-value scenario did not follow its root parities"
  ensure ((← get (ForwardedCall.checkProtocol value observed)) == ["returned", "returned", "reverted"])
    "forwarded-value history broke its refund or balance protocol"
  -- A committed child or a moved balance breaks the protocol check.
  let observedRows ← rows observed
  let accounts ← get ((← field observedRows[1]! "committedAccounts").getArr?)
  let changedAccounts := accounts.map fun account =>
    if (account.getObjValAs? String "role").toOption == some "child" then account.setObjVal! "balance" (toJson "6") else account
  let forgedRow := observedRows[1]!.setObjVal! "committedAccounts" (.arr changedAccounts)
  let forged := observed.setObjVal! "transactions" (.arr (observedRows.set! 1 forgedRow))
  rejected (ForwardedCall.checkProtocol value forged) "a child account changed by a reverted child passed the protocol"
  ensure ((← rows (ForwardedCall.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩, ⟨203, by decide⟩⟩ 100000)).map
      (fun row => (row.getObjVal? "output").toOption) == observedRows.map (fun row => (row.getObjVal? "output").toOption))
    "address-independent forwarded-value outcomes changed with bindings"
  rejected (ForwardedCall.checkedScenario identity (transactions [(0, 2 ^ 70 + 1, 0)])) "call value above 2^70 accepted"
  rejected (ForwardedCall.checkedScenario identity (transactions [(0, 0, 2 ^ 70 + 1)])) "amount above 2^70 accepted"
  ensure (ForwardedCall.modeInput (Word.ofNatModulo 6) 1 == Word.ofNatModulo 5 &&
    ForwardedCall.modeInput Word.maximum 0 == Word.ofNatModulo (2 ^ 256 - 4)) "call modes do not replace the low two bits"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := ForwardedCall.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 12 && (choices.zip ForwardedCall.sequenceBounds).all (fun (value, bound) => value < bound))
      "sequence choices escaped their banks"
    match ForwardedCall.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 && ForwardedCall.combinedNodes value.plan.step ≤ 384 &&
          value.plan.step.helpers.length == 1 + seed % 3) "forwarded-value recipe lost node/transaction/helper bounds"
        ensure (value.transactions.map (fun tx => tx.input.val % 4) == (choices.drop 3).take 3)
          "generated call modes escaped their draws"
        ensure (value.transactions.all fun tx => ForwardedCall.valueBank.contains tx.value && ForwardedCall.valueBank.contains tx.amount)
          "generated value or amount escaped its bank"
        ensure (value.transactions.all fun tx => ForwardedCall.boundaryInputs.any fun input =>
            ForwardedCall.modeInput input (tx.input.val % 4) == tx.input)
          "generated input is not a bank input with a call mode"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (ForwardedCall.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (ForwardedCall.generatedScenario (Seed.ofNat 0) ForwardedCall.programOverhead) "undersized node budget accepted"
  let corpus := ForwardedCall.generateCases (Seed.ofNat 0) 384 4 512 100000
  ensure (corpus == ForwardedCall.generateCases (Seed.ofNat 0) 384 4 512 100000) "forwarded-value generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "forwarded-value count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (ForwardedCall.replayCase saved 100000)) == saved) "generated forwarded-value provenance did not replay"
    let low ← get (ForwardedCall.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := ForwardedCall.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "forwarded-value generation resource exhaustion was not distinguished"
  ensure ((← rows (ForwardedCall.generateCases (Seed.ofNat seed) 384 2 1 100000) "cases").size == 1 &&
    (← natural (ForwardedCall.generateCases (Seed.ofNat seed) 384 0 10 100000) "attempted") == 0 &&
    (← rows (ForwardedCall.generateCases (Seed.ofNat seed) 384 1 0 100000) "cases").isEmpty)
    "forwarded-value generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("input", toJson "01"),
      ("input", toJson (toString (2 ^ 256))), ("value", toJson "07"), ("value", toJson (toString (2 ^ 70 + 1))),
      ("amount", toJson "05"), ("amount", toJson (toString (2 ^ 70 + 1))), ("amount", Json.null),
      ("target", toJson "child"), ("callee", toJson "parent"), ("calldata", toJson "0x"), ("extra", toJson true)] do
    rejected (ForwardedCall.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical forwarded-value transaction accepted"
  rejected (ForwardedCall.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (ForwardedCall.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (ForwardedCall.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  let initial ← field saved "initialState"
  for (name, bad) in [("initialState", initial.setObjVal! "callerBalance" (toJson "0")),
      ("initialState", Json.mkObj [("accounts", toJson ([] : List Json))]),
      ("observedSlots", toJson (["0"] : List String)), ("executionFuel", toJson (10000001 : Nat)),
      ("forwardPlan", Json.null), ("programs", Json.mkObj [("parent", Json.null), ("child", Json.null)])] do
    rejected (ForwardedCall.caseProgram (saved.setObjVal! name bad)) "invalid forwarded-value case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (ForwardedCall.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 100000)
      "tampered forwarded-value provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (ForwardedCall.replayCase (withOrigin (origin.setObjVal! name bad)) 100000)
      "tampered generated forwarded-value recipe accepted"
  let generatedRows ← rows generated
  let generatedAmount := (generatedRows[0]!.getObjValAs? String "amount").toOption.getD ""
  rejected (ForwardedCall.replayCase (generated.setObjVal! "transactions"
      (.arr (generatedRows.set! 0 (generatedRows[0]!.setObjVal! "amount"
        (toJson (if generatedAmount == "0" then "1" else "0")))))) 100000)
    "generated amount replaced without its seed"
  let plan ← field saved "forwardPlan"
  rejected (ForwardedCall.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical forwarded-value plan accepted"
  rejected (ForwardedCall.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.call-plan.v1")))
    "call plan schema accepted as a forwarded-value plan"
  rejected (ForwardedCall.replayCase (saved.setObjVal! "source" (toJson "stale")) 100000) "stale source accepted"
  let contracts ← field saved "contracts"
  let parent ← field contracts "parent"
  rejected (ForwardedCall.replayCase (saved.setObjVal! "contracts" (contracts.setObjVal! "parent"
      (parent.setObjVal! "constructorValue" (toJson "8")))) 100000)
    "the nested-call endowment accepted for the forwarding parent"
  rejected (ForwardedCall.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-call-case.v1")) 100000)
    "nested-call case schema accepted by the forwarded-value tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [(7, 2 ^ 70, 2 ^ 64), (5, 7, 2 ^ 64 - 1), (2 ^ 255, 2 ^ 64, 2 ^ 70)]
  let saved ← imported value
  let candidates ← get (ForwardedCall.shrinkCases saved 2000 100000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (ForwardedCall.shrinkCases saved 2000 100000)))
    "forwarded-value reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredInput := false
  let mut clearedRevert := false
  let mut loweredValue := false
  let mut loweredAmount := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (ForwardedCall.caseProgram row)
    ensure (decide (ForwardedCall.StrictlySmaller reduced value) && reduced.plan.childProgram.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "forwarded-value reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("programs", ForwardedCall.programsJson reduced.plan),
      ("transactions", ForwardedCall.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate forwarded-value reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    let sameCount := reduced.transactions.length == value.transactions.length
    loweredInput := loweredInput || (sameCount && pairs.any fun (left, right) => left.input.val < right.input.val)
    clearedRevert := clearedRevert || (sameCount && pairs.any fun (left, right) =>
      left.input.val + 1 == right.input.val || left.input.val + 2 == right.input.val)
    loweredValue := loweredValue || (sameCount && pairs.any fun (left, right) => left.value.val < right.value.val)
    loweredAmount := loweredAmount || (sameCount && pairs.any fun (left, right) => left.amount.val < right.amount.val)
    changedStep := changedStep || ForwardedCall.programsJson reduced.plan != ForwardedCall.programsJson value.plan
    ensure ((← get (ForwardedCall.replayCase row 100000)) == row) "reduced forwarded-value case did not replay"
  ensure (removed && loweredInput && clearedRevert && loweredValue && loweredAmount && changedStep)
    "forwarded-value shrink omitted sequence/input/revert/value/amount/step axes"
  ensure ((← rows (← get (ForwardedCall.shrinkCases saved 2 100000)) "cases") == result.extract 0 2 &&
    (← rows (← get (ForwardedCall.shrinkCases saved 0 100000)) "cases").isEmpty) "forwarded-value shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (ForwardedCall.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", ForwardedCall.planJson reduced.plan),
    ("parentPrograms", ForwardedCall.programsJson reduced.plan),
    ("parentTransactions", ForwardedCall.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (ForwardedCall.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 100000)
    "non-strict forwarded-value reduction provenance accepted"

def testSourceForwardedCallCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceForwardedCallCases
end

section
-- leanmerge: from Solcore.Test.SourceForwardedCallCorpus
/-! The fixed forwarded-value corpus checks actual original Core histories
against independently computed expectations: root status and payload, both
contracts' balances and slots zero and one, and empty logs after every
transaction. Coverage describes the checked step AST, the inputs and call
modes, the call values and forwarded amounts, the amounts child reverts keep
with the parent and the call values root reverts return. Source/Rust/EVM
agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceForwardedCallCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers (left right : List String) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", ForwardedCall.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.ForwardedCall.version),
  ("templateVersion", ForwardedCall.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", ForwardedCall.emitterVersion), ("wrapperVersion", ForwardedCall.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := ForwardedCall.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← ForwardedCall.checkedPlan (← entry.getObjVal? "forwardPlan")
  let scenario ← ForwardedCall.checkedScenario plan (← ForwardedCall.decodeTransactions (← entry.getObjVal? "transactions"))
  ForwardedCall.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "forward-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-call-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-forwarded-value" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected forwarded-value manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("forwarded-value manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words ForwardedCall.boundaryInputs))
    "forwarded-value corpus must require all ten boundary inputs"
  require ((← manifest.getObjValAs? (List Nat) "requiredCallModes") == [0, 1, 2, 3])
    "forwarded-value corpus must require all four call modes"
  require (sameMembers (← strings manifest "requiredValues") (words ForwardedCall.valueBank) &&
      sameMembers (← strings manifest "requiredForwardedValues") (words ForwardedCall.valueBank))
    "forwarded-value corpus must require the whole bank as call values and amounts"
  let requiredRefunded ← strings manifest "requiredRefundedForwards"
  let requiredReverted ← strings manifest "requiredRevertedValues"
  require (requiredRefunded.length ≥ 3 && requiredRefunded.all ((words ForwardedCall.valueBank).contains ·) &&
      !requiredRefunded.contains "0")
    "forwarded-value corpus must require at least three nonzero forwards kept by child reverts"
  require (requiredReverted.length ≥ 3 && requiredReverted.all ((words ForwardedCall.valueBank).contains ·) &&
      requiredReverted.contains "0" && requiredReverted.any (· != "0"))
    "forwarded-value corpus must require root refunds of zero and of nonzero call values"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "forwarded-value corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "forwarded-value corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "forwarded-value corpus must require both outcomes"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "forwarded-value corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut modes : List Nat := []
  let mut values : List String := []
  let mut amounts : List String := []
  let mut refunded : List String := []
  let mut reverted : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate forwarded-value corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← ForwardedCall.replayCase saved fuel) == saved) ("forwarded-value corpus entry did not replay: " ++ identifier)
    let scenario ← ForwardedCall.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "forwardPlan") == (← entry.getObjVal? "forwardPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported forwarded-value entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("forwarded-value corpus features changed: " ++ identifier)
    let history := ForwardedCall.observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
    let statuses ← ForwardedCall.checkProtocol scenario history
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("forwarded-value expected history length changed: " ++ identifier)
    for ((row, golden), tx) in (observed.zip expected).zip scenario.transactions do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedAccounts", ← row.getObjVal? "committedAccounts"),
        ("logs", ← row.getObjVal? "logs")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
      inputs := (inputs ++ [toString tx.input.val]).eraseDups
      modes := (modes ++ [tx.input.val % 4]).eraseDups
      values := (values ++ [toString tx.value.val]).eraseDups
      amounts := (amounts ++ [toString tx.amount.val]).eraseDups
      let status ← string row "status"
      if status == "returned" && ForwardedCall.childReverts tx then
        refunded := (refunded ++ [toString tx.amount.val]).eraseDups
      if status == "reverted" then
        reverted := (reverted ++ [toString tx.value.val]).eraseDups
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
  require (requiredFeatures.all features.contains) "forwarded-value corpus misses a required step feature"
  require (requiredInputs.all inputs.contains && [0, 1, 2, 3].all modes.contains)
    "forwarded-value corpus misses an input or call mode"
  require ((words ForwardedCall.valueBank).all values.contains && (words ForwardedCall.valueBank).all amounts.contains)
    "forwarded-value corpus misses a call value or amount"
  require (requiredRefunded.all refunded.contains && requiredReverted.all reverted.contains)
    "forwarded-value corpus misses a child-revert or root-revert refund"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "forwarded-value corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "forwarded-value corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains) "forwarded-value corpus misses an observed outcome"
  return Json.mkObj [("profile", toJson "stateful-forwarded-value"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("refundedForwards", toJson refunded), ("revertedValues", toJson reverted)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid forwarded-value corpus unexpectedly passed: " ++ message))

def testSourceForwardedCallCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-forward-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first forwarded-value case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated forwarded-value case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let withRow := fun (index : Nat) (row : Json) =>
    replace first (first.setObjVal! "expectedHistory" (.arr (history.set! index row)))
  let row := history[0]!
  rejects (validateManifest (withRow 0 (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let accounts ← checked (row.getObjValAs? (Array Json) "committedAccounts")
  let withAccount := fun (index : Nat) (row : Json) (role : Nat) (account : Json) => do
    let rowAccounts ← checked (row.getObjValAs? (Array Json) "committedAccounts")
    pure (withRow index (row.setObjVal! "committedAccounts" (.arr (rowAccounts.set! role account))))
  rejects (validateManifest (← withAccount 0 row 1 (accounts[1]!.setObjVal! "balance" (toJson "6")))) "changed child balance"
  rejects (validateManifest (← withAccount 0 row 0 (accounts[0]!.setObjVal! "balance" (toJson "8")))) "changed parent balance"
  rejects (validateManifest (withRow 0 (row.setObjVal! "logs" (toJson [Json.mkObj [("address", toJson "101")]])))) "invented log"
  -- The first scenario's second transaction reverts its child: committing the
  -- forwarded 2^70 to the child is wrong.
  let childRevert := history[1]!
  let childAccounts ← checked (childRevert.getObjValAs? (Array Json) "committedAccounts")
  rejects (validateManifest (← withAccount 1 childRevert 1 (childAccounts[1]!.setObjVal! "balance"
    (toJson (toString (5 + 2 ^ 70)))))) "a child-reverted forward committed"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let generatedStatus ← checked (generatedHistory[0]!.getObjValAs? String "status")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status"
      (toJson (if generatedStatus == "returned" then "reverted" else "returned")))))))) "flipped status"
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "amount" (toJson "7"))))))) "changed amount"
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "value" (toJson "1"))))))) "changed call value"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String))))) "features"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))])))) "changed seed"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first)))) "duplicate entry"
  for (key, value) in [
      ("profile", toJson "stateful-calls"), ("wrapperVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCallModes", toJson [0, 1, 2]), ("requiredValues", toJson (["0", "1"] : List String)),
      ("requiredForwardedValues", toJson (["0"] : List String)),
      ("requiredRefundedForwards", toJson (["0", "1", "7"] : List String)),
      ("requiredRevertedValues", toJson (["1", "7", "5"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "zero fuel"
  IO.println summary.compress

end Tests.SourceForwardedCallCorpus
end

section
-- leanmerge: from Solcore.Test.SourceForwardedCallEmitter
/-! Forwarded-value protocol regressions through actual installed
ContractRuntime code. Golden histories are hand-computed: they cover committed
forwards on both sides of the 64-bit boundary, the call value folded into the
parent's slot, the forwarded value folded into the child's step, wrapping
arithmetic, a child revert that keeps its amount with the parent, root reverts
alone and after a child revert, and a call value the caller cannot fund.
Calldata comes from Foundry's `cast calldata` encoder. -/
set_option autoImplicit false

namespace Tests.SourceForwardedCallEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ForwardedCall (CheckedPlan)
open Solcore.Synthesis.Source.NestedCall (EmittedContracts)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1
private def endowment : Nat := 2 ^ 72

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "forwarded-value step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "forwarded-value wrappers did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedContracts :=
  match Solcore.Synthesis.Source.ForwardedCall.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"forwarded-value source emission failed: {reprStr error}")

private def transactions (rows : List (Nat × Nat × Nat)) : List ForwardedCallExecution.Transaction :=
  rows.zipIdx.map fun ((input, value, amount), index) =>
    ⟨"tx-" ++ toString index, Word.ofNatModulo input, Word.ofNatModulo value, Word.ofNatModulo amount⟩

/-- Both committed accounts at the fixture addresses: balance and slots zero and one. -/
private def accounts (parent child : Nat × Nat × Nat) : Json := toJson ([("parent", "101", parent), ("child", "102", child)].map
  fun (role, address, balance, slot0, slot1) => Json.mkObj [
    ("role", toJson role), ("address", toJson address), ("balance", toJson (toString balance)),
    ("storage", toJson [Json.mkObj [("slot", toJson "0"), ("value", toJson (toString slot0))],
      Json.mkObj [("slot", toJson "1"), ("value", toJson (toString slot1))]])])

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexWord (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  "0x" ++ String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

/-- One hand-computed row: root status and payload, both accounts and no logs. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × Nat × Nat))
    (expected : List (String × Nat × (Nat × Nat × Nat) × (Nat × Nat × Nat))) : IO Unit := do
  let history := ForwardedCallExecution.observe plan (transactions rows) NestedCallExecution.fixtureBindings 100000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length &&
    (history.getObjVal? "initialAccounts").toOption == some (accounts (endowment, 0, 0) (0, 0, 0)))
    "forwarded-value golden history did not complete from the endowed deployment"
  for (row, (status, payload, parent, child)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (hexWord payload) &&
      (row.getObjVal? "committedAccounts").toOption == some (accounts parent child) &&
      (row.getObjVal? "logs").toOption == some (toJson ([] : List Json)))
      s!"forwarded-value golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x: a committed forward of five, a child revert that keeps 2^70
  -- with the parent, then a root revert that keeps both accounts.
  historyCheck (← checked [.var 0]) [(0, 7, 5), (1, 0, 2 ^ 70), (2, 1, 1)] [
    ("returned", 12, (endowment + 2, 7, 5), (5, 5, 5)),
    ("returned", 2 ^ 70 + 15, (endowment + 2, 8, 2 ^ 70 + 7), (5, 5, 5)),
    ("reverted", 19, (endowment + 2, 8, 2 ^ 70 + 7), (5, 5, 5))]
  -- step(x) = x + 1 with values across the 64-bit boundary; the maximum input
  -- wraps and makes both frames revert.
  historyCheck (← checked [increment]) [(4, 2 ^ 64, 2 ^ 64 - 1), (5, 2 ^ 70, 2 ^ 64), (maximum, 7, 7)] [
    ("returned", 2 ^ 65 + 8, (endowment + 1, 2 ^ 64 + 4, 2 ^ 64 + 4), (2 ^ 64 - 1, 2 ^ 64 + 4, 2 ^ 64 - 1)),
    ("returned", 2 ^ 70 + 2 ^ 65 + 2 ^ 64 + 20,
      (endowment + 1 + 2 ^ 70, 2 ^ 70 + 2 ^ 64 + 9, 2 ^ 65 + 11), (2 ^ 64 - 1, 2 ^ 64 + 4, 2 ^ 64 - 1)),
    ("reverted", 2 ^ 70 + 2 ^ 65 + 27,
      (endowment + 1 + 2 ^ 70, 2 ^ 70 + 2 ^ 64 + 9, 2 ^ 65 + 11), (2 ^ 64 - 1, 2 ^ 64 + 4, 2 ^ 64 - 1))]

/-- The reverted root's working world holds the call value, the forward and
both frames' writes; the public runtime commits the pre-transfer world. -/
private def refundChecks : IO Unit := do
  let plan ← checked [.var 0]
  let bindings := NestedCallExecution.fixtureBindings
  let world := ForwardedCallExecution.initialWorld plan bindings
  let registry : CheckedContractRegistry := ⟨fun address =>
    if address == bindings.parent then some plan.parentContract
    else if address == bindings.child then some plan.childContract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.parent |
    throw (IO.userError "forwarding parent did not resolve")
  let invocation : TopLevelInvocation := {
    target := bindings.parent, caller := bindings.caller, callValue := Word.ofNatModulo 7,
    inputData := ForwardedCallExecution.inputData bindings (Word.ofNatModulo 2) (Word.ofNatModulo 5) }
  match (BalancedTopLevelExecution.run contract invocation installed registry 100000).view with
  | .rejected _ => throw (IO.userError "a funded call value was rejected")
  | .execution execution =>
      match execution.view with
      | .outOfFuel _ _ _ => throw (IO.userError "forwarded-value golden call exhausted fuel")
      | .completed terminal =>
          ensure (terminal.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo 16)))
            "bit two did not revert the root with slot zero plus the child payload"
          let working := terminal.terminalContext.context.values.working.1
          let some parent := working.account? bindings.parent | throw (IO.userError "working parent missing")
          let some child := working.account? bindings.child | throw (IO.userError "working child missing")
          ensure (parent.balance == Word.ofNatModulo (endowment + 2) && parent.storageRead Word.zero == Word.ofNatModulo 9 &&
            child.balance == Word.ofNatModulo 5 && child.storageRead (Word.ofNatModulo 1) == Word.ofNatModulo 5)
            "the working world lost the call value, the forward or a write"
          let some committedParent := terminal.finalWorld.account? bindings.parent | throw (IO.userError "committed parent missing")
          let some committedChild := terminal.finalWorld.account? bindings.child | throw (IO.userError "committed child missing")
          let some caller := terminal.finalWorld.account? bindings.caller | throw (IO.userError "committed caller missing")
          ensure (committedParent.balance == Word.ofNatModulo endowment && committedChild.balance == Word.zero &&
            (committedParent.storageValue? Word.zero).isNone && (committedChild.storageValue? Word.zero).isNone &&
            caller.balance == Word.ofNatModulo ForwardedCallExecution.callerFunds)
            "the reverted root committed its value, forward or writes"
  -- A caller that cannot fund the call value is rejected before any execution.
  let poor := ((WorldState.empty.putAccount bindings.caller (Account.empty.withBalance (Word.ofNatModulo 6))).putAccount
    bindings.parent ((Account.empty.withCode plan.parentContract.code).withBalance (Word.ofNatModulo endowment))).putAccount
    bindings.child (Account.empty.withCode plan.childContract.code)
  let some ⟨poorContract, poorInstalled⟩ := registry.resolve? poor bindings.parent |
    throw (IO.userError "forwarding parent did not resolve in the unfunded world")
  match (BalancedTopLevelExecution.run poorContract invocation poorInstalled registry 100000).view with
  | .rejected rejected => ensure (rejected.failure == .insufficientBalance) "unfunded value was not an insufficient balance"
  | .execution _ => throw (IO.userError "an unfunded call value executed")

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [.var 0]] do
    ensure (plan.parentProgram.check && plan.childProgram.check && plan.parentProgram.toCore.checkHost &&
      plan.childProgram.toCore.checkHost && plan.parentProgram.resultType == .sum .word (.sum .word .word) &&
      plan.parentContract.entryProfile == .wordOutcomeV1 && plan.childContract.entryProfile == .wordOutcomeV1)
      "forwarded-value plan lost full host checking or the typed outcome convention"
    ensure (plan.parentContract.code.program == plan.parentProgram.toCore &&
      plan.childContract.code.program == plan.childProgram.toCore) "admission replaced an original contract"
    ensure (ForwardedCall.combinedNodes plan.step ==
        Wire.programNodes plan.parentProgram + Wire.programNodes plan.childProgram &&
      ForwardedCall.combinedNodes plan.step == Wire.programNodes plan.step.program + ForwardedCall.programOverhead)
      "forwarded-value wrapper overhead differs from the complete original Core"
    match plan.childProgram.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "forwarded-value child ignored its arbitrary entry closure"
    | _ => throw (IO.userError "forwarded-value child lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "forwarded-value emission is nondeterministic"
  ensure (Wire.encodeProgram (← checked [increment]).parentProgram == Wire.encodeProgram (← checked [.var 0]).parentProgram &&
      ForwardedCall.programOverhead == 169) "the parent program depends on the step or the overhead changed"

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mload, mstore, calldataload, gas, call, returndatasize, return_, revert_, invalid, callvalue as sc_callvalue} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedRecipient {",
  "    fallback() payable {",
  "        let sc_input: word = calldataload(0);",
  "        let sc_value: word = sc_callvalue();",
  "        let sc_old0: word = sload(0);", "        let sc_old1: word = sload(1);",
  "        let sc_computed: word = sc_step(sc_input + sc_value + sc_old0);",
  "        sstore(0, sc_computed);", "        sstore(1, sc_old1 + sc_value);",
  "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 32);",
  "        mstore(sc_ptr, sc_computed);",
  "        if ((sc_input & 1) == 1) {", "            revert_(sc_ptr, 32);", "        }",
  "        return_(sc_ptr, 32);", "    }", "}", "",
  "contract SynthesizedForwarder {",
  "    constructor() payable {}",
  "    function run(target: uint256, input: uint256, amount: uint256) public payable returns (uint256) {",
  "        let sc_target: word = Typedef.rep(target);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_amount: word = Typedef.rep(amount);",
  "        let sc_before: word = sload(0) + sc_input + sc_callvalue();",
  "        sstore(0, sc_before);",
  "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 64);",
  "        mstore(sc_ptr, sc_input);",
  "        let sc_ok: word = call(gas(), sc_target, sc_amount, sc_ptr, 32, sc_ptr + 32, 32);",
  "        if (!(returndatasize() == 32)) {", "            invalid();", "        }",
  "        let sc_after: word = mload(sc_ptr + 32);",
  "        if (sc_ok == 0) {", "            sc_after = sc_after + 1;", "        }",
  "        sstore(1, sc_after);",
  "        let sc_result: word = sload(0) + sload(1);",
  "        if ((sc_input & 2) == 2) {",
  "            mstore(sc_ptr, sc_result);", "            revert_(sc_ptr, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "forwarded-value protocol source changed"
  ensure (source.parentContractName == "SynthesizedForwarder" && source.childContractName == "SynthesizedRecipient" &&
    source.parentMethodSignature == "run(uint256,uint256,uint256)" && source.selector == "0x24b912e5" &&
    source.parentConstructorValue == toString endowment && source.childConstructorValue == "0" &&
    source.parentDeployPath == ["SynthesizedForwarderDeploy"] &&
    source.childRuntimePath == ["SynthesizedRecipientDeploy", "SynthesizedRecipient"])
    "forwarded-value wrapper metadata changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)])
  ensure ((divided.source.splitOn "invalid, callvalue as sc_callvalue, div as sc_div, ").length == 2)
    "forwarded-value emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.ForwardedCall.emitterVersion == "solcore-source-forwarded-value-v1" &&
    Solcore.Synthesis.Source.ForwardedCall.wrapperVersion == "solcore-word-forwarded-value-v1" &&
    ForwardedCall.version == "core-forwarded-value-call-v1" &&
    ForwardedCallExecution.parentEndowment == endowment) "forwarded-value provenance changed"

private def observerChecks : IO Unit := do
  -- `cast calldata "run(uint256,uint256,uint256)" 102 5 1180591620717411303424`
  ensure (ForwardedCallExecution.calldata NestedCallExecution.fixtureBindings (Word.ofNatModulo 5) (Word.ofNatModulo (2 ^ 70)) ==
    "0x24b912e5" ++ String.ofList (List.replicate 62 '0') ++ "66" ++ String.ofList (List.replicate 63 '0') ++ "5" ++
      String.ofList (List.replicate 46 '0') ++ "40" ++ String.ofList (List.replicate 16 '0'))
    "forwarded-value calldata is not the selector, child, input and amount Words"
  let plan ← checked [.var 0]
  let calls := transactions [(0, 7, 5), (1, 0, 1), (0, 0, 0)]
  let exhausted := ForwardedCallExecution.observe plan calls NestedCallExecution.fixtureBindings 0
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] && rows.length == 1 &&
    (rows[0]!.getObjValAs? String "status").toOption == some "out-of-fuel" &&
    (rows[0]!.getObjVal? "logs").toOption == some Json.null &&
    (exhausted.getObjVal? "finalAccounts").toOption == (exhausted.getObjVal? "initialAccounts").toOption)
    "forwarded-value observer conflated fuel exhaustion with completion or committed its value"
  let complete := ForwardedCallExecution.observe plan calls NestedCallExecution.fixtureBindings 100000
  ensure ((complete.getObjValAs? String "schema").toOption == some "solcore-lean.forward-history.v2" &&
    (complete.getObjValAs? String "status").toOption == some "complete")
    "history did not declare its schema or complete"

def testSourceForwardedCallEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  refundChecks
  formattingChecks
  observerChecks

end Tests.SourceForwardedCallEmitter
end
