import Solcore.Synthesis.Source.CallSequenceCases
import Solcore.Synthesis.Source.CallBranchEmitter
import Solcore.Synthesis.Stateful.CallBranchExecution

/-! A call-branch case retains the original checked Core contracts, the plan's
sites and a role-based transaction sequence. Every replay reconstructs the
contracts from the plan. Each transaction records the calls it makes and the
parent's revert, computed by the byte-level model; saved outcomes are never an
oracle, and the choice chain selects the committed worlds. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallBranch
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallBranch (CheckedPlan Site Kind)
open Solcore.Synthesis.Core.CallSequence (Window)
open Solcore.Synthesis.Stateful.CallBranchExecution (Transaction Bindings CallRow)

def caseSchema : String := "solcore-lean.semantic-call-branch-case.v1"
def planSchema : String := "solcore-lean.call-branch-plan.v1"
def profileVersion : String := "stateful-call-branches-v1/call-branch-seed-v1"
def templateVersion : String := "std-raw-call-branch-loop-sites-step-revert-odd-class-v1"
def corpusSchema : String := "solcore-lean.semantic-call-branch-corpus.v1"

abbrev validTransactions := Storage.validTransactions

def offsetBank : List Nat := Solcore.Synthesis.Source.CallSequence.offsetBank
def widthBank : List Nat := Solcore.Synthesis.Source.CallSequence.widthBank
def lengthBank : List Nat := Solcore.Synthesis.Source.CallSequence.lengthBank

/-- Random steps and the child's shell stay within the largest step budget. -/
def maxStepNodes : Nat := 512

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The child's shell and its step, which a node budget bounds. -/
def budgetNodes (plan : CheckedPlan) : Nat :=
  CallSequence.childShellNodes + Wire.programNodes plan.step.program

/-- The parent's phases: the call phase and the resume program. -/
def phasePrograms (plan : CheckedPlan) : List Wire.Program := [plan.callProgram, plan.resumeProgram]

def bounded (plan : CheckedPlan) : Bool :=
  Wire.programNodes plan.childProgram ≤ CallBranch.maxChildNodes &&
    (phasePrograms plan).all (Wire.programNodes · ≤ CallBranch.maxPhaseNodes)

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  withinBounds : bounded plan = true

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if withinBounds : bounded plan = true then
      return ⟨plan, transactions, valid, withinBounds⟩
    else throw "call-branch contracts exceed the 1024-node child or 2048-node phase limit"
  else throw s!"call-branch scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

/-! ### Plans -/

def windowJson (window : Window) : Json :=
  Json.mkObj [("offset", toJson window.offset), ("width", toJson window.width)]

def kindName : Kind → String
  | .branch => "branch"
  | .loop => "loop"

def siteJson (site : Site) : Json := Json.mkObj [
  ("kind", toJson (kindName site.kind)), ("bound", toJson site.bound), ("stop", toJson site.stop),
  ("callWindow", windowJson site.callWindow), ("exitWindow", windowJson site.exitWindow)]

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("sites", toJson (plan.sites.map siteJson)),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

private def decodeWindow (json : Json) : Except String Window := do
  return {offset := ← json.getObjValAs? Nat "offset", width := ← json.getObjValAs? Nat "width"}

private def decodeSite (json : Json) : Except String Site := do
  let kind ← match ← json.getObjValAs? String "kind" with
    | "branch" => pure Kind.branch
    | "loop" => pure Kind.loop
    | _ => throw "a site is a branch or a loop"
  let bound ← json.getObjValAs? Nat "bound"
  let stop ← json.getObjValAs? Nat "stop"
  let callWindow ← decodeWindow (← json.getObjVal? "callWindow")
  let exitWindow ← decodeWindow (← json.getObjVal? "exitWindow")
  return ⟨kind, bound, stop, callWindow, exitWindow⟩

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported call-branch plan schema"
  let sites ← (← (← json.getObjVal? "sites").getArr?).toList.mapM decodeSite
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step sites
    | throw "call-branch plan needs one to three valid sites of at most three positions, and full host-Core admission"
  unless json == planJson plan do throw "call-branch plan differs from its canonical checked representation"
  return plan

/-! ### Transactions and their prescribed outcomes -/

/-- Each transaction's calls and whether the parent reverts, from the model. -/
def prescribed (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) :
    Except String (List (List CallRow × Bool)) := do
  let some rows := Stateful.CallBranchExecution.model plan fuel transactions
    | throw "call-branch model exhausted Core fuel"
  return rows.map fun row => (row.calls, row.reverted)

def callRowJson (row : CallRow) : Json := Json.mkObj [
  ("position", toJson row.position), ("status", toJson (if row.returned then "returned" else "reverted")),
  ("length", toJson row.length)]

def transactionJson (tx : Transaction) (calls : List CallRow) (reverts : Bool) : Json := Json.mkObj [
  ("id", toJson tx.id), ("input", toJson (toString tx.input.val)),
  ("value", toJson "0"), ("target", toJson "parent"), ("callee", toJson "child"),
  ("calls", toJson (calls.map callRowJson)), ("parentReverts", toJson reverts)]

def transactionsJson (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) : Except String Json := do
  let outcomes ← prescribed plan fuel transactions
  return toJson ((transactions.zip outcomes).map fun (tx, (calls, reverts)) => transactionJson tx calls reverts)

def decodeTransactions (plan : CheckedPlan) (fuel : Nat) (json : Json) : Except String (List Transaction) := do
  let transactions ← CallReturn.decodeSequence json
  unless json == (← transactionsJson plan fuel transactions) do
    throw "transactions differ from their canonical ID, input, role metadata or prescribed outcomes"
  return transactions

/-! ### Cases -/

def programsJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("parentCall", Wire.encodeProgram plan.callProgram),
  ("parentResume", Wire.encodeProgram plan.resumeProgram),
  ("child", Wire.encodeProgram plan.childProgram)]

def observedSlotsJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("parent", toJson ((Stateful.CallBranchExecution.parentSlots plan).map fun slot => toString slot.val)),
  ("child", toJson (Stateful.CallBranchExecution.childSlots.map fun slot => toString slot.val))]

def makeCase (scenario : CheckedScenario) (emitted : CallReturn.EmittedContracts) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  return Json.mkObj [
    ("schema", toJson caseSchema), ("callBranchPlan", planJson scenario.plan),
    ("programs", programsJson scenario.plan),
    ("sources", Json.mkObj [("parent", toJson emitted.parentSource), ("child", toJson emitted.childSource)]),
    ("transactions", ← transactionsJson scenario.plan fuel scenario.transactions),
    ("initialState", CallReturn.initialStateJson), ("observedSlots", observedSlotsJson scenario.plan),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson CallSequence.childVersion), ("parentVersion", toJson CallBranch.parentVersion),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contracts", CallReturn.contractsJson), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  makeCase scenario emitted origin fuel revision mask

private def decodeProgram (json : Json) : Except String Wire.Program :=
  (Wire.decodeProgramWithBudget {maxDepth := 512, maxNodes := CallBranch.maxPhaseNodes, maxIntegerBytes := 4096}
    json).mapError (fun
    | .protocol error => error.toJson.compress
    | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)

private def sameProgram (json : Json) (expected : Wire.Program) : Except String Unit := do
  let program ← decodeProgram json
  unless Wire.encodeProgram program == Wire.encodeProgram expected do
    throw "saved original Core program differs from its canonical call-branch plan"

/-- Every origin must reconstruct the fixed host contracts, including imports
and reductions. Arbitrary well-typed programs are not admissible
replacements. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic call-branch case schema"
  let plan ← checkedPlan (← json.getObjVal? "callBranchPlan")
  let fuel ← json.getObjValAs? Nat "executionFuel"
  unless fuel ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let transactions ← decodeTransactions plan fuel (← json.getObjVal? "transactions")
  let originals ← json.getObjVal? "programs"
  sameProgram (← originals.getObjVal? "parentCall") plan.callProgram
  sameProgram (← originals.getObjVal? "parentResume") plan.resumeProgram
  sameProgram (← originals.getObjVal? "child") plan.childProgram
  unless originals == programsJson plan do throw "saved program roles are not canonical"
  unless (← json.getObjVal? "initialState") == CallReturn.initialStateJson do
    throw "initial accounts must be empty and unfunded"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson plan do
    throw "observed slots must be the parent's 0 to B + 4P and the child's 0 and 1"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Stateful.CallBranchExecution.observe scenario.plan scenario.transactions bindings fuel

/-! ### Generation -/

/-- SplitMix64's finalizer. The generator's draws are affine in its start, so
consecutive seeds would otherwise start streams whose draws step by a fixed
residue. -/
private def mixed (value : Nat) : Nat :=
  let z := value % 2 ^ 64
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9 % 2 ^ 64
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb % 2 ^ 64
  z ^^^ (z >>> 31)

/-- High halves of successive draws from the stream that starts at the mixed
`seed` xor `domain`, each below its bound. -/
private def boundedDraws (seed : Seed) (domain : Nat) (bounds : List Nat) : List Nat := Id.run do
  let mut state := Seed.ofNat (mixed (seed.toNat ^^^ domain))
  let mut values : Array Nat := #[]
  for bound in bounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- Per site: the kind, a loop's bound draw, a stop selector and a uniform stop,
then per window an offset selector and a uniform offset, a width selector and a
uniform width. -/
def siteBounds : List Nat := [2, 6, 20, 97] ++ (List.replicate 2 [18, 97, 8, 33]).flatten

/-- The site count, then three sites' draws. -/
def planBounds : List Nat := [3] ++ (List.replicate 3 siteBounds).flatten

def planChoices (seed : Seed) : List Nat := boundedDraws seed 0x6272632d706c616e planBounds

/-- The bank entry when the selector names one, otherwise the uniform draw. -/
private def banked (bank : List Nat) (selector uniform : Nat) : Nat :=
  if selector < bank.length then bank.getD selector 0 else uniform

/-- One to three sites, each a branch or a loop whose bound is uniform from one
to the positions left; sites stop once three positions are used. -/
def generatedSites (seed : Seed) : List Site := Id.run do
  let choices := planChoices seed
  let mut sites : Array Site := #[]
  let mut used := 0
  for index in List.range (1 + choices.getD 0 0) do
    if used < CallBranch.maxCalls then
      let at_ := fun position => choices.getD (1 + siteBounds.length * index + position) 0
      let spot := fun first : Nat => (⟨banked offsetBank (at_ first) (at_ (first + 1)),
        banked widthBank (at_ (first + 2)) (at_ (first + 3))⟩ : Window)
      let site : Site := if at_ 0 == 0 then ⟨.branch, 1, 0, spot 4, spot 8⟩
        else ⟨.loop, 1 + at_ 1 % (CallBranch.maxCalls - used), banked lengthBank (at_ 2) (at_ 3), spot 4, spot 8⟩
      sites := sites.push site
      used := used + site.bound
  return sites.toList

/-- Per transaction: per position the revert draw, a length selector and a
uniform length; per site a control draw; the parent's revert draw; and seven
32-bit parts of `input >> 32`. -/
def transactionBounds : List Nat :=
  (List.replicate 3 [3, 20, 97]).flatten ++ List.replicate 3 4 ++ [4] ++ List.replicate 7 (2 ^ 32)

def sequenceBounds : List Nat := (List.replicate 3 transactionBounds).flatten

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x6272632d74786e73 sequenceBounds

/-- An input from its draws: each position's class byte `2L + revert`, each
site's control bits, the parent's revert at bit 30 and the high part from bit
32. A branch takes one bit and a loop two. -/
def inputOf (sites : List Site) (draws : List Nat) : Word :=
  let positions := CallBranch.positions sites
  let classes := (List.range positions).map fun position =>
    let at_ := fun offset => draws.getD (3 * position + offset) 0
    2 * banked lengthBank (at_ 1) (at_ 2) + (if at_ 0 == 0 then 1 else 0)
  let low := classes.zipIdx.foldl (fun total (value, position) => total + value * 2 ^ (8 * position)) 0
  let control := sites.zipIdx.foldl (fun total (site, index) =>
    let draw := draws.getD (9 + index) 0
    let bits := match site.kind with
      | .branch => draw % 2
      | .loop => draw
    total + bits * 2 ^ CallBranch.controlBit index) 0
  let reverts := if draws.getD 12 0 == 0 then 2 ^ CallBranch.revertBit else 0
  let high := (List.range 7).foldl (fun total part => total * 2 ^ 32 + draws.getD (13 + part) 0) 0
  w (high * 2 ^ 32 + reverts + control + low)

def blockTransactions (sites : List Site) (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (List.range 3).map fun index =>
    ⟨"tx-" ++ toString (first + index), inputOf sites (choices.drop (transactionBounds.length * index))⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (sites : List Site) (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks (blockTransactions sites) seed count

/-- The child's shell lies inside the budget with the step, which the complete
measure bounds again. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let sites := generatedSites seed
  let shell := CallSequence.childShellNodes
  unless nodes ≤ maxStepNodes && shell < nodes do
    throw "node budget is too small for the call-branch child or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - shell) revision
  let some plan := CheckedPlan.ofParts? step sites | throw "generated call-branch plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions sites seed transactions)
  unless budgetNodes scenario.plan ≤ nodes do throw "call-branch child exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "call-branch-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("planChoices", toJson (planChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

/-- The history must complete with the model's outcomes. -/
def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless (← observed.getObjValAs? String "status") = "complete" do
    if rows.any (fun row => rowStatus row == some "out-of-fuel") then throw "call-branch history exhausted Core fuel"
    else throw "call-branch history stopped without a permitted root completion"
  let some expected := Stateful.CallBranchExecution.model scenario.plan fuel scenario.transactions
    | throw "call-branch history exhausted Core fuel"
  unless rows.map rowStatus == expected.map (fun row => some (if row.reverted then "reverted" else "returned")) do
    throw "call-branch history did not follow its prescribed outcomes"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        makeCase scenario emitted (origin.setObjVal! "validationFuel" (toJson fuel)) fuel revision (revision.caseMask seed)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "call-branch history exhausted Core fuel" || error == "call-branch model exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "call-branch-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok case => cases := cases.push case
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-! ### Reductions -/

/-- The windows' offsets and widths and the loops' stop lengths. -/
def siteWeight (plan : CheckedPlan) : Nat :=
  plan.sites.foldl (fun total site => total + site.callWindow.offset + site.callWindow.width +
    site.exitWindow.offset + site.exitWindow.width + site.stop) 0

def inputWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.input.val) 0

def scenarioComplexity (scenario : CheckedScenario) : Complexity := complexity scenario.plan.childProgram.body

/-- Transaction count, site count, positions, the windows and stops, the child's
size and literals, then the inputs. Every axis is a natural number and the
comparison is strictly lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (candidate.plan.sites.length < source.plan.sites.length ∨
    (candidate.plan.sites.length = source.plan.sites.length ∧
      (candidate.plan.positions < source.plan.positions ∨
      (candidate.plan.positions = source.plan.positions ∧
        (siteWeight candidate.plan < siteWeight source.plan ∨
        (siteWeight candidate.plan = siteWeight source.plan ∧
          ((scenarioComplexity candidate).StrictlySmaller (scenarioComplexity source) ∨
          (scenarioComplexity candidate = scenarioComplexity source ∧
            inputWeight candidate < inputWeight source)))))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (sites : List Site)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step sites
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

/-- The earlier entries of a bank before `value`, or the whole bank when it is
not in it, below `value`. -/
private def earlier (bank : List Nat) (value : Nat) : List Nat :=
  (bank.take ((bank.idxOf? value).getD bank.length)).filter (· < value)

/-- A window's smaller variants: an earlier offset, then an earlier or zero
width. -/
private def smallerWindows (spot : Window) : List Window :=
  (earlier offsetBank spot.offset).map (fun offset => {spot with offset}) ++
    (earlier widthBank spot.width ++ (if spot.width > 0 then [0] else [])).eraseDups.map fun width => {spot with width}

/-- An input's smaller variants: the parent's revert cleared, the high part
cleared, each control bit cleared, and per class byte its revert cleared and
its length an earlier bank entry, then zero. -/
def smallerInputs (input : Word) : List Word :=
  let value := input.val
  let byte := fun position => value / 2 ^ (8 * position) % 256
  let replace := fun position (next : Nat) => w (value - byte position * 2 ^ (8 * position) + next * 2 ^ (8 * position))
  let revert := if value / 2 ^ CallBranch.revertBit % 2 == 1 then [w (value - 2 ^ CallBranch.revertBit)] else []
  let high := if value ≥ 2 ^ 32 then [w (value % 2 ^ 32)] else []
  let controls := (List.range 6).filterMap fun offset =>
    let bit := 24 + offset
    if value / 2 ^ bit % 2 == 1 then some (w (value - 2 ^ bit)) else none
  let classes := (List.range CallBranch.maxCalls).flatMap fun position =>
    let class_ := byte position
    let length := min (class_ / 2) CallSequence.capacity
    (if class_ % 2 == 1 then [replace position (class_ - 1)] else []) ++
      ((earlier lengthBank length ++ (if length > 0 then [0] else [])).eraseDups.map fun shorter =>
        replace position (2 * shorter + class_ % 2))
  revert ++ high ++ controls ++ classes

/-- One-transaction removals, the last site dropped, a loop's bound lowered,
earlier or narrower windows and earlier stops, step reductions, then per
transaction each smaller input. Candidates still need execution to establish
that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let sites := source.plan.sites
  let mut raw : List (Aggregates.CheckedDAG × List Site × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, sites,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  if sites.length > 1 then
    raw := raw ++ [(source.plan.step, sites.dropLast, source.transactions)]
  for (site, index) in sites.zipIdx do
    if site.kind == .loop && site.bound > 1 then
      raw := raw ++ [(source.plan.step, sites.set index {site with bound := site.bound - 1}, source.transactions)]
  for (site, index) in sites.zipIdx do
    for spot in smallerWindows site.callWindow do
      raw := raw ++ [(source.plan.step, sites.set index {site with callWindow := spot}, source.transactions)]
    for spot in smallerWindows site.exitWindow do
      raw := raw ++ [(source.plan.step, sites.set index {site with exitWindow := spot}, source.transactions)]
    for stop in earlier lengthBank site.stop do
      raw := raw ++ [(source.plan.step, sites.set index {site with stop}, source.transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, sites, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    for input in smallerInputs transaction.input do
      let transactions := source.transactions.set index {transaction with input}
      raw := raw ++ [(source.plan.step, sites, transactions)]
  let mut seen : List String := []
  let mut result := []
  for (step, sites, transactions) in raw do
    if let some reduced := sealReduction source step sites transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", toJson (reduced.candidate.transactions.map fun tx => toString tx.input.val ++ tx.id))]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def sequenceJson (transactions : List Transaction) : Json :=
  toJson (transactions.map fun tx => Json.mkObj [("id", toJson tx.id), ("input", toJson (toString tx.input.val))])

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentPrograms", programsJson parent.plan), ("parentTransactions", sequenceJson parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", CallSequence.childVersion), ("parentVersion", CallBranch.parentVersion),
      ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  let sources ← json.getObjVal? "sources"
  unless (← sources.getObjValAs? String "parent") = emitted.parentSource &&
      (← sources.getObjValAs? String "child") = emitted.childSource &&
      sources == Json.mkObj [("parent", toJson emitted.parentSource), ("child", toJson emitted.childSource)] do
    throw "saved sources differ from call-branch plan emission"
  unless (← json.getObjVal? "contracts") == CallReturn.contractsJson do
    throw "saved contract metadata differs from call-branch wrappers"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "call-branch-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated call-branch provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        sequenceJson expected.transactions == sequenceJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← CallReturn.decodeSequence (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentPrograms") == programsJson parent.plan do
      throw "reduction parent programs differ from their plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.sites admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported call-branch case origin"
  makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced =>
    emitCase reduced.candidate (reducedOrigin source) fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

/-! ### Imported scenarios -/

/-- An imported plan and transaction sequence. -/
def checkedImport (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario :=
  checkedScenario plan transactions

end Solcore.Synthesis.Source.CallBranch
