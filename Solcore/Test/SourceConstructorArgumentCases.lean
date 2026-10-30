import Solcore.Synthesis.Source.ConstructorArgumentsCases

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
