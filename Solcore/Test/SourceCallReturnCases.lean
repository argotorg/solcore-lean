import Solcore.Synthesis.Source.CallReturnCases

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
