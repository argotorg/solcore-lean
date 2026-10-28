import Solcore.Synthesis.Source.AssemblyLoopCases

/-! The `runtime-assembly-loops` profile. Its Core reference is the
`runtime-call-graph-loops` plan of the same seed and budget, with the same
inputs, observations and exclusions. Each form renders the whole plan in one
`assembly` block, with the helpers as Yul functions and the loop as a Yul `for`
loop bounded by its condition, exited by `break` or `leave`, or skipping the
step with `continue`, or advanced by a two-result step function. Generation
draws all fifteen shapes and replays exactly; tampering is refused, and
reductions are the call-graph loop reductions in the parent's form. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyLoopCases

open Lean
open Solcore.Core (Word)
open Solcore.Core.Wire (Expr)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.AssemblyLoop (Form)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def errorOf {α : Type} : Except String α → Option String
  | .error error => some error
  | .ok _ => none

private def fuel : Nat := 1000000

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def excluded (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "excluded")

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def origin (case : Json) : IO Json := do get ((← provenance case).getObjVal? "origin")

private def withOrigin (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "provenance" ((← provenance case).setObjVal! "origin" (change (← origin case)))

private def withPlan (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "assemblyLoopPlan" (change (← get (case.getObjVal? "assemblyLoopPlan")))

private def other : Form → Form
  | .bounded => .breaks
  | .breaks => .continues
  | .continues => .leaves
  | .leaves => .pair
  | .pair => .bounded

/-- `h0(a) = if a > 5 then a * 3 else a + 1`, `h1(a) = let b = h0(a) in b ^ a`
and the entry `let b = h1(a) in b + h0(b)`. -/
private def helpers : List Expr := [
  .ifE (.binary .wordGt (.var 0) (word 5)) (.binary .wordMul (.var 0) (word 3))
    (.binary .wordAdd (.var 0) (word 1)),
  .letE (.apply (.var 1) (.var 0)) (.binary .wordXor (.var 0) (.var 1))]

private def entry : Expr :=
  .letE (.apply (.var 1) (.var 0)) (.binary .wordAdd (.var 0) (.apply (.var 3) (.var 0)))

private def fixture : IO CallGraphLoop.CheckedPlan := do
  let some graph := CheckedWordFunctionDAG.ofParts? helpers entry | throw (IO.userError "fixture graph refused")
  let some plan := CallGraphLoop.CheckedPlan.ofParts? graph 3 | throw (IO.userError "fixture plan refused")
  return plan

private def wrapper (yul : List String) : String :=
  String.intercalate "\n" (["import * from std;", "import * from std.dispatch;", "",
    "contract SynthesizedAssemblyLoops {", "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);", "        let sc_out: word = 0;", "        assembly {"] ++
    yul.map ("            " ++ ·) ++ ["        }", "        return uint256(sc_out);", "    }", "}"]) ++ "\n"

private def helperLines : List String := [
  "function sc_fn0(sc_arg) -> sc_ret {", "    let sc_y0 := 0", "    switch gt(sc_arg, 5)", "    case 0 {",
  "        sc_y0 := add(sc_arg, 1)", "    }", "    default {", "        sc_y0 := mul(sc_arg, 3)", "    }",
  "    sc_ret := sc_y0", "}",
  "function sc_fn1(sc_arg) -> sc_ret {", "    let sc_y1 := sc_fn0(sc_arg)", "    sc_ret := xor(sc_y1, sc_arg)", "}"]

private def header : List String := ["let sc_limit := and(sc_input, 3)", "let sc_acc := sc_input"]

private def inlineStep : List String :=
  ["    let sc_y2 := sc_fn1(sc_acc)", "    sc_acc := add(sc_y2, sc_fn0(sc_y2))", "}", "sc_out := sc_acc"]

/-- The exact source of each form for the fixture. -/
private def golden : Form → String
  | .bounded => wrapper (helperLines ++ header ++
      ["for { let sc_i := 0 } lt(sc_i, sc_limit) { sc_i := add(sc_i, 1) } {"] ++ inlineStep)
  | .breaks => wrapper (helperLines ++ header ++ ["for { let sc_i := 0 } 1 { sc_i := add(sc_i, 1) } {",
      "    if iszero(lt(sc_i, sc_limit)) { break }"] ++ inlineStep)
  | .continues => wrapper (helperLines ++ ["function sc_bound() -> sc_ret {", "    sc_ret := 3", "}"] ++ header ++
      ["for { let sc_i := 0 } lt(sc_i, sc_bound()) { sc_i := add(sc_i, 1) } {",
        "    if iszero(lt(sc_i, sc_limit)) { continue }"] ++ inlineStep)
  | .leaves => wrapper [
      "function sc_fn0(sc_arg) -> sc_ret {", "    if gt(sc_arg, 5) {", "        sc_ret := mul(sc_arg, 3)",
      "        leave", "    }", "    sc_ret := add(sc_arg, 1)", "}",
      "function sc_fn1(sc_arg) -> sc_ret {", "    let sc_y0 := sc_fn0(sc_arg)", "    sc_ret := xor(sc_y0, sc_arg)", "}",
      "function sc_loop(sc_acc, sc_limit) -> sc_ret {", "    sc_ret := sc_acc",
      "    for { let sc_i := 0 } 1 { sc_i := add(sc_i, 1) } {", "        if iszero(lt(sc_i, sc_limit)) { leave }",
      "        let sc_y1 := sc_fn1(sc_ret)", "        sc_ret := add(sc_y1, sc_fn0(sc_y1))", "    }", "}",
      "sc_out := sc_loop(sc_input, and(sc_input, 3))"]
  | .pair => wrapper ([
      "function sc_fn0(sc_arg) -> sc_ret, sc_aux {", "    let sc_y0 := 0", "    switch gt(sc_arg, 5)", "    case 0 {",
      "        sc_y0 := add(sc_arg, 1)", "    }", "    default {", "        sc_y0 := mul(sc_arg, 3)", "    }",
      "    sc_ret := sc_y0", "    sc_aux := sc_arg", "}",
      "function sc_fn1(sc_arg) -> sc_ret, sc_aux {", "    let sc_y1, sc_y2 := sc_fn0(sc_arg)", "    let sc_y3 := sc_y1",
      "    sc_ret := xor(sc_y3, sc_arg)", "    sc_aux := sc_arg", "}",
      "function sc_iterate(sc_arg, sc_count) -> sc_ret, sc_next {", "    let sc_y4, sc_y5 := sc_fn1(sc_arg)",
      "    let sc_y6 := sc_y4", "    let sc_y7, sc_y8 := sc_fn0(sc_y6)", "    sc_ret := add(sc_y6, sc_y7)",
      "    sc_next := add(sc_count, 1)", "}"] ++ header ++
      ["let sc_i := 0", "for { } lt(sc_i, sc_limit) { } {", "    sc_acc, sc_i := sc_iterate(sc_acc, sc_i)", "}",
        "sc_out := sc_acc"])

private def directWord (case : Json) : IO Nat := do
  let text ← get ((← get (case.getObjVal? "directCore")).getObjValAs? String "word")
  let some value := text.toNat? | throw (IO.userError "invalid result Word")
  return value

/-- Golden sources, the Core reference of the fixture at inputs of zero to three
iterations, and refused plans. -/
private def formChecks : IO Unit := do
  ensure (Form.all.map Form.name == ["for", "break", "continue", "leave", "pair"] &&
      Form.all.all (fun form => Form.ofString? form.name == some form) && Form.ofString? "bounded" == none)
    "assembly loop form names changed"
  let loop ← fixture
  for form in Form.all do
    let emitted ← get ((AssemblyLoop.emit form loop).mapError reprStr)
    ensure (emitted.source == golden form) s!"{form.name}: the emitted source differs from its golden text"
    for (input, result) in [(0, 0), (1, 7), (2, 28), (3, 2304), (4, 4), (7, 4608)] do
      let case ← get (AssemblyLoop.emitCase ⟨loop, form⟩ (Word.ofNatModulo input)
        (Json.mkObj [("kind", toJson "imported")]) fuel)
      ensure ((← directWord case) == result) s!"{form.name}: the Core reference of input {input} changed"
      ensure ((← get (AssemblyLoop.replayCase case fuel)) == case) s!"{form.name}: an imported case failed exact replay"
  let plan := AssemblyLoop.planJson ⟨loop, .bounded⟩
  for (changed, error) in [
      (plan.setObjVal! "form" (toJson "while"), "assembly loop form must be for, break, continue, leave or pair"),
      (plan.setObjVal! "extra" (toJson (1 : Nat)),
        "saved assembly loop plan differs from its canonical checked representation"),
      (plan.setObjVal! "mask" (toJson (5 : Nat)),
        "call-graph loop plan has an invalid mask or failed the full Core checker"),
      (plan.setObjVal! "schema" (toJson "solcore-lean.call-graph-loop-plan.v1"),
        "unsupported assembly loop plan schema")] do
    ensure (errorOf (AssemblyLoop.checkedPlan changed) == some error) s!"a tampered plan was not refused with: {error}"

/-- The fields both profiles' cases must share for one seed and budget: the Core
reference, the input, its observation and every generation record apart from
the form. -/
private def agrees (assembly loop : Json) : IO Bool := do
  let (a, l) := (← provenance assembly, ← provenance loop)
  let some seed := (← get ((← origin assembly).getObjValAs? String "seed")).toNat? |
    throw (IO.userError "invalid seed")
  let expected := ((← origin loop).setObjVal! "kind" (toJson "assembly-loop-generated")).setObjVal! "form"
    (toJson (AssemblyLoop.formFor (Seed.ofNat seed)).name)
  return (← origin assembly) == expected &&
    ["program", "input", "directCore", "executionFuel"].all (fun key =>
      (assembly.getObjVal? key).toOption == (loop.getObjVal? key).toOption) &&
    ["generatorVersion", "functionVersion", "loopVersion", "stepFunctionVersion", "aggregateVersion",
      "boundaryVersion", "stepBoundaryVersion", "callShapeVersion", "features", "helperCount", "callShapes"].all
      (fun key => (a.getObjVal? key).toOption == (l.getObjVal? key).toOption) &&
    (a.getObjValAs? String "loopProfileVersion").toOption == some CallGraphLoop.profileVersion &&
    ((← get (assembly.getObjVal? "assemblyLoopPlan")).setObjVal! "form" .null).setObjVal! "schema" .null ==
      ((← get (loop.getObjVal? "loopPlan")).setObjVal! "form" .null).setObjVal! "schema" .null

private def exclusion (entry : Json) : List (Option Json) :=
  ["seed", "reason", "code", "category"].map fun key => (entry.getObjVal? key).toOption

/-- The roadmap's requirement: the same plan as `runtime-call-graph-loops`. -/
private def agreementChecks : IO Unit := do
  for (nodes, inputs) in [(256, InputSelection.boundary), (256, .seeded), (128, .boundary), (384, .seeded)] do
    let assembly := AssemblyLoop.generateCases (Seed.ofNat 1) nodes 1024 60 fuel inputs
    let loop := CallGraphLoop.generateCases (Seed.ofNat 1) nodes 1024 60 fuel inputs
    let (a, l) := (← cases assembly, ← cases loop)
    ensure (a.size == l.size && a.size ≥ 60) s!"{nodes}: the two profiles accepted different plans"
    for (case, index) in a.zipIdx do
      ensure (← agrees case l[index]!) s!"{nodes}: case {index} differs from the call-graph loop plan"
    ensure ((← excluded assembly).map exclusion == (← excluded loop).map exclusion)
      s!"{nodes}: the two profiles excluded different seeds or for different reasons"
    ensure ((assembly.getObjVal? "attempted").toOption == (loop.getObjVal? "attempted").toOption)
      s!"{nodes}: the two profiles attempted different numbers of seeds"

/-- The lines that only the form's loop has. -/
private def marker : Form → String
  | .bounded => "            for { let sc_i := 0 } lt(sc_i, sc_limit) { sc_i := add(sc_i, 1) } {"
  | .breaks => "                if iszero(lt(sc_i, sc_limit)) { break }"
  | .continues => "                if iszero(lt(sc_i, sc_limit)) { continue }"
  | .leaves => "                    if iszero(lt(sc_i, sc_limit)) { leave }"
  | .pair => "                sc_acc, sc_i := sc_iterate(sc_acc, sc_i)"

private def generationChecks : IO (Array Json) := do
  let corpus := AssemblyLoop.generateCases (Seed.ofNat 1) 256 1020 1000 fuel
  ensure (corpus == AssemblyLoop.generateCases (Seed.ofNat 1) 256 1020 1000 fuel)
    "assembly loop generation is not deterministic"
  let generated ← cases corpus
  ensure (generated.size == 1020) "assembly loop generation did not complete"
  let mut shapes : List String := []
  for case in generated do
    let admitted ← get (AssemblyLoop.caseProgram case)
    let form := admitted.plan.form
    let some seed := (← get ((← origin case).getObjValAs? String "seed")).toNat? | throw (IO.userError "invalid seed")
    ensure (form == AssemblyLoop.formFor (Seed.ofNat seed)) "a case's form is not its seed's form"
    ensure ((← get ((← origin case).getObjValAs? String "form")) == form.name) "a case's origin records another form"
    let source ← get (case.getObjValAs? String "source")
    ensure ((source.splitOn "assembly {").length == 2 && (source.splitOn (marker form)).length == 2 &&
        Form.all.all (fun candidate => candidate == form || (source.splitOn (marker candidate)).length == 1))
      s!"{form.name}: the source lacks its form's loop or has another form's"
    ensure ((source.splitOn "            function sc_fn").length == admitted.plan.loop.graph.helpers.length + 1)
      s!"{form.name}: the source does not define one Yul function per helper"
    shapes := s!"{admitted.plan.loop.mask}:{form.name}" :: shapes
  ensure (shapes.eraseDups.length == 15) s!"generation drew {shapes.eraseDups.length} of fifteen shapes"
  return generated

/-- One generated case of each form. -/
private def representatives (generated : Array Json) : IO (List Json) := do
  let mut chosen : List Json := []
  let mut forms : List Form := []
  for case in generated do
    let form := (← get (AssemblyLoop.caseProgram case)).plan.form
    if !forms.contains form then
      forms := form :: forms
      chosen := chosen ++ [case]
  return chosen

private def replayChecks (case : Json) : IO Unit := do
  ensure ((← get (AssemblyLoop.replayCase case fuel)) == case) "a generated assembly loop case failed exact replay"
  let admitted ← get (AssemblyLoop.caseProgram case)
  let form := admitted.plan.form
  -- A consistent case of another form, with the seed's own origin and source.
  let relabeled ← get (AssemblyLoop.emitCase ⟨admitted.plan.loop, other form⟩ admitted.input (← origin case) fuel)
  ensure (errorOf (AssemblyLoop.replayCase relabeled fuel) ==
      some "saved assembly loop form differs from its generation seed")
    "a generated case replayed in another form"
  let mask := admitted.plan.loop.mask
  for changed in [
      ← withPlan case (·.setObjVal! "form" (toJson (other form).name)),
      ← withPlan case (·.setObjVal! "mask" (toJson (if mask == 7 then 3 else 7))),
      ← withOrigin case (·.setObjVal! "form" (toJson (other form).name)),
      ← withOrigin case (·.setObjVal! "kind" (toJson "call-graph-loop-generated")),
      case.setObjVal! "source" (toJson ((← get (case.getObjValAs? String "source")) ++ "\n"))] do
    ensure (AssemblyLoop.replayCase changed fuel matches .error _) "a tampered assembly loop case replayed"

private def reductionChecks (case : Json) : IO Unit := do
  let source ← get (AssemblyLoop.caseProgram case)
  let loop := CallGraphLoop.reductions ⟨source.plan.loop, source.input⟩
  let reduced := AssemblyLoop.reductions source
  ensure (!reduced.isEmpty && reduced.length == loop.length) "the reductions are not the call-graph loop reductions"
  for (candidate, expected) in reduced.zip loop do
    ensure (candidate.candidate.plan.form == source.plan.form) "a reduction changed the form"
    ensure (Solcore.Core.Wire.encodeProgram candidate.candidate.program ==
        Solcore.Core.Wire.encodeProgram expected.candidate.program)
      "a reduction differs from the call-graph loop reduction"
  let emitted ← cases (← get (AssemblyLoop.shrinkCases case 4 fuel))
  ensure (!emitted.isEmpty) "an assembly loop case has no reduction"
  for candidate in emitted do
    ensure ((← get (AssemblyLoop.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
    let form := (← get (AssemblyLoop.caseProgram candidate)).plan.form
    ensure (form == source.plan.form) "an emitted reduction changed the form"
    let moved ← withOrigin candidate fun saved =>
      saved.setObjVal! "parentPlan" (AssemblyLoop.planJson ⟨source.plan.loop, other form⟩)
    ensure (errorOf (AssemblyLoop.replayCase moved fuel) ==
        some "saved assembly loop reduction changes its parent's form")
      "a reduction claimed a parent of another form"

def testSourceAssemblyLoopCases : IO Unit := do
  formChecks
  agreementChecks
  let generated ← generationChecks
  for case in ← representatives generated do
    replayChecks case
    reductionChecks case

end Tests.SourceAssemblyLoopCases
