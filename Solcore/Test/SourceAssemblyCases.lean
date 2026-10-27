import Solcore.Synthesis.Source.AssemblyCases

/-! The `runtime-assembly` profile. Its Core reference is the `runtime-primitives`
function of the same seed, budget and revision, with the same inputs,
observations and exclusions. Each form renders the whole body in one
`assembly` block, as `switch` or as two Yul `if`s, or puts each operation in its
own block under Solcore control flow. Generation draws all three forms and
replays exactly; tampering is refused, and reductions are the primitive
reductions in the parent's form. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyCases

open Lean
open Solcore.Core (Word)
open Solcore.Core.Wire (Expr)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.AssemblyRenderer (Form)

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
  return case.setObjVal! "assemblyPlan" (change (← get (case.getObjVal? "assemblyPlan")))

private def other : Form → Form
  | .switch => .branches
  | .branches => .operations
  | .operations => .switch

/-- `let a = input + 1 in if !(a == 5) then a << input else mulmod(input, ~a, 0)`. -/
private def fixture : Expr :=
  .letE (.binary .wordAdd (.var 0) (word 1))
    (.ifE (.unary .boolNot (.binary .wordEq (.var 0) (word 5)))
      (.binary .wordShl (.var 0) (.var 1))
      (.ternary .wordMulMod (.var 1) (.unary .wordNot (.var 0)) (word 0)))

private def header : List String :=
  ["import * from std;", "import * from std.dispatch;", "", "contract SynthesizedAssembly {",
    "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"]

private def footer (value : String) : List String :=
  ["        return uint256(" ++ value ++ ");", "    }", "}"]

private def wholeBody (yul : List String) (result : String) : String :=
  String.intercalate "\n" (header ++ ["        let sc_out: word = 0;", "        assembly {"] ++
    yul.map ("            " ++ ·) ++ ["            sc_out := " ++ result, "        }"] ++ footer "sc_out") ++ "\n"

/-- The exact source of each form for the fixture. -/
private def golden : Form → String
  | .switch => wholeBody ["let sc_y0 := add(sc_input, 1)", "let sc_y1 := 0", "switch iszero(eq(sc_y0, 5))",
      "case 0 {", "    sc_y1 := mulmod(sc_input, not(sc_y0), 0)", "}", "default {", "    sc_y1 := shl(sc_input, sc_y0)",
      "}"] "sc_y1"
  | .branches => wholeBody ["let sc_y0 := add(sc_input, 1)", "let sc_y1 := iszero(eq(sc_y0, 5))", "let sc_y2 := 0",
      "if sc_y1 {", "    sc_y2 := shl(sc_input, sc_y0)", "}", "if iszero(sc_y1) {",
      "    sc_y2 := mulmod(sc_input, not(sc_y0), 0)", "}"] "sc_y2"
  | .operations => String.intercalate "\n" (header ++ [
      "        let sc_v0: word = 1;", "        let sc_v1: word = 0;", "        assembly {",
      "            sc_v1 := add(sc_input, sc_v0)", "        }", "        let sc_v2: word = sc_v1;",
      "        let sc_v3: word = 5;", "        let sc_v4: word = 0;", "        assembly {",
      "            sc_v4 := eq(sc_v2, sc_v3)", "        }", "        let sc_v5: bool = tobool(sc_v4);",
      "        let sc_v6: bool = (!sc_v5);", "        let sc_v7: word = 0;", "        if (sc_v6) {",
      "            let sc_v8: word = 0;", "            assembly {", "                sc_v8 := shl(sc_input, sc_v2)",
      "            }", "            sc_v7 = sc_v8;", "        } else {", "            let sc_v9: word = 0;",
      "            assembly {", "                sc_v9 := not(sc_v2)", "            }",
      "            let sc_v10: word = 0;", "            let sc_v11: word = 0;", "            assembly {",
      "                sc_v11 := mulmod(sc_input, sc_v9, sc_v10)", "            }", "            sc_v7 = sc_v11;",
      "        }"] ++ footer "sc_v7") ++ "\n"

private def directWord (case : Json) : IO Nat := do
  let text ← get ((← get (case.getObjVal? "directCore")).getObjValAs? String "word")
  let some value := text.toNat? | throw (IO.userError "invalid result Word")
  return value

private def formChecks : IO Unit := do
  ensure (Form.all.map Form.name == ["switch", "if", "operations"] &&
      Form.all.all (fun form => Form.ofString? form.name == some form) && Form.ofString? "branches" == none)
    "assembly form names changed"
  ensure (Assembly.featureSupport == Primitive.featureSupport && Assembly.featureSupport == FeatureMask.all)
    "the inline Yul renderer does not render every primitive feature"
  let some function := CheckedWordFunction.ofBody? fixture | throw (IO.userError "fixture refused")
  for form in Form.all do
    let emitted ← get ((Assembly.emit form function).mapError reprStr)
    ensure (emitted.source == golden form) s!"{form.name}: the emitted source differs from its golden text"
    for (input, result) in [(4, 0), (7, 1024)] do
      let case ← get (Assembly.emitCase ⟨function, form⟩ (Word.ofNatModulo input)
        (Json.mkObj [("kind", toJson "imported")]) fuel)
      ensure ((← directWord case) == result) s!"{form.name}: the Core reference of input {input} changed"
      ensure ((← get (Assembly.replayCase case fuel)) == case) s!"{form.name}: an imported case failed exact replay"
  let plan := Assembly.planJson ⟨function, .switch⟩
  for (changed, error) in [
      (plan.setObjVal! "form" (toJson "loop"), "assembly form must be switch, if or operations"),
      (plan.setObjVal! "extra" (toJson (1 : Nat)), "saved assembly plan differs from its canonical checked representation"),
      (plan.setObjVal! "schema" (toJson "solcore-lean.recursion-plan.v1"), "unsupported assembly plan schema")] do
    ensure (errorOf (Assembly.checkedPlan changed) == some error) s!"a tampered plan was not refused with: {error}"

/-- The fields both profiles' cases must share for one seed, budget and
revision: the Core reference, the input, its observation and every generation
record apart from the form. -/
private def agrees (assembly primitive : Json) : IO Bool := do
  let (a, p) := (← provenance assembly, ← provenance primitive)
  let some seed := (← get ((← origin assembly).getObjValAs? String "seed")).toNat? |
    throw (IO.userError "invalid seed")
  let expected := ((← origin primitive).setObjVal! "kind" (toJson "assembly-generated")).setObjVal! "form"
    (toJson (Assembly.formFor (Seed.ofNat seed)).name)
  return (← origin assembly) == expected &&
    ["program", "input", "directCore", "executionFuel"].all (fun key =>
      (assembly.getObjVal? key).toOption == (primitive.getObjVal? key).toOption) &&
    ["generatorVersion", "baseGeneratorVersion", "boundaryVersion", "functionVersion", "abstractionVersion",
      "features", "swarmMask"].all (fun key => (a.getObjVal? key).toOption == (p.getObjVal? key).toOption) &&
    (a.getObjValAs? String "functionProfileVersion").toOption == some Primitive.profileVersion

private def exclusion (entry : Json) : List (Option Json) :=
  ["seed", "reason", "code", "category"].map fun key => (entry.getObjVal? key).toOption

/-- The roadmap's requirement: the same function as `runtime-primitives`. -/
private def agreementChecks : IO Unit := do
  for (revision, nodes, inputs, acceptance) in [
      (GeneratorRevision.v1, 96, InputSelection.boundary, Acceptance.profile),
      (.v4, 96, .seeded, .nonIdentity), (.v4, 200, .boundary, .profile), (.v3, 128, .boundary, .nonIdentity)] do
    let assembly := Assembly.generateCases (Seed.ofNat 1) nodes 1024 40 fuel revision inputs acceptance
    let primitive := Primitive.generateCases (Seed.ofNat 1) nodes 1024 40 fuel revision inputs acceptance
    let (a, p) := (← cases assembly, ← cases primitive)
    ensure (a.size == p.size && a.size ≥ 64) s!"{revision.version}: the two profiles accepted different functions"
    for (case, index) in a.zipIdx do
      ensure (← agrees case p[index]!) s!"{revision.version}: case {index} differs from the primitive function"
    ensure ((← excluded assembly).map exclusion == (← excluded primitive).map exclusion)
      s!"{revision.version}: the two profiles excluded different seeds or for different reasons"
    ensure ((assembly.getObjVal? "attempted").toOption == (primitive.getObjVal? "attempted").toOption)
      s!"{revision.version}: the two profiles attempted different numbers of seeds"

private def generationChecks : IO (Array Json) := do
  let corpus := Assembly.generateCases (Seed.ofNat 1) 96 1024 60 fuel .v4
  ensure (corpus == Assembly.generateCases (Seed.ofNat 1) 96 1024 60 fuel .v4) "assembly generation is not deterministic"
  let generated ← cases corpus
  let mut forms : List String := []
  for case in generated do
    let form ← get ((← get (case.getObjVal? "assemblyPlan")).getObjValAs? String "form")
    let some seed := (← get ((← origin case).getObjValAs? String "seed")).toNat? | throw (IO.userError "invalid seed")
    ensure (form == (Assembly.formFor (Seed.ofNat seed)).name) "a case's form is not its seed's form"
    ensure ((← get ((← origin case).getObjValAs? String "form")) == form) "a case's origin records another form"
    forms := form :: forms
  ensure (forms.eraseDups.length == 3) s!"generation drew {forms.eraseDups.length} of three forms"
  return generated

/-- One generated case of each form. -/
private def representatives (generated : Array Json) : IO (List Json) := do
  let mut chosen : List Json := []
  let mut forms : List String := []
  for case in generated do
    let form ← get ((← get (case.getObjVal? "assemblyPlan")).getObjValAs? String "form")
    if !forms.contains form then
      forms := form :: forms
      chosen := chosen ++ [case]
  return chosen

private def replayChecks (case : Json) : IO Unit := do
  ensure ((← get (Assembly.replayCase case fuel)) == case) "a generated assembly case failed exact replay"
  let admitted ← get (Assembly.caseProgram case)
  let form := admitted.plan.form
  let provenanceJson ← provenance case
  let revision := savedPureRevision provenanceJson "baseGeneratorVersion"
  let mask ← get (savedMask provenanceJson revision Assembly.featureSupport)
  -- A consistent case of another form, with the seed's own origin and source.
  let relabeled ← get (Assembly.emitCase ⟨admitted.plan.function, other form⟩ admitted.input (← origin case) fuel
    revision mask)
  ensure (errorOf (Assembly.replayCase relabeled fuel) == some "saved assembly form differs from its generation seed")
    "a generated case replayed in another form"
  for changed in [
      ← withPlan case (·.setObjVal! "form" (toJson (other form).name)),
      ← withPlan case (·.setObjVal! "functionProgram" (Solcore.Core.Wire.encodeProgram
        (wordFunctionProgram (.binary .wordAdd (.var 0) (word 1))))),
      ← withOrigin case (·.setObjVal! "form" (toJson (other form).name)),
      case.setObjVal! "source" (toJson ((← get (case.getObjValAs? String "source")) ++ "\n"))] do
    ensure (Assembly.replayCase changed fuel matches .error _) "a tampered assembly case replayed"

private def reductionChecks (case : Json) : IO Unit := do
  let source ← get (Assembly.caseProgram case)
  let primitive := Primitive.reductions ⟨source.plan.function, source.input⟩
  let reduced := Assembly.reductions source
  ensure (!reduced.isEmpty && reduced.length == primitive.length) "the reductions are not the primitive reductions"
  for (candidate, expected) in reduced.zip primitive do
    ensure (candidate.candidate.plan.form == source.plan.form) "a reduction changed the form"
    ensure (Solcore.Core.Wire.encodeProgram candidate.candidate.program == Solcore.Core.Wire.encodeProgram expected.candidate.program)
      "a reduction differs from the primitive reduction"
  let emitted ← cases (← get (Assembly.shrinkCases case 4 fuel))
  ensure (!emitted.isEmpty) "an assembly case has no reduction"
  for candidate in emitted do
    ensure ((← get (Assembly.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
    let form := (← get (Assembly.caseProgram candidate)).plan.form
    ensure (form == source.plan.form) "an emitted reduction changed the form"
    let moved ← withOrigin candidate fun saved =>
      saved.setObjVal! "parentPlan" (Assembly.planJson ⟨source.plan.function, other form⟩)
    ensure (errorOf (Assembly.replayCase moved fuel) == some "saved assembly reduction changes its parent's form")
      "a reduction claimed a parent of another form"

def testSourceAssemblyCases : IO Unit := do
  formChecks
  agreementChecks
  let generated ← generationChecks
  for case in ← representatives generated do
    replayChecks case
    reductionChecks case

end Tests.SourceAssemblyCases
