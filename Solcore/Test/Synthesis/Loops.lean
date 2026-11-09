import Solcore.Synthesis.Internal.Assembly
import Solcore.Synthesis.Internal.Storage
import Solcore.Abi.Keccak256
import Solcore.Synthesis.Internal.StorageLoops
import Solcore.Synthesis.Internal.Loops
import Solcore.Core.Machine

/-!
# Loop profile tests

Loops, nested loops, storage and Keccak loops, and inline assembly.
-/

section
-- leanmerge: from Solcore.Test.SourceAssemblyCases
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
  ["pragma solcore;", "import * from std;", "import * from std.dispatch;", "",
    "contract SynthesizedAssembly {",
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
end

section
-- leanmerge: from Solcore.Test.SourceAssemblyKeccakLoopCases
/-! Generated inline Yul Keccak-loop cases. For the same seed, budget, G0
revision and transaction count, generation must agree with the Keccak-loop
profile: the same attempts and exclusions, and per case the same plan,
original Core program, transactions, initial state, observed slots, fuel and
observation, with an origin that differs only in its kind and recorded form.
The form must be the seed's, every form must be drawn, and each source must
have its form's blocks and call no std storage, hash, log or revert wrapper.
Each case must replay to itself, and every reduction keeps the parent case's
form and replays. An unknown form, a Keccak-loop plan or case schema and a
form that its source was not emitted in are refused. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyKeccakLoopCases

open Lean
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Source.AssemblyStorage (Form)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def occurs (text part : String) : Bool := (text.splitOn part).length > 1

/-- The marks of a form: `split` writes through a fresh hash, `carried`
advances the counter in Yul without a conditional read, and `pipelined` reads
under two conditionals, before the loop and after the writes. -/
private def hasForm (source : String) : Form → Bool
  | .split => occurs source "sstore(keccak256(sc_ptr, 64), sc_value)" && !occurs source "sc_counter := add(sc_counter, 1)"
  | .carried => occurs source "sc_counter := add(sc_counter, 1)" && !occurs source "if gt(sc_limit, sc_counter)"
  | .pipelined => (source.splitOn "if gt(sc_limit, sc_counter)").length == 3

/-- The Keccak-loop case fields that an inline Yul case keeps. -/
private def kept : List String := ["program", "transactions", "initialState", "observedSlots", "executionFuel"]

def testSourceAssemblyKeccakLoopCases : IO Unit := do
  let fuel := 1000000
  let mut forms : List Form := []
  let mut cases : Array Json := #[]
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three.
  for (revision, transactions, count) in [(GeneratorRevision.v3, 8, 4), (GeneratorRevision.v1, 3, 4)] do
    let generated := Solcore.Synthesis.Source.AssemblyKeccakLoop.generateCases (Seed.ofNat 1) 384 count 512 fuel
      revision transactions
    let parent := Solcore.Synthesis.Source.KeccakLoop.generateCases (Seed.ofNat 1) 384 count 512 fuel revision transactions
    ensure ((generated.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    for key in ["requested", "attempted", "status"] do
      ensure ((generated.getObjVal? key).toOption == (parent.getObjVal? key).toOption)
        s!"{revision.version}: {key} differs from the Keccak-loop profile"
    let excluded ← get (generated.getObjValAs? (Array Json) "excluded")
    ensure (excluded.map (·.setObjVal! "stage" (toJson "keccak-loop-profile")) ==
        (← get (parent.getObjValAs? (Array Json) "excluded"))) s!"{revision.version}: the exclusions differ"
    let ours ← get (generated.getObjValAs? (Array Json) "cases")
    let theirs ← get (parent.getObjValAs? (Array Json) "cases")
    ensure (ours.size == theirs.size) s!"{revision.version}: the case counts differ"
    for ((json, base), index) in (ours.zip theirs).zipIdx do
      let name := s!"{revision.version} case {index}"
      for key in kept do
        ensure ((json.getObjVal? key).toOption == (base.getObjVal? key).toOption) s!"{name}: {key} differs"
      let scenario ← get (Solcore.Synthesis.Source.AssemblyKeccakLoop.caseProgram json)
      let loop ← get (Solcore.Synthesis.Source.KeccakLoop.caseProgram base)
      ensure (Solcore.Synthesis.Source.KeccakLoop.planJson scenario.plan ==
        Solcore.Synthesis.Source.KeccakLoop.planJson loop.plan) s!"{name}: the plan differs"
      let origin ← get ((← get (json.getObjVal? "provenance")).getObjVal? "origin")
      let parentOrigin ← get ((← get (base.getObjVal? "provenance")).getObjVal? "origin")
      let some seed := (← get (origin.getObjValAs? String "seed")).toNat? | throw (IO.userError s!"{name}: no seed")
      ensure (scenario.form == Solcore.Synthesis.Source.AssemblyKeccakLoop.formFor (Seed.ofNat seed))
        s!"{name}: the form is not the seed's"
      ensure (origin == (parentOrigin.setObjVal! "kind" (toJson "assembly-keccak-loop-generated")).setObjVal!
        "form" (toJson scenario.form.name)) s!"{name}: the origin differs beyond its kind and form"
      if index == 0 then
        ensure (Solcore.Synthesis.Source.AssemblyKeccakLoop.observe scenario StorageExecution.fixtureBindings fuel ==
            Solcore.Synthesis.Source.KeccakLoop.observe loop StorageExecution.fixtureBindings fuel)
          s!"{name}: the observation differs"
      ensure ((Solcore.Synthesis.Source.AssemblyKeccakLoop.replayCase json fuel).toOption == some json)
        s!"{name}: replay differs"
      let source ← get (json.getObjValAs? String "source")
      ensure (Form.all.all fun form => hasForm source form == (form == scenario.form))
        s!"{name}: the source does not have exactly the {scenario.form.name} form's blocks"
      ensure (!occurs source "revert_(" && !occurs source "sc_log2" && !occurs source "entries[")
        s!"{name}: the source calls a std wrapper"
      forms := scenario.form :: forms
      cases := cases.push json
  for form in Form.all do
    ensure (forms.contains form) s!"generation never drew the {form.name} form"
  -- Reductions are the Keccak-loop profile's in the parent case's form, and
  -- every emitted candidate replays.
  for json in cases.toList.take 1 ++ (cases.toList.drop 4).take 1 do
    let source ← get (Solcore.Synthesis.Source.AssemblyKeccakLoop.caseProgram json)
    let reduced := Solcore.Synthesis.Source.AssemblyKeccakLoop.reductions source
    ensure (!reduced.isEmpty && reduced.length == (Solcore.Synthesis.Source.KeccakLoop.reductions source.loop).length)
      "the reductions differ from the Keccak-loop profile's"
    ensure (reduced.all fun candidate => candidate.candidate.form == source.form) "a reduction changes the form"
    let shrunk ← get (Solcore.Synthesis.Source.AssemblyKeccakLoop.shrinkCases json 16 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.AssemblyKeccakLoop.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      ensure ((← get (Solcore.Synthesis.Source.AssemblyKeccakLoop.caseProgram candidate)).form == source.form)
        "an emitted reduction changes the form"
  -- An unknown form, the parent's schemas and another form's plan are refused.
  let some json := cases[0]? | throw (IO.userError "no case")
  let scenario ← get (Solcore.Synthesis.Source.AssemblyKeccakLoop.caseProgram json)
  let plan ← get (json.getObjVal? "keccakLoopPlan")
  ensure (Solcore.Synthesis.Source.AssemblyKeccakLoop.checkedPlan (plan.setObjVal! "form" (toJson "blocks"))).toOption.isNone
    "an unknown form was admitted"
  ensure (Solcore.Synthesis.Source.AssemblyKeccakLoop.checkedPlan
      (plan.setObjVal! "schema" (toJson Solcore.Synthesis.Source.KeccakLoop.planSchema))).toOption.isNone
    "a Keccak-loop plan schema was admitted"
  ensure (Solcore.Synthesis.Source.AssemblyKeccakLoop.caseProgram
      (json.setObjVal! "schema" (toJson Solcore.Synthesis.Source.KeccakLoop.caseSchema))).toOption.isNone
    "a Keccak-loop case schema was admitted"
  ensure (Solcore.Synthesis.Source.KeccakLoop.caseProgram json).toOption.isNone
    "the Keccak-loop profile admitted an inline Yul case"
  for other in Form.all do
    if other != scenario.form then
      let changed := json.setObjVal! "keccakLoopPlan" (plan.setObjVal! "form" (toJson other.name))
      ensure (Solcore.Synthesis.Source.AssemblyKeccakLoop.caseProgram changed).toOption.isSome
        "a plan in another form failed decoding"
      ensure (Solcore.Synthesis.Source.AssemblyKeccakLoop.replayCase changed fuel).toOption.isNone
        s!"the {other.name} form replayed with a {scenario.form.name} source"

end Tests.SourceAssemblyKeccakLoopCases
end

section
-- leanmerge: from Solcore.Test.SourceAssemblyKeccakLoopCorpus
/-! The fixed inline Yul Keccak-loop corpus is the Keccak-loop corpus in the
three forms: its generated seeds stay generated, its imported entries take
`split`, `carried` and `pipelined` in turn, in corpus order, and the entries
`seven-wide`, `seven-shared` and `seven-counts` also run in the other two
forms. The manifest must be exactly that construction, with the Keccak-loop
corpus's requirements and the form requirements. Every entry must replay, and
its actual original Core history must equal the expected history, which is
the Keccak-loop corpus's, since the Core reference is unchanged. Each form must
cover the iteration counts zero, one and seven and every carry. Source/Rust/EVM
agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyKeccakLoopCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Source.AssemblyStorage (Form)

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", AssemblyKeccakLoop.profileVersion),
  ("loopProfileVersion", KeccakLoop.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.KeccakLoop.version),
  ("framingVersion", Solcore.Synthesis.Core.EventLog.framingVersion),
  ("templateVersion", KeccakLoop.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", AssemblyKeccakLoop.emitterVersion), ("wrapperVersion", AssemblyKeccakLoop.wrapperVersion)]

/-- The entries that run in every form. -/
private def everyForm : List String := ["seven-wide", "seven-shared", "seven-counts"]

private def carryNames : List String := ["entry", "iteration", "rollback", "transaction"]

/-- An imported Keccak-loop entry in a form. -/
private def inForm (entry : Json) (form : Form) : Except String Json := do
  let plan ← entry.getObjVal? "keccakLoopPlan"
  return (entry.setObjVal! "id" (toJson ((← string entry "id") ++ "-" ++ form.name))).setObjVal! "keccakLoopPlan"
    ((plan.setObjVal! "schema" (toJson AssemblyKeccakLoop.planSchema)).setObjVal! "form" (toJson form.name))

/-- The corpus the definitions build from the Keccak-loop corpus. -/
def construction (parent : Json) : Except String (List Json) := do
  let mut turn := 0
  let mut result : List Json := []
  for entry in ← parent.getObjValAs? (List Json) "cases" do
    if (entry.getObjVal? "generation").isOk then
      result := result ++ [entry]
    else
      let form := Form.all.getD (turn % 3) .split
      turn := turn + 1
      result := result ++ [← inForm entry form]
      if everyForm.contains (← string entry "id") then
        for other in Form.all do
          if other != form then result := result ++ [← inForm entry other]
  return result

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := AssemblyKeccakLoop.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let (plan, form) ← AssemblyKeccakLoop.checkedPlan (← entry.getObjVal? "keccakLoopPlan")
  let loop ← KeccakLoop.checkedScenario plan (← KeccakLoop.decodeTransactions plan.mask (← entry.getObjVal? "transactions"))
  AssemblyKeccakLoop.emitCase ⟨loop, form⟩ (Json.mkObj [("kind", toJson "imported")]) fuel

/-- The carries of one scenario, as the Keccak-loop corpus defines them. -/
private def carries (keys : List (List Word)) (statuses : List String) : List String :=
  let trips := keys.map List.length
  (if trips.any (· ≥ 2) then ["iteration"] else []) ++
  (if keys.any (fun values => values.eraseDups.length < values.length) then ["entry"] else []) ++
  (if keys.zipIdx.any (fun (values, index) => values.any fun key =>
      ((keys.zip statuses).take index).any fun (earlier, status) => status == "returned" && earlier.contains key)
    then ["transaction"] else []) ++
  (if (trips.zip statuses).any (fun (count, status) => count ≥ 1 && status == "reverted") then ["rollback"] else [])

def validateManifest (manifest parent : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-assembly-keccak-loops" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected inline Yul Keccak-loop manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("inline Yul Keccak-loop manifest changed " ++ key)
  require ((← string parent "profile") == "stateful-keccak-loops") "the parent corpus is not the Keccak-loop corpus"
  -- The Keccak-loop corpus's requirements carry over unchanged.
  for key in ["requiredFeatures", "requiredInputs", "requiredMasks", "requiredKeyMasks", "requiredIterationCounts",
      "requiredIterationCarries", "requiredHelperCounts", "requiredTransactionCounts", "requiredOutcomes",
      "requiredCompletionPatterns", "generationRecipeRequirements", "coverageKind", "generatorVersion"] do
    require ((← manifest.getObjVal? key) == (← parent.getObjVal? key)) ("inline Yul Keccak-loop manifest changed " ++ key)
  require ((← manifest.getObjValAs? (List String) "requiredForms") == Form.all.map Form.name &&
    (← manifest.getObjValAs? (List String) "requiredFormIterations") ==
      (Form.all.flatMap fun form => [0, 1, 7].map fun count => form.name ++ ":" ++ toString count) &&
    (← manifest.getObjValAs? (List String) "requiredFormCarries") ==
      (Form.all.flatMap fun form => carryNames.map fun carry => form.name ++ ":" ++ carry))
    "inline Yul Keccak-loop corpus must require every form with iterations 0, 1 and 7 and every carry"
  let entries ← manifest.getObjValAs? (List Json) "cases"
  require (entries == (← construction parent)) "inline Yul Keccak-loop corpus differs from its construction"
  let mut identifiers : List String := []
  let mut forms : List String := []
  let mut formIterations : List String := []
  let mut formCarries : List String := []
  let mut transactionTotal := 0
  let mut logTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate inline Yul Keccak-loop corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← AssemblyKeccakLoop.replayCase saved fuel) == saved)
      ("inline Yul Keccak-loop corpus entry did not replay: " ++ identifier)
    let scenario ← AssemblyKeccakLoop.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "keccakLoopPlan") == (← entry.getObjVal? "keccakLoopPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported inline Yul Keccak-loop entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    let expectedFeatures ← entry.getObjValAs? (List String) "expectedFeatures"
    require (expectedFeatures.all caseFeatures.contains && caseFeatures.all expectedFeatures.contains)
      ("inline Yul Keccak-loop corpus features changed: " ++ identifier)
    let history := AssemblyKeccakLoop.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("inline Yul Keccak-loop corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("inline Yul Keccak-loop expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage"),
        ("logs", ← row.getObjVal? "logs")]
      require (actual == golden)
        ("original Core differs from the expected Keccak-loop history: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
      logTotal := logTotal + (← row.getObjValAs? (List Json) "logs").length
    let keys := scenario.transactions.map fun tx =>
      Solcore.Synthesis.Stateful.KeccakLoopExecution.keys scenario.plan.mask scenario.plan.keyMask tx.input
    let form := scenario.form.name
    transactionTotal := transactionTotal + observed.length
    forms := (forms ++ [form]).eraseDups
    formIterations := (formIterations ++ keys.map fun values => form ++ ":" ++ toString values.length).eraseDups
    formCarries := (formCarries ++ (carries keys statuses).map (form ++ ":" ++ ·)).eraseDups
  require ((← manifest.getObjValAs? (List String) "requiredForms").all forms.contains &&
    (← manifest.getObjValAs? (List String) "requiredFormIterations").all formIterations.contains &&
    (← manifest.getObjValAs? (List String) "requiredFormCarries").all formCarries.contains)
    "inline Yul Keccak-loop corpus misses a form, a form's iteration count or a form's carry"
  return Json.mkObj [("profile", toJson "stateful-assembly-keccak-loops"), ("scenarios", toJson entries.length),
    ("transactions", toJson transactionTotal), ("logs", toJson logTotal), ("forms", toJson forms),
    ("formIterations", toJson formIterations), ("formCarries", toJson formCarries)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (reason : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid inline Yul Keccak-loop corpus unexpectedly passed: " ++ reason))

def testSourceAssemblyKeccakLoopCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-assembly-keccak-loop-corpus.json"))
  let parent ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-keccak-loop-corpus.json"))
  let summary ← checked (validateManifest manifest parent)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first inline Yul Keccak-loop case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let withRow := fun (changed : Json) => replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changed)))
  -- An output, a log and a missing row are checked, and so is the construction.
  rejects (validateManifest (withRow (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))))
    parent) "changed output"
  let logs ← checked (row.getObjValAs? (Array Json) "logs")
  rejects (validateManifest (withRow (row.setObjVal! "logs" (.arr logs.pop))) parent) "removed log"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop))) parent) "popped history"
  let plan ← checked (first.getObjVal? "keccakLoopPlan")
  rejects (validateManifest (replace first (first.setObjVal! "keccakLoopPlan" (plan.setObjVal! "form" (toJson "pipelined"))))
    parent) "changed form"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr entries.pop)) parent) "dropped entry"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))) parent) "duplicated entry"
  for (key, value) in [
      ("profile", toJson "stateful-keccak-loops"), ("emitterVersion", toJson "forged"),
      ("requiredMasks", toJson [1, 3, 7]), ("requiredForms", toJson ["split", "carried"]),
      ("requiredFormIterations", toJson ["split:0"]), ("requiredFormCarries", toJson ["split:entry"])] do
    rejects (validateManifest (manifest.setObjVal! key value) parent) key
  rejects (validateManifest manifest (parent.setObjVal! "cases" (.arr #[]))) "another parent corpus"
  rejects (validateManifest manifest parent 0) "no fuel"
  IO.println summary.compress

end Tests.SourceAssemblyKeccakLoopCorpus
end

section
-- leanmerge: from Solcore.Test.SourceAssemblyLoopCases
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
  String.intercalate "\n" (["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    "",
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
end

section
-- leanmerge: from Solcore.Test.SourceAssemblyMemoryCases
/-! The `runtime-assembly-memory` profile. Its step is the `runtime-primitives`
function of the same seed by the same steps, and its Core reference keeps the
96-byte window as three Words with byte placement as shifts and masks and the
hash as a closure over the Core Keccak builders. Each length's closure agrees
with `cast keccak` and the separate `Solcore.Abi.V1.Keccak256`, the 64-byte one
is the mapping profile's closure, and the reference agrees with a byte-list
model of the schedule on generated plans. A fixture's source and results are
golden. Generation draws every stage count, width, delta class and hash option
and replays exactly; tampering is refused, and reductions are strictly smaller
and replay. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyMemoryCases

open Lean
open Solcore.Core (Word)
open Solcore.Core.Wire (Expr)
open Solcore.ContractRuntime (encodeWordBytesBE decodeWordBytesBE?)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Core.AssemblyMemory (Schedule Stage Hash Width)

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

private def withPlan (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "assemblyMemoryPlan" (change (← get (case.getObjVal? "assemblyMemoryPlan")))

private def run (program : Solcore.Core.Wire.Program) : IO Nat :=
  match program.toCore.runStateful fuel with
  | .done (.word value) _ => pure value.val
  | _ => throw (IO.userError "a reference program did not return a Word")

/-- Keccak-256 of the first `length` bytes of two big-endian Words, by the separate ABI implementation. -/
private def abiHash (length first second : Nat) : Nat :=
  let bytes := (encodeWordBytesBE (Word.ofNatModulo first) ++ encodeWordBytesBE (Word.ofNatModulo second)).extract 0 length
  ((decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash bytes)).map (·.val)).getD 0

private def closed (body : Expr) : Solcore.Core.Wire.Program := {resultType := .word, dataDefinitions := [], body}

private def closureHash (length first second : Nat) : IO Nat :=
  run (closed (.apply (AssemblyMemory.hashClosure length) (.pair (word first) (word second))))

private def closureNodes (length : Nat) : Nat :=
  Solcore.Core.Wire.programNodes
    ({resultType := .function (.product .word .word) .word, dataDefinitions := [], body := AssemblyMemory.hashClosure length} :
      Solcore.Core.Wire.Program)

private def maximum : Nat := 2 ^ 256 - 1

/-- `cast keccak` of the first bytes of `0x00..1f ++ 0x20..3f`, for each length. -/
private def castHashes : List (Nat × Nat) := [
  (0, 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470),
  (1, 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a), (31, 0x3e50547cf72e8583ee91462f9d99fe624f53282f78e1a5ec2347b1d0123d0d9b), (32, 0x8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d), (33, 0xf08683775f4a25dfef721c487073fb77026d45ac57e423424290e47af9fd2835), (64, 0x002030bde3d4cf89919649775cd71875c4d0ab1708a380e03fefc3a28aa24831)]

private def counting : Nat × Nat :=
  ((List.range 32).foldl (fun acc index => acc * 256 + index) 0,
   (List.range 32).foldl (fun acc index => acc * 256 + 32 + index) 0)

private def hashChecks : IO Unit := do
  ensure (AssemblyMemory.hashLengths.map closureNodes == [2270, 2278, 2458, 2462, 2470, 2654])
    "a hash closure changed size"
  ensure (Solcore.Core.Wire.encodeExpr (AssemblyMemory.hashClosure 64) ==
      Solcore.Core.Wire.encodeExpr StorageMapping.hashClosure)
    "the 64-byte closure is not the mapping profile's closure"
  for (length, expected) in castHashes do
    ensure ((← closureHash length counting.1 counting.2) == expected && abiHash length counting.1 counting.2 == expected)
      s!"the {length}-byte closure differs from cast keccak"
  for length in AssemblyMemory.hashLengths do
    for (first, second) in [(0, 0), (maximum, 7), (2 ^ 255 + 1, maximum - 2 ^ 128)] do
      ensure ((← closureHash length first second) == abiHash length first second)
        s!"the {length}-byte closure differs from Solcore.Abi.V1.Keccak256"

/-- A byte-list model of a plan at one input: the window bytes, the step by
its own Core function, and the hash by the separate ABI Keccak-256. -/
private def byteModel (plan : AssemblyMemory.CheckedPlan) (input : Nat) : IO Nat := do
  let step := fun (value : Nat) => run (plan.function.instantiate (Word.ofNatModulo value))
  let bytesOf := fun (value : Nat) => (List.range 32).map fun index => value / 256 ^ (31 - index) % 256
  let readWord := fun (memory : Array Nat) (offset : Nat) =>
    (List.range 32).foldl (fun acc index => acc * 256 + memory.getD (offset + index) 0) 0
  let mut memory : Array Nat := (bytesOf input ++ bytesOf (← step input) ++ bytesOf (maximum - input)).toArray
  for stage in plan.schedule.stages do
    let value ← step (readWord memory stage.read)
    match stage.width with
    | .word =>
        for (byte, index) in (bytesOf value).zipIdx do
          memory := memory.set! (stage.write + index) byte
    | .byte => memory := memory.set! stage.write (value % 256)
  let result ← step (readWord memory plan.schedule.final)
  match plan.schedule.hash with
  | none => return result
  | some hash =>
      let bytes := ByteArray.mk ((List.range hash.length).map
        fun index => UInt8.ofNat (memory.getD (hash.offset + index) 0)).toArray
      let digest := ((decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash bytes)).map (·.val)).getD 0
      return (result + digest) % 2 ^ 256

private def modelChecks : IO Unit := do
  let corpus := AssemblyMemory.generateCases (Seed.ofNat 1) 96 (8 * 24) 512 fuel .v4
  let all ← cases corpus
  ensure (all.size == 8 * 24) "model generation did not complete"
  let mut hashed := 0
  for case in all do
    let checked ← get (AssemblyMemory.caseProgram case)
    if checked.plan.schedule.hash.isSome then hashed := hashed + 1
    let observed ← get ((← get (case.getObjVal? "directCore")).getObjValAs? String "word")
    ensure (observed == toString (← byteModel checked.plan checked.input.val))
      s!"the Core reference differs from the byte model at input {checked.input.val}"
  ensure (hashed > 0 && hashed < all.size) "the model plans did not mix hashed and unhashed schedules"

/-- `if a > 1000 then (3a) xor (a >> 7) else a + 77`. -/
private def fixtureStep : Expr :=
  .ifE (.binary .wordGt (.var 0) (word 1000))
    (.binary .wordXor (.binary .wordMul (.var 0) (word 3)) (.binary .wordShr (.var 0) (word 7)))
    (.binary .wordAdd (.var 0) (word 77))

private def fixtureSchedule : Schedule :=
  {stages := [⟨7, .word, 13⟩, ⟨40, .byte, 70⟩], final := 33, hash := some ⟨5, 33⟩}

private def alignedSchedule : Schedule := {stages := [⟨0, .word, 0⟩], final := 0, hash := none}

private def fixtureInputs : List Nat := [0, 1, 1001, maximum, 2 ^ 255]

/-- From a separate Python byte model with `cast`-checked Keccak-256. -/
private def fixtureResults : List Nat := [
  110185045784767375427769875027799576749316767568423648043270614598653477256537,
  61429659347378633297406769563880590345839053942026463851594556187924875762631,
  47432681453954187113048786422149475504612106509254933618506966340297808359691,
  86278112449216878584690821040707056911088705185690605313631675068037507226035,
  87400343485929131098010694833534200512004183788348265012709545369942392530013]

private def alignedResults : List Nat := [154, 155, 8995,
  113975770454724016332759355177924187618999331219652427750508572832984316510214,
  58804204009954187257191307419725814043770319055814350164203297591420971384832]

private def fixtureSource : String := String.intercalate "\n" [
  "pragma solcore;", "import * from std;",
  "import * from std.dispatch;",
  "",
  "contract SynthesizedAssemblyMemory {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_out: word = 0;",
  "        assembly {",
  "            function sc_step(sc_arg) -> sc_ret {",
  "                let sc_y0 := 0",
  "                switch gt(sc_arg, 1000)",
  "                case 0 {",
  "                    sc_y0 := add(sc_arg, 77)",
  "                }",
  "                default {",
  "                    sc_y0 := xor(mul(sc_arg, 3), shr(7, sc_arg))",
  "                }",
  "                sc_ret := sc_y0",
  "            }",
  "            let sc_base := mload(64)",
  "            mstore(sc_base, sc_input)",
  "            mstore(add(sc_base, 32), sc_step(sc_input))",
  "            mstore(add(sc_base, 64), not(sc_input))",
  "            let sc_m0 := mload(add(sc_base, 7))",
  "            mstore(add(sc_base, 13), sc_step(sc_m0))",
  "            let sc_m1 := mload(add(sc_base, 40))",
  "            mstore8(add(sc_base, 70), sc_step(sc_m1))",
  "            let sc_m2 := mload(add(sc_base, 33))",
  "            let sc_h := keccak256(add(sc_base, 5), 33)",
  "            sc_out := add(sc_step(sc_m2), sc_h)",
  "        }",
  "        return uint256(sc_out);",
  "    }",
  "}"] ++ "\n"

private def fixturePlan (schedule : Schedule) : IO AssemblyMemory.CheckedPlan := do
  let some function := CheckedWordFunction.ofBody? fixtureStep |
    throw (IO.userError "the fixture step is not a checked Word function")
  let some plan := AssemblyMemory.CheckedPlan.ofParts? function schedule |
    throw (IO.userError "the fixture plan failed admission")
  return plan

private def fixtureChecks : IO Unit := do
  let plan ← fixturePlan fixtureSchedule
  let emitted ← get ((AssemblyMemory.emit plan.function plan.schedule).mapError reprStr)
  ensure (emitted.source == fixtureSource) "the fixture's source differs from its golden text"
  for (input, expected) in fixtureInputs.zip fixtureResults do
    ensure ((← run (plan.program (Word.ofNatModulo input))) == expected)
      s!"the fixture's Core reference differs from its golden result at {input}"
    ensure ((← byteModel plan input) == expected) s!"the byte model differs from the golden result at {input}"
  let aligned ← fixturePlan alignedSchedule
  for (input, expected) in fixtureInputs.zip alignedResults do
    ensure ((← run (aligned.program (Word.ofNatModulo input))) == expected)
      s!"the aligned fixture differs from its golden result at {input}"
  ensure (Solcore.Core.Wire.programNodes (aligned.program Word.zero) < 100)
    "an unhashed plan carries a closure"
  -- Outside the window, an unadmitted length and four stages are refused.
  for schedule in [{fixtureSchedule with final := 65}, {fixtureSchedule with hash := some ⟨64, 33⟩},
      {fixtureSchedule with hash := some ⟨0, 2⟩}, {fixtureSchedule with stages := [⟨0, .byte, 96⟩]},
      {fixtureSchedule with stages := [⟨0, .word, 65⟩]}, {fixtureSchedule with stages := []},
      {fixtureSchedule with stages := List.replicate 4 ⟨0, .word, 0⟩}] do
    ensure (AssemblyMemory.CheckedPlan.ofParts? plan.function schedule).isNone
      "an unadmitted schedule passed admission"

private def classOf (offset : Nat) : Nat :=
  (AssemblyMemory.deltaClasses.findIdx? fun (low, high) => low ≤ offset % 32 && offset % 32 ≤ high).getD 6

private def generationChecks : IO Unit := do
  let mut counts : List Nat := []
  let mut widths : List Width := []
  let mut reads : List Nat := []
  let mut words : List Nat := []
  let mut bytes : List Nat := []
  let mut hashes : List (Option Nat) := []
  for index in List.range 600 do
    let schedule := AssemblyMemory.scheduleFor (Seed.ofNat (index + 1))
    ensure schedule.admitted s!"the schedule of seed {index + 1} is not admitted"
    counts := counts ++ [schedule.stages.length]
    hashes := hashes ++ [schedule.hash.map (·.length)]
    reads := reads ++ [classOf schedule.final]
    for stage in schedule.stages do
      widths := widths ++ [stage.width]
      reads := reads ++ [classOf stage.read]
      match stage.width with
      | .word => words := words ++ [classOf stage.write]
      | .byte => bytes := bytes ++ [classOf stage.write]
  ensure ([1, 2, 3].all counts.contains && [Width.word, .byte].all widths.contains)
    "generation missed a stage count or a width"
  ensure ((List.range 6).all fun index => reads.contains index && words.contains index && bytes.contains index)
    "generation missed a delta class"
  ensure ((none :: AssemblyMemory.hashLengths.map some).all hashes.contains) "generation missed a hash option"
  let corpus := AssemblyMemory.generateCases (Seed.ofNat 1) 96 64 256 fuel .v4
  ensure (corpus == AssemblyMemory.generateCases (Seed.ofNat 1) 96 64 256 fuel .v4) "generation is not deterministic"
  for case in ← cases corpus do
    let checked ← get (AssemblyMemory.caseProgram case)
    let seed ← get (((← provenance case).getObjVal? "origin" >>= (·.getObjValAs? String "seed")))
    ensure (checked.plan.schedule == AssemblyMemory.scheduleFor (Seed.ofNat seed.toNat!))
      "a generated plan's schedule differs from its seed's"
    ensure ((← get (AssemblyMemory.replayCase case fuel)) == case) "a generated case failed exact replay"
  for entry in ← excluded corpus do
    ensure ((entry.getObjValAs? String "stage").toOption == some "assembly-memory-profile")
      "an exclusion lacks the profile's stage"

private def tamperChecks : IO Unit := do
  let all ← cases (AssemblyMemory.generateCases (Seed.ofNat 1) 96 64 256 fuel .v4)
  let some hashed := all.find? fun case =>
      ((case.getObjVal? "assemblyMemoryPlan" >>= (·.getObjVal? "hash")).toOption.getD .null) != .null |
    throw (IO.userError "no generated case hashes")
  ensure (errorOf (AssemblyMemory.replayCase (← withPlan hashed (·.setObjVal! "hash" (Json.mkObj
      [("offset", toJson 0), ("length", toJson 2)]))) fuel) ==
      some "assembly memory schedule is outside the admitted stages, offsets and hashed lengths")
    "an unadmitted hashed length replayed"
  ensure (errorOf (AssemblyMemory.replayCase (← withPlan hashed (·.setObjVal! "finalRead" (toJson 65))) fuel) ==
      some "assembly memory schedule is outside the admitted stages, offsets and hashed lengths")
    "a read past the window replayed"
  let moved ← withPlan hashed (·.setObjVal! "finalRead" (toJson 0))
  ensure (AssemblyMemory.replayCase moved fuel matches .error _) "a changed schedule replayed"
  ensure (errorOf (AssemblyMemory.replayCase (hashed.setObjVal! "source" (toJson "contract X {}")) fuel) ==
      some "saved source differs from emission of the assembly memory plan")
    "a changed source replayed"
  ensure (AssemblyMemory.replayCase (hashed.setObjVal! "program" (Solcore.Core.Wire.encodeProgram (closed (word 1)))) fuel
      matches .error _)
    "a changed reference replayed"
  ensure (errorOf (AssemblyMemory.replayCase (hashed.setObjVal! "provenance" ((← provenance hashed).setObjVal!
      "memoryVersion" (toJson "core-assembly-memory-v0"))) fuel) == some "memoryVersion changed")
    "a changed memory version replayed"
  -- A reduction is strictly smaller, replays, and a hashed plan's shrink batch holds at most eight.
  let reduced ← cases (← get (AssemblyMemory.shrinkCases hashed 64 fuel))
  ensure (!reduced.isEmpty && reduced.size ≤ 8) "a hashed plan's shrink batch is empty or exceeds eight"
  for candidate in reduced do
    ensure ((← get (AssemblyMemory.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
  let parent ← get (AssemblyMemory.caseProgram hashed)
  for reduction in AssemblyMemory.reductions parent do
    ensure (decide (reduction.candidate.measure.StrictlySmaller parent.measure)) "a reduction is not strictly smaller"
  let reducedPlan ← get ((reduced[0]!.getObjVal? "provenance") >>= (·.getObjVal? "origin"))
  ensure (AssemblyMemory.replayCase (reduced[0]!.setObjVal! "provenance" ((← provenance reduced[0]!).setObjVal!
      "origin" (reducedPlan.setObjVal! "parentPlan" (← get (reduced[0]!.getObjVal? "assemblyMemoryPlan"))))) fuel
      matches .error _)
    "a reduction claiming itself as its parent replayed"

def testSourceAssemblyMemoryCases : IO Unit := do
  hashChecks
  fixtureChecks
  generationChecks
  tamperChecks
  modelChecks

end Tests.SourceAssemblyMemoryCases
end

section
-- leanmerge: from Solcore.Test.SourceAssemblyStorageLoopCases
/-! Generated inline Yul storage-loop cases. For the same seed, budget, G0
revision and transaction count, generation must agree with the storage-loop
profile: the same attempts and exclusions, and per case the same plan,
original Core program, transactions, initial state, observed slots, fuel and
observation, with an origin that differs only in its kind and recorded form.
The form must be the seed's, every form must be drawn, and each source must
have its form's blocks and call no std storage or revert wrapper. Each case
must replay to itself, and every reduction keeps the parent case's form and
replays. An unknown form, a storage-loop plan or case schema and a form that
its source was not emitted in are refused. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyStorageLoopCases

open Lean
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Source.AssemblyStorage (Form)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def occurs (text part : String) : Bool := (text.splitOn part).length > 1

/-- The marks of a form: `split` writes through a fresh slot expression,
`carried` advances the counter in Yul without a conditional read, and
`pipelined` reads under two conditionals, before the loop and after the
writes. -/
private def hasForm (source : String) : Form → Bool
  | .split => occurs source "sstore(add(sc_counter, 2), sc_value)" && !occurs source "sc_counter := add(sc_counter, 1)"
  | .carried => occurs source "sc_counter := add(sc_counter, 1)" && !occurs source "if gt(sc_limit, sc_counter)"
  | .pipelined => (source.splitOn "if gt(sc_limit, sc_counter)").length == 3

/-- The storage-loop case fields that an inline Yul case keeps. -/
private def kept : List String := ["program", "transactions", "initialState", "observedSlots", "executionFuel"]

def testSourceAssemblyStorageLoopCases : IO Unit := do
  let fuel := 1000000
  let mut forms : List Form := []
  let mut cases : Array Json := #[]
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three, from seed 4, the first whose eight
  -- consecutive seeds draw every form.
  for (revision, transactions, count) in [(GeneratorRevision.v3, 8, 8), (GeneratorRevision.v1, 3, 8)] do
    let generated := Solcore.Synthesis.Source.AssemblyStorageLoop.generateCases (Seed.ofNat 4) 384 count 512 fuel
      revision transactions
    let parent := Solcore.Synthesis.Source.StorageLoop.generateCases (Seed.ofNat 4) 384 count 512 fuel revision transactions
    ensure ((generated.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    for key in ["requested", "attempted", "status"] do
      ensure ((generated.getObjVal? key).toOption == (parent.getObjVal? key).toOption)
        s!"{revision.version}: {key} differs from the storage-loop profile"
    let excluded ← get (generated.getObjValAs? (Array Json) "excluded")
    ensure (excluded.map (·.setObjVal! "stage" (toJson "storage-loop-profile")) ==
        (← get (parent.getObjValAs? (Array Json) "excluded"))) s!"{revision.version}: the exclusions differ"
    let ours ← get (generated.getObjValAs? (Array Json) "cases")
    let theirs ← get (parent.getObjValAs? (Array Json) "cases")
    ensure (ours.size == theirs.size) s!"{revision.version}: the case counts differ"
    for ((json, base), index) in (ours.zip theirs).zipIdx do
      let name := s!"{revision.version} case {index}"
      for key in kept do
        ensure ((json.getObjVal? key).toOption == (base.getObjVal? key).toOption) s!"{name}: {key} differs"
      let scenario ← get (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram json)
      let loop ← get (Solcore.Synthesis.Source.StorageLoop.caseProgram base)
      ensure (Solcore.Synthesis.Source.StorageLoop.planJson scenario.plan ==
        Solcore.Synthesis.Source.StorageLoop.planJson loop.plan) s!"{name}: the plan differs"
      let origin ← get ((← get (json.getObjVal? "provenance")).getObjVal? "origin")
      let parentOrigin ← get ((← get (base.getObjVal? "provenance")).getObjVal? "origin")
      let some seed := (← get (origin.getObjValAs? String "seed")).toNat? | throw (IO.userError s!"{name}: no seed")
      ensure (scenario.form == Solcore.Synthesis.Source.AssemblyStorageLoop.formFor (Seed.ofNat seed))
        s!"{name}: the form is not the seed's"
      ensure (origin == (parentOrigin.setObjVal! "kind" (toJson "assembly-storage-loop-generated")).setObjVal!
        "form" (toJson scenario.form.name)) s!"{name}: the origin differs beyond its kind and form"
      if index == 0 then
        ensure (Solcore.Synthesis.Source.AssemblyStorageLoop.observe scenario StorageExecution.fixtureBindings fuel ==
            Solcore.Synthesis.Source.StorageLoop.observe loop StorageExecution.fixtureBindings fuel)
          s!"{name}: the observation differs"
      ensure ((Solcore.Synthesis.Source.AssemblyStorageLoop.replayCase json fuel).toOption == some json)
        s!"{name}: replay differs"
      let source ← get (json.getObjValAs? String "source")
      ensure (Form.all.all fun form => hasForm source form == (form == scenario.form))
        s!"{name}: the source does not have exactly the {scenario.form.name} form's blocks"
      ensure (!occurs source "revert_(" && !occurs source "{sload")
        s!"{name}: the source calls a std wrapper"
      forms := scenario.form :: forms
      cases := cases.push json
  for form in Form.all do
    ensure (forms.contains form) s!"generation never drew the {form.name} form"
  -- Reductions are the storage-loop profile's in the parent case's form, and
  -- every emitted candidate replays.
  for json in cases.toList.take 1 ++ (cases.toList.drop 8).take 1 do
    let source ← get (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram json)
    let reduced := Solcore.Synthesis.Source.AssemblyStorageLoop.reductions source
    ensure (!reduced.isEmpty && reduced.length == (Solcore.Synthesis.Source.StorageLoop.reductions source.loop).length)
      "the reductions differ from the storage-loop profile's"
    ensure (reduced.all fun candidate => candidate.candidate.form == source.form) "a reduction changes the form"
    let shrunk ← get (Solcore.Synthesis.Source.AssemblyStorageLoop.shrinkCases json 16 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.AssemblyStorageLoop.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      ensure ((← get (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram candidate)).form == source.form)
        "an emitted reduction changes the form"
  -- An unknown form, the parent's schemas and another form's plan are refused.
  let some json := cases[0]? | throw (IO.userError "no case")
  let scenario ← get (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram json)
  let plan ← get (json.getObjVal? "storageLoopPlan")
  ensure (Solcore.Synthesis.Source.AssemblyStorageLoop.checkedPlan (plan.setObjVal! "form" (toJson "blocks"))).toOption.isNone
    "an unknown form was admitted"
  ensure (Solcore.Synthesis.Source.AssemblyStorageLoop.checkedPlan
      (plan.setObjVal! "schema" (toJson Solcore.Synthesis.Source.StorageLoop.planSchema))).toOption.isNone
    "a storage-loop plan schema was admitted"
  ensure (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram
      (json.setObjVal! "schema" (toJson Solcore.Synthesis.Source.StorageLoop.caseSchema))).toOption.isNone
    "a storage-loop case schema was admitted"
  ensure (Solcore.Synthesis.Source.StorageLoop.caseProgram json).toOption.isNone
    "the storage-loop profile admitted an inline Yul case"
  for other in Form.all do
    if other != scenario.form then
      let changed := json.setObjVal! "storageLoopPlan" (plan.setObjVal! "form" (toJson other.name))
      ensure (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram changed).toOption.isSome
        "a plan in another form failed decoding"
      ensure (Solcore.Synthesis.Source.AssemblyStorageLoop.replayCase changed fuel).toOption.isNone
        s!"the {other.name} form replayed with a {scenario.form.name} source"

end Tests.SourceAssemblyStorageLoopCases
end

section
-- leanmerge: from Solcore.Test.SourceAssemblyStorageLoopCorpus
/-! The fixed inline Yul storage-loop corpus is the storage-loop corpus in the
three forms: its generated seeds stay generated, its imported entries take
`split`, `carried` and `pipelined` in turn, in corpus order, and the entries
`seven-carried` and `seven-counts` also run in the other two forms. The
manifest must be exactly that construction, with the storage-loop corpus's
requirements and the form requirements. Every entry must replay, and its
actual original Core history must equal the expected history, which is the
storage-loop corpus's, since the Core reference is unchanged. Each form must
cover the iteration counts zero, one and seven and both carries.
Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyStorageLoopCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Source.AssemblyStorage (Form)

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", AssemblyStorageLoop.profileVersion),
  ("loopProfileVersion", StorageLoop.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.StorageLoop.version),
  ("templateVersion", StorageLoop.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", AssemblyStorageLoop.emitterVersion), ("wrapperVersion", AssemblyStorageLoop.wrapperVersion)]

/-- The entries that run in every form. -/
private def everyForm : List String := ["seven-carried", "seven-counts"]

private def carryNames : List String := ["iteration", "rollback"]

/-- An imported storage-loop entry in a form. -/
private def inForm (entry : Json) (form : Form) : Except String Json := do
  let plan ← entry.getObjVal? "storageLoopPlan"
  return (entry.setObjVal! "id" (toJson ((← string entry "id") ++ "-" ++ form.name))).setObjVal! "storageLoopPlan"
    ((plan.setObjVal! "schema" (toJson AssemblyStorageLoop.planSchema)).setObjVal! "form" (toJson form.name))

/-- The corpus the definitions build from the storage-loop corpus. -/
def construction (parent : Json) : Except String (List Json) := do
  let mut turn := 0
  let mut result : List Json := []
  for entry in ← parent.getObjValAs? (List Json) "cases" do
    if (entry.getObjVal? "generation").isOk then
      result := result ++ [entry]
    else
      let form := Form.all.getD (turn % 3) .split
      turn := turn + 1
      result := result ++ [← inForm entry form]
      if everyForm.contains (← string entry "id") then
        for other in Form.all do
          if other != form then result := result ++ [← inForm entry other]
  return result

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := AssemblyStorageLoop.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let (plan, form) ← AssemblyStorageLoop.checkedPlan (← entry.getObjVal? "storageLoopPlan")
  let loop ← StorageLoop.checkedScenario plan (← StorageLoop.decodeTransactions plan.mask (← entry.getObjVal? "transactions"))
  AssemblyStorageLoop.emitCase ⟨loop, form⟩ (Json.mkObj [("kind", toJson "imported")]) fuel

/-- The carries of one scenario, as the storage-loop corpus defines them. -/
private def carries (trips : List Nat) (statuses : List String) : List String :=
  (if trips.any (· ≥ 2) then ["iteration"] else []) ++
  (if (trips.zip statuses).any (fun (count, status) => count ≥ 1 && status == "reverted") then ["rollback"] else [])

def validateManifest (manifest parent : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-assembly-storage-loops" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected inline Yul storage-loop manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("inline Yul storage-loop manifest changed " ++ key)
  require ((← string parent "profile") == "stateful-storage-loops") "the parent corpus is not the storage-loop corpus"
  -- The storage-loop corpus's requirements carry over unchanged.
  for key in ["requiredFeatures", "requiredInputs", "requiredMasks", "requiredIterationCounts", "requiredCarriedSlots",
      "requiredIterationCarries", "requiredHelperCounts", "requiredTransactionCounts", "requiredOutcomes",
      "requiredCompletionPatterns", "generationRecipeRequirements", "coverageKind", "generatorVersion"] do
    require ((← manifest.getObjVal? key) == (← parent.getObjVal? key)) ("inline Yul storage-loop manifest changed " ++ key)
  require ((← manifest.getObjValAs? (List String) "requiredForms") == Form.all.map Form.name &&
    (← manifest.getObjValAs? (List String) "requiredFormIterations") ==
      (Form.all.flatMap fun form => [0, 1, 7].map fun count => form.name ++ ":" ++ toString count) &&
    (← manifest.getObjValAs? (List String) "requiredFormCarries") ==
      (Form.all.flatMap fun form => carryNames.map fun carry => form.name ++ ":" ++ carry))
    "inline Yul storage-loop corpus must require every form with iterations 0, 1 and 7 and both carries"
  let entries ← manifest.getObjValAs? (List Json) "cases"
  require (entries == (← construction parent)) "inline Yul storage-loop corpus differs from its construction"
  let mut identifiers : List String := []
  let mut forms : List String := []
  let mut formIterations : List String := []
  let mut formCarries : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate inline Yul storage-loop corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← AssemblyStorageLoop.replayCase saved fuel) == saved)
      ("inline Yul storage-loop corpus entry did not replay: " ++ identifier)
    let scenario ← AssemblyStorageLoop.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "storageLoopPlan") == (← entry.getObjVal? "storageLoopPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported inline Yul storage-loop entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    let expectedFeatures ← entry.getObjValAs? (List String) "expectedFeatures"
    require (expectedFeatures.all caseFeatures.contains && caseFeatures.all expectedFeatures.contains)
      ("inline Yul storage-loop corpus features changed: " ++ identifier)
    let history := AssemblyStorageLoop.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("inline Yul storage-loop corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("inline Yul storage-loop expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the expected storage-loop history: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    let trips := scenario.transactions.map fun tx =>
      Solcore.Synthesis.Stateful.StorageLoopExecution.iterations scenario.plan.mask tx.input
    let form := scenario.form.name
    transactionTotal := transactionTotal + observed.length
    forms := (forms ++ [form]).eraseDups
    formIterations := (formIterations ++ trips.map fun count => form ++ ":" ++ toString count).eraseDups
    formCarries := (formCarries ++ (carries trips statuses).map (form ++ ":" ++ ·)).eraseDups
  require ((← manifest.getObjValAs? (List String) "requiredForms").all forms.contains &&
    (← manifest.getObjValAs? (List String) "requiredFormIterations").all formIterations.contains &&
    (← manifest.getObjValAs? (List String) "requiredFormCarries").all formCarries.contains)
    "inline Yul storage-loop corpus misses a form, a form's iteration count or a form's carry"
  return Json.mkObj [("profile", toJson "stateful-assembly-storage-loops"), ("scenarios", toJson entries.length),
    ("transactions", toJson transactionTotal), ("forms", toJson forms),
    ("formIterations", toJson formIterations), ("formCarries", toJson formCarries)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (reason : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid inline Yul storage-loop corpus unexpectedly passed: " ++ reason))

def testSourceAssemblyStorageLoopCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-assembly-storage-loop-corpus.json"))
  let parent ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-storage-loop-corpus.json"))
  let summary ← checked (validateManifest manifest parent)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first inline Yul storage-loop case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let withRow := fun (changed : Json) => replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changed)))
  -- An output, a slot and a missing row are checked, and so is the construction.
  rejects (validateManifest (withRow (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))))
    parent) "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow (row.setObjVal! "committedStorage"
    (.arr (storage.set! 8 (storage[8]!.setObjVal! "value" (toJson "7")))))) parent) "changed slot"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop))) parent) "popped history"
  let plan ← checked (first.getObjVal? "storageLoopPlan")
  rejects (validateManifest (replace first (first.setObjVal! "storageLoopPlan" (plan.setObjVal! "form" (toJson "pipelined"))))
    parent) "changed form"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr entries.pop)) parent) "dropped entry"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))) parent) "duplicated entry"
  for (key, value) in [
      ("profile", toJson "stateful-storage-loops"), ("emitterVersion", toJson "forged"),
      ("requiredMasks", toJson [1, 3, 7]), ("requiredForms", toJson ["split", "carried"]),
      ("requiredFormIterations", toJson ["split:0"]), ("requiredFormCarries", toJson ["split:iteration"])] do
    rejects (validateManifest (manifest.setObjVal! key value) parent) key
  rejects (validateManifest manifest (parent.setObjVal! "cases" (.arr #[]))) "another parent corpus"
  rejects (validateManifest manifest parent 0) "no fuel"
  IO.println summary.compress

end Tests.SourceAssemblyStorageLoopCorpus
end

section
-- leanmerge: from Solcore.Test.SourceKeccakLoopCases
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
end

section
-- leanmerge: from Solcore.Test.SourceKeccakLoopCorpus
/-! The fixed Keccak-loop corpus checks actual original Core histories against
expectations computed without the guarded contract: the source-loop model, a
counter over a slot map with Keccak slots and a log list, in which each step
runs alone in Core. The expectations cover status, output, slot zero, every
addressed entry slot and every committed log's emitter, topics and data.
Coverage describes the checked steps' AST, the inputs, the loop and key masks,
the iteration counts, the carries within a transaction, across committed
transactions and through a rollback, and the completions. Source/Rust/EVM
agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceKeccakLoopCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

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
  ("generatorVersion", generatorVersion), ("profileVersion", KeccakLoop.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.KeccakLoop.version),
  ("framingVersion", Solcore.Synthesis.Core.EventLog.framingVersion),
  ("templateVersion", KeccakLoop.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", KeccakLoop.emitterVersion), ("wrapperVersion", KeccakLoop.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := KeccakLoop.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← KeccakLoop.checkedPlan (← entry.getObjVal? "keccakLoopPlan")
  let scenario ← KeccakLoop.checkedScenario plan
    (← KeccakLoop.decodeTransactions plan.mask (← entry.getObjVal? "transactions"))
  KeccakLoop.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "keccak-loop-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

private def naturals (manifest : Json) (key : String) : Except String (List Nat) :=
  manifest.getObjValAs? (List Nat) key

/-- The carries of one scenario: `iteration` when an iteration reads the slot
zero the previous one wrote, `entry` when two iterations of a transaction
address one entry, `transaction` when an iteration reads an entry an earlier
committed transaction wrote, and `rollback` when a revert follows logged
iterations. -/
private def carries (keys : List (List Word)) (statuses : List String) : List String :=
  let trips := keys.map List.length
  (if trips.any (· ≥ 2) then ["iteration"] else []) ++
  (if keys.any (fun values => values.eraseDups.length < values.length) then ["entry"] else []) ++
  (if keys.zipIdx.any (fun (values, index) => values.any fun key =>
      ((keys.zip statuses).take index).any fun (earlier, status) => status == "returned" && earlier.contains key)
    then ["transaction"] else []) ++
  (if (trips.zip statuses).any (fun (count, status) => count ≥ 1 && status == "reverted") then ["rollback"] else [])

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-keccak-loops" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected Keccak-loop manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("Keccak-loop manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words KeccakLoop.boundaryInputs))
    "Keccak-loop corpus must require all six boundary inputs"
  require ((← naturals manifest "requiredMasks") == [0, 1, 3, 7] &&
    (← naturals manifest "requiredKeyMasks") == [0, 1, 3, 7] &&
    (← naturals manifest "requiredIterationCounts") == List.range 8)
    "Keccak-loop corpus must require every loop mask, key mask and iteration count"
  require ((← strings manifest "requiredIterationCarries") == ["entry", "iteration", "rollback", "transaction"])
    "Keccak-loop corpus must require carries within a transaction, across transactions and through a rollback"
  require ((← naturals manifest "requiredHelperCounts") == [1, 2, 3] &&
    (← naturals manifest "requiredTransactionCounts") == [1, 2, 3])
    "Keccak-loop corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "Keccak-loop corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "Keccak-loop corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "Keccak-loop corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "Keccak-loop corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut masks : List Nat := []
  let mut keyMasks : List Nat := []
  let mut counts : List Nat := []
  let mut carried : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  let mut logTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate Keccak-loop corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← KeccakLoop.replayCase saved fuel) == saved) ("Keccak-loop corpus entry did not replay: " ++ identifier)
    let scenario ← KeccakLoop.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "keccakLoopPlan") == (← entry.getObjVal? "keccakLoopPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported Keccak-loop entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("Keccak-loop corpus features changed: " ++ identifier)
    let history := KeccakLoop.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("Keccak-loop corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("Keccak-loop expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage"),
        ("logs", ← row.getObjVal? "logs")]
      require (actual == golden)
        ("original Core differs from the source-loop model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
      logTotal := logTotal + (← row.getObjValAs? (List Json) "logs").length
    let mask := scenario.plan.mask
    let keys := scenario.transactions.map fun tx =>
      Solcore.Synthesis.Stateful.KeccakLoopExecution.keys mask scenario.plan.keyMask tx.input
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    masks := (masks ++ [mask]).eraseDups
    keyMasks := (keyMasks ++ [scenario.plan.keyMask]).eraseDups
    counts := (counts ++ keys.map List.length).eraseDups
    carried := (carried ++ carries keys statuses).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "Keccak-loop corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "Keccak-loop corpus misses a boundary input"
  require ([0, 1, 3, 7].all masks.contains && [0, 1, 3, 7].all keyMasks.contains && (List.range 8).all counts.contains)
    "Keccak-loop corpus misses a loop mask, a key mask or an iteration count"
  require (["entry", "iteration", "rollback", "transaction"].all carried.contains) "Keccak-loop corpus misses a carry"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "Keccak-loop corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "Keccak-loop corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "Keccak-loop corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-keccak-loops"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("logs", toJson logTotal), ("masks", toJson masks),
    ("keyMasks", toJson keyMasks), ("iterationCounts", toJson counts), ("carries", toJson carried),
    ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (reason : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid Keccak-loop corpus unexpectedly passed: " ++ reason))

def testSourceKeccakLoopCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-keccak-loop-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first Keccak-loop case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated Keccak-loop case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let withRow := fun (changed : Json) => replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changed)))
  -- An output, a slot, a log, a missing row and a status are all checked.
  rejects (validateManifest (withRow (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let last := storage.size - 1
  rejects (validateManifest (withRow (row.setObjVal! "committedStorage"
    (.arr (storage.set! last (storage[last]!.setObjVal! "value" (toJson "7"))))))) "changed entry"
  rejects (validateManifest (withRow (row.setObjVal! "committedStorage" (.arr storage.pop)))) "dropped slot"
  let logs ← checked (row.getObjValAs? (Array Json) "logs")
  let some log := logs[0]? | throw (IO.userError "the first Keccak-loop history row commits no log")
  let topics ← checked (log.getObjValAs? (Array String) "topics")
  for (changed, reason) in [
      (logs.set! 0 (log.setObjVal! "topics" (toJson (topics.set! 1 "1"))), "changed key topic"),
      (logs.set! 0 (log.setObjVal! "topics" (toJson topics.reverse)), "reordered topics"),
      (logs.set! 0 (log.setObjVal! "data" (toJson "0x")), "removed data"),
      (logs.pop, "removed log"), (logs.push log, "duplicated log")] do
    rejects (validateManifest (withRow (row.setObjVal! "logs" (.arr changed)))) reason
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped))))))) "flipped status"
  -- A recorded iteration count, the loop mask and the key mask are all checked.
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "iterations" (toJson 0))))))) "changed iterations"
  let plan ← checked (first.getObjVal? "keccakLoopPlan")
  rejects (validateManifest (replace first (first.setObjVal! "keccakLoopPlan" (plan.setObjVal! "mask" (toJson 3)))))
    "changed loop mask"
  let keyMask ← checked (plan.getObjValAs? Nat "keyMask")
  rejects (validateManifest (replace first (first.setObjVal! "keccakLoopPlan"
    (plan.setObjVal! "keyMask" (toJson (if keyMask == 7 then 3 else 7)))))) "changed key mask"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
    "removed features"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first)))) "duplicated entry"
  for (key, value) in [
      ("profile", toJson "stateful-storage-loops"), ("templateVersion", toJson "forged"),
      ("framingVersion", toJson "forged"), ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredMasks", toJson [1, 3, 7]), ("requiredKeyMasks", toJson [0, 7]),
      ("requiredIterationCounts", toJson [0, 1, 7]),
      ("requiredIterationCarries", toJson (["iteration", "rollback"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "no fuel"
  IO.println summary.compress

end Tests.SourceKeccakLoopCorpus
end

section
-- leanmerge: from Solcore.Test.SourceKeccakLoopGolden
/-! Golden cases for the Keccak-loop profile. Every expected value is written
out by hand from the protocol, not computed by either model; only the slots
that hold the entries come from the independent `Solcore.Abi.V1.Keccak256`.
The steps add a known constant `c`, so iteration `i` writes
`entries[key] + acc + input + c` to the entry of its key
`(input & ~7) | (i & keyMask)` and then to `acc`, and logs the counter, the key
and the value; afterwards the result is `acc` plus the iteration count, which
odd flags revert. The sequences cover key masks 0, 1, 3 and 7, loop masks 0, 3
and 7, zero to three and five to seven iterations, reverts after one, two,
five and seven logged iterations, which keep the prior storage and commit no
log, entries reused within a transaction and across transactions, entries
keyed by the input's high part and wrapping sums. Both the guarded Core
contract and the source-loop model must give each row. -/
set_option autoImplicit false

namespace Tests.SourceKeccakLoopGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.KeccakLoopExecution (Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- The expected row: status, output Word, `acc`, every nonzero entry as a
`(key, value)` pair and the committed logs as `(counter, key, value)`. -/
structure Expected where
  status : String
  output : Nat
  acc : Nat
  entries : List (Nat × Nat)
  logs : List (Nat × Nat × Nat)

def highKey : Nat := 2 ^ 255
def topKey : Nat := 2 ^ 256 - 8

private def tx (index flags input : Nat) : Transaction := ⟨"tx-" ++ toString index, w flags, w input⟩

private def sevenEntries : List (Nat × Nat) := [(0, 12), (1, 20), (2, 28), (3, 36), (4, 44), (5, 52), (6, 60)]

/-- Loop and key masks 7 and `c = 1`: every iteration has its own entry. No
iteration; one; seven, the first rereading entry 0; a revert after seven
logged iterations; then three iterations on the high part's entries, whose
sums wrap. -/
def sevenRows : List (Transaction × Expected) := [
  (tx 0 0 0, ⟨"returned", 0, 0, [], []⟩),
  -- 0 + 0 + 1 + 1 = 2 at key 0; result 2 + 1.
  (tx 1 0 1, ⟨"returned", 3, 2, [(0, 2)], [(0, 0, 2)]⟩),
  -- With 7 + 1 added: 2 + 2 + 8 = 12 at key 0, then 0 + 12 + 8 = 20 at key 1,
  -- 28, 36, 44, 52 and 60; result 60 + 7.
  (tx 2 0 7, ⟨"returned", 67, 60, sevenEntries,
    [(0, 0, 12), (1, 1, 20), (2, 2, 28), (3, 3, 36), (4, 4, 44), (5, 5, 52), (6, 6, 60)]⟩),
  -- 12 + 60 + 8 = 80, then 20 + 80 + 8 = 108, 144, 188, 240, 300 and 368;
  -- result 375, reverted: no log and the prior storage.
  (tx 3 1 7, ⟨"reverted", 375, 60, sevenEntries, []⟩),
  -- With 2^255 + 3 + 1 added: 0 + 60 gives 2^255 + 64 at key 2^255, then
  -- 0 + 2^255 + 64 wraps to 68 at key 2^255 + 1, and 0 + 68 gives 2^255 + 72
  -- at key 2^255 + 2; result 2^255 + 75.
  (tx 4 2 (highKey + 3), ⟨"returned", highKey + 75, highKey + 72,
    sevenEntries ++ [(highKey, highKey + 64), (highKey + 1, 68), (highKey + 2, highKey + 72)],
    [(0, highKey, highKey + 64), (1, highKey + 1, 68), (2, highKey + 2, highKey + 72)]⟩)]

/-- Loop mask 7, key mask 0 and `c = 0`: every iteration of a transaction
shares one entry. Three iterations on entry 0; one on entry 8, from the
input's high part; a revert after two iterations on entry 0; one iteration
rereading the entry the revert left; then seven. -/
def zeroRows : List (Transaction × Expected) := [
  -- 0 + 0 + 3 = 3, then 3 + 3 + 3 = 9 and 9 + 9 + 3 = 21; result 24.
  (tx 0 0 3, ⟨"returned", 24, 21, [(0, 21)], [(0, 0, 3), (1, 0, 9), (2, 0, 21)]⟩),
  -- 0 + 21 + 9 = 30 at key 8; result 31.
  (tx 1 0 9, ⟨"returned", 31, 30, [(0, 21), (8, 30)], [(0, 8, 30)]⟩),
  -- 21 + 30 + 2 = 53, then 53 + 53 + 2 = 108; result 110, reverted.
  (tx 2 3 2, ⟨"reverted", 110, 30, [(0, 21), (8, 30)], []⟩),
  -- 21 + 30 + 1 = 52; result 53.
  (tx 3 0 1, ⟨"returned", 53, 52, [(0, 52), (8, 30)], [(0, 0, 52)]⟩),
  -- 52 + 52 + 7 = 111, then twice the last plus 7: 229, 465, 937, 1881, 3769
  -- and 7545; result 7552.
  (tx 4 0 7, ⟨"returned", 7552, 7545, [(0, 7545), (8, 30)],
    [(0, 0, 111), (1, 0, 229), (2, 0, 465), (3, 0, 937), (4, 0, 1881), (5, 0, 3769), (6, 0, 7545)]⟩)]

/-- Loop mask 3, key mask 1 and `c = 2`: iterations alternate two entries.
Three iterations on entries 0, 1 and 0; three on the top input's entries,
where `input + c` wraps to 1; a revert after one iteration; then two
iterations rereading entries 0 and 1. -/
def oneRows : List (Transaction × Expected) := [
  -- 0 + 0 + 5 = 5 at key 0, 0 + 5 + 5 = 10 at key 1, 5 + 10 + 5 = 20 at key 0.
  (tx 0 0 3, ⟨"returned", 23, 20, [(0, 20), (1, 10)], [(0, 0, 5), (1, 1, 10), (2, 0, 20)]⟩),
  -- 0 + 20 + 1 = 21 at key 2^256 - 8, 0 + 21 + 1 = 22 at the next, then
  -- 21 + 22 + 1 = 44 at 2^256 - 8 again; result 47.
  (tx 1 0 (2 ^ 256 - 1), ⟨"returned", 47, 44, [(0, 20), (1, 10), (topKey, 44), (topKey + 1, 22)],
    [(0, topKey, 21), (1, topKey + 1, 22), (2, topKey, 44)]⟩),
  -- 20 + 44 + 3 = 67; result 68, reverted.
  (tx 2 1 1, ⟨"reverted", 68, 44, [(0, 20), (1, 10), (topKey, 44), (topKey + 1, 22)], []⟩),
  -- 20 + 44 + 4 = 68 at key 0, then 10 + 68 + 4 = 82 at key 1; result 84.
  (tx 3 0 2, ⟨"returned", 84, 82, [(0, 68), (1, 82), (topKey, 44), (topKey + 1, 22)],
    [(0, 0, 68), (1, 1, 82)]⟩)]

/-- Loop mask 7, key mask 3 and `c = 0`: iterations cycle four entries. Six
iterations, the last two rereading entries 0 and 1; then a revert after five
iterations, the fifth rewriting the entry of the first. -/
def threeRows : List (Transaction × Expected) := [
  -- 6, 12, 18 and 24 at keys 0 to 3, then 6 + 24 + 6 = 36 at key 0 and
  -- 12 + 36 + 6 = 54 at key 1; result 60.
  (tx 0 0 6, ⟨"returned", 60, 54, [(0, 36), (1, 54), (2, 18), (3, 24)],
    [(0, 0, 6), (1, 1, 12), (2, 2, 18), (3, 3, 24), (4, 0, 36), (5, 1, 54)]⟩),
  -- 36 + 54 + 5 = 95, 154, 177, 206, then 95 + 206 + 5 = 306; result 311.
  (tx 1 1 5, ⟨"reverted", 311, 54, [(0, 36), (1, 54), (2, 18), (3, 24)], []⟩)]

/-- Loop mask 0 and `c = 5`: no iteration whatever the input. -/
def idleRows : List (Transaction × Expected) := [
  (tx 0 0 7, ⟨"returned", 0, 0, [], []⟩),
  (tx 1 1 1, ⟨"reverted", 0, 0, [], []⟩)]

private def emitter : String := toString StorageExecution.fixtureBindings.address.val

private def wordText (value : Nat) : String := encodeBytesText (encodeWordBytesBE (w value))

private def valueAt (expected : Expected) (slot : Word) : Nat :=
  if slot == w 0 then expected.acc
  else ((expected.entries.find? fun (key, _) => KeccakLoopExecution.entrySlot (w key) == slot).map Prod.snd).getD 0

private def storageJson (slots : List Word) (expected : Expected) : Json :=
  toJson (slots.map fun slot => Json.mkObj [
    ("slot", toJson (toString slot.val)), ("value", toJson (toString (valueAt expected slot)))])

private def logsJson (expected : Expected) : Json :=
  toJson (expected.logs.map fun (counter, key, value) => Json.mkObj [
    ("address", toJson emitter), ("topics", toJson [toString counter, toString key]),
    ("data", toJson (wordText value))])

def check (name : String) (slots : List Word) (row : Json) (model : KeccakLoopExecution.ModelRow)
    (expected : Expected) : IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (wordText expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (storageJson slots expected) &&
      (row.getObjVal? "logs").toOption == some (logsJson expected))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") && model.result == w expected.output &&
      KeccakLoopExecution.modelSlots model slots == slots.map (fun slot => w (valueAt expected slot)) &&
      model.logs == expected.logs.map (fun (counter, key, value) =>
        ({ordinal := counter, key := w key, value := w value} : KeccakLoopExecution.ModelLog)))
    s!"{name}: the source-loop model differs from the expected row"

/-- Each golden sequence's name, loop mask, key mask, step constant, rows and
addressed keys. -/
def goldenPlans : List (String × Nat × Nat × Nat × List (Transaction × Expected) × List Nat) := [
  ("key mask 7", 7, 7, 1, sevenRows, (List.range 7) ++ [highKey, highKey + 1, highKey + 2]),
  ("key mask 0", 7, 0, 0, zeroRows, [0, 8]),
  ("key mask 1", 3, 1, 2, oneRows, [0, 1, topKey, topKey + 1]),
  ("key mask 3", 7, 3, 0, threeRows, [0, 1, 2, 3]),
  ("loop mask 0", 0, 3, 5, idleRows, [])]

def testSourceKeccakLoopGolden : IO Unit := do
  let fuel := 1000000
  for (name, mask, keyMask, constant, rows, addressed) in goldenPlans do
    let step ← step constant
    let some plan := KeccakLoop.CheckedPlan.ofParts? step mask keyMask
      | throw (IO.userError s!"{name}: the Keccak-loop wrapper failed admission")
    let transactions := rows.map Prod.fst
    -- The observed slots are slot zero and the entry slot of every addressed
    -- key, in increasing order.
    let slots := KeccakLoopExecution.observedSlots mask keyMask transactions
    ensure (slots.length == addressed.length + 1 && slots.contains (w 0) &&
        addressed.all (fun key => slots.contains (KeccakLoopExecution.entrySlot (w key))) &&
        (slots.zip slots.tail).all (fun (lower, upper) => lower.val < upper.val))
      s!"{name}: the observed slots differ from the addressed keys"
    let history := KeccakLoopExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    ensure ((history.getObjVal? "observedSlots").toOption == some (KeyedStorageExecution.slotsJson slots))
      s!"{name}: the history observes other slots"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := KeccakLoopExecution.model step fuel mask keyMask transactions
      | throw (IO.userError s!"{name}: the source-loop model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" slots row model expected
      -- The recorded iteration count is the input's bits under the mask.
      ensure (KeccakLoopExecution.iterations mask transaction.input ≤ mask) s!"{name}: iterations exceed the mask"
  -- The plan admits exactly the four loop masks and the four key masks.
  let constant ← step 1
  for mask in [2, 4, 5, 6, 8, 15] do
    ensure (KeccakLoop.CheckedPlan.ofParts? constant mask 0).isNone s!"loop mask {mask} was admitted"
    ensure (KeccakLoop.CheckedPlan.ofParts? constant 1 mask).isNone s!"key mask {mask} was admitted"

end Tests.SourceKeccakLoopGolden
end

section
-- leanmerge: from Solcore.Test.SourceAssemblyKeccakLoopGolden
/-! Golden cases for the inline Yul Keccak-loop profile. The contract of each
form is written out by hand for the plan with loop mask seven and key mask
one, and the step functions must be the Keccak-loop profile's. The Keccak-loop
profile's hand-written rows, with every entry and log, must come back through
the new cases: every golden plan, in every form, is emitted as an inline Yul
case, decoded, and its unchanged Core reference observed. A changed
expectation must fail. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyKeccakLoopGolden

open Lean
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Source.AssemblyStorage (Form)
open Tests.SourceKeccakLoopGolden (Expected goldenPlans)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def occurs (text part : String) : Bool := (text.splitOn part).length > 1

private def head : List String := [
  "contract SynthesizedAssemblyKeccakLoops {",
  "    acc: word;",
  "    entries: mapping(word => word);",
  "",
  "    function run(flags: uint256, input: uint256) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_limit: word = (sc_input & 7);",
  "        let sc_base: word = (sc_input & ~7);",
  "        let sc_counter: word = 0;",
  "        let sc_key: word = 0;"]

private def locals : List String := [
  "        let sc_sum: word = 0;",
  "        let sc_value: word = 0;",
  "        let sc_result: word = 0;",
  "        let sc_ptr: word = 0;",
  "        assembly {",
  "            sc_ptr := mload(64)",
  "            mstore(64, add(sc_ptr, 64))",
  "        }"]

private def tail : List String := [
  "        assembly {",
  "            sc_result := add(sload(0), sc_limit)",
  "            if and(sc_flags, 1) {",
  "                mstore(sc_ptr, sc_result)",
  "                revert(sc_ptr, 32)",
  "            }",
  "        }",
  "        return uint256(sc_result);",
  "    }",
  "}"]

/-- The contract of the plan with loop mask seven and key mask one in each form. -/
private def contracts : List (Form × List String) := [
  (.split, head ++ locals ++ [
    "        while (sc_limit > sc_counter) {",
    "            assembly {",
    "                sc_key := or(sc_base, and(sc_counter, 1))",
    "                mstore(sc_ptr, 1)",
    "                mstore(add(sc_ptr, 32), sc_key)",
    "                sc_sum := add(add(sload(keccak256(sc_ptr, 64)), sload(0)), sc_input)",
    "            }",
    "            sc_value = sc_step(sc_sum);",
    "            assembly {",
    "                mstore(sc_ptr, 1)",
    "                mstore(add(sc_ptr, 32), sc_key)",
    "                sstore(keccak256(sc_ptr, 64), sc_value)",
    "                sstore(0, sc_value)",
    "                mstore(sc_ptr, sc_value)",
    "                log2(sc_ptr, 32, sc_counter, sc_key)",
    "            }",
    "            sc_counter = (sc_counter + 1);",
    "        }"] ++ tail),
  (.carried, head ++ ["        let sc_slot: word = 0;"] ++ locals ++ [
    "        while (sc_limit > sc_counter) {",
    "            assembly {",
    "                sc_key := or(sc_base, and(sc_counter, 1))",
    "                mstore(sc_ptr, 1)",
    "                mstore(add(sc_ptr, 32), sc_key)",
    "                sc_slot := keccak256(sc_ptr, 64)",
    "                sc_sum := add(add(sload(sc_slot), sload(0)), sc_input)",
    "            }",
    "            sc_value = sc_step(sc_sum);",
    "            assembly {",
    "                sstore(sc_slot, sc_value)",
    "                sstore(0, sc_value)",
    "                mstore(sc_ptr, sc_value)",
    "                log2(sc_ptr, 32, sc_counter, sc_key)",
    "                sc_counter := add(sc_counter, 1)",
    "            }",
    "        }"] ++ tail),
  (.pipelined, head ++ ["        let sc_slot: word = 0;"] ++ locals ++ [
    "        assembly {",
    "            if gt(sc_limit, sc_counter) {",
    "                sc_key := or(sc_base, and(sc_counter, 1))",
    "                mstore(sc_ptr, 1)",
    "                mstore(add(sc_ptr, 32), sc_key)",
    "                sc_slot := keccak256(sc_ptr, 64)",
    "                sc_sum := add(add(sload(sc_slot), sload(0)), sc_input)",
    "            }",
    "        }",
    "        while (sc_limit > sc_counter) {",
    "            sc_value = sc_step(sc_sum);",
    "            assembly {",
    "                sstore(sc_slot, sc_value)",
    "                sstore(0, sc_value)",
    "                mstore(sc_ptr, sc_value)",
    "                log2(sc_ptr, 32, sc_counter, sc_key)",
    "                sc_counter := add(sc_counter, 1)",
    "                if gt(sc_limit, sc_counter) {",
    "                    sc_key := or(sc_base, and(sc_counter, 1))",
    "                    mstore(sc_ptr, 1)",
    "                    mstore(add(sc_ptr, 32), sc_key)",
    "                    sc_slot := keccak256(sc_ptr, 64)",
    "                    sc_sum := add(add(sload(sc_slot), sload(0)), sc_input)",
    "                }",
    "            }",
    "        }"] ++ tail)]

/-- The source before the contract, without its `std.opcodes` import. -/
private def stepPart (source : String) : List String :=
  ((source.splitOn "contract ").headD "").splitOn "\n" |>.filter (!·.endsWith "from std.opcodes;")

/-- Every row of a golden plan through the inline Yul case of one form. -/
private def checkRows (name : String) (form : Form) (mask keyMask constant : Nat)
    (rows : List (KeccakLoopExecution.Transaction × Expected)) (fuel : Nat) : IO Unit := do
  let step ← Tests.SourceKeccakLoopGolden.step constant
  let some plan := KeccakLoop.CheckedPlan.ofParts? step mask keyMask
    | throw (IO.userError s!"{name}: the Keccak-loop wrapper failed admission")
  let transactions := rows.map Prod.fst
  let loop ← get (Solcore.Synthesis.Source.KeccakLoop.checkedScenario plan transactions)
  let json ← get (Solcore.Synthesis.Source.AssemblyKeccakLoop.emitCase ⟨loop, form⟩
    (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((Solcore.Synthesis.Source.AssemblyKeccakLoop.replayCase json fuel).toOption == some json)
    s!"{name} {form.name}: the case does not replay"
  let scenario ← get (Solcore.Synthesis.Source.AssemblyKeccakLoop.caseProgram json)
  ensure (scenario.form == form) s!"{name} {form.name}: the decoded form differs"
  let slots := scenario.loop.observedSlots
  let history := Solcore.Synthesis.Source.AssemblyKeccakLoop.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name} {form.name}: the history is incomplete"
  let observed ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := KeccakLoopExecution.model step fuel mask keyMask transactions
    | throw (IO.userError s!"{name}: the source-loop model failed")
  ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name} {form.name}: a row is missing"
  for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
    Tests.SourceKeccakLoopGolden.check s!"{name} {form.name} {transaction.id}" slots row model expected

def testSourceAssemblyKeccakLoopGolden : IO Unit := do
  let fuel := 1000000
  -- Each form's contract, and the Keccak-loop profile's step functions.
  let step ← Tests.SourceKeccakLoopGolden.step 2
  let some plan := KeccakLoop.CheckedPlan.ofParts? step 7 1
    | throw (IO.userError "the plan with masks seven and one failed admission")
  let parent ← get ((Solcore.Synthesis.Source.KeccakLoop.emit plan).mapError reprStr)
  for (form, expected) in contracts do
    let emitted ← get ((Solcore.Synthesis.Source.AssemblyKeccakLoop.emit form plan).mapError reprStr)
    let some contract := (emitted.source.splitOn "contract ").getLast?
      | throw (IO.userError "the emitted source has no contract")
    ensure (("contract " ++ contract) == String.intercalate "\n" expected ++ "\n")
      s!"{form.name}: the emitted contract differs from the golden text:\n{contract}"
    ensure (stepPart emitted.source == stepPart parent.source && !occurs emitted.source "revert_(" &&
        !occurs emitted.source "sc_log2" && !occurs emitted.source "entries[" &&
        !occurs emitted.source "from std.opcodes")
      s!"{form.name}: the step functions or imports differ from the Keccak-loop profile's"
  -- The Keccak-loop profile's rows, through every form.
  for (name, mask, keyMask, constant, rows, _) in goldenPlans do
    for form in Form.all do
      checkRows name form mask keyMask constant rows fuel
  -- A changed expectation fails.
  let some (name, mask, keyMask, constant, rows, _) := goldenPlans.head? | throw (IO.userError "no golden plan")
  let some ((transaction, expected), rest) := rows.getLast?.map (fun last => (last, rows.dropLast))
    | throw (IO.userError "no golden row")
  let changed := rest ++ [(transaction, {expected with output := expected.output + 1})]
  let failed ← tryCatch (do checkRows name .pipelined mask keyMask constant changed fuel; pure false)
    (fun _ => pure true)
  ensure failed "a changed expectation passed"

end Tests.SourceAssemblyKeccakLoopGolden
end

section
-- leanmerge: from Solcore.Test.SourceLoopCases
/-! Loop case regressions cover the canonical reference, arbitrary step entry,
zero and positive iterations, provenance, resource exits and sealed reductions. -/
set_option autoImplicit false

namespace Tests.SourceLoopCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.BoundedLoop (CheckedPlan)

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
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "loop step fixture failed checked admission")
private def plan (step : Aggregates.CheckedDAG) (mask : Nat) : IO CheckedPlan :=
  match CheckedPlan.ofParts? step mask with
  | some value => pure value
  | none => throw (IO.userError "loop plan fixture failed checked admission")
private def imported (value : CheckedPlan) (input : Word) : IO Json :=
  get (Loop.emitCase value input (Json.mkObj [("kind", toJson "imported")]) 10000)
private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

/-- Every step call must allocate a fresh private cell. The arbitrary entry
subtracts one, so substituting the last helper would give the wrong recurrence. -/
private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

private def referenceChecks : IO Unit := do
  let graph ← checked [privateStep] (.binary .wordSub entry (word 1))
  for mask in [0, 1, 3, 7] do
    let value ← plan graph mask
    ensure (Wire.programNodes (value.instantiate Word.zero) ==
      Wire.programNodes graph.program + BoundedLoop.appliedOverhead mask)
      "measured loop wrapper overhead did not match the complete reference"
    ensure (BoundedLoop.appliedOverhead mask == 14 + 12 * mask)
      "canonical loop guard skeleton changed unexpectedly"
    let mut source : Option String := none
    for input in Loop.boundaryInputs do
      let iterations := input.bitAnd (Word.ofNatModulo mask)
      ensure (Loop.observe value input 10000 == returned (input.add iterations))
        s!"loop index/entry/private-cell mismatch: mask {mask}, input {input.val}"
      let saved ← imported value input
      let current ← string saved "source"
      if let some previous := source then ensure (current == previous) "loop source depends on runtime input"
      source := some current
      let admitted ← get (Loop.caseProgram saved)
      ensure (admitted.program.check && admitted.input == input && admitted.plan.mask == mask)
        "loop case lost its checked canonical reference"
      ensure ((← get (Loop.replayCase saved 10000)) == saved) "imported loop did not replay"
      ensure ((← get (Loop.replayCase (saved.setObjVal! "directCore" (returned Word.zero)) 10000)) == saved)
        "loop replay trusted its stored expected result"
      let low ← get (Loop.replayCase saved 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "loop fuel exhaustion was treated as completion"
  let identity ← checked [.var 0]
  let identityPlan ← plan identity 7
  ensure (!(Loop.inputSensitive identityPlan 10000).isOk)
    "zero-iteration input differences allowed an identity loop through the filter"
  let constant ← checked [word 4]
  let constantPlan ← plan constant 7
  ensure (!(Loop.inputSensitive constantPlan 10000).isOk)
    "generated loop lost the step's input-sensitive requirement"
  let zero ← plan graph 0
  ensure (!(Loop.inputSensitive zero 10000).isOk) "generated mask-zero loop passed nontriviality"
  ensure ((Loop.checkedPlan (Loop.planJson zero)).isOk) "imported mask-zero loop was rejected"
  ensure ((CheckedPlan.ofParts? graph 2).isNone) "non-mask loop bound was admitted"

private def minimumBudget (seed : Nat) : IO Nat := do
  for nodes in List.range 513 do
    if (Loop.generatedPlan (Seed.ofNat seed) nodes).isOk then return nodes
  throw (IO.userError "loop skeleton did not fit the case node limit")

private def generationChecks : IO Json := do
  -- All joint helper/template/mask residues have a bounded, fully checked skeleton.
  for seed in List.range 36 do
    let budget ← minimumBudget seed
    ensure (budget ≤ 384) "default loop budget cannot hold a selected template skeleton"
    let (value, _) ← get (Loop.generatedPlan (Seed.ofNat seed) budget)
    ensure (Wire.programNodes (value.instantiate Word.zero) ≤ budget &&
      value.mask == Loop.maskFor (Seed.ofNat seed) && value.step.helpers.length == 1 + seed % 3)
      "loop generation escaped its full node, mask or helper constraints"
    ensure (!(Loop.generatedPlan (Seed.ofNat seed) (budget - 1)).isOk &&
      !(Loop.generatedPlan (Seed.ofNat seed) 513).isOk) "loop node bounds were not enforced"
  let corpus := Loop.generateCases (Seed.ofNat 0) 384 12 512 10000
  ensure (corpus == Loop.generateCases (Seed.ofNat 0) 384 12 512 10000)
    "loop generation is nondeterministic"
  let rows ← cases corpus
  ensure (rows.size == 12 && (← natural corpus "attempted") ≤ 512)
    "bounded loop generation did not complete"
  for (row, index) in rows.toList.zipIdx do
    let admitted ← get (Loop.caseProgram row)
    ensure (Wire.programNodes admitted.program ≤ 384 &&
      some admitted.input == Loop.boundaryInputs[index % 6]?) "loop generation changed boundary order/budget"
    ensure ((← get (Loop.replayCase row 10000)) == row) "generated loop provenance did not replay"
    let low ← get (Loop.replayCase row 0)
    ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
      "fresh loop observation fuel changed saved validation fuel"
  let saved := rows[5]!
  let origin ← field (← field saved "provenance") "origin"
  let seedText ← string origin "seed"
  let some seed := seedText.toNat? | throw (IO.userError "invalid generated seed")
  let low := Loop.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource")
    "loop generation fuel exhaustion was classified as a semantic exclusion"
  ensure ((← cases (Loop.generateCases (Seed.ofNat seed) 384 5 1 10000)).size == 5 &&
    (← string (Loop.generateCases (Seed.ofNat seed) 384 7 1 10000) "status") == "generation-exhausted")
    "loop count/attempt limits did not distinguish cases from function candidates"
  ensure ((← natural (Loop.generateCases (Seed.ofNat seed) 384 0 100 10000) "attempted") == 0 &&
    (← cases (Loop.generateCases (Seed.ofNat seed) 384 1 0 10000)).isEmpty)
    "empty loop generation budgets consumed work"
  return saved

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion",
      "stepProfileVersion", "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Loop.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 10000) "tampered loop version accepted"
  for (name, value) in [("seed", toJson "00"), ("finalSeed", toJson "forged"),
      ("maxProgramNodes", toJson (513 : Nat)), ("mask", toJson (0 : Nat)),
      ("stepOrigin", Json.null), ("inputIndex", toJson (6 : Nat)),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Loop.replayCase (withOrigin (origin.setObjVal! name value)) 10000)
      s!"tampered loop {name} accepted"
  let stepOrigin ← field origin "stepOrigin"
  for name in ["seed", "finalSeed", "maxProgramNodes", "helpers", "helperCount"] do
    rejected (Loop.replayCase (withOrigin (origin.setObjVal! "stepOrigin"
      (stepOrigin.setObjVal! name Json.null))) 10000) "tampered nested step recipe accepted"
  let admitted ← get (Loop.caseProgram saved)
  let wrongProgram := Wire.encodeProgram (admitted.plan.step.instantiate admitted.input)
  for kind in ["imported", "reduced", "loop-generated"] do
    let changed := (withOrigin (origin.setObjVal! "kind" (toJson kind))).setObjVal! "program" wrongProgram
    rejected (Loop.caseProgram changed) "noncanonical program accepted under a different origin"
    rejected (Loop.replayCase changed 10000) "replay skipped canonical comparison for an origin"
  let loopPlan ← field saved "loopPlan"
  for (name, value) in [("mask", toJson (2 : Nat)), ("schema", toJson "unknown"),
      ("unexpected", toJson true)] do
    rejected (Loop.checkedPlan (loopPlan.setObjVal! name value)) "malformed loop plan accepted"
  rejected (Loop.caseProgram (saved.setObjVal! "input" (toJson "01"))) "noncanonical loop input accepted"
  rejected (Loop.caseProgram (saved.setObjVal! "input" (toJson "0"))) "input/reference mismatch accepted"
  rejected (Loop.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale loop source accepted"
  let contract ← field saved "contract"
  rejected (Loop.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "calldata" (toJson "0x"))) 10000)
    "wrong loop ABI input accepted"

private def shrinkChecks : IO Unit := do
  let graph ← checked [Aggregate.template 3 (word 2)]
  let value ← plan graph 7
  let saved ← imported value Word.maximum
  let original ← get (Loop.caseProgram saved)
  let shrunk ← get (Loop.shrinkCases saved 1000 10000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Loop.shrinkCases saved 1000 10000)))
    "loop shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut inputReduced := false
  let mut maskReduced := false
  let mut stepReduced := false
  for row in rows do
    let candidate ← get (Loop.caseProgram row)
    ensure (candidate.program.check && candidate.plan.step.helpers.length == graph.helpers.length &&
      Aggregate.bindingInventory candidate.plan.step == Aggregate.bindingInventory graph &&
      candidate.plan.mask ≤ value.mask)
      "loop reduction lost a step binder/helper or enlarged its mask"
    ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
      "loop reduction did not decrease the full original Core program"
    let key := (Wire.encodeProgram candidate.program).compress
    ensure (!seen.contains key) "loop reduction duplicated a canonical program"
    seen := key :: seen
    ensure ((← get (Loop.replayCase row 10000)) == row) "loop reduction did not replay"
    inputReduced := inputReduced || candidate.input != original.input
    maskReduced := maskReduced || candidate.plan.mask == 0
    stepReduced := stepReduced || Wire.encodeProgram candidate.plan.step.program != Wire.encodeProgram graph.program
  ensure (inputReduced && maskReduced && stepReduced) "loop reduction omitted input, zero-mask or step candidates"
  ensure ((← cases (← get (Loop.shrinkCases saved 2 10000))) == rows.extract 0 2 &&
    (← cases (← get (Loop.shrinkCases saved 0 10000))).isEmpty) "loop shrink limit changed ordering"

def testSourceLoopCases : IO Unit := do
  referenceChecks
  let saved ← generationChecks
  tamperingChecks saved
  shrinkChecks

end Tests.SourceLoopCases
end

section
-- leanmerge: from Solcore.Test.SourceLoopEmitter
/-! The finite Core oracle and source while loop share a checked step DAG, not
a counter implementation. Regression cases cover fixed initial bounds, all
allowed masks, arbitrary entries, wrapping Words and fresh cells on every call. -/
set_option autoImplicit false

namespace Tests.SourceLoopEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Core.BoundedLoop (CheckedPlan)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
def entry : Wire.Expr := .apply (.var 1) (.var 0)
def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

/-- One private cell per step, with its left pair field snapshotted before the
right field overwrites the cell. Reusing a prior call's cell changes the result. -/
def mutableStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.pair (.loadCell (.var 0))
      (.letE (.storeCell (.var 0) (word 2)) (.loadCell (.var 1))))
      (.binary .wordAdd (.first (.var 0)) (.second (.var 0))))

def arbitraryEntry : Wire.Expr := .binary .wordAdd (.apply (.var 1) (.var 0)) (word 10)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def step (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "loop step did not pass the aggregate DAG checker")

private def checked (graph : Aggregates.CheckedDAG) (mask : Nat) : IO CheckedPlan :=
  match CheckedPlan.ofParts? graph mask with
  | some plan => pure plan
  | none => throw (IO.userError "bounded loop plan failed checked admission")

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Loop.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"loop emission failed: {reprStr error}")

private def inputs : List Nat := [0, 1, 3, 7, Word.maximum.val, 2 ^ 255]

/-- For the allowed masks, the bound is the low zero, one, two or three bits.
This arithmetic reference does not inspect or execute the generated guards. -/
private def trips (mask input : Nat) : Nat := input % (mask + 1)

private def observe (plan : CheckedPlan) (input expected : Nat)
    (expectedCells : Nat) (privateValue : Nat := 2) : IO Unit := do
  let applied := plan.instantiate (Word.ofNatModulo input)
  ensure applied.check "applied loop failed full Core checking"
  match applied.toCore.runStateful 10000 with
  | .done (.word value) store =>
      ensure (value.val == expected)
        s!"Core loop result changed: mask {plan.mask}, input {input}, expected {expected}, got {value.val}"
      ensure (store.length == expectedCells) "loop call reused a private cell or executed the wrong number of steps"
      match (store[0]? : Option Value) with
      | some (.word accumulated) => ensure (accumulated == value) "returned accumulator differs from its cell"
      | _ => throw (IO.userError "Core loop lost its accumulator cell")
      for cell in store.drop 1 do
        match cell with
        | .word final => ensure (final.val == privateValue) "callee's private cell contents escaped between calls"
        | _ => throw (IO.userError "loop allocated a non-Word cell")
  | _ => throw (IO.userError "bounded Core loop did not return a Word")

private def admissionChecks : IO Unit := do
  let graph ← step [increment]
  for mask in [0, 1, 3, 7] do
    let plan ← checked graph mask
    ensure (plan.program.check && plan.mask == mask) "loop admission changed mask or escaped checking"
    match plan.program.body with
    | .letE saved (.lambda .word .word _) =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr graph.program.body)
          "Core loop did not bind the whole original entry closure once"
    | _ => throw (IO.userError "Core loop's closure-before-input shape changed")
    let measured := Wire.programNodes (plan.instantiate Word.maximum)
    ensure (measured == BoundedLoop.appliedNodes graph mask &&
      measured == BoundedLoop.canonicalNodes graph mask &&
      measured == Wire.programNodes graph.program + BoundedLoop.appliedOverhead mask &&
      BoundedLoop.appliedOverhead mask == 14 + 12 * mask)
      "loop node overhead differs from the complete Core program"
    let source ← emitted plan
    ensure (source == (← emitted plan)) "loop emission is nondeterministic"
    ensure (source.contractName == "SynthesizedLoops" && source.methodSignature == "run(uint256)" &&
      source.deployPath == ["SynthesizedLoopsDeploy"] &&
      source.runtimePath == ["SynthesizedLoopsDeploy", "SynthesizedLoops"])
      "loop wrapper metadata changed"
  for mask in [2, 4, 5, 6, 8, 15, 256, 1000000] do
    ensure (CheckedPlan.ofParts? graph mask).isNone "loop admitted an unbounded or unsupported mask"
  let mixed ← step [increment, mutableStep] (.apply (.var 1) (.apply (.var 2) (.var 0)))
  for mask in [0, 1, 3, 7] do
    let plan ← checked mixed mask
    ensure (Wire.programNodes (plan.instantiate Word.zero) ==
      Wire.programNodes mixed.program + BoundedLoop.appliedOverhead mask)
      "loop overhead depends on the helper or arbitrary entry shape"

private def executionChecks : IO Unit := do
  let incrementGraph ← step [increment]
  let arbitraryGraph ← step [increment] arbitraryEntry
  let mutableGraph ← step [mutableStep]
  let mixedGraph ← step [increment, mutableStep] (.apply (.var 1) (.apply (.var 2) (.var 0)))
  let identityGraph ← step [increment] (.var 0)
  let constantGraph ← step [increment] (word 42)
  for mask in [0, 1, 3, 7] do
    let incrementPlan ← checked incrementGraph mask
    let arbitraryPlan ← checked arbitraryGraph mask
    let mutablePlan ← checked mutableGraph mask
    let mixedPlan ← checked mixedGraph mask
    let identityPlan ← checked identityGraph mask
    let constantPlan ← checked constantGraph mask
    for input in inputs do
      let count := trips mask input
      observe incrementPlan input (Word.ofNatModulo (input + count)).val 1
      observe arbitraryPlan input (Word.ofNatModulo (input + 11 * count)).val 1
      observe mutablePlan input (Word.ofNatModulo (input + 2 * count)).val (1 + count)
      observe mixedPlan input (Word.ofNatModulo (input + 3 * count)).val (1 + count)
      observe identityPlan input input 1
      observe constantPlan input (if count == 0 then input else 42) 1
  let maximum ← checked mutableGraph 7
  observe maximum 7 21 8
  observe maximum 0 0 1
  observe maximum (2 ^ 255) (2 ^ 255) 1
  match (maximum.instantiate (Word.ofNatModulo 7)).toCore.runStateful 0 with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero fuel was confused with a completed bounded loop")
  -- Raw primitives render through the call-graph helpers with the alias import.
  let divided ← step [.binary .wordDiv (.var 0) (word 1)]
  match Loop.emit (← checked divided 0) with
  | .ok emitted => unless (emitted.source.splitOn "import { div as sc_div, mod as sc_mod, ").length == 2 && (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
      throw (IO.userError "loop emission lost the raw division alias or its operand snapshots")
  | .error error => throw (IO.userError s!"loop raw division was rejected: {reprStr error}")

private def expectedIncrement : String := String.intercalate "\n" [
  "pragma solcore;", "import * from std;", "import * from std.dispatch;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;",
  "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);",
  "    return sc_v0;", "}", "",
  "contract SynthesizedLoops {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_limit: word = (sc_input & 3);",
  "        let sc_acc: word = sc_input;",
  "        let sc_counter: word = 0;",
  "        while (sc_limit > sc_counter) {",
  "            sc_acc = sc_step(sc_acc);",
  "            sc_counter = (sc_counter + 1);",
  "        }",
  "        return uint256(sc_acc);", "    }", "}", ""]

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def formattingChecks : IO Unit := do
  let graph ← step [increment]
  ensure ((← emitted (← checked graph 3)).source == expectedIncrement)
    "source loop no longer uses its own counter and fixed initial bound"
  let arbitrary ← emitted (← checked (← step [increment] arbitraryEntry) 7)
  ensure (contains arbitrary.source (String.intercalate "\n" [
    "function sc_step(sc_arg: word) returns (word) {",
    "    let sc_v0: word = sc_fn0(sc_arg);",
    "    let sc_v1: word = 10;",
    "    let sc_v2: word = (sc_v0 + sc_v1);",
    "    return sc_v2;", "}"])) "source loop ignored the arbitrary checked entry"
  ensure ((arbitrary.source.splitOn "while (").length == 2 &&
    (arbitrary.source.splitOn "sc_acc = sc_step(sc_acc);").length == 2)
    "source output unrolled or duplicated the actual while loop"
  let identity ← emitted (← checked (← step [increment] (.var 0)) 1)
  ensure (contains identity.source
    "function sc_step(sc_arg: word) returns (word) {\n    return sc_arg;\n}")
    "identity entry was replaced with the last helper"
  let mutable ← emitted (← checked (← step [mutableStep]) 7)
  ensure (contains mutable.source "function sc_fn0(sc_arg: word) returns (word) {\n    let sc_c0: word = sc_arg;" &&
    !contains mutable.source "sc_acc = sc_fn0") "private step allocation moved outside its function"
  ensure (Loop.emitterVersion == "solcore-source-loops-v3" &&
    Loop.wrapperVersion == "solcore-word-loops-contract-v1" &&
    Loop.selector == "0xa444f5e9" && BoundedLoop.version == "core-bounded-loop-plan-v1")
    "loop provenance changed"

def testSourceLoopEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceLoopEmitter
end

section
-- leanmerge: from Solcore.Test.SourceNestedLoopCases
/-! The `runtime-nested-loops` profile. Plans admit masks 0, 1 and 3 and three
inner-bound forms. The unrolled Core reference returns the accumulator of an
independent call-by-call loop specification over the step's original Core,
which also gives every recorded iteration count, at most three outer
iterations, three inner iterations in each and nine step calls. Generation
draws all twelve shapes, excludes boundary identities and replays exactly;
tampering is refused, and reductions lower masks, replace the inner bound or
the input and stay strictly smaller. -/
set_option autoImplicit false

namespace Tests.SourceNestedLoopCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.NestedLoop (CheckedPlan Bound)
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def fuel : Nat := 1000000

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def directWord (case : Json) : IO Word := do
  let text ← get ((← get (case.getObjVal? "directCore")).getObjValAs? String "word")
  let some value := text.toNat? | throw (IO.userError "invalid result Word")
  return Word.ofNatModulo value

private def withPlan (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "nestedLoopPlan" (change (← get (case.getObjVal? "nestedLoopPlan")))

private def withProvenance (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "provenance" (change (← get (case.getObjVal? "provenance")))

/-- Masks 0, 1 and 3 are admitted for both loops; 2 and 7 are not. -/
private def admissionChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for outer in [0, 1, 3] do
    for inner in [0, 1, 3] do
      for bound in Bound.all do
        ensure (CheckedPlan.ofParts? step outer inner bound).isSome
          s!"masks {outer} and {inner} with bound {bound.name} were refused"
  for (outer, inner) in [(2, 1), (1, 2), (7, 3), (3, 7)] do
    ensure (CheckedPlan.ofParts? step outer inner .input).isNone s!"masks {outer} and {inner} were admitted"

/-- The wrapper's inner bound and both loops, for each form. -/
private def emitterChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for (bound, text) in [(Bound.input, "(sc_input & 3)"), (.counter, "((sc_i + 1) & 3)"),
      (.accumulator, "(sc_acc & 3)")] do
    let some plan := CheckedPlan.ofParts? step 1 3 bound | throw (IO.userError "plan refused")
    let source := (← get ((NestedLoop.emit plan).mapError reprStr)).source
    for line in ["        let sc_outer: word = (sc_input & 1);", "        while (sc_outer > sc_i) {",
        "            sc_inner = " ++ text ++ ";", "            sc_j = 0;", "            while (sc_inner > sc_j) {",
        "                sc_acc = sc_step(sc_acc);", "            sc_i = (sc_i + 1);"] do
      ensure ((source.splitOn line).length == 2) s!"{bound.name}: the wrapper lacks the line {line}"

/-- Every case's Core result equals the loop specification evaluated call by
call, which also gives its recorded iteration counts within the bounds. -/
private def referenceChecks (plan : CheckedPlan) (input : Word) (case : Json) : IO Unit := do
  let some (trips, accumulator) := NestedLoop.simulate plan input fuel |
    throw (IO.userError "a step call did not return a Word")
  ensure (accumulator == (← directWord case)) "the Core reference differs from the loop specification"
  ensure (trips.length == plan.outerTrips input && trips.length ≤ 3 && trips.all (· ≤ plan.inner) &&
      trips.foldl (· + ·) 0 ≤ 9) "iteration counts exceed the plan's bounds"
  match plan.bound with
  | .input => ensure (trips.all (· == (input.bitAnd (Word.ofNatModulo plan.inner)).val)) "input bound differs"
  | .counter =>
      ensure (trips == (List.range trips.length).map fun ordinal => (ordinal + 1) &&& plan.inner)
        "counter bound differs"
  | .accumulator => pure ()
  ensure ((← get ((← get (case.getObjVal? "provenance")).getObjVal? "iterations")) == toJson trips)
    "a case records other iteration counts"

private def generationChecks : IO Unit := do
  let corpus := NestedLoop.generateCases (Seed.ofNat 1) 384 1020 400 fuel .v4 .seeded
  ensure (corpus == NestedLoop.generateCases (Seed.ofNat 1) 384 1020 400 fuel .v4 .seeded)
    "nested loop generation is not deterministic"
  let generated ← cases corpus
  ensure (generated.size == 1020) "nested loop generation did not complete"
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  for entry in excluded do
    let reason ← get (entry.getObjValAs? String "reason")
    ensure (reason == Acceptance.identityReason ||
        reason == "node budget is too small for the selected aggregate template or exceeds 512")
      s!"unexpected nested loop exclusion: {reason}"
  let mut shapes : List String := []
  let mut functions := 0
  for index in List.range (generated.size / 10) do
    let function := generated.extract (10 * index) (10 * index + 10)
    let some first := function[0]? | throw (IO.userError "empty function")
    let admitted ← get (NestedLoop.caseProgram first)
    let plan := admitted.plan
    shapes := (s!"{plan.outer}x{plan.inner}:{plan.bound.name}") :: shapes
    functions := functions + 1
    let mut identity := true
    for (case, position) in function.zipIdx do
      let input := (← get (NestedLoop.caseProgram case)).input
      referenceChecks plan input case
      if position < 6 && (← directWord case) != input then identity := false
    ensure (!identity) "a generated nested loop returned every boundary input"
  ensure (shapes.eraseDups.length == 12) s!"generation drew {shapes.eraseDups.length} of twelve shapes"
  ensure (functions == 102) "a function lost some of its inputs"

private def replayChecks (case : Json) : IO Unit := do
  ensure ((← get (NestedLoop.replayCase case fuel)) == case) "a nested loop case failed exact replay"
  let plan ← get (case.getObjVal? "nestedLoopPlan")
  let outer ← get (plan.getObjValAs? Nat "outerMask")
  let inner ← get (plan.getObjValAs? Nat "innerMask")
  let bound ← get (plan.getObjValAs? String "innerBound")
  for changed in [
      ← withPlan case (·.setObjVal! "outerMask" (toJson (if outer == 3 then 1 else 3))),
      ← withPlan case (·.setObjVal! "innerMask" (toJson (if inner == 3 then 1 else 3))),
      ← withPlan case (·.setObjVal! "innerBound" (toJson (if bound == "input" then "counter" else "input"))),
      ← withPlan case (·.setObjVal! "innerMask" (toJson (2 : Nat))),
      ← withProvenance case (·.setObjVal! "iterations" (toJson [9])),
      ← withProvenance case (·.setObjVal! "iterations" Json.null)] do
    ensure (NestedLoop.replayCase changed fuel matches .error _) "a tampered nested loop case replayed"

private def reductionChecks (case : Json) : IO Unit := do
  let source ← get (NestedLoop.caseProgram case)
  let mut lowered := false
  let mut rebound := false
  for reduced in NestedLoop.reductions source do
    let plan := reduced.candidate.plan
    ensure (plan.outer ≤ source.plan.outer && plan.inner ≤ source.plan.inner &&
        plan.step.helpers.length == source.plan.step.helpers.length)
      "a reduction raised a mask or changed the helper count"
    ensure ((complexity reduced.candidate.program.body).isStrictlySmaller (complexity source.program.body))
      "a reduction is not strictly smaller"
    if plan.outer < source.plan.outer || plan.inner < source.plan.inner then lowered := true
    if plan.bound == .input && source.plan.bound != .input then rebound := true
  ensure lowered "no reduction lowered a mask"
  ensure (rebound || source.plan.bound == .input) "no reduction replaced the inner bound by the input"
  let emitted ← cases (← get (NestedLoop.shrinkCases case 4 fuel))
  ensure (!emitted.isEmpty) "a nested loop case has no reduction"
  for candidate in emitted do
    ensure ((← get (NestedLoop.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"

/-- An imported plan with an outer mask of zero runs no iteration. -/
private def importChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  let some plan := CheckedPlan.ofParts? step 0 3 .accumulator | throw (IO.userError "plan refused")
  let case ← get (NestedLoop.emitCase plan (Word.ofNatModulo 3) (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((← directWord case) == Word.ofNatModulo 3) "a plan without outer iterations changed its input"
  ensure ((← get (NestedLoop.replayCase case fuel)) == case) "an imported nested loop case failed exact replay"

def testSourceNestedLoopCases : IO Unit := do
  let generated ← cases (NestedLoop.generateCases (Seed.ofNat 7) 384 6 16 fuel .v4)
  let some first := generated[0]? | throw (IO.userError "no nested loop case")
  let source ← get (NestedLoop.caseProgram first)
  admissionChecks source.plan.step
  emitterChecks source.plan.step
  importChecks source.plan.step
  generationChecks
  for case in generated do
    replayChecks case
  for case in generated.extract 0 4 do
    reductionChecks case

end Tests.SourceNestedLoopCases
end

section
-- leanmerge: from Solcore.Test.SourceStorageLoopCases
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
end

section
-- leanmerge: from Solcore.Test.SourceStorageLoopCorpus
/-! The fixed storage-loop corpus checks actual original Core histories against
expectations computed without the guarded contract: the source-loop model, a
counter over a slot map in which each step runs alone in Core. Coverage
describes the checked steps' AST, the inputs, the masks, the iteration counts,
the carries within a transaction and through a rollback, the iteration slots
carried across transactions and the completions. Source/Rust/EVM agreement is
a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceStorageLoopCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

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
  ("generatorVersion", generatorVersion), ("profileVersion", StorageLoop.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.StorageLoop.version),
  ("templateVersion", StorageLoop.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", StorageLoop.emitterVersion), ("wrapperVersion", StorageLoop.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := StorageLoop.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← StorageLoop.checkedPlan (← entry.getObjVal? "storageLoopPlan")
  let scenario ← StorageLoop.checkedScenario plan
    (← StorageLoop.decodeTransactions plan.mask (← entry.getObjVal? "transactions"))
  StorageLoop.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "storage-loop-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-storage-loops" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected storage-loop manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("storage-loop manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words StorageLoop.boundaryInputs))
    "storage-loop corpus must require all six boundary inputs"
  require ((← manifest.getObjValAs? (List Nat) "requiredMasks") == [0, 1, 3, 7] &&
    (← manifest.getObjValAs? (List Nat) "requiredIterationCounts") == List.range 8 &&
    (← manifest.getObjValAs? (List Nat) "requiredCarriedSlots") == (List.range 7).map (· + 2))
    "storage-loop corpus must require every mask, iteration count and carried slot"
  require ((← strings manifest "requiredIterationCarries") == ["iteration", "rollback"])
    "storage-loop corpus must require carries within a transaction and through a rollback"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "storage-loop corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "storage-loop corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "storage-loop corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "storage-loop corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "storage-loop corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut masks : List Nat := []
  let mut counts : List Nat := []
  let mut carries : List String := []
  let mut carried : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate storage-loop corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← StorageLoop.replayCase saved fuel) == saved) ("storage-loop corpus entry did not replay: " ++ identifier)
    let scenario ← StorageLoop.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "storageLoopPlan") == (← entry.getObjVal? "storageLoopPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported storage-loop entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("storage-loop corpus features changed: " ++ identifier)
    let history := StorageLoop.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("storage-loop corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("storage-loop expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the source-loop model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    let mask := scenario.plan.mask
    let trips := scenario.transactions.map fun tx => Solcore.Synthesis.Stateful.StorageLoopExecution.iterations mask tx.input
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    masks := (masks ++ [mask]).eraseDups
    counts := (counts ++ trips).eraseDups
    if trips.any (· ≥ 2) then carries := (carries ++ ["iteration"]).eraseDups
    if (trips.zip statuses).any (fun (count, status) => count ≥ 1 && status == "reverted") then
      carries := (carries ++ ["rollback"]).eraseDups
    for (count, index) in trips.zipIdx do
      for iteration in List.range count do
        if ((trips.zip statuses).take index).any (fun (earlier, status) => status == "returned" && earlier > iteration) then
          carried := (carried ++ [2 + iteration]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "storage-loop corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "storage-loop corpus misses a boundary input"
  require ([0, 1, 3, 7].all masks.contains && (List.range 8).all counts.contains)
    "storage-loop corpus misses a mask or an iteration count"
  require (["iteration", "rollback"].all carries.contains && ((List.range 7).map (· + 2)).all carried.contains)
    "storage-loop corpus misses a carry or a carried slot"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "storage-loop corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "storage-loop corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "storage-loop corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-storage-loops"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("masks", toJson masks), ("iterationCounts", toJson counts),
    ("carriedSlots", toJson carried), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid storage-loop corpus unexpectedly passed")

def testSourceStorageLoopCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-storage-loop-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first storage-loop case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated storage-loop case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  -- An output, a slot, a missing row and a status are all checked.
  let changedOutput := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 8 (storage[8]!.setObjVal! "value" (toJson "7"))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped)))))))
  -- A recorded iteration count and the plan's mask are both checked.
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "iterations" (toJson 0)))))))
  let plan ← checked (first.getObjVal? "storageLoopPlan")
  rejects (validateManifest (replace first (first.setObjVal! "storageLoopPlan" (plan.setObjVal! "mask" (toJson 3)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredMasks", toJson [1, 3, 7]), ("requiredIterationCounts", toJson [0, 1, 7]),
      ("requiredCarriedSlots", toJson [2, 3]), ("requiredIterationCarries", toJson (["iteration"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceStorageLoopCorpus
end

section
-- leanmerge: from Solcore.Test.SourceStorageLoopGolden
/-! Golden cases for the storage-loop profile. Every expected row is written
out by hand from the protocol, not computed by either model. The steps add a
known constant `c`, so iteration `i` writes
`slot 0 + slot 1 + slot (1 + i) + slot (2 + i) + input + c` to slot `2 + i`
and to slot zero; afterwards slot one grows by the iteration count and the
result is slot zero plus slot one, which odd flags revert. The sequences cover
zero, one, two, three and seven iterations, masks zero, one, three and seven,
a revert after loop writes, a slot written by one iteration and read by the
next, slots written by one transaction and read by a later one, and wrapping
sums. Both the guarded Core contract and the source-loop model must give each
row. -/
set_option autoImplicit false

namespace Tests.SourceStorageLoopGolden

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

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- The expected row: status, output Word and slots zero to eight. -/
structure Expected where
  status : String
  output : Nat
  values : List Nat

private def slots (values : List Nat) : Json :=
  toJson ((List.range StorageLoop.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def wordText (value : Nat) : String := encodeBytesText (encodeWordBytesBE (w value))

private def tx (index flags input : Nat) : Transaction := ⟨"tx-" ++ toString index, w flags, w input⟩

/-- Mask 7 and `c = 1`. No iteration; one; seven over the carried slots; a
revert after seven iterations, which keeps the prior slots; then three. -/
def sevenRows : List (Transaction × Expected) := [
  (tx 0 0 0, ⟨"returned", 0, []⟩),
  -- 0 + 0 + 0 + 0 + 1 + 1 = 2; slot one 1; result 3.
  (tx 1 0 1, ⟨"returned", 3, [2, 1, 2]⟩),
  -- With 7 + 1 added: 2 + 1 + 1 + 2 = 14, then 14 + 1 + 14 = 37, 83, 175, 359,
  -- 727 and 1463; slot one 8; result 1471.
  (tx 2 0 7, ⟨"returned", 1471, [1463, 8, 14, 37, 83, 175, 359, 727, 1463]⟩),
  -- 1463 + 8 + 8 + 14 + 8 = 1501, then 1501 + 8 + 1501 + 37 + 8 = 3055, 6209,
  -- 12609, 25593, 51929 and 105337; slot one 15; result 105352, reverted.
  (tx 3 1 7, ⟨"reverted", 105352, [1463, 8, 14, 37, 83, 175, 359, 727, 1463]⟩),
  -- With 3 + 1 added: 1463 + 8 + 8 + 14 + 4 = 1497, then
  -- 1497 + 8 + 1497 + 37 + 4 = 3043 and 3043 + 8 + 3043 + 83 + 4 = 6181.
  (tx 4 2 3, ⟨"returned", 6192, [6181, 11, 1497, 3043, 6181, 175, 359, 727, 1463]⟩)]

/-- Mask 0 and `c = 5`: no iteration whatever the input. -/
def zeroRows : List (Transaction × Expected) := [
  (tx 0 0 7, ⟨"returned", 0, []⟩),
  (tx 1 1 1, ⟨"reverted", 0, []⟩)]

/-- Mask 1 and `c = 0`; the second sum wraps: 3 + 1 + 1 + 3 + (2^256 - 1) = 7. -/
def oneRows : List (Transaction × Expected) := [
  (tx 0 0 3, ⟨"returned", 4, [3, 1, 3]⟩),
  (tx 1 0 (2 ^ 256 - 1), ⟨"returned", 9, [7, 2, 7]⟩),
  (tx 2 3 2, ⟨"reverted", 9, [7, 2, 7]⟩)]

/-- Mask 3 and `c = 2`. Two iterations: 8, then 8 + 0 + 8 + 0 + 8 = 24. Three
iterations of an input with the high bit: with 2^255 + 5 added,
24 + 2 + 2 + 8 gives 2^255 + 41, then 2^255 + 113 and 2^255 + 233, since
twice 2^255 wraps to zero. -/
def threeRows : List (Transaction × Expected) := [
  (tx 0 0 6, ⟨"returned", 26, [24, 2, 8, 24]⟩),
  (tx 1 0 (2 ^ 255 + 3), ⟨"returned", 2 ^ 255 + 238,
    [2 ^ 255 + 233, 5, 2 ^ 255 + 41, 2 ^ 255 + 113, 2 ^ 255 + 233]⟩)]

def check (name : String) (row : Json) (model : StorageLoopExecution.ModelRow) (expected : Expected) : IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (wordText expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (slots expected.values))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") && model.result == w expected.output &&
      model.slots == (List.range StorageLoop.slotCount).map (fun slot => w (expected.values.getD slot 0)))
    s!"{name}: the source-loop model differs from the expected row"

/-- Each golden sequence's name, mask, step constant and rows. -/
def goldenPlans : List (String × Nat × Nat × List (Transaction × Expected)) := [
  ("mask 7", 7, 1, sevenRows), ("mask 0", 0, 5, zeroRows), ("mask 1", 1, 0, oneRows), ("mask 3", 3, 2, threeRows)]

def testSourceStorageLoopGolden : IO Unit := do
  let fuel := 1000000
  for (name, mask, constant, rows) in goldenPlans do
    let step ← step constant
    let some plan := StorageLoop.CheckedPlan.ofParts? step mask
      | throw (IO.userError s!"{name}: the storage-loop wrapper failed admission")
    let transactions := rows.map Prod.fst
    let history := StorageLoopExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := StorageLoopExecution.model step fuel mask transactions
      | throw (IO.userError s!"{name}: the source-loop model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" row model expected
      -- The recorded iteration count is the input's bits under the mask.
      ensure (StorageLoopExecution.iterations mask transaction.input ≤ mask) s!"{name}: iterations exceed the mask"
  -- The plan admits exactly the four masks.
  let constant ← step 1
  for mask in [2, 4, 5, 6, 8, 15] do
    ensure (StorageLoop.CheckedPlan.ofParts? constant mask).isNone s!"mask {mask} was admitted"

end Tests.SourceStorageLoopGolden
end

section
-- leanmerge: from Solcore.Test.SourceAssemblyStorageLoopGolden
/-! Golden cases for the inline Yul storage-loop profile. The contract of each
form is written out by hand for the mask-three plan, and the step functions
must be the storage-loop profile's. The storage-loop profile's hand-written
rows must come back through the new cases: every golden plan, in every form,
is emitted as an inline Yul case, decoded, and its unchanged Core reference
observed. A changed expectation must fail. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyStorageLoopGolden

open Lean
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Source.AssemblyStorage (Form)
open Tests.SourceStorageLoopGolden (Expected goldenPlans)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def head : List String := [
  "contract SynthesizedAssemblyStorageLoops {",
  "    function run(flags: uint256, input: uint256) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_limit: word = (sc_input & 3);",
  "        let sc_counter: word = 0;"]

private def tail : List String := [
  "        assembly {",
  "            sstore(1, add(sload(1), sc_limit))",
  "            sc_result := add(sload(0), sload(1))",
  "            if and(sc_flags, 1) {",
  "                mstore(0, sc_result)",
  "                revert(0, 32)",
  "            }",
  "        }",
  "        return uint256(sc_result);",
  "    }",
  "}"]

/-- The contract of the mask-three plan in each form. -/
private def contracts : List (Form × List String) := [
  (.split, head ++ [
    "        let sc_sum: word = 0;",
    "        let sc_value: word = 0;",
    "        let sc_result: word = 0;",
    "        while (sc_limit > sc_counter) {",
    "            assembly {",
    "                let sc_slot := add(sc_counter, 2)",
    "                sc_sum := add(add(add(add(sload(0), sload(1)), sload(sub(sc_slot, 1))), sload(sc_slot)), sc_input)",
    "            }",
    "            sc_value = sc_step(sc_sum);",
    "            assembly {",
    "                sstore(add(sc_counter, 2), sc_value)",
    "                sstore(0, sc_value)",
    "            }",
    "            sc_counter = (sc_counter + 1);",
    "        }"] ++ tail),
  (.carried, head ++ [
    "        let sc_slot: word = 0;",
    "        let sc_sum: word = 0;",
    "        let sc_value: word = 0;",
    "        let sc_result: word = 0;",
    "        while (sc_limit > sc_counter) {",
    "            assembly {",
    "                sc_slot := add(sc_counter, 2)",
    "                sc_sum := add(add(add(add(sload(0), sload(1)), sload(sub(sc_slot, 1))), sload(sc_slot)), sc_input)",
    "            }",
    "            sc_value = sc_step(sc_sum);",
    "            assembly {",
    "                sstore(sc_slot, sc_value)",
    "                sstore(0, sc_value)",
    "                sc_counter := add(sc_counter, 1)",
    "            }",
    "        }"] ++ tail),
  (.pipelined, head ++ [
    "        let sc_slot: word = 0;",
    "        let sc_sum: word = 0;",
    "        let sc_value: word = 0;",
    "        let sc_result: word = 0;",
    "        assembly {",
    "            if gt(sc_limit, sc_counter) {",
    "                sc_slot := add(sc_counter, 2)",
    "                sc_sum := add(add(add(add(sload(0), sload(1)), sload(sub(sc_slot, 1))), sload(sc_slot)), sc_input)",
    "            }",
    "        }",
    "        while (sc_limit > sc_counter) {",
    "            sc_value = sc_step(sc_sum);",
    "            assembly {",
    "                sstore(sc_slot, sc_value)",
    "                sstore(0, sc_value)",
    "                sc_counter := add(sc_counter, 1)",
    "                if gt(sc_limit, sc_counter) {",
    "                    sc_slot := add(sc_counter, 2)",
    "                    sc_sum := add(add(add(add(sload(0), sload(1)), sload(sub(sc_slot, 1))), sload(sc_slot)), sc_input)",
    "                }",
    "            }",
    "        }"] ++ tail)]

private def occurs (text part : String) : Bool := (text.splitOn part).length > 1

/-- The source before the contract, without its `std.opcodes` import. -/
private def stepPart (source : String) : List String :=
  ((source.splitOn "contract ").headD "").splitOn "\n" |>.filter (!·.endsWith "from std.opcodes;")

/-- Every row of a golden plan through the inline Yul case of one form. -/
private def checkRows (name : String) (form : Form) (mask constant : Nat)
    (rows : List (StorageLoopExecution.Transaction × Expected)) (fuel : Nat) : IO Unit := do
  let step ← Tests.SourceStorageLoopGolden.step constant
  let some plan := StorageLoop.CheckedPlan.ofParts? step mask
    | throw (IO.userError s!"{name}: the storage-loop wrapper failed admission")
  let transactions := rows.map Prod.fst
  let loop ← get (Solcore.Synthesis.Source.StorageLoop.checkedScenario plan transactions)
  let json ← get (Solcore.Synthesis.Source.AssemblyStorageLoop.emitCase ⟨loop, form⟩
    (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((Solcore.Synthesis.Source.AssemblyStorageLoop.replayCase json fuel).toOption == some json)
    s!"{name} {form.name}: the case does not replay"
  let scenario ← get (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram json)
  ensure (scenario.form == form) s!"{name} {form.name}: the decoded form differs"
  let history := Solcore.Synthesis.Source.AssemblyStorageLoop.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name} {form.name}: the history is incomplete"
  let observed ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := StorageLoopExecution.model step fuel mask transactions
    | throw (IO.userError s!"{name}: the source-loop model failed")
  ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name} {form.name}: a row is missing"
  for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
    Tests.SourceStorageLoopGolden.check s!"{name} {form.name} {transaction.id}" row model expected

def testSourceAssemblyStorageLoopGolden : IO Unit := do
  let fuel := 1000000
  -- Each form's contract, and the storage-loop profile's step functions.
  let step ← Tests.SourceStorageLoopGolden.step 2
  let some plan := StorageLoop.CheckedPlan.ofParts? step 3
    | throw (IO.userError "the mask-three plan failed admission")
  let parent ← get ((Solcore.Synthesis.Source.StorageLoop.emit plan).mapError reprStr)
  for (form, expected) in contracts do
    let emitted ← get ((Solcore.Synthesis.Source.AssemblyStorageLoop.emit form plan).mapError reprStr)
    let some contract := (emitted.source.splitOn "contract ").getLast?
      | throw (IO.userError "the emitted source has no contract")
    ensure (("contract " ++ contract) == String.intercalate "\n" expected ++ "\n")
      s!"{form.name}: the emitted contract differs from the golden text:\n{contract}"
    ensure (stepPart emitted.source == stepPart parent.source && !occurs emitted.source "revert_(" &&
        !occurs emitted.source "from std.opcodes")
      s!"{form.name}: the step functions or imports differ from the storage-loop profile's"
  -- The storage-loop profile's rows, through every form.
  for (name, mask, constant, rows) in goldenPlans do
    for form in Form.all do
      checkRows name form mask constant rows fuel
  -- A changed expectation fails.
  let some (name, mask, constant, rows) := goldenPlans.head? | throw (IO.userError "no golden plan")
  let some ((transaction, expected), rest) := rows.getLast?.map (fun last => (last, rows.dropLast))
    | throw (IO.userError "no golden row")
  let changed := rest ++ [(transaction, {expected with output := expected.output + 1})]
  let failed ← tryCatch (do checkRows name .pipelined mask constant changed fuel; pure false)
    (fun _ => pure true)
  ensure failed "a changed expectation passed"

end Tests.SourceAssemblyStorageLoopGolden
end
