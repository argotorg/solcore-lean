import Solcore.Synthesis.Source.EnumCases

/-! The `runtime-enums` profile. Its Core reference compiles every match to
nested `caseE` with fall-through thunks; it agrees with a direct interpreter
of the plan's first-match semantics and scoping on generated plans, and a
fixture's source and results are golden, the results from a separate Python
model. Admission refuses unreachable arms, non-exhaustive matches and
ill-formed plans; generation draws every shape and replays exactly; tampering
is refused, and reductions are strictly smaller and replay. -/
set_option autoImplicit false

namespace Tests.SourceEnumCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core (Seed)
open Solcore.Synthesis.Core.Enums
open Solcore.Synthesis.Source

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

private def modulus : Nat := 2 ^ 256

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def excluded (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "excluded")

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def run (program : Solcore.Core.Wire.Program) : IO Nat :=
  match program.toCore.runStateful fuel with
  | .done (.word value) _ => pure value.val
  | _ => throw (IO.userError "a reference program did not return a Word")

/-! A direct interpreter of a plan: values as trees, the first arm whose
patterns accept them, names by their innermost binding. It shares no code
with the Core compilation. -/

private inductive Runtime where
  | word (value : Nat)
  | tuple (left right : Runtime)
  | ctor (index : Nat) (fields : List Runtime)
  deriving Inhabited

private def evaluate (input : Nat) : Value → Runtime
  | .leaf .input _ => .word input
  | .leaf .add constant => .word ((input + constant) % modulus)
  | .leaf .xor constant => .word (input ^^^ constant)
  | .leaf .mul constant => .word ((input * constant) % modulus)
  | .tuple left right => .tuple (evaluate input left) (evaluate input right)
  | .ctor0 index _ => .ctor index []
  | .ctor1 index field _ => .ctor index [evaluate input field]
  | .ctor2 index first second _ => .ctor index [evaluate input first, evaluate input second]

private def bind : Pat → Runtime → Option (List (Nat × Runtime))
  | .wild, _ => some []
  | .var name, value => some [(name, value)]
  | .tuple left right, .tuple first second => do return (← bind left first) ++ (← bind right second)
  | .ctor0 index _, .ctor other [] => if index = other then some [] else none
  | .ctor1 index field _, .ctor other [value] => if index = other then bind field value else none
  | .ctor2 index left right _, .ctor other [first, second] =>
      if index = other then do return (← bind left first) ++ (← bind right second) else none
  | _, _ => none

private def bindRow (patterns : List Pat) (values : List Runtime) : Option (List (Nat × Runtime)) :=
  if patterns.isEmpty then some []
  else (patterns.zip values).foldlM (fun bound (pattern, value) => do return bound ++ (← bind pattern value)) []

private def termValue (scope : List (Nat × Runtime)) : Solcore.Synthesis.Core.Enums.Term → Option Nat
  | .constant value => some value
  | .name name => match scope.find? (·.1 = name) with
      | some (_, .word value) => some value
      | _ => none

private def operate : Op → Nat → Nat → Nat
  | .add, left, right => (left + right) % modulus
  | .sub, left, right => (left + modulus - right) % modulus
  | .xor, left, right => left ^^^ right
  | .mul, left, right => (left * right) % modulus

private def bodyValue (scope : List (Nat × Runtime)) (body : Body) : Option Nat := do
  let first ← termValue scope body.first
  let folded ← body.rest.foldlM (fun accumulated (op, term) => do
    return operate op accumulated (← termValue scope term)) first
  return (folded + body.constant) % modulus

private def matchArms (arms : List Arm) (values : List Runtime) (w : Nat) : Option Nat := do
  let (bound, arm) ← arms.findSome? fun arm => (bindRow arm.patterns values).map (·, arm)
  let scope := bound.reverse ++ [(parameterName, Runtime.word w)]
  match arm.body with
  | .expr body => bodyValue scope body
  | .nested scrutinee inner =>
      let (_, value) ← scope.find? (·.1 = scrutinee)
      let (innerBound, innerArm) ← inner.findSome? fun innerArm =>
        (bindRow innerArm.patterns [value]).map (·, innerArm)
      bodyValue (innerBound.reverse ++ scope) innerArm.body

private def selected (builder : Builder) (input : Nat) : Value :=
  builder.trees.getD (min ((input + builder.offset) % 4) (builder.trees.length - 1)) default

private def interpret (plan : Plan) (input : Nat) : Option Nat := do
  let results ← plan.views.flatMap (fun view =>
      let w := (input + view.wordOffset) % modulus
      let values := view.builders.map fun builder => evaluate input (selected builder input)
      match view.kind with
      | .generic => values.map fun value => matchArms view.arms [value] w
      | _ => [matchArms view.arms values w]) |>.mapM id
  return results.zipIdx.foldl (fun accumulated (result, index) =>
    (accumulated + result * (2 * index + 1)) % modulus) 0

private def boundary : List Nat := [0, 1, 2, 255, 256, 2 ^ 256 - 1, 2 ^ 255, 2 ^ 255 - 1]

/-- The reference agrees with the interpreter on 240 generated plans at the
eight boundary inputs and four others. -/
private def modelChecks : IO Unit := do
  let mut compared := 0
  for seed in List.range 240 do
    match Enums.generatedPlan (Seed.ofNat (seed + 1)) Enums.defaultNodes with
    | .error _ => pure ()
    | .ok checked =>
        for input in boundary ++ [3, 1001, 0x1234567890abcdef, 2 ^ 200 + 77] do
          let core ← run (checked.program (Word.ofNatModulo input))
          ensure (interpret checked.plan input == some core)
            s!"seed {seed + 1} input {input}: the reference differs from the interpreter"
          compared := compared + 1
  ensure (compared ≥ 2400) "fewer than 200 generated plans compared with the interpreter"

/-! A fixture with every view kind, both generic instances, a pair view, a
nested match and the dot and same-name forms. -/

private def fixtureDecls : List Decl := [
  {generic := false, sameName := false, constructors := [[], [.word], [.word, .tuple .word .word]]},
  {generic := true, sameName := true, constructors := [[.param, .word], [], [.enum 0]]}]

private def body (first : Solcore.Synthesis.Core.Enums.Term) (rest : List (Op × Solcore.Synthesis.Core.Enums.Term)) (constant : Nat) : Body := {first, rest, constant}

private def fixtureViews : List View := [
  {kind := .single, scrutinees := [.enum 0], instances := [], wordOffset := 13,
   arms := [
     {patterns := [.ctor2 2 (.var 0) (.tuple (.var 1) .wild) .qualified],
      body := .expr (body (.name 0) [(.sub, .name 1)] 5)},
     {patterns := [.ctor1 1 (.var 4) .dot], body := .expr (body (.name 4) [(.mul, .constant 3)] 7)},
     {patterns := [], body := .expr (body (.name 4) [] 11)}],
   builders := [{offset := 1, trees := [.ctor0 0 .qualified, .ctor1 1 (.leaf .add 2) .qualified,
     .ctor2 2 (.leaf .input 0) (.tuple (.leaf .mul 3) (.leaf .xor 5)) .qualified]}]},
  {kind := .generic, scrutinees := [.applied 1 .param], instances := [.word, .tuple .word .word], wordOffset := 37,
   arms := [
     {patterns := [.ctor2 0 .wild (.var 2) .sameName], body := .expr (body (.name 2) [] 17)},
     {patterns := [.ctor1 2 (.var 0) .qualified], body := .nested 0 [
       {patterns := [.ctor1 1 (.var 0) .qualified], body := body (.name 0) [(.xor, .name 4)] 19},
       {patterns := [.wild], body := body (.name 4) [] 23}]},
     {patterns := [.var 3], body := .expr (body (.name 4) [(.mul, .constant 29)] 31)}],
   builders := [
     {offset := 0, trees := [.ctor2 0 (.leaf .input 0) (.leaf .add 7) .sameName, .ctor0 1 .qualified,
       .ctor1 2 (.ctor1 1 (.leaf .mul 9) .qualified) .qualified]},
     {offset := 2, trees := [.ctor2 0 (.tuple (.leaf .input 0) (.leaf .input 0)) (.leaf .xor 3) .qualified,
       .ctor1 2 (.ctor0 0 .qualified) .dot]}]},
  {kind := .pair, scrutinees := [.enum 0, .applied 1 .word], instances := [], wordOffset := 53,
   arms := [
     {patterns := [.ctor1 1 (.var 0) .qualified, .ctor2 0 (.var 1) .wild .sameName],
      body := .expr (body (.name 0) [(.add, .name 1)] 41)},
     {patterns := [.wild, .ctor0 1 .qualified], body := .expr (body (.name 4) [] 43)},
     {patterns := [.var 2, .wild], body := .expr (body (.name 4) [(.xor, .constant 47)] 0)}],
   builders := [
     {offset := 3, trees := [.ctor1 1 (.leaf .input 0) .qualified, .ctor0 0 .qualified]},
     {offset := 0, trees := [.ctor2 0 (.leaf .add 1) (.leaf .input 0) .qualified, .ctor0 1 .qualified]}]}]

private def fixturePlan : Plan := {decls := fixtureDecls, views := fixtureViews}

/-- Golden results of `scratchpad/u12/fixture_model.py`, a separate Python
model of the fixture. -/
private def fixtureResults : List (Nat × Nat) := [(0, 567), (1, 4386), (2, 993), (3, 1245), (255, 11913),
  (2 ^ 255, 567), (2 ^ 256 - 1, 905)]

private def fixtureSource : String := String.intercalate "\n" [
  "import * from std;",
  "import * from std.dispatch;",
  "",
  "enum Sc_T0 {",
  "    Sc_T0_0,",
  "    Sc_T0_1(word),",
  "    Sc_T0_2(word, (word, word))",
  "}",
  "",
  "enum Sc_T1<a> {",
  "    Sc_T1(a, word),",
  "    Sc_T1_1,",
  "    Sc_T1_2(Sc_T0)",
  "}",
  "",
  "function sc_view0(sc_e: Sc_T0, sc_w: word) returns (word) {",
  "    match (sc_e) {",
  "        case Sc_T0.Sc_T0_2(sc_a, (sc_b, _)) {",
  "            return ((sc_a - sc_b) + 5);",
  "        }",
  "        case .Sc_T0_1(sc_w) {",
  "            return ((sc_w * 3) + 7);",
  "        }",
  "        default {",
  "            return (sc_w + 11);",
  "        }",
  "    }",
  "}",
  "",
  "function sc_make0_0(sc_x: word) returns (Sc_T0) {",
  "    let sc_k: word = ((sc_x + 1) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T0.Sc_T0_0;",
  "    }",
  "    if (sc_k == 1) {",
  "        return Sc_T0.Sc_T0_1((sc_x + 2));",
  "    }",
  "    return Sc_T0.Sc_T0_2(sc_x, ((sc_x * 3), (sc_x ^ 5)));",
  "}",
  "",
  "function sc_view1<a>(sc_e: Sc_T1<a>, sc_w: word) returns (word) {",
  "    match (sc_e) {",
  "        case Sc_T1(_, sc_c) {",
  "            return (sc_c + 17);",
  "        }",
  "        case Sc_T1.Sc_T1_2(sc_a) {",
  "            match (sc_a) {",
  "                case Sc_T0.Sc_T0_1(sc_a) {",
  "                    return ((sc_a ^ sc_w) + 19);",
  "                }",
  "                case _ {",
  "                    return (sc_w + 23);",
  "                }",
  "            }",
  "        }",
  "        case sc_d {",
  "            return ((sc_w * 29) + 31);",
  "        }",
  "    }",
  "}",
  "",
  "function sc_make1_0(sc_x: word) returns (Sc_T1<word>) {",
  "    let sc_k: word = ((sc_x + 0) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T1(sc_x, (sc_x + 7));",
  "    }",
  "    if (sc_k == 1) {",
  "        return Sc_T1.Sc_T1_1;",
  "    }",
  "    return Sc_T1.Sc_T1_2(Sc_T0.Sc_T0_1((sc_x * 9)));",
  "}",
  "",
  "function sc_make1_1(sc_x: word) returns (Sc_T1<(word, word)>) {",
  "    let sc_k: word = ((sc_x + 2) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T1.Sc_T1((sc_x, sc_x), (sc_x ^ 3));",
  "    }",
  "    return .Sc_T1_2(Sc_T0.Sc_T0_0);",
  "}",
  "",
  "function sc_view2(sc_e: Sc_T0, sc_f: Sc_T1<word>, sc_w: word) returns (word) {",
  "    match (sc_e, sc_f) {",
  "        case (Sc_T0.Sc_T0_1(sc_a), Sc_T1(sc_b, _)) {",
  "            return ((sc_a + sc_b) + 41);",
  "        }",
  "        case (_, Sc_T1.Sc_T1_1) {",
  "            return (sc_w + 43);",
  "        }",
  "        case (sc_c, _) {",
  "            return ((sc_w ^ 47) + 0);",
  "        }",
  "    }",
  "}",
  "",
  "function sc_make2_0(sc_x: word) returns (Sc_T0) {",
  "    let sc_k: word = ((sc_x + 3) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T0.Sc_T0_1(sc_x);",
  "    }",
  "    return Sc_T0.Sc_T0_0;",
  "}",
  "",
  "function sc_make2_1(sc_x: word) returns (Sc_T1<word>) {",
  "    let sc_k: word = ((sc_x + 0) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T1.Sc_T1((sc_x + 1), sc_x);",
  "    }",
  "    return Sc_T1.Sc_T1_1;",
  "}",
  "",
  "contract SynthesizedEnums {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_r0: word = sc_view0(sc_make0_0(sc_input), (sc_input + 13));",
  "        let sc_r1: word = sc_view1(sc_make1_0(sc_input), (sc_input + 37));",
  "        let sc_r2: word = sc_view1(sc_make1_1(sc_input), (sc_input + 37));",
  "        let sc_r3: word = sc_view2(sc_make2_0(sc_input), sc_make2_1(sc_input), (sc_input + 53));",
  "        return uint256((((sc_r0 + (sc_r1 * 3)) + (sc_r2 * 5)) + (sc_r3 * 7)));",
  "    }",
  "}", ""]

private def fixtureChecks : IO Unit := do
  ensure fixturePlan.admitted "the fixture plan is not admitted"
  let some checked := Enums.CheckedPlan.ofPlan? fixturePlan | throw (IO.userError "the fixture failed the checker")
  ensure ((Solcore.Synthesis.Source.Enums.emit fixturePlan).source == fixtureSource) "the fixture source changed"
  for (input, expected) in fixtureResults do
    ensure ((← run (checked.program (Word.ofNatModulo input))) == expected) s!"fixture input {input}: Core result"
    ensure (interpret fixturePlan input == some expected) s!"fixture input {input}: interpreter result"
  let shapes := fixturePlan.shapes
  let has := fun (dimension value : String) => ((shapes.find? (·.1 == dimension)).map (·.2.contains value)).getD false
  for (dimension, value) in [("views", "single"), ("views", "pair"), ("views", "generic"), ("patterns", "dot"),
      ("patterns", "same-name"), ("patterns", "nested"), ("patterns", "shadow"), ("patterns", "rebound"),
      ("patterns", "default"), ("patterns", "nullary"), ("wildcards", "column"), ("wildcards", "component"),
      ("wildcards", "field"), ("wildcards", "arm"), ("depths", "2"), ("declarations", "argument:tuple")] do
    ensure (has dimension value) s!"the fixture lacks {dimension}:{value}"

/-- Admission refuses what the compiler or the reference cannot take. -/
private def admissionChecks : IO Unit := do
  let views := fixtureViews
  let withArms := fun (index : Nat) (arms : List Arm) =>
    ({fixturePlan with views := views.set index {(views.getD index default) with arms}} : Plan)
  let armsOf := fun (index : Nat) => (views.getD index default).arms
  let withPatterns := fun (index arm : Nat) (patterns : List Pat) =>
    withArms index ((armsOf index).set arm {((armsOf index).getD arm default) with patterns})
  let withBody := fun (index arm : Nat) (body : ArmBody) =>
    withArms index ((armsOf index).set arm {((armsOf index).getD arm default) with body})
  let refused := fun (label : String) (plan : Plan) => ensure (!plan.admitted) s!"admitted {label}"
  let catchAll : Arm := {patterns := [.wild], body := .expr (body (.constant 1) [] 1)}
  -- An arm after the default, an unreachable arm, a non-exhaustive match.
  refused "an arm after default" (withArms 0 (armsOf 0 ++ [catchAll]))
  refused "an unreachable arm" (withArms 0 ((armsOf 0).take 1 ++ [(armsOf 0).headD default] ++ (armsOf 0).drop 1))
  refused "a non-exhaustive match" (withArms 0 ((armsOf 0).take 2))
  -- A constructor out of range, a same-name form of another constructor, a nested dot value.
  refused "a constructor out of range" (withPatterns 0 1 [.ctor1 3 (.var 4) .qualified])
  refused "a misplaced same-name pattern" (withPatterns 0 1 [.ctor1 1 (.var 4) .sameName])
  let genericView := views.getD 1 default
  let nestedDot : Builder := {offset := 0, trees := [.ctor1 2 (.ctor1 1 (.leaf .mul 9) .dot) .qualified]}
  refused "a nested dot value"
    {fixturePlan with views := views.set 1 {genericView with builders := genericView.builders.set 0 nestedDot}}
  -- A name bound twice in a row, a body naming a non-Word, a nested match on a Word.
  refused "a repeated name in one row" (withPatterns 0 0 [.ctor2 2 (.var 0) (.tuple (.var 0) .wild) .qualified])
  refused "a body naming a non-Word" (withBody 2 2 (.expr (body (.name 2) [] 0)))
  refused "a nested match on a Word" (withBody 0 1 (.nested 4 [{patterns := [], body := body (.constant 0) [] 0}]))
  -- A generic view inspecting its parameter, a declaration referring to a later one.
  refused "a generic view inspecting its parameter" (withPatterns 1 0 [.ctor2 0 (.ctor0 0 .qualified) (.var 2) .sameName])
  let firstDecl := fixtureDecls.headD default
  refused "a forward declaration reference"
    {fixturePlan with decls := fixtureDecls.set 0 {firstDecl with constructors := [[], [.enum 1], [.word]]}}
  -- A same-name declaration whose constructor 0 has no field.
  refused "a nullary same-name constructor"
    {fixturePlan with decls := fixtureDecls.set 0 {firstDecl with sameName := true}}

private def shapeValues : List (String × List String) := [
  ("constructors", ["2", "3", "4"]),
  ("fields", ["count:0", "count:1", "count:2", "type:applied", "type:enum", "type:param", "type:tuple", "type:word"]),
  ("declarations", ["argument:enum", "argument:param", "argument:tuple", "argument:word", "generic", "plain",
    "same-name"]),
  ("views", ["generic", "pair", "single"]),
  ("patterns", ["default", "dot", "exhaustive", "nested", "nullary", "qualified", "rebound", "repeated",
    "same-name", "shadow", "tuple", "variable", "wildcard"]),
  ("wildcards", ["arm", "column", "component", "deep", "field"]),
  ("depths", ["1", "2", "3"])]

/-- Generation is deterministic, draws every shape within 600 seeds,
replays exactly and drops views to fit a smaller budget. -/
private def generationChecks : IO Unit := do
  let mut seen : List (String × String) := []
  for seed in List.range 600 do
    let plan := generate (UInt64.ofNat (seed + 1))
    ensure (planJsonEq plan (generate (UInt64.ofNat (seed + 1)))) "generation is not deterministic"
    for (dimension, values) in plan.shapes do
      for value in values do
        unless seen.contains (dimension, value) do seen := (dimension, value) :: seen
  for (dimension, values) in shapeValues do
    for value in values do
      ensure (seen.contains (dimension, value)) s!"600 seeds never drew {dimension}:{value}"
  let corpus := Enums.generateCases (Seed.ofNat 1) Enums.defaultNodes 64 64 fuel
  let all ← cases corpus
  ensure (all.size = 64) "generation from seed 1 did not return 64 cases"
  for case in all do
    ensure ((← get (Enums.replayCase case fuel)) == case) "a generated case failed exact replay"
  -- Seeded inputs and the identity filter are recorded and replay.
  let seeded ← cases (Enums.generateCases (Seed.ofNat 7) Enums.defaultNodes 12 4 fuel .seeded .nonIdentity)
  ensure (seeded.size = 12) "seeded generation did not return twelve inputs"
  for case in seeded do
    ensure ((← get (Enums.replayCase case fuel)) == case) "a seeded case failed exact replay"
  -- Constant plans are excluded, and a 256-node budget drops views.
  let mut constant := false
  for seed in List.range 120 do
    if let .ok plan := Enums.generatedPlan (Seed.ofNat (seed + 1)) Enums.defaultNodes then
      if errorOf (Enums.inputSensitive plan fuel) == some "all eight boundary inputs returned the same Word" then
        constant := true
  ensure constant "no constant plan was excluded in 120 seeds"
  let mut dropped := false
  for seed in List.range 40 do
    if let .ok small := Enums.generatedPlan (Seed.ofNat (seed + 1)) Enums.minimumNodes then
      ensure (small.plan.nodes ≤ Enums.minimumNodes) "a fitted plan exceeds its budget"
      if small.plan.views.length < (generate (UInt64.ofNat (seed + 1))).views.length then dropped := true
  ensure dropped "a 256-node budget never dropped a view"
where
  planJsonEq (left right : Plan) : Bool := Enums.planJson left == Enums.planJson right

/-- Tampering is refused; reductions are admitted, strictly smaller and
replay, and a shrink response stays below its byte cap. -/
private def tamperChecks : IO Unit := do
  let all ← cases (Enums.generateCases (Seed.ofNat 1) Enums.defaultNodes 8 4 fuel)
  let case := all[0]!
  let plan ← get (case.getObjVal? "enumPlan")
  ensure (Enums.replayCase (case.setObjVal! "source" (toJson "contract C {}")) fuel matches .error _)
    "a changed source replayed"
  ensure (Enums.replayCase (case.setObjVal! "program" (Solcore.Core.Wire.encodeProgram
      {resultType := .word, dataDefinitions := [], body := .word Word.zero})) fuel matches .error _)
    "a changed reference replayed"
  ensure (errorOf (Enums.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "generatorVersion" (toJson "core-enum-match-v0"))) fuel) == some "generatorVersion changed")
    "a changed generator version replayed"
  ensure (Enums.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "enumShapes" (Json.mkObj []))) fuel matches .error _) "changed enum shapes replayed"
  ensure (Enums.replayCase (case.setObjVal! "enumPlan" (plan.setObjVal! "views" (.arr #[]))) fuel matches .error _)
    "a plan without views replayed"
  let origin ← get ((← provenance case).getObjVal? "origin")
  ensure (Enums.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "origin" (origin.setObjVal! "seed" (toJson "2")))) fuel matches .error _) "a changed seed replayed"
  let shrunk ← get (Enums.shrinkCases case 4096 fuel)
  let reduced ← cases shrunk
  ensure (!reduced.isEmpty) "no reduction of the first generated case"
  ensure (shrunk.compress.utf8ByteSize ≤ 2 * 1024 * 1024) "a shrink response exceeds 2 MiB"
  for candidate in reduced do
    ensure ((← get (Enums.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
  let parent ← get (Enums.caseProgram case)
  let all := Enums.reductions parent
  for reduction in all do
    ensure (decide (reduction.candidate.measure.StrictlySmaller parent.measure)) "a reduction is not strictly smaller"
  -- Every kind of plan reduction applies somewhere in the first 40 plans.
  let mut kinds : List String := []
  for seed in List.range 40 do
    if let .ok checked := Enums.generatedPlan (Seed.ofNat (seed + 1)) Enums.defaultNodes then
      let source : Enums.CheckedInput := ⟨checked, Word.ofNatModulo 5⟩
      for reduction in Enums.reductions source do
        let next := reduction.candidate.plan.plan
        let kind := if next.views.length < checked.plan.views.length then "view"
          else if next.decls.length < checked.plan.decls.length then "declaration"
          else if (next.decls.map (·.constructors.length)) != (checked.plan.decls.map (·.constructors.length)) then
            "constructor"
          else if (next.decls.map Decl.size) != (checked.plan.decls.map Decl.size) then "field"
          else if reduction.candidate.input != source.input then "input" else "view-part"
        unless kinds.contains kind do kinds := kind :: kinds
  for kind in ["view", "declaration", "constructor", "field", "input", "view-part"] do
    ensure (kinds.contains kind) s!"no {kind} reduction in 40 plans"
  let reducedOrigin ← get ((← provenance reduced[0]!).getObjVal? "origin")
  ensure (Enums.replayCase (reduced[0]!.setObjVal! "provenance" ((← provenance reduced[0]!).setObjVal!
      "origin" (reducedOrigin.setObjVal! "parentPlan" (← get (reduced[0]!.getObjVal? "enumPlan"))))) fuel
      matches .error _)
    "a reduction claiming itself as its parent replayed"

def testSourceEnumCases : IO Unit := do
  fixtureChecks
  admissionChecks
  modelChecks
  generationChecks
  tamperChecks

end Tests.SourceEnumCases
