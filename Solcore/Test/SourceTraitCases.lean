import Solcore.Synthesis.Source.TraitCases

/-! The `runtime-traits` profile. Its Core reference has one closure per
instance type and method reachable from the uses; it agrees with a direct
interpreter that dispatches every impl by the instance type at run time, on
generated plans, and a fixture's source and results are golden, the results
from a separate Python model. Admission refuses missing and misordered impls,
ill-formed steps and helpers, and ill-formed uses; generation draws every
shape and replays exactly; tampering is refused, and reductions are strictly
smaller and replay. -/
set_option autoImplicit false

namespace Tests.SourceTraitCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core (Seed)
open Solcore.Synthesis.Core.Traits
open Solcore.Synthesis.Source

abbrev Decl := Solcore.Synthesis.Core.Enums.Decl

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

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def run (program : Solcore.Core.Wire.Program) : IO Nat :=
  match program.toCore.runStateful fuel with
  | .done (.word value) _ => pure value.val
  | _ => throw (IO.userError "a reference program did not return a Word")

/-! A direct interpreter of a plan: values as trees, each method dispatched
by its instance type to that type's impl when it is called, a declaration's
fields substituted here. It shares no code with the Core reference. -/

private inductive Runtime where
  | word (value : Nat)
  | tuple (left right : Runtime)
  | side (right : Bool) (value : Runtime)
  | ctor (index : Nat) (fields : List Runtime)
  deriving Inhabited

private def evaluate (input : Nat) : Val → Runtime
  | .leaf .input _ => .word input
  | .leaf .add constant => .word ((input + constant) % modulus)
  | .leaf .xor constant => .word (input ^^^ constant)
  | .leaf .mul constant => .word ((input * constant) % modulus)
  | .tuple left right => .tuple (evaluate input left) (evaluate input right)
  | .inl value => .side false (evaluate input value)
  | .inr value => .side true (evaluate input value)
  | .ctor0 index _ => .ctor index []
  | .ctor1 index field _ => .ctor index [evaluate input field]
  | .ctor2 index first second _ => .ctor index [evaluate input first, evaluate input second]

private def operate : Op → Nat → Nat → Nat
  | .add, left, right => (left + right) % modulus
  | .sub, left, right => (left + modulus - right) % modulus
  | .xor, left, right => left ^^^ right
  | .mul, left, right => (left * right) % modulus

private def stepValue (step : Step) : List Nat → Nat
  | [] => step.constant
  | first :: rest => operate step.op (rest.foldl (operate step.combine) first) step.constant

private def substitute (argument : Inst) : Solcore.Synthesis.Core.Enums.Ty → Inst
  | .word => .word
  | .param => argument
  | .tuple left right => .tuple (substitute argument left) (substitute argument right)
  | .enum index => .enum index
  | .applied index inner => .applied index (substitute argument inner)

private def fieldsOf (plan : Plan) : Inst → List (List Inst)
  | .tuple left right => [[left, right]]
  | .sum left right => [[left], [right]]
  | .enum index => ((plan.decls[index]?).map (·.constructors.map (·.map (substitute .word)))).getD []
  | .applied index argument => ((plan.decls[index]?).map (·.constructors.map (·.map (substitute argument)))).getD []
  | .word => []

private def headOfInst : Inst → Head
  | .word => .word
  | .tuple _ _ => .tuple
  | .sum _ _ => .sum
  | .enum index | .applied index _ => .decl index

private def interpretFuel : Nat := 64

private def foldValue (plan : Plan) : Nat → Inst → Runtime → Option Nat
  | 0, _, _ => none
  | fuel + 1, type, value => do
      let impl ← plan.impls.find? (·.head == headOfInst type)
      match type, value with
      | .word, .word word => return stepValue (← impl.unary.head?) [word]
      | .tuple left right, .tuple first second =>
          return stepValue (← impl.unary.head?) [← foldValue plan fuel left first, ← foldValue plan fuel right second]
      | .sum left _, .side false inner => return stepValue (← impl.unary[0]?) [← foldValue plan fuel left inner]
      | .sum _ right, .side true inner => return stepValue (← impl.unary[1]?) [← foldValue plan fuel right inner]
      | _, .ctor index fields =>
          let types ← (fieldsOf plan type)[index]?
          let operands ← (types.zip fields).mapM fun (fieldType, field) => foldValue plan fuel fieldType field
          return stepValue (← impl.unary[index]?) operands
      | _, _ => none

private def bothValue (plan : Plan) : Nat → Inst → Runtime → Runtime → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, type, first, second => do
      let impl ← plan.impls.find? (·.head == headOfInst type)
      match type, first, second with
      | .word, .word left, .word right => return stepValue (← impl.binary.head?) [left, right]
      | .tuple left right, .tuple a b, .tuple c d =>
          return stepValue (← impl.binary.head?) [← bothValue plan fuel left a c, ← bothValue plan fuel right b d]
      | .sum left _, .side false a, .side false c => return stepValue (← impl.binary[0]?) [← bothValue plan fuel left a c]
      | .sum _ right, .side true b, .side true d => return stepValue (← impl.binary[1]?) [← bothValue plan fuel right b d]
      | .sum _ _, .side false _, .side true _ => impl.mismatch[0]?
      | .sum _ _, .side true _, .side false _ => impl.mismatch[1]?
      | _, .ctor index xs, .ctor other ys =>
          if index != other then impl.mismatch[0]?
          else
            let types ← (fieldsOf plan type)[index]?
            let operands ← ((types.zip xs).zip ys).mapM fun ((fieldType, x), y) => bothValue plan fuel fieldType x y
            return stepValue (← impl.binary[index]?) operands
      | _, _, _ => none

private def selected (builder : Solcore.Synthesis.Core.Traits.Builder) (input : Nat) : Val :=
  builder.trees.getD (min ((input + builder.offset) % 4) (builder.trees.length - 1)) default

private def interpret (plan : Plan) (input : Nat) : Option Nat := do
  let results ← plan.uses.mapM fun use => do
    let first := evaluate input (selected use.builder input)
    let shifted := (input + use.shift) % modulus
    let second := evaluate shifted (selected use.builder shifted)
    let value ← match use.call, use.method with
      | .lifted, .unary => foldValue plan interpretFuel (.tuple use.type use.type) (.tuple first first)
      | .lifted, .binary =>
          bothValue plan interpretFuel (.tuple use.type use.type) (.tuple first second) (.tuple second first)
      | _, .unary => foldValue plan interpretFuel use.type first
      | _, .binary => bothValue plan interpretFuel use.type first second
    match plan.helpers.find? (fun helper => helper.call == use.call && helper.method == use.method) with
    | some helper => return operate helper.op value helper.constant
    | none => return value
  return results.zipIdx.foldl (fun accumulated (result, index) =>
    (accumulated + result * (2 * index + 1)) % modulus) 0

private def boundary : List Nat := [0, 1, 2, 255, 256, 2 ^ 256 - 1, 2 ^ 255, 2 ^ 255 - 1]

/-- The reference agrees with the interpreter on 200 generated plans at the
eight boundary inputs and four others. -/
private def modelChecks : IO Unit := do
  let mut compared := 0
  for seed in List.range 200 do
    match Traits.generatedPlan (Seed.ofNat (seed + 1)) Traits.defaultNodes with
    | .error _ => pure ()
    | .ok checked =>
        for input in boundary ++ [3, 1001, 0x1234567890abcdef, 2 ^ 200 + 77] do
          let core ← run (checked.program (Word.ofNatModulo input))
          ensure (interpret checked.plan input == some core)
            s!"seed {seed + 1} input {input}: the reference differs from the interpreter"
          compared := compared + 1
  ensure (compared ≥ 2000) "fewer than 167 generated plans compared with the interpreter"

/-! A fixture with every instance kind under both methods, every call form,
every generic argument kind, both match forms of a declaration and the
sum-of-product shape. -/

private def step (combine op : Op) (constant : Nat) : Step := {combine, op, constant}

private def fixtureDecls : List Decl := [
  {generic := false, sameName := false, constructors := [[], [.word], [.word, .word]]},
  {generic := true, sameName := true, constructors := [[.param, .word], [], [.enum 0]]},
  {generic := true, sameName := false, constructors := [[.tuple .param .param], [.applied 1 .param, .param]]}]

private def fixtureImpls : List Impl := [
  {head := .word, unary := [step .add .mul 3], binary := [step .sub .xor 5], form := .nested, mismatch := []},
  {head := .tuple, unary := [step .add .mul 7], binary := [step .xor .add 11], form := .nested, mismatch := []},
  {head := .sum, unary := [step .add .add 13, step .add .mul 17], binary := [step .add .add 19, step .add .xor 31],
   form := .nested, mismatch := [23, 29]},
  {head := .decl 0, unary := [step .add .add 37, step .add .sub 41, step .mul .add 43],
   binary := [step .add .add 47, step .add .add 53, step .sub .xor 59], form := .columns, mismatch := [61]},
  {head := .decl 1, unary := [step .add .xor 67, step .add .add 71, step .add .mul 73],
   binary := [step .add .mul 79, step .add .add 89, step .add .sub 101], form := .nested, mismatch := [83]},
  {head := .decl 2, unary := [step .add .add 107, step .xor .sub 109],
   binary := [step .add .mul 113, step .add .xor 127], form := .columns, mismatch := [131]}]

private def fixtureHelpers : List Helper := [
  {call := .generic, method := .unary, op := .add, constant := 137},
  {call := .generic, method := .binary, op := .mul, constant := 139},
  {call := .lifted, method := .unary, op := .xor, constant := 149},
  {call := .lifted, method := .binary, op := .sub, constant := 151}]

private def input : Val := .leaf .input 0

private def fixtureUses : List Use := [
  {method := .binary, call := .direct, type := .sum (.tuple .word .word) .word, shift := 4,
   builder := {offset := 1, trees := [.inl (.tuple input (.leaf .add 3)), .inr (.leaf .mul 5)]}},
  {method := .unary, call := .generic, type := .tuple (.sum .word (.enum 0)) .word, shift := 0,
   builder := {offset := 0, trees := [.tuple (.inl input) (.leaf .xor 7),
     .tuple (.inr (.ctor2 2 input (.leaf .add 2) .qualified)) input,
     .tuple (.inr (.ctor1 1 (.leaf .mul 9) .qualified)) (.leaf .add 1)]}},
  {method := .binary, call := .generic, type := .applied 1 (.sum .word .word), shift := 4,
   builder := {offset := 0, trees := [.ctor2 0 (.inl input) (.leaf .add 9) .sameName, .ctor0 1 .qualified,
     .ctor2 0 (.inr (.leaf .mul 3)) input .sameName, .ctor1 2 (.ctor1 1 input .qualified) .dot]}},
  {method := .unary, call := .lifted, type := .applied 1 (.applied 1 .word), shift := 0,
   builder := {offset := 2, trees := [.ctor2 0 (.ctor2 0 input input .sameName) (.leaf .xor 5) .sameName,
     .ctor2 0 (.ctor1 2 (.ctor0 0 .qualified) .qualified) (.leaf .mul 7) .qualified,
     .ctor1 2 (.ctor2 2 (.leaf .add 1) input .qualified) .dot]}},
  {method := .binary, call := .lifted, type := .applied 1 (.tuple .word .word), shift := 2,
   builder := {offset := 3, trees := [.ctor2 0 (.tuple input (.leaf .add 4)) (.leaf .mul 3) .qualified,
     .ctor1 2 (.ctor2 2 (.leaf .add 6) (.leaf .xor 9) .qualified) .qualified, .ctor0 1 .dot]}},
  {method := .unary, call := .direct, type := .applied 2 (.enum 0), shift := 0,
   builder := {offset := 1, trees := [.ctor1 0 (.tuple (.ctor0 0 .qualified) (.ctor1 1 input .qualified)) .qualified,
     .ctor2 1 (.ctor2 0 (.ctor2 2 input (.leaf .mul 11) .qualified) (.leaf .add 13) .sameName)
       (.ctor1 1 (.leaf .xor 17) .qualified) .dot,
     .ctor2 1 (.ctor1 2 (.ctor0 0 .qualified) .qualified) (.ctor2 2 (.leaf .add 19) input .qualified) .qualified]}}]

private def fixturePlan : Plan :=
  {decls := fixtureDecls, unary := true, binary := true, impls := fixtureImpls, helpers := fixtureHelpers,
   uses := fixtureUses}

/-- Golden results of `scratchpad/u13/fixture_model.py`, a separate Python
model of the fixture. -/
private def fixtureResults : List (Nat × Nat) := [(0, 580351), (1, 549501),
  (2, 115792089237316195423570985008687907853269984665640564039457584007913128306364), (3, 240971),
  (255, 3264495), (2 ^ 255, 580351), (2 ^ 256 - 1, 194799)]

private def fixtureSource : String := String.intercalate "\n" [
  "import * from std;",
  "import * from std.dispatch;",
  "",
  "enum Sc_T0 {",
  "    Sc_T0_0,",
  "    Sc_T0_1(word),",
  "    Sc_T0_2(word, word)",
  "}",
  "",
  "enum Sc_T1<a> {",
  "    Sc_T1(a, word),",
  "    Sc_T1_1,",
  "    Sc_T1_2(Sc_T0)",
  "}",
  "",
  "enum Sc_T2<a> {",
  "    Sc_T2_0((a, a)),",
  "    Sc_T2_1(Sc_T1<a>, a)",
  "}",
  "",
  "trait Sc_Fold<a> {",
  "    function sc_fold(sc_x: a) returns (word);",
  "    function sc_both(sc_x: a, sc_y: a) returns (word);",
  "}",
  "",
  "impl Sc_Fold<word> {",
  "    function sc_fold(sc_x: word) returns (word) {",
  "        return (sc_x * 3);",
  "    }",
  "    function sc_both(sc_x: word, sc_y: word) returns (word) {",
  "        return ((sc_x - sc_y) ^ 5);",
  "    }",
  "}",
  "",
  "impl<f, g> Sc_Fold<(f, g)> where f: Sc_Fold, g: Sc_Fold {",
  "    function sc_fold(sc_x: (f, g)) returns (word) {",
  "        match (sc_x) {",
  "            case (sc_a, sc_b) {",
  "                return ((Sc_Fold.sc_fold(sc_a) + Sc_Fold.sc_fold(sc_b)) * 7);",
  "            }",
  "        }",
  "    }",
  "    function sc_both(sc_x: (f, g), sc_y: (f, g)) returns (word) {",
  "        match (sc_x) {",
  "            case (sc_a, sc_b) {",
  "                match (sc_y) {",
  "                    case (sc_c, sc_d) {",
  "                        return ((Sc_Fold.sc_both(sc_a, sc_c) ^ Sc_Fold.sc_both(sc_b, sc_d)) + 11);",
  "                    }",
  "                }",
  "            }",
  "        }",
  "    }",
  "}",
  "",
  "impl<f, g> Sc_Fold<sum<f, g>> where f: Sc_Fold, g: Sc_Fold {",
  "    function sc_fold(sc_x: sum<f, g>) returns (word) {",
  "        match (sc_x) {",
  "            case inl(sc_a) {",
  "                return (Sc_Fold.sc_fold(sc_a) + 13);",
  "            }",
  "            case inr(sc_b) {",
  "                return (Sc_Fold.sc_fold(sc_b) * 17);",
  "            }",
  "        }",
  "    }",
  "    function sc_both(sc_x: sum<f, g>, sc_y: sum<f, g>) returns (word) {",
  "        match (sc_x) {",
  "            case inl(sc_a) {",
  "                match (sc_y) {",
  "                    case inl(sc_c) {",
  "                        return (Sc_Fold.sc_both(sc_a, sc_c) + 19);",
  "                    }",
  "                    case inr(_) {",
  "                        return 23;",
  "                    }",
  "                }",
  "            }",
  "            case inr(sc_b) {",
  "                match (sc_y) {",
  "                    case inl(_) {",
  "                        return 29;",
  "                    }",
  "                    case inr(sc_d) {",
  "                        return (Sc_Fold.sc_both(sc_b, sc_d) ^ 31);",
  "                    }",
  "                }",
  "            }",
  "        }",
  "    }",
  "}",
  "",
  "impl Sc_Fold<Sc_T0> {",
  "    function sc_fold(sc_x: Sc_T0) returns (word) {",
  "        match (sc_x) {",
  "            case Sc_T0.Sc_T0_0 {",
  "                return 37;",
  "            }",
  "            case Sc_T0.Sc_T0_1(sc_a) {",
  "                return (Sc_Fold.sc_fold(sc_a) - 41);",
  "            }",
  "            case Sc_T0.Sc_T0_2(sc_a, sc_b) {",
  "                return ((Sc_Fold.sc_fold(sc_a) * Sc_Fold.sc_fold(sc_b)) + 43);",
  "            }",
  "        }",
  "    }",
  "    function sc_both(sc_x: Sc_T0, sc_y: Sc_T0) returns (word) {",
  "        match (sc_x, sc_y) {",
  "            case (Sc_T0.Sc_T0_0, Sc_T0.Sc_T0_0) {",
  "                return 47;",
  "            }",
  "            case (Sc_T0.Sc_T0_1(sc_a), Sc_T0.Sc_T0_1(sc_c)) {",
  "                return (Sc_Fold.sc_both(sc_a, sc_c) + 53);",
  "            }",
  "            case (Sc_T0.Sc_T0_2(sc_a, sc_b), Sc_T0.Sc_T0_2(sc_c, sc_d)) {",
  "                return ((Sc_Fold.sc_both(sc_a, sc_c) - Sc_Fold.sc_both(sc_b, sc_d)) ^ 59);",
  "            }",
  "            default {",
  "                return 61;",
  "            }",
  "        }",
  "    }",
  "}",
  "",
  "impl<a> Sc_Fold<Sc_T1<a>> where a: Sc_Fold {",
  "    function sc_fold(sc_x: Sc_T1<a>) returns (word) {",
  "        match (sc_x) {",
  "            case Sc_T1(sc_a, sc_b) {",
  "                return ((Sc_Fold.sc_fold(sc_a) + Sc_Fold.sc_fold(sc_b)) ^ 67);",
  "            }",
  "            case Sc_T1.Sc_T1_1 {",
  "                return 71;",
  "            }",
  "            case Sc_T1.Sc_T1_2(sc_a) {",
  "                return (Sc_Fold.sc_fold(sc_a) * 73);",
  "            }",
  "        }",
  "    }",
  "    function sc_both(sc_x: Sc_T1<a>, sc_y: Sc_T1<a>) returns (word) {",
  "        match (sc_x) {",
  "            case Sc_T1(sc_a, sc_b) {",
  "                match (sc_y) {",
  "                    case Sc_T1(sc_c, sc_d) {",
  "                        return ((Sc_Fold.sc_both(sc_a, sc_c) + Sc_Fold.sc_both(sc_b, sc_d)) * 79);",
  "                    }",
  "                    default {",
  "                        return 83;",
  "                    }",
  "                }",
  "            }",
  "            case Sc_T1.Sc_T1_1 {",
  "                match (sc_y) {",
  "                    case Sc_T1.Sc_T1_1 {",
  "                        return 89;",
  "                    }",
  "                    default {",
  "                        return 83;",
  "                    }",
  "                }",
  "            }",
  "            case Sc_T1.Sc_T1_2(sc_a) {",
  "                match (sc_y) {",
  "                    case Sc_T1.Sc_T1_2(sc_c) {",
  "                        return (Sc_Fold.sc_both(sc_a, sc_c) - 101);",
  "                    }",
  "                    default {",
  "                        return 83;",
  "                    }",
  "                }",
  "            }",
  "        }",
  "    }",
  "}",
  "",
  "impl<a> Sc_Fold<Sc_T2<a>> where a: Sc_Fold {",
  "    function sc_fold(sc_x: Sc_T2<a>) returns (word) {",
  "        match (sc_x) {",
  "            case Sc_T2.Sc_T2_0(sc_a) {",
  "                return (Sc_Fold.sc_fold(sc_a) + 107);",
  "            }",
  "            case Sc_T2.Sc_T2_1(sc_a, sc_b) {",
  "                return ((Sc_Fold.sc_fold(sc_a) ^ Sc_Fold.sc_fold(sc_b)) - 109);",
  "            }",
  "        }",
  "    }",
  "    function sc_both(sc_x: Sc_T2<a>, sc_y: Sc_T2<a>) returns (word) {",
  "        match (sc_x, sc_y) {",
  "            case (Sc_T2.Sc_T2_0(sc_a), Sc_T2.Sc_T2_0(sc_c)) {",
  "                return (Sc_Fold.sc_both(sc_a, sc_c) * 113);",
  "            }",
  "            case (Sc_T2.Sc_T2_1(sc_a, sc_b), Sc_T2.Sc_T2_1(sc_c, sc_d)) {",
  "                return ((Sc_Fold.sc_both(sc_a, sc_c) + Sc_Fold.sc_both(sc_b, sc_d)) ^ 127);",
  "            }",
  "            default {",
  "                return 131;",
  "            }",
  "        }",
  "    }",
  "}",
  "",
  "function sc_once<t>(sc_x: t) returns (word) where t: Sc_Fold {",
  "    return (Sc_Fold.sc_fold(sc_x) + 137);",
  "}",
  "",
  "function sc_twice<t>(sc_x: t, sc_y: t) returns (word) where t: Sc_Fold {",
  "    return (Sc_Fold.sc_both(sc_x, sc_y) * 139);",
  "}",
  "",
  "function sc_lift<t>(sc_x: t) returns (word) where t: Sc_Fold {",
  "    return (Sc_Fold.sc_fold((sc_x, sc_x)) ^ 149);",
  "}",
  "",
  "function sc_lift2<t>(sc_x: t, sc_y: t) returns (word) where t: Sc_Fold {",
  "    return (Sc_Fold.sc_both((sc_x, sc_y), (sc_y, sc_x)) - 151);",
  "}",
  "",
  "function sc_u0(sc_x: word) returns (sum<(word, word), word>) {",
  "    let sc_k: word = ((sc_x + 1) & 3);",
  "    if (sc_k == 0) {",
  "        return inl((sc_x, (sc_x + 3)));",
  "    }",
  "    return inr((sc_x * 5));",
  "}",
  "",
  "function sc_u1(sc_x: word) returns ((sum<word, Sc_T0>, word)) {",
  "    let sc_k: word = ((sc_x + 0) & 3);",
  "    if (sc_k == 0) {",
  "        return (inl(sc_x), (sc_x ^ 7));",
  "    }",
  "    if (sc_k == 1) {",
  "        return (inr(Sc_T0.Sc_T0_2(sc_x, (sc_x + 2))), sc_x);",
  "    }",
  "    return (inr(Sc_T0.Sc_T0_1((sc_x * 9))), (sc_x + 1));",
  "}",
  "",
  "function sc_u2(sc_x: word) returns (Sc_T1<sum<word, word>>) {",
  "    let sc_k: word = ((sc_x + 0) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T1(inl(sc_x), (sc_x + 9));",
  "    }",
  "    if (sc_k == 1) {",
  "        return Sc_T1.Sc_T1_1;",
  "    }",
  "    if (sc_k == 2) {",
  "        return Sc_T1(inr((sc_x * 3)), sc_x);",
  "    }",
  "    return .Sc_T1_2(Sc_T0.Sc_T0_1(sc_x));",
  "}",
  "",
  "function sc_u3(sc_x: word) returns (Sc_T1<Sc_T1<word>>) {",
  "    let sc_k: word = ((sc_x + 2) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T1(Sc_T1(sc_x, sc_x), (sc_x ^ 5));",
  "    }",
  "    if (sc_k == 1) {",
  "        return Sc_T1.Sc_T1(Sc_T1.Sc_T1_2(Sc_T0.Sc_T0_0), (sc_x * 7));",
  "    }",
  "    return .Sc_T1_2(Sc_T0.Sc_T0_2((sc_x + 1), sc_x));",
  "}",
  "",
  "function sc_u4(sc_x: word) returns (Sc_T1<(word, word)>) {",
  "    let sc_k: word = ((sc_x + 3) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T1.Sc_T1((sc_x, (sc_x + 4)), (sc_x * 3));",
  "    }",
  "    if (sc_k == 1) {",
  "        return Sc_T1.Sc_T1_2(Sc_T0.Sc_T0_2((sc_x + 6), (sc_x ^ 9)));",
  "    }",
  "    return .Sc_T1_1;",
  "}",
  "",
  "function sc_u5(sc_x: word) returns (Sc_T2<Sc_T0>) {",
  "    let sc_k: word = ((sc_x + 1) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T2.Sc_T2_0((Sc_T0.Sc_T0_0, Sc_T0.Sc_T0_1(sc_x)));",
  "    }",
  "    if (sc_k == 1) {",
  "        return .Sc_T2_1(Sc_T1(Sc_T0.Sc_T0_2(sc_x, (sc_x * 11)), (sc_x + 13)), Sc_T0.Sc_T0_1((sc_x ^ 17)));",
  "    }",
  "    return Sc_T2.Sc_T2_1(Sc_T1.Sc_T1_2(Sc_T0.Sc_T0_0), Sc_T0.Sc_T0_2((sc_x + 19), sc_x));",
  "}",
  "",
  "contract SynthesizedTraits {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_r0: word = Sc_Fold.sc_both(sc_u0(sc_input), sc_u0((sc_input + 4)));",
  "        let sc_r1: word = sc_once(sc_u1(sc_input));",
  "        let sc_r2: word = sc_twice(sc_u2(sc_input), sc_u2((sc_input + 4)));",
  "        let sc_r3: word = sc_lift(sc_u3(sc_input));",
  "        let sc_r4: word = sc_lift2(sc_u4(sc_input), sc_u4((sc_input + 2)));",
  "        let sc_r5: word = Sc_Fold.sc_fold(sc_u5(sc_input));",
  "        return uint256((((((sc_r0 + (sc_r1 * 3)) + (sc_r2 * 5)) + (sc_r3 * 7)) + (sc_r4 * 9)) + (sc_r5 * 11)));",
  "    }",
  "}", ""]

private def fixtureChecks : IO Unit := do
  ensure fixturePlan.admitted "the fixture plan is not admitted"
  let some checked := Traits.CheckedPlan.ofPlan? fixturePlan | throw (IO.userError "the fixture failed the checker")
  ensure ((Traits.emit fixturePlan).source == fixtureSource) "the fixture source changed"
  for (value, expected) in fixtureResults do
    ensure ((← run (checked.program (Word.ofNatModulo value))) == expected) s!"fixture input {value}: Core result"
    ensure (interpret fixturePlan value == some expected) s!"fixture input {value}: interpreter result"
  let shapes := fixturePlan.shapes
  let has := fun (dimension value : String) => ((shapes.find? (·.1 == dimension)).map (·.2.contains value)).getD false
  for (dimension, values) in shapeValues do
    for value in values do
      unless (dimension, value) ∈ [("depths", "0"), ("depths", "1"), ("forms", "tuple:columns")] do
        ensure (has dimension value) s!"the fixture lacks {dimension}:{value}"
where
  shapeValues : List (String × List String) := [
    ("instances", ["generic:binary", "generic:unary", "plain:binary", "plain:unary", "sum:binary", "sum:unary",
      "tuple:binary", "tuple:unary", "word:binary", "word:unary"]),
    ("calls", ["binary:direct", "binary:generic", "binary:lifted", "unary:direct", "unary:generic", "unary:lifted"]),
    ("depths", ["0", "1", "2", "3"]),
    ("arguments", ["generic", "plain", "sum", "tuple", "word"]),
    ("forms", ["enum:columns", "enum:nested", "tuple:columns", "tuple:nested"]),
    ("shapes", ["sum-of-product"])]

/-- Admission refuses what the compiler or the reference cannot take. -/
private def admissionChecks : IO Unit := do
  let refused := fun (label : String) (plan : Plan) => ensure (!plan.admitted) s!"admitted {label}"
  let impls := fixtureImpls
  let uses := fixtureUses
  let withImpl := fun (index : Nat) (impl : Impl) => ({fixturePlan with impls := impls.set index impl} : Plan)
  let withUse := fun (index : Nat) (use : Use) => ({fixturePlan with uses := uses.set index use} : Plan)
  let implAt := fun (index : Nat) => impls.getD index default
  let useAt := fun (index : Nat) => uses.getD index default
  refused "a use without the sum impl" {fixturePlan with impls := impls.eraseIdx 2}
  refused "a declaration impl without the Word impl" {fixturePlan with impls := impls.eraseIdx 0}
  refused "impls out of order" {fixturePlan with impls := [implAt 1, implAt 0] ++ impls.drop 2}
  refused "a missing arm" (withImpl 3 {implAt 3 with unary := (implAt 3).unary.take 2})
  refused "a fold operator on a one-operand arm" (withImpl 2 {implAt 2 with unary := [step .mul .add 13, step .add .mul 17]})
  refused "an operator on a nullary arm" (withImpl 3 {implAt 3 with unary := [step .add .xor 37, step .add .sub 41, step .mul .add 43]})
  refused "a two-column sum match" (withImpl 2 {implAt 2 with form := .columns})
  refused "one sum mismatch constant" (withImpl 2 {implAt 2 with mismatch := [23]})
  refused "a helper no use needs" {fixturePlan with helpers := fixtureHelpers ++ [fixtureHelpers.headD default]}
  refused "a missing helper" {fixturePlan with helpers := fixtureHelpers.drop 1}
  refused "a binary use without a shift" (withUse 0 {useAt 0 with shift := 0})
  refused "a binary use shifted by five" (withUse 0 {useAt 0 with shift := 5})
  refused "a shifted unary use" (withUse 5 {useAt 5 with shift := 1})
  refused "a use four levels deep" (withUse 1 {useAt 1 with type := .tuple (.tuple (.sum .word (.enum 0)) .word) .word})
  refused "a generic declaration used as plain" (withUse 5 {useAt 5 with type := .enum 1})
  refused "a nested dot value"
    (withUse 5 {useAt 5 with builder := {offset := 0, trees := [.ctor1 0 (.tuple (.ctor0 0 .dot) (.ctor0 0 .qualified)) .qualified]}})
  refused "a misplaced same-name value"
    (withUse 5 {useAt 5 with builder := {offset := 0, trees := [.ctor1 0 (.tuple (.ctor0 0 .sameName) (.ctor0 0 .qualified)) .qualified]}})
  refused "a use of a method the trait lacks"
    {fixturePlan with binary := false, impls := impls.map fun impl => {impl with binary := [], mismatch := [], form := .nested}}
  refused "a lifted use over the type limit"
    (withUse 3 {useAt 3 with type := .applied 2 (.applied 2 .word), builder := {offset := 0, trees := [.ctor1 0
      (.tuple (.ctor1 0 (.tuple input input) .qualified) (.ctor1 0 (.tuple input input) .qualified)) .qualified]}})
  refused "seven uses" {fixturePlan with uses := uses ++ [useAt 5]}

private def shapeValues : List (String × List String) := [
  ("instances", ["generic:binary", "generic:unary", "plain:binary", "plain:unary", "sum:binary", "sum:unary",
    "tuple:binary", "tuple:unary", "word:binary", "word:unary"]),
  ("calls", ["binary:direct", "binary:generic", "binary:lifted", "unary:direct", "unary:generic", "unary:lifted"]),
  ("depths", ["0", "1", "2", "3"]),
  ("arguments", ["generic", "plain", "sum", "tuple", "word"]),
  ("forms", ["enum:columns", "enum:nested", "tuple:columns", "tuple:nested"]),
  ("shapes", ["sum-of-product"])]

/-- Generation is deterministic, draws every shape within 300 seeds,
replays exactly and drops uses to fit a smaller budget. -/
private def generationChecks : IO Unit := do
  let mut seen : List (String × String) := []
  for seed in List.range 300 do
    let plan := generate (UInt64.ofNat (seed + 1))
    ensure (Traits.planJson plan == Traits.planJson (generate (UInt64.ofNat (seed + 1)))) "generation is not deterministic"
    for (dimension, values) in plan.shapes do
      for value in values do
        unless seen.contains (dimension, value) do seen := (dimension, value) :: seen
  for (dimension, values) in shapeValues do
    for value in values do
      ensure (seen.contains (dimension, value)) s!"300 seeds never drew {dimension}:{value}"
  let corpus := Traits.generateCases (Seed.ofNat 1) Traits.defaultNodes 64 64 fuel
  let all ← cases corpus
  ensure (all.size = 64) "generation from seed 1 did not return 64 cases"
  for case in all do
    ensure ((← get (Traits.replayCase case fuel)) == case) "a generated case failed exact replay"
  let seeded ← cases (Traits.generateCases (Seed.ofNat 7) Traits.defaultNodes 12 4 fuel .seeded .nonIdentity)
  ensure (seeded.size = 12) "seeded generation did not return twelve inputs"
  for case in seeded do
    ensure ((← get (Traits.replayCase case fuel)) == case) "a seeded case failed exact replay"
  let mut dropped := false
  for seed in List.range 40 do
    if let .ok small := Traits.generatedPlan (Seed.ofNat (seed + 1)) Traits.minimumNodes then
      ensure (small.plan.nodes ≤ Traits.minimumNodes) "a fitted plan exceeds its budget"
      if small.plan.uses.length < (generate (UInt64.ofNat (seed + 1))).uses.length then dropped := true
  ensure dropped "a 256-node budget never dropped a use"

/-- Tampering is refused; reductions are admitted, strictly smaller and
replay, and a shrink response stays below its byte cap. -/
private def tamperChecks : IO Unit := do
  let all ← cases (Traits.generateCases (Seed.ofNat 1) Traits.defaultNodes 8 4 fuel)
  let case := all[0]!
  let plan ← get (case.getObjVal? "traitPlan")
  ensure (Traits.replayCase (case.setObjVal! "source" (toJson "contract C {}")) fuel matches .error _)
    "a changed source replayed"
  ensure (Traits.replayCase (case.setObjVal! "program" (Solcore.Core.Wire.encodeProgram
      {resultType := .word, dataDefinitions := [], body := .word Word.zero})) fuel matches .error _)
    "a changed reference replayed"
  ensure (errorOf (Traits.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "generatorVersion" (toJson "core-trait-instances-v0"))) fuel) == some "generatorVersion changed")
    "a changed generator version replayed"
  ensure (Traits.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "traitShapes" (Json.mkObj []))) fuel matches .error _) "changed trait shapes replayed"
  ensure (Traits.replayCase (case.setObjVal! "traitPlan" (plan.setObjVal! "uses" (.arr #[]))) fuel matches .error _)
    "a plan without uses replayed"
  ensure (Traits.replayCase (case.setObjVal! "traitPlan" (plan.setObjVal! "methods" (toJson ["binary", "unary"])))
    fuel matches .error _) "a noncanonical method list replayed"
  let origin ← get ((← provenance case).getObjVal? "origin")
  ensure (Traits.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "origin" (origin.setObjVal! "seed" (toJson "2")))) fuel matches .error _) "a changed seed replayed"
  let shrunk ← get (Traits.shrinkCases case 4096 fuel)
  let reduced ← cases shrunk
  ensure (!reduced.isEmpty) "no reduction of the first generated case"
  ensure (shrunk.compress.utf8ByteSize ≤ 2 * 1024 * 1024) "a shrink response exceeds 2 MiB"
  for candidate in reduced do
    ensure ((← get (Traits.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
  let parent ← get (Traits.caseProgram case)
  for reduction in Traits.reductions parent do
    ensure (decide (reduction.candidate.measure.StrictlySmaller parent.measure)) "a reduction is not strictly smaller"
  let mut kinds : List String := []
  for seed in List.range 40 do
    if let .ok checked := Traits.generatedPlan (Seed.ofNat (seed + 1)) Traits.defaultNodes then
      let source : Traits.CheckedInput := ⟨checked, Word.ofNatModulo 5⟩
      for reduction in Traits.reductions source do
        let next := reduction.candidate.plan.plan
        let previous := checked.plan
        let kind := if next.uses.length < previous.uses.length then "use"
          else if next.decls.length < previous.decls.length then "declaration"
          else if (next.unary, next.binary) != (previous.unary, previous.binary) then "method"
          else if next.impls.length < previous.impls.length then "impl"
          else if (next.uses.map (·.type)) != (previous.uses.map (·.type)) then "nesting"
          else if (next.uses.map (·.call)) != (previous.uses.map (·.call)) then "call"
          else if reduction.candidate.input != source.input then "input" else "builder"
        unless kinds.contains kind do kinds := kind :: kinds
  for kind in ["use", "declaration", "method", "impl", "nesting", "call", "input", "builder"] do
    ensure (kinds.contains kind) s!"no {kind} reduction in 40 plans"
  let reducedOrigin ← get ((← provenance reduced[0]!).getObjVal? "origin")
  ensure (Traits.replayCase (reduced[0]!.setObjVal! "provenance" ((← provenance reduced[0]!).setObjVal!
      "origin" (reducedOrigin.setObjVal! "parentPlan" (← get (reduced[0]!.getObjVal? "traitPlan"))))) fuel
      matches .error _)
    "a reduction claiming itself as its parent replayed"

def testSourceTraitCases : IO Unit := do
  fixtureChecks
  admissionChecks
  modelChecks
  generationChecks
  tamperChecks

end Tests.SourceTraitCases
