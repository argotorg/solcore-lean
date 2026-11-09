import Solcore.Synthesis.Internal.Traits
import Solcore.Synthesis.Internal.Calls

/-!
# Trait profile tests

Runtime traits, trait hierarchies and several methods on one contract.
-/

section
-- leanmerge: from Solcore.Test.SourceHierarchyCases
/-! The `runtime-trait-hierarchies` profile. Its Core reference has the base
trait's closures and one subclass closure per receiver and argument type the
uses reach; it agrees with a direct interpreter that dispatches every method
by the instance type at run time, on generated plans, and a fixture's source
and results are golden, the results from a separate Python model. Admission
refuses missing and misordered impls of every trait, ill-formed steps,
helpers and uses; generation draws every shape and replays exactly;
tampering is refused, and reductions are strictly smaller and replay. -/
set_option autoImplicit false

namespace Tests.SourceHierarchyCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core (Seed)
open Solcore.Synthesis.Core.Hierarchies
open Solcore.Synthesis.Core.Traits (Inst Val Step Impl Head)
open Solcore.Synthesis.Source

abbrev Decl := Solcore.Synthesis.Core.Enums.Decl
abbrev Op := Solcore.Synthesis.Core.Enums.Op

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
fields substituted here, a helper's operator applied after its method. It
shares no code with the Core reference. -/

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

/-- The subclass method: a Word with the argument's base fold, any other
receiver at its bound values with the same argument. -/
private def mixValue (plan : Plan) (argumentType : Inst) (argument : Runtime) : Nat → Inst → Runtime → Option Nat
  | 0, _, _ => none
  | fuel + 1, type, value => do
      let impl ← plan.subImpls.find? (·.head == headOfInst type)
      match type, value with
      | .word, .word word =>
          return stepValue (← impl.steps.head?) [word, ← foldValue plan interpretFuel argumentType argument]
      | .tuple left right, .tuple first second =>
          return stepValue (← impl.steps.head?)
            [← mixValue plan argumentType argument fuel left first, ← mixValue plan argumentType argument fuel right second]
      | .sum left _, .side false inner => return stepValue (← impl.steps[0]?) [← mixValue plan argumentType argument fuel left inner]
      | .sum _ right, .side true inner => return stepValue (← impl.steps[1]?) [← mixValue plan argumentType argument fuel right inner]
      | _, .ctor index fields =>
          let types ← (fieldsOf plan type)[index]?
          let operands ← (types.zip fields).mapM fun (fieldType, field) =>
            mixValue plan argumentType argument fuel fieldType field
          return stepValue (← impl.steps[index]?) operands
      | _, _ => none

private def selected (builder : Solcore.Synthesis.Core.Traits.Builder) (input : Nat) : Val :=
  builder.trees.getD (min ((input + builder.offset) % 4) (builder.trees.length - 1)) default

private def helped (plan : Plan) (call : Call) (method : Method) (value : Nat) : Option Nat := do
  let apply := fun (call : Call) (value : Nat) => do
    let helper ← plan.helpers.find? fun helper => helper.call == call && helper.method == method
    return operate helper.op value helper.constant
  match call with
  | .direct => return value
  | .function => apply .function (← apply .sub value)
  | call => apply call value

private def interpret (plan : Plan) (input : Nat) : Option Nat := do
  let results ← plan.uses.mapM fun use => do
    let first := evaluate input (selected use.builder input)
    match use.method with
    | .unary => helped plan use.call use.method (← foldValue plan interpretFuel use.type first)
    | .binary =>
        let shifted := (input + use.shift) % modulus
        let second := evaluate shifted (selected use.builder shifted)
        helped plan use.call use.method (← bothValue plan interpretFuel use.type first second)
    | .mix =>
        let calls ← use.arguments.mapM fun argument => do
          let value := evaluate input (selected argument.builder input)
          helped plan use.call use.method (← mixValue plan argument.type value interpretFuel use.type first)
        return calls.foldl (fun sum call => (sum + call) % modulus) 0
  return results.zipIdx.foldl (fun accumulated (result, index) =>
    (accumulated + result * (2 * index + 1)) % modulus) 0

private def boundary : List Nat := [0, 1, 2, 255, 256, 2 ^ 256 - 1, 2 ^ 255, 2 ^ 255 - 1]

/-- The reference agrees with the interpreter on 200 generated plans at the
eight boundary inputs and four others. -/
private def modelChecks : IO Unit := do
  let mut compared := 0
  for seed in List.range 200 do
    match Hierarchies.generatedPlan (Seed.ofNat (seed + 1)) Hierarchies.defaultNodes with
    | .error _ => pure ()
    | .ok checked =>
        for input in boundary ++ [3, 1001, 0x1234567890abcdef, 2 ^ 200 + 77] do
          let core ← run (checked.program (Word.ofNatModulo input))
          ensure (interpret checked.plan input == some core)
            s!"seed {seed + 1} input {input}: the reference differs from the interpreter"
          compared := compared + 1
  ensure (compared ≥ 2000) "fewer than 167 generated plans compared with the interpreter"

/-! A fixture with the subclass's method-level generic called directly,
through `Sc_Top` and as a method value at five argument kinds, a `top` use
at a plain declaration, a generic function value and a method value. -/

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

private def fixtureSubImpls : List SubImpl := [
  {head := .word, steps := [step .add .mul 157]},
  {head := .tuple, steps := [step .xor .add 163]},
  {head := .sum, steps := [step .add .sub 167, step .add .mul 173]},
  {head := .decl 0, steps := [step .add .add 179, step .add .add 181, step .mul .xor 191]},
  {head := .decl 1, steps := [step .add .sub 193, step .add .add 197, step .add .xor 199]},
  {head := .decl 2, steps := [step .add .add 211, step .sub .mul 223]}]

private def fixtureHeads : List Head := [.word, .tuple, .sum, .decl 0, .decl 1, .decl 2]

private def fixtureHelpers : List Helper := [
  {call := .sub, method := .unary, op := .add, constant := 227},
  {call := .top, method := .binary, op := .sub, constant := 239},
  {call := .value, method := .binary, op := .xor, constant := 251},
  {call := .function, method := .unary, op := .mul, constant := 257},
  {call := .top, method := .mix, op := .xor, constant := 269},
  {call := .value, method := .mix, op := .sub, constant := 271}]

private def input : Val := .leaf .input 0

private def builder (offset : Nat) (trees : List Val) : Solcore.Synthesis.Core.Traits.Builder := {offset, trees}

private def fixtureUses : List Use := [
  {method := .binary, call := .top, type := .enum 0, shift := 4, arguments := [],
   builder := builder 1 [.ctor1 1 input .qualified, .ctor2 2 (.leaf .add 3) input .qualified, .ctor0 0 .qualified]},
  {method := .unary, call := .function, type := .tuple (.sum .word (.enum 0)) .word, shift := 0, arguments := [],
   builder := builder 0 [.tuple (.inl input) (.leaf .xor 7),
     .tuple (.inr (.ctor2 2 input (.leaf .add 2) .qualified)) input,
     .tuple (.inr (.ctor1 1 (.leaf .mul 9) .qualified)) (.leaf .add 1)]},
  {method := .binary, call := .value, type := .applied 1 (.sum .word .word), shift := 2, arguments := [],
   builder := builder 0 [.ctor2 0 (.inl input) (.leaf .add 9) .sameName, .ctor0 1 .qualified,
     .ctor2 0 (.inr (.leaf .mul 3)) input .sameName, .ctor1 2 (.ctor1 1 input .qualified) .dot]},
  {method := .mix, call := .direct, type := .enum 0, shift := 0,
   builder := builder 2 [.ctor2 2 input (.leaf .add 1) .qualified, .ctor1 1 (.leaf .mul 5) .qualified,
     .ctor0 0 .dot],
   arguments := [{type := .word, builder := builder 0 [.leaf .add 5]},
     {type := .tuple .word .word, builder := builder 1 [.tuple input (.leaf .mul 3), .tuple (.leaf .xor 1) input]}]},
  {method := .mix, call := .top, type := .tuple .word (.applied 1 .word), shift := 0,
   builder := builder 3 [.tuple input (.ctor2 0 input (.leaf .add 4) .sameName), .tuple (.leaf .mul 7) (.ctor0 1 .qualified),
     .tuple input (.ctor1 2 (.ctor1 1 input .qualified) .qualified)],
   arguments := [{type := .sum .word .word, builder := builder 0 [.inl input, .inr (.leaf .add 2)]},
     {type := .applied 2 (.enum 0), builder := builder 1 [
       .ctor1 0 (.tuple (.ctor0 0 .qualified) (.ctor1 1 input .qualified)) .qualified,
       .ctor2 1 (.ctor1 2 (.ctor0 0 .qualified) .qualified) (.ctor2 2 input (.leaf .mul 11) .qualified) .qualified]}]},
  {method := .mix, call := .value, type := .applied 2 (.tuple .word .word), shift := 0,
   builder := builder 0 [.ctor1 0 (.tuple (.tuple input input) (.tuple (.leaf .add 1) input)) .qualified,
     .ctor2 1 (.ctor2 0 (.tuple input input) (.leaf .add 2) .sameName) (.tuple input (.leaf .mul 3)) .qualified],
   arguments := [{type := .enum 0, builder := builder 0 [.ctor1 1 input .qualified, .ctor0 0 .qualified]},
     {type := .word, builder := builder 0 [.leaf .xor 13]}]}]

private def fixturePlan : Plan :=
  {decls := fixtureDecls, unary := true, binary := true, impls := fixtureImpls, sub := .mix,
   subImpls := fixtureSubImpls, tops := fixtureHeads, helpers := fixtureHelpers, uses := fixtureUses}

/-- Golden results of `scratchpad/u14/fixture_model.py`, a separate Python
model of the fixture. -/
private def fixtureResults : List (Nat × Nat) := [(0, 474593), (1, 34199480), (2, 2117668746), (3, 31548999),
  (255, 645060223), (2 ^ 255, 474593),
  (2 ^ 256 - 1, 115792089237316195423570985008687907853269984665640564039457584007913118515327)]

private def fixtureSource : String := String.intercalate "\n" [
  "pragma solcore;", "import * from std;",
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
  "trait Sc_Sub<a> where a: Sc_Fold {",
  "    function sc_mix<u>(sc_x: a, sc_y: u) returns (word) where u: Sc_Fold;",
  "}",
  "",
  "trait Sc_Top<a> where a: Sc_Sub {}",
  "",
  "impl Sc_Sub<word> {",
  "    function sc_mix<u>(sc_x: word, sc_y: u) returns (word) where u: Sc_Fold {",
  "        return ((sc_x + Sc_Fold.sc_fold(sc_y)) * 157);",
  "    }",
  "}",
  "",
  "impl<f, g> Sc_Sub<(f, g)> where f: Sc_Sub, g: Sc_Sub {",
  "    function sc_mix<u>(sc_x: (f, g), sc_y: u) returns (word) where u: Sc_Fold {",
  "        match (sc_x) {",
  "            case (sc_a, sc_b) {",
  "                return ((Sc_Sub.sc_mix(sc_a, sc_y) ^ Sc_Sub.sc_mix(sc_b, sc_y)) + 163);",
  "            }",
  "        }",
  "    }",
  "}",
  "",
  "impl<f, g> Sc_Sub<sum<f, g>> where f: Sc_Sub, g: Sc_Sub {",
  "    function sc_mix<u>(sc_x: sum<f, g>, sc_y: u) returns (word) where u: Sc_Fold {",
  "        match (sc_x) {",
  "            case inl(sc_a) {",
  "                return (Sc_Sub.sc_mix(sc_a, sc_y) - 167);",
  "            }",
  "            case inr(sc_b) {",
  "                return (Sc_Sub.sc_mix(sc_b, sc_y) * 173);",
  "            }",
  "        }",
  "    }",
  "}",
  "",
  "impl Sc_Sub<Sc_T0> {",
  "    function sc_mix<u>(sc_x: Sc_T0, sc_y: u) returns (word) where u: Sc_Fold {",
  "        match (sc_x) {",
  "            case Sc_T0.Sc_T0_0 {",
  "                return 179;",
  "            }",
  "            case Sc_T0.Sc_T0_1(sc_a) {",
  "                return (Sc_Sub.sc_mix(sc_a, sc_y) + 181);",
  "            }",
  "            case Sc_T0.Sc_T0_2(sc_a, sc_b) {",
  "                return ((Sc_Sub.sc_mix(sc_a, sc_y) * Sc_Sub.sc_mix(sc_b, sc_y)) ^ 191);",
  "            }",
  "        }",
  "    }",
  "}",
  "",
  "impl<a> Sc_Sub<Sc_T1<a>> where a: Sc_Sub {",
  "    function sc_mix<u>(sc_x: Sc_T1<a>, sc_y: u) returns (word) where u: Sc_Fold {",
  "        match (sc_x) {",
  "            case Sc_T1(sc_a, sc_b) {",
  "                return ((Sc_Sub.sc_mix(sc_a, sc_y) + Sc_Sub.sc_mix(sc_b, sc_y)) - 193);",
  "            }",
  "            case Sc_T1.Sc_T1_1 {",
  "                return 197;",
  "            }",
  "            case Sc_T1.Sc_T1_2(sc_a) {",
  "                return (Sc_Sub.sc_mix(sc_a, sc_y) ^ 199);",
  "            }",
  "        }",
  "    }",
  "}",
  "",
  "impl<a> Sc_Sub<Sc_T2<a>> where a: Sc_Sub {",
  "    function sc_mix<u>(sc_x: Sc_T2<a>, sc_y: u) returns (word) where u: Sc_Fold {",
  "        match (sc_x) {",
  "            case Sc_T2.Sc_T2_0(sc_a) {",
  "                return (Sc_Sub.sc_mix(sc_a, sc_y) + 211);",
  "            }",
  "            case Sc_T2.Sc_T2_1(sc_a, sc_b) {",
  "                return ((Sc_Sub.sc_mix(sc_a, sc_y) - Sc_Sub.sc_mix(sc_b, sc_y)) * 223);",
  "            }",
  "        }",
  "    }",
  "}",
  "",
  "impl Sc_Top<word> {}",
  "",
  "impl<f, g> Sc_Top<(f, g)> where f: Sc_Top, g: Sc_Top {}",
  "",
  "impl<f, g> Sc_Top<sum<f, g>> where f: Sc_Top, g: Sc_Top {}",
  "",
  "impl Sc_Top<Sc_T0> {}",
  "",
  "impl<a> Sc_Top<Sc_T1<a>> where a: Sc_Top {}",
  "",
  "impl<a> Sc_Top<Sc_T2<a>> where a: Sc_Top {}",
  "",
  "function sc_up<t>(sc_x: t) returns (word) where t: Sc_Sub {",
  "    return (Sc_Fold.sc_fold(sc_x) + 227);",
  "}",
  "",
  "function sc_top2<t>(sc_x: t, sc_y: t) returns (word) where t: Sc_Top {",
  "    return (Sc_Fold.sc_both(sc_x, sc_y) - 239);",
  "}",
  "",
  "function sc_val2<t>(sc_x: t, sc_y: t) returns (word) where t: Sc_Sub {",
  "    let sc_f = Sc_Fold.sc_both;",
  "    return (sc_f(sc_x, sc_y) ^ 251);",
  "}",
  "",
  "function sc_fun<t>(sc_x: t) returns (word) where t: Sc_Sub {",
  "    let sc_f = sc_up;",
  "    return (sc_f(sc_x) * 257);",
  "}",
  "",
  "function sc_mixt<t, u>(sc_x: t, sc_y: u) returns (word) where t: Sc_Top, u: Sc_Fold {",
  "    return (Sc_Sub.sc_mix(sc_x, sc_y) ^ 269);",
  "}",
  "",
  "function sc_mixv<t, u>(sc_x: t, sc_y: u) returns (word) where t: Sc_Sub, u: Sc_Fold {",
  "    let sc_f = Sc_Sub.sc_mix;",
  "    return (sc_f(sc_x, sc_y) - 271);",
  "}",
  "",
  "function sc_u0(sc_x: word) returns (Sc_T0) {",
  "    let sc_k: word = ((sc_x + 1) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T0.Sc_T0_1(sc_x);",
  "    }",
  "    if (sc_k == 1) {",
  "        return Sc_T0.Sc_T0_2((sc_x + 3), sc_x);",
  "    }",
  "    return Sc_T0.Sc_T0_0;",
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
  "function sc_u3(sc_x: word) returns (Sc_T0) {",
  "    let sc_k: word = ((sc_x + 2) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T0.Sc_T0_2(sc_x, (sc_x + 1));",
  "    }",
  "    if (sc_k == 1) {",
  "        return Sc_T0.Sc_T0_1((sc_x * 5));",
  "    }",
  "    return .Sc_T0_0;",
  "}",
  "",
  "function sc_v3(sc_x: word) returns (word) {",
  "    return (sc_x + 5);",
  "}",
  "",
  "function sc_w3(sc_x: word) returns ((word, word)) {",
  "    let sc_k: word = ((sc_x + 1) & 3);",
  "    if (sc_k == 0) {",
  "        return (sc_x, (sc_x * 3));",
  "    }",
  "    return ((sc_x ^ 1), sc_x);",
  "}",
  "",
  "function sc_u4(sc_x: word) returns ((word, Sc_T1<word>)) {",
  "    let sc_k: word = ((sc_x + 3) & 3);",
  "    if (sc_k == 0) {",
  "        return (sc_x, Sc_T1(sc_x, (sc_x + 4)));",
  "    }",
  "    if (sc_k == 1) {",
  "        return ((sc_x * 7), Sc_T1.Sc_T1_1);",
  "    }",
  "    return (sc_x, Sc_T1.Sc_T1_2(Sc_T0.Sc_T0_1(sc_x)));",
  "}",
  "",
  "function sc_v4(sc_x: word) returns (sum<word, word>) {",
  "    let sc_k: word = ((sc_x + 0) & 3);",
  "    if (sc_k == 0) {",
  "        return inl(sc_x);",
  "    }",
  "    return inr((sc_x + 2));",
  "}",
  "",
  "function sc_w4(sc_x: word) returns (Sc_T2<Sc_T0>) {",
  "    let sc_k: word = ((sc_x + 1) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T2.Sc_T2_0((Sc_T0.Sc_T0_0, Sc_T0.Sc_T0_1(sc_x)));",
  "    }",
  "    return Sc_T2.Sc_T2_1(Sc_T1.Sc_T1_2(Sc_T0.Sc_T0_0), Sc_T0.Sc_T0_2(sc_x, (sc_x * 11)));",
  "}",
  "",
  "function sc_u5(sc_x: word) returns (Sc_T2<(word, word)>) {",
  "    let sc_k: word = ((sc_x + 0) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T2.Sc_T2_0(((sc_x, sc_x), ((sc_x + 1), sc_x)));",
  "    }",
  "    return Sc_T2.Sc_T2_1(Sc_T1((sc_x, sc_x), (sc_x + 2)), (sc_x, (sc_x * 3)));",
  "}",
  "",
  "function sc_v5(sc_x: word) returns (Sc_T0) {",
  "    let sc_k: word = ((sc_x + 0) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T0.Sc_T0_1(sc_x);",
  "    }",
  "    return Sc_T0.Sc_T0_0;",
  "}",
  "",
  "function sc_w5(sc_x: word) returns (word) {",
  "    return (sc_x ^ 13);",
  "}",
  "",
  "contract SynthesizedTraitHierarchies {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_r0: word = sc_top2(sc_u0(sc_input), sc_u0((sc_input + 4)));",
  "        let sc_r1: word = sc_fun(sc_u1(sc_input));",
  "        let sc_r2: word = sc_val2(sc_u2(sc_input), sc_u2((sc_input + 2)));",
  "        let sc_r3: word = (Sc_Sub.sc_mix(sc_u3(sc_input), sc_v3(sc_input)) + Sc_Sub.sc_mix(sc_u3(sc_input), sc_w3(sc_input)));",
  "        let sc_r4: word = (sc_mixt(sc_u4(sc_input), sc_v4(sc_input)) + sc_mixt(sc_u4(sc_input), sc_w4(sc_input)));",
  "        let sc_r5: word = (sc_mixv(sc_u5(sc_input), sc_v5(sc_input)) + sc_mixv(sc_u5(sc_input), sc_w5(sc_input)));",
  "        return uint256((((((sc_r0 + (sc_r1 * 3)) + (sc_r2 * 5)) + (sc_r3 * 7)) + (sc_r4 * 9)) + (sc_r5 * 11)));",
  "    }",
  "}", ""]

/-- The shadowing form renames the subclass method's declarations and calls,
not the helpers `sc_mixt` and `sc_mixv`. -/
private def shadowSource : String :=
  (fixtureSource.replace "sc_mix<" "sc_fold<").replace "Sc_Sub.sc_mix" "Sc_Sub.sc_fold"

private def fixtureShapes : List (String × List String) := [
  ("instances", ["generic:binary", "generic:mix", "generic:unary", "plain:binary", "plain:mix", "plain:unary",
    "sum:binary", "sum:unary", "tuple:mix", "tuple:unary", "word:binary", "word:mix", "word:unary"]),
  ("calls", ["binary:top", "binary:value", "mix:direct", "mix:top", "mix:value", "unary:function"]),
  ("depths", ["1", "2", "3"]),
  ("arguments", ["plain", "sum", "tuple", "word"]),
  ("parameters", ["generic", "plain", "sum", "tuple", "word"]),
  ("forms", ["enum:columns", "enum:nested"]),
  ("subclass", ["mix"])]

private def fixtureChecks : IO Unit := do
  ensure fixturePlan.admitted "the fixture plan is not admitted"
  let some checked := Hierarchies.CheckedPlan.ofPlan? fixturePlan | throw (IO.userError "the fixture failed the checker")
  ensure ((Hierarchies.emit fixturePlan).source == fixtureSource) "the fixture source changed"
  for (value, expected) in fixtureResults do
    ensure ((← run (checked.program (Word.ofNatModulo value))) == expected) s!"fixture input {value}: Core result"
    ensure (interpret fixturePlan value == some expected) s!"fixture input {value}: interpreter result"
  ensure (fixturePlan.shapes == fixtureShapes) "the fixture shapes changed"
  let shadow : Plan := {fixturePlan with sub := .shadow}
  let some shadowChecked := Hierarchies.CheckedPlan.ofPlan? shadow | throw (IO.userError "the shadowing fixture failed")
  ensure ((Hierarchies.emit shadow).source == shadowSource) "the shadowing source is not the renamed fixture source"
  ensure (shadowSource != fixtureSource) "the shadowing source renamed nothing"
  for (value, expected) in fixtureResults do
    ensure ((← run (shadowChecked.program (Word.ofNatModulo value))) == expected) s!"shadowing input {value}"

/-- Admission refuses what the compiler or the reference cannot take. -/
private def admissionChecks : IO Unit := do
  let refused := fun (label : String) (plan : Plan) => ensure (!plan.admitted) s!"admitted {label}"
  let uses := fixtureUses
  let withUse := fun (index : Nat) (use : Use) => ({fixturePlan with uses := uses.set index use} : Plan)
  let withSub := fun (index : Nat) (impl : SubImpl) =>
    ({fixturePlan with subImpls := fixtureSubImpls.set index impl} : Plan)
  let useAt := fun (index : Nat) => uses.getD index default
  let subAt := fun (index : Nat) => fixtureSubImpls.getD index default
  let baseUses := uses.take 3
  let markerImpls := fixtureSubImpls.map fun (impl : SubImpl) => ({impl with steps := []} : SubImpl)
  let markerHelpers := fixtureHelpers.filter fun (helper : Helper) => helper.method != .mix
  let marker : Plan :=
    {fixturePlan with sub := .marker, uses := baseUses, subImpls := markerImpls, helpers := markerHelpers}
  ensure marker.admitted "the marker fixture without its mix uses is not admitted"
  refused "a mix use with a marker" {marker with uses := uses}
  refused "a marker with steps" {marker with subImpls := fixtureSubImpls}
  let noUnary := fixtureImpls.map fun (impl : Impl) => ({impl with unary := []} : Impl)
  refused "a subclass method without the unary base method" {fixturePlan with unary := false, impls := noUnary}
  refused "a subclass impl over no base impl" {fixturePlan with impls := fixtureImpls.eraseIdx 5}
  refused "a chain impl over no subclass impl" {marker with subImpls := (marker.subImpls).eraseIdx 3}
  refused "subclass impls out of order" {fixturePlan with subImpls := [subAt 1, subAt 0] ++ fixtureSubImpls.drop 2}
  refused "chain impls out of order" {fixturePlan with tops := [.tuple, .word] ++ fixtureHeads.drop 2}
  refused "a missing subclass arm" (withSub 3 {subAt 3 with steps := (subAt 3).steps.take 2})
  refused "a fold operator on a one-operand subclass arm" (withSub 2 {subAt 2 with steps := [step .mul .sub 167, step .add .mul 173]})
  refused "an operator on a nullary subclass arm"
    (withSub 3 {subAt 3 with steps := [step .add .xor 179, step .add .add 181, step .mul .xor 191]})
  refused "a top use without the chain's impls" {fixturePlan with tops := []}
  refused "a subclass bound without the subclass impl"
    {fixturePlan with subImpls := fixtureSubImpls.eraseIdx 4, tops := fixtureHeads.eraseIdx 4}
  refused "a mix use with one argument" (withUse 3 {useAt 3 with arguments := (useAt 3).arguments.take 1})
  refused "a mix use with equal arguments"
    (withUse 3 {useAt 3 with arguments := [(useAt 3).arguments.headD default, (useAt 3).arguments.headD default]})
  refused "a shifted mix use" (withUse 3 {useAt 3 with shift := 1})
  refused "a mix use through sub" (withUse 3 {useAt 3 with call := .sub})
  refused "a mix use through function" (withUse 3 {useAt 3 with call := .function})
  refused "arguments on a base method" (withUse 1 {useAt 1 with arguments := (useAt 3).arguments})
  refused "an argument four levels deep" (withUse 3 {useAt 3 with arguments := [(useAt 3).arguments.headD default,
    {type := .tuple (.tuple (.tuple (.tuple .word .word) .word) .word) .word,
     builder := builder 0 [.tuple (.tuple (.tuple (.tuple input input) input) input) input]}]})
  refused "a binary use without a shift" (withUse 0 {useAt 0 with shift := 0})
  refused "a helper no use needs" {fixturePlan with helpers := fixtureHelpers ++ [fixtureHelpers.headD default]}
  refused "a function use without its sub helper" {fixturePlan with helpers := fixtureHelpers.drop 1}
  refused "a generic declaration used as plain" (withUse 0 {useAt 0 with type := .enum 1})
  refused "seven uses" {fixturePlan with uses := uses ++ [useAt 5]}

private def shapeValues : List (String × List String) := [
  ("instances", ["generic:binary", "generic:mix", "generic:unary", "plain:binary", "plain:mix", "plain:unary",
    "sum:binary", "sum:mix", "sum:unary", "tuple:binary", "tuple:mix", "tuple:unary", "word:binary", "word:mix",
    "word:unary"]),
  ("calls", ["binary:direct", "binary:function", "binary:sub", "binary:top", "binary:value", "mix:direct", "mix:top",
    "mix:value", "unary:direct", "unary:function", "unary:sub", "unary:top", "unary:value"]),
  ("depths", ["0", "1", "2", "3"]),
  ("arguments", ["generic", "plain", "sum", "tuple", "word"]),
  ("parameters", ["generic", "plain", "sum", "tuple", "word"]),
  ("forms", ["enum:columns", "enum:nested", "tuple:columns", "tuple:nested"]),
  ("subclass", ["marker", "mix", "shadow"])]

/-- Generation is deterministic, draws every shape within 300 seeds,
replays exactly and drops uses to fit a smaller budget. -/
private def generationChecks : IO Unit := do
  let mut seen : List (String × String) := []
  for seed in List.range 300 do
    let plan := generate (UInt64.ofNat (seed + 1))
    ensure (Hierarchies.planJson plan == Hierarchies.planJson (generate (UInt64.ofNat (seed + 1))))
      "generation is not deterministic"
    for (dimension, values) in plan.shapes do
      for value in values do
        unless seen.contains (dimension, value) do seen := (dimension, value) :: seen
  for (dimension, values) in shapeValues do
    for value in values do
      ensure (seen.contains (dimension, value)) s!"300 seeds never drew {dimension}:{value}"
  let corpus := Hierarchies.generateCases (Seed.ofNat 1) Hierarchies.defaultNodes 64 64 fuel
  let all ← cases corpus
  ensure (all.size = 64) "generation from seed 1 did not return 64 cases"
  for case in all do
    ensure ((← get (Hierarchies.replayCase case fuel)) == case) "a generated case failed exact replay"
  let seeded ← cases (Hierarchies.generateCases (Seed.ofNat 7) Hierarchies.defaultNodes 12 4 fuel .seeded .nonIdentity)
  ensure (seeded.size = 12) "seeded generation did not return twelve inputs"
  for case in seeded do
    ensure ((← get (Hierarchies.replayCase case fuel)) == case) "a seeded case failed exact replay"
  let mut dropped := false
  for seed in List.range 40 do
    if let .ok small := Hierarchies.generatedPlan (Seed.ofNat (seed + 1)) Hierarchies.minimumNodes then
      ensure (small.plan.nodes ≤ Hierarchies.minimumNodes) "a fitted plan exceeds its budget"
      if small.plan.uses.length < (generate (UInt64.ofNat (seed + 1))).uses.length then dropped := true
  ensure dropped "a 256-node budget never dropped a use"

private def implCount (plan : Plan) : Nat := plan.impls.length + plan.subImpls.length + plan.tops.length

/-- Tampering is refused; reductions are admitted, strictly smaller and
replay, and a shrink response stays below its byte cap. -/
private def tamperChecks : IO Unit := do
  let all ← cases (Hierarchies.generateCases (Seed.ofNat 1) Hierarchies.defaultNodes 8 4 fuel)
  let case := all[0]!
  let plan ← get (case.getObjVal? "hierarchyPlan")
  ensure (Hierarchies.replayCase (case.setObjVal! "source" (toJson "contract C {}")) fuel matches .error _)
    "a changed source replayed"
  ensure (Hierarchies.replayCase (case.setObjVal! "program" (Solcore.Core.Wire.encodeProgram
      {resultType := .word, dataDefinitions := [], body := .word Word.zero})) fuel matches .error _)
    "a changed reference replayed"
  ensure (errorOf (Hierarchies.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "generatorVersion" (toJson "core-trait-hierarchies-v0"))) fuel) == some "generatorVersion changed")
    "a changed generator version replayed"
  ensure (Hierarchies.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "hierarchyShapes" (Json.mkObj []))) fuel matches .error _) "changed hierarchy shapes replayed"
  ensure (Hierarchies.replayCase (case.setObjVal! "hierarchyPlan" (plan.setObjVal! "uses" (.arr #[]))) fuel
    matches .error _) "a plan without uses replayed"
  ensure (Hierarchies.replayCase (case.setObjVal! "hierarchyPlan" (plan.setObjVal! "methods" (toJson ["binary", "unary"])))
    fuel matches .error _) "a noncanonical method list replayed"
  ensure (Hierarchies.replayCase (case.setObjVal! "hierarchyPlan" (plan.setObjVal! "subclass" (toJson "shadow")))
    fuel matches .error _) "a changed subclass form replayed"
  ensure (Hierarchies.replayCase (case.setObjVal! "hierarchyPlan" (plan.setObjVal! "tops" (.arr #[]))) fuel
    matches .error _) "a plan without the chain's impls replayed"
  let origin ← get ((← provenance case).getObjVal? "origin")
  ensure (Hierarchies.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "origin" (origin.setObjVal! "seed" (toJson "2")))) fuel matches .error _) "a changed seed replayed"
  let shrunk ← get (Hierarchies.shrinkCases case 4096 fuel)
  let reduced ← cases shrunk
  ensure (!reduced.isEmpty) "no reduction of the first generated case"
  ensure (shrunk.compress.utf8ByteSize ≤ 2 * 1024 * 1024) "a shrink response exceeds 2 MiB"
  for candidate in reduced do
    ensure ((← get (Hierarchies.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
  let parent ← get (Hierarchies.caseProgram case)
  for reduction in Hierarchies.reductions parent do
    ensure (decide (reduction.candidate.measure.StrictlySmaller parent.measure)) "a reduction is not strictly smaller"
  let mut kinds : List String := []
  for seed in List.range 40 do
    if let .ok checked := Hierarchies.generatedPlan (Seed.ofNat (seed + 1)) Hierarchies.defaultNodes then
      let source : Hierarchies.CheckedInput := ⟨checked, Word.ofNatModulo 5⟩
      for reduction in Hierarchies.reductions source do
        let next := reduction.candidate.plan.plan
        let previous := checked.plan
        let kind := if next.uses.length < previous.uses.length then "use"
          else if next.decls.length < previous.decls.length then "declaration"
          else if (next.unary, next.binary) != (previous.unary, previous.binary) then "method"
          else if next.sub != previous.sub then "subclass"
          else if implCount next < implCount previous then "impl"
          else if (next.uses.map (·.type)) != (previous.uses.map (·.type)) then "nesting"
          else if (next.uses.map (·.call)) != (previous.uses.map (·.call)) then "call"
          else if (next.uses.map fun use => use.arguments.map (·.type)) !=
              (previous.uses.map fun use => use.arguments.map (·.type)) then "argument"
          else if reduction.candidate.input != source.input then "input" else "builder"
        unless kinds.contains kind do kinds := kind :: kinds
  for kind in ["use", "declaration", "method", "subclass", "impl", "nesting", "call", "argument", "input", "builder"] do
    ensure (kinds.contains kind) s!"no {kind} reduction in 40 plans"
  let reducedOrigin ← get ((← provenance reduced[0]!).getObjVal? "origin")
  ensure (Hierarchies.replayCase (reduced[0]!.setObjVal! "provenance" ((← provenance reduced[0]!).setObjVal!
      "origin" (reducedOrigin.setObjVal! "parentPlan" (← get (reduced[0]!.getObjVal? "hierarchyPlan"))))) fuel
      matches .error _)
    "a reduction claiming itself as its parent replayed"

def testSourceHierarchyCases : IO Unit := do
  fixtureChecks
  admissionChecks
  modelChecks
  generationChecks
  tamperChecks

end Tests.SourceHierarchyCases
end

section
-- leanmerge: from Solcore.Test.SourceMethodsCases
/-! Several-methods cases: generation is deterministic and validates every
prescribed outcome against original Core; generated, imported and reduced
cases replay exactly; reductions remove transactions first, then methods no
transaction calls, and keep the G0 revision and swarm mask; and the case
boundary rejects method lists outside two to four, invalid or repeated names,
more than two arguments, colliding or missing selectors, calls of undeclared
methods or with other arguments, and any calldata, selector or std outcome that
differs from the transaction. -/
set_option autoImplicit false

namespace Tests.SourceMethodsCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Stateful.MethodsExecution (Method Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def fuel : Nat := 1000000

private def cases (corpus : Json) : IO (Array Json) := get (corpus.getObjValAs? (Array Json) "cases")

private def w (value : Nat) : Word := Word.ofNatModulo value

def testSourceMethodsCases : IO Unit := do
  let corpus := Methods.generateCases (Seed.ofNat 1) 448 4 64 fuel .v3 8
  ensure (corpus == Methods.generateCases (Seed.ofNat 1) 448 4 64 fuel .v3 8) "generation is nondeterministic"
  ensure ((← get (corpus.getObjValAs? String "status")) == "complete") "generation did not complete"
  let generated ← cases corpus
  let mut outcomes : List String := []
  let mut counts : List Nat := []
  for saved in generated do
    ensure ((← get (Methods.replayCase saved fuel)) == saved) "a generated case failed exact replay"
    let scenario ← get (Methods.caseProgram saved)
    ensure (scenario.transactions.length == 8) "a generated case lost its requested length"
    counts := (counts ++ [scenario.methods.length]).eraseDups
    outcomes := (outcomes ++ scenario.transactions.map fun tx =>
      (Methods.prescribed scenario tx).map Methods.selectorText |>.getD "accepted").eraseDups
    let contract ← get (saved.getObjVal? "contract")
    ensure ((contract.getObjValAs? String "selectorOrder").toOption == some (Methods.selectorOrder scenario.methods))
      "a case records another selector order"
  ensure (["0x4924aef0", "accepted"].all outcomes.contains) "generation misses an outcome"
  ensure (counts.length ≥ 2) "generation draws one method count only"
  let some first := generated[0]? | throw (IO.userError "no generated case")
  let provenance ← get (first.getObjVal? "provenance")
  let reduced ← cases (← get (Methods.shrinkCases first 12 fuel))
  let some removal := reduced[0]? | throw (IO.userError "a generated case has no reduction")
  let original ← get (first.getObjValAs? (List Json) "transactions")
  ensure ((← get (removal.getObjValAs? (List Json) "transactions")) == original.dropLast)
    "the first reduction does not remove the last transaction"
  for candidate in reduced do
    ensure ((← get (Methods.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
    let candidateProvenance ← get (candidate.getObjVal? "provenance")
    ensure ((candidateProvenance.getObjVal? "swarmMask").toOption == (provenance.getObjVal? "swarmMask").toOption &&
      (candidateProvenance.getObjVal? "generatorVersion").toOption == (provenance.getObjVal? "generatorVersion").toOption)
      "a reduction lost the parent's revision or swarm mask"
  -- An imported contract of four methods with the step `x ↦ x + 1`, two of
  -- them never called, through the case boundary; removing an uncalled method
  -- is a reduction.
  let some step := Aggregates.CheckedDAG.ofParts? [Aggregate.template 0 (.word (w 1))] (.apply (.var 1) (.var 0))
    | throw (IO.userError "the constant step failed admission")
  let methods : List Method := [⟨"m_00000001", 1⟩, ⟨"m_00000002", 0⟩, ⟨"m_00000003", 2⟩, ⟨"m_00000004", 1⟩]
  let missing := 0x43c9d5b5
  let some plan := ContractMethods.CheckedPlan.ofParts? (methods.map (·.shape)) (List.replicate 4 step)
    | throw (IO.userError "an imported plan failed admission")
  let transactions : List Transaction := [⟨"tx-0", some 2, [w 2, w 4]⟩, ⟨"tx-1", none, [w 1]⟩, ⟨"tx-2", some 0, [w 7]⟩]
  let imported ← get (Methods.checkedScenario plan methods missing transactions)
  let importedCase ← get (Methods.emitCase imported (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((← get (Methods.replayCase importedCase fuel)) == importedCase) "an imported case failed exact replay"
  let rows ← get (importedCase.getObjValAs? (Array Json) "transactions")
  ensure ((rows.map fun row => (row.getObjVal? "stdRejection").toOption) ==
      #[some Json.null, some (toJson "0x4924aef0"), some Json.null]) "an imported case records other std outcomes"
  ensure ((rows.map fun row => (row.getObjVal? "selector").toOption) ==
      #[some (toJson "0x336e1e08"), some (toJson "0x43c9d5b5"), some (toJson "0x935853e4")])
    "an imported case records other selectors"
  let importedReductions ← cases (← get (Methods.shrinkCases importedCase 8 fuel))
  ensure (importedReductions.any fun candidate =>
      ((candidate.getObjVal? "contract").toOption.bind (·.getObjValAs? (List Json) "methods" |>.toOption)).map (·.length) ==
        some 3) "no reduction removes the uncalled methods"
  -- Method lists outside two to four, invalid or repeated names, three
  -- arguments, colliding or missing selectors, undeclared methods and wrong
  -- argument counts are rejected.
  let check := fun (methods : List Method) (missing : Nat) (transactions : List Transaction) =>
    match ContractMethods.CheckedPlan.ofParts? (methods.map (·.shape)) (methods.map fun _ => step) with
    | some plan => Methods.checkedScenario plan methods missing transactions
    | none => .error "plan failed admission"
  rejected (check [⟨"m_00000001", 1⟩] missing [⟨"tx-0", some 0, [w 2]⟩]) "one method was admitted"
  rejected (check (methods ++ [⟨"m_00000005", 1⟩]) missing [⟨"tx-0", some 0, [w 2]⟩]) "five methods were admitted"
  rejected (check [⟨"m_0000000G", 1⟩, ⟨"m_00000002", 0⟩] missing [⟨"tx-0", some 0, [w 2]⟩]) "an invalid name was admitted"
  rejected (check [⟨"m_00000001", 1⟩, ⟨"m_00000001", 0⟩] missing [⟨"tx-0", some 0, [w 2]⟩]) "a repeated name was admitted"
  rejected (check [⟨"m_00000001", 3⟩, ⟨"m_00000002", 0⟩] missing [⟨"tx-0", some 1, []⟩]) "three arguments were admitted"
  rejected (check methods 0x935853e4 [⟨"tx-0", some 0, [w 2]⟩]) "a missing selector of a method was admitted"
  rejected (check methods missing [⟨"tx-0", some 4, [w 2]⟩]) "an undeclared method was admitted"
  rejected (check methods missing [⟨"tx-0", some 1, [w 2]⟩]) "a call with another argument count was admitted"
  rejected (check methods missing [⟨"tx-0", none, []⟩]) "a missing selector without its Word was admitted"
  let row := rows[0]!
  for (key, value) in [("calldata", toJson "0x336e1e08"), ("selector", toJson "0x935853e4"),
      ("stdRejection", toJson "0x4924aef0"), ("method", toJson "m_0000000f"), ("value", toJson "1")] do
    rejected (Methods.decodeTransactions methods missing (toJson [row.setObjVal! key value]))
      s!"a transaction with a changed {key} was admitted"

end Tests.SourceMethodsCases
end

section
-- leanmerge: from Solcore.Test.SourceMethodsCorpus
/-! The fixed several-methods corpus checks actual original Core histories
against expectations computed without the std-modeling wrapper: the byte-level
dispatch picks the method or the rejection, the method's step runs alone in
Core and the protocol's slot arithmetic is written out. Coverage describes the
checked steps' AST, the inputs, the method counts, the positions transactions
call, the selector orders, the arities, the prescribed std outcomes and the
completions. Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceMethodsCorpus
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
  ("generatorVersion", generatorVersion), ("profileVersion", Methods.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.ContractMethods.version),
  ("templateVersion", Methods.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", Methods.emitterVersion), ("wrapperVersion", Methods.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

private def outcomeNames : List String := ["0x4924aef0", "accepted"]
private def orderNames : List String := ["ascending", "descending", "mixed"]

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := Methods.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let (plan, methods, missing) ← Methods.checkedPlan (← entry.getObjVal? "methodsPlan")
  let scenario ← Methods.checkedScenario plan methods missing
    (← Methods.decodeTransactions methods missing (← entry.getObjVal? "transactions"))
  Methods.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "methods-generated" then return []
  let stepOrigins ← origin.getObjValAs? (List Json) "stepOrigins"
  let helpers ← stepOrigins.mapM fun stepOrigin => stepOrigin.getObjValAs? (List Json) "helpers"
  helpers.flatten.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-methods" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected several-methods manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("several-methods manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words Methods.boundaryInputs))
    "several-methods corpus must require all six boundary inputs"
  require ((← manifest.getObjValAs? (List Nat) "requiredMethodCounts") == [2, 3, 4] &&
    (← manifest.getObjValAs? (List Nat) "requiredMethodPositions") == [0, 1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredArities") == [0, 1, 2])
    "several-methods corpus must require two to four methods, every position and every arity"
  require ((← strings manifest "requiredSelectorOrders") == orderNames)
    "several-methods corpus must require ascending, descending and mixed selectors"
  require ((← strings manifest "requiredRejections") == outcomeNames)
    "several-methods corpus must require the missing-selector rejection and acceptance"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "several-methods corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "several-methods corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "several-methods corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "several-methods corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "several-methods corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut counts : List Nat := []
  let mut positions : List Nat := []
  let mut orders : List String := []
  let mut arities : List Nat := []
  let mut rejections : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate several-methods corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← Methods.replayCase saved fuel) == saved) ("several-methods corpus entry did not replay: " ++ identifier)
    let scenario ← Methods.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "methodsPlan") == (← entry.getObjVal? "methodsPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported several-methods entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("several-methods corpus features changed: " ++ identifier)
    let history := Methods.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("several-methods corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("several-methods expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the expectation without the std wrapper: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.flatMap fun tx => words tx.inputs).eraseDups
    counts := (counts ++ [scenario.methods.length]).eraseDups
    positions := (positions ++ scenario.transactions.filterMap (·.target)).eraseDups
    orders := (orders ++ [Methods.selectorOrder scenario.methods]).eraseDups
    arities := (arities ++ scenario.methods.map (·.arity)).eraseDups
    rejections := (rejections ++ scenario.transactions.map fun tx =>
      (Methods.prescribed scenario tx).map Methods.selectorText |>.getD "accepted").eraseDups
    helperCounts := (helperCounts ++ scenario.plan.steps.map (·.helpers.length)).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "several-methods corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "several-methods corpus misses a boundary input"
  require ([2, 3, 4].all counts.contains && [0, 1, 2, 3].all positions.contains && [0, 1, 2].all arities.contains)
    "several-methods corpus misses a method count, called position or arity"
  require (orderNames.all orders.contains) "several-methods corpus misses a selector order"
  require (outcomeNames.all rejections.contains) "several-methods corpus misses a std outcome"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "several-methods corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "several-methods corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "several-methods corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-methods"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("methodCounts", toJson counts), ("orders", toJson orders),
    ("rejections", toJson rejections), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid several-methods corpus unexpectedly passed")

def testSourceMethodsCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-methods-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first several-methods case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated several-methods case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  -- An output, a slot, a missing row and a status are all checked.
  let changedOutput := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 1 (storage[1]!.setObjVal! "value" (toJson "7"))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped)))))))
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "method" Json.null))))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredMethodCounts", toJson [2, 3]), ("requiredMethodPositions", toJson [0, 1, 2]),
      ("requiredSelectorOrders", toJson (["mixed"] : List String)),
      ("requiredRejections", toJson (["accepted"] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceMethodsCorpus
end

section
-- leanmerge: from Solcore.Test.SourceMethodsGolden
/-! Golden dispatch cases for the several-methods profile. The expected outcome
of every case is written out from the pinned std's `dispatch.sol` and the
compiler's `prepare.rs`, not computed by either model: a method runs exactly
when the calldata selector is its own; calldata shorter than four bytes or
with another selector reverts with `0x4924aef0`; a method whose arguments are
missing reverts with `0x08638556`. The steps add a known constant, so each
method's slots and result follow by hand: with input `x` and constant `c` from
empty storage, slot zero and the method's slot hold `x + c`, slot one holds 1
and the result is `2(x + c) + 1`, which an odd input reverts. Contracts declare
the same methods with ascending, descending and mixed selectors, and one
sequence checks the shared slots across methods. Both the Core wrapper and the
byte-level `stdDispatch` must give each outcome. -/
set_option autoImplicit false

namespace Tests.SourceMethodsGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.MethodsExecution (Method Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The byte model's dispatch decision: the method position, or the rejection. -/
private def dispatches (shapes : List ContractMethods.Shape) (input : ByteArray) (expected : Except Nat Nat) : Bool :=
  match MethodsExecution.stdDispatch shapes input, expected with
  | .ok actual, .ok wanted => actual == wanted
  | .error actual, .error wanted => actual == wanted
  | _, _ => false

/-- The four methods with their selectors, as `cast sig` prints them, and
their constants. -/
private def P : Method := ⟨"m_00000001", 1⟩
private def Q : Method := ⟨"m_00000002", 0⟩
private def R : Method := ⟨"m_00000003", 2⟩
private def S : Method := ⟨"m_00000004", 1⟩
private def selectors : List (Method × Nat) :=
  [(P, 0x935853e4), (Q, 0xf3cfdf58), (R, 0x336e1e08), (S, 0x06d154aa)]
private def constant (method : Method) : Nat :=
  if method == P then 1 else if method == Q then 2 else if method == R then 3 else 4
/-- The missing selector, of `m_0000000f(uint256)`. -/
private def missing : Nat := 0x43c9d5b5

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
private def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- Contracts by name and expected selector order. -/
private def contracts : List (String × List Method × String) := [
  ("two-ascending", [S, P], "ascending"), ("two-descending", [Q, R], "descending"),
  ("three-ascending", [R, P, Q], "ascending"), ("three-descending", [Q, P, S], "descending"),
  ("three-mixed", [P, S, Q], "mixed"), ("four-ascending", [S, R, P, Q], "ascending"),
  ("four-descending", [Q, P, R, S], "descending"), ("four-mixed", [P, Q, R, S], "mixed")]

private def slots (values : List Nat) : Json :=
  toJson ((List.range 6).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def wordText (value : Nat) : String := encodeBytesText (encodeWordBytesBE (w value))

/-- The expected row: status, output Word and slots zero to five. -/
private structure Expected where
  status : String
  output : Nat
  values : List Nat

private def noSelector : Expected := ⟨"reverted", StdDispatch.noSelectorError, []⟩
private def truncated : Expected := ⟨"reverted", StdDispatch.truncatedError, []⟩

/-- One call of method `position` with input sum `x` from empty storage. -/
private def fromEmpty (methods : List Method) (position x : Nat) : Expected :=
  let computed := x + constant (methods.getD position P)
  let result := 2 * computed + 1
  if x % 2 = 1 then ⟨"reverted", result, []⟩
  else ⟨"returned", result, (List.range 6).map fun slot =>
    if slot = 0 || slot = 2 + position then computed else if slot = 1 then 1 else 0⟩

private def selectorBytes (selector : Nat) : List UInt8 :=
  [(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

private def raw (selector : Nat) (words : List Nat) : ByteArray :=
  words.foldl (fun bytes value => bytes ++ encodeWordBytesBE (w value)) (ByteArray.mk (selectorBytes selector).toArray)

/-- The original Core contract run once from an empty world on raw calldata. -/
private def runRaw (contract : CheckedCoreContract) (input : ByteArray) (fuel : Nat) : IO Json := do
  let bindings := StorageExecution.fixtureBindings
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let world := StorageExecution.initialWorldForContract contract bindings
  let some ⟨resolved, installed⟩ := registry.resolve? world bindings.address
    | throw (IO.userError "contract does not resolve")
  if bounded : input.size < Solcore.Core.wordModulus then
    let invocation : TopLevelInvocation := {
      target := bindings.address, caller := bindings.caller, callValue := Word.zero,
      inputData := ⟨input, bounded⟩ }
    match TopLevelExecution.run resolved invocation installed fuel with
    | .completed terminal =>
        let storage := match terminal.finalWorld.account? bindings.address with
          | some account => MethodsExecution.storageJson account
          | none => Json.null
        let fields := match terminal.outcome with
          | .returned output => [("status", toJson "returned"), ("output", toJson (encodeBytesText output))]
          | .reverted output => [("status", toJson "reverted"), ("output", toJson (encodeBytesText output))]
          | .trapped _ => [("status", toJson "trapped")]
        return Json.mkObj (fields ++ [("committedStorage", storage)])
    | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "golden case exhausted fuel")
  else throw (IO.userError "golden input exceeds a Word")

private def check (name : String) (row : Json) (expected : Expected) : IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (wordText expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (slots expected.values))
    s!"{name}: original Core differs from the expected row {row.compress}"

def testSourceMethodsGolden : IO Unit := do
  let fuel := 1000000
  for (method, expected) in selectors do
    ensure (method.selector == expected) s!"{method.signature}: the Keccak selector differs from cast sig"
  ensure ((⟨"m_0000000f", 1⟩ : Method).selector == missing) "the missing selector differs from cast sig"
  for (name, methods, order) in contracts do
    let shapes := methods.map (·.shape)
    let some plan := ContractMethods.CheckedPlan.ofParts? shapes (← methods.mapM (step ∘ constant))
      | throw (IO.userError s!"{name}: the methods wrapper failed admission")
    ensure (Solcore.Synthesis.Source.Methods.selectorOrder methods == order) s!"{name}: selector order differs"
    for (method, position) in methods.zipIdx do
      -- Each method with an even and, if it has arguments, an odd input.
      let inputs : List (List Nat) := match method.arity with
        | 0 => [[]]
        | 1 => [[6], [7]]
        | _ => [[2, 4], [2, 5]]
      for values in inputs do
        let tx : Transaction := ⟨"tx-0", some position, values.map w⟩
        let input := MethodsExecution.inputBytes methods missing tx
        ensure (dispatches shapes input (.ok position)) s!"{name}: the byte model dispatches elsewhere"
        let history := MethodsExecution.observe plan methods missing [tx] StorageExecution.fixtureBindings fuel
        let some row := (← get (history.getObjValAs? (Array Json) "transactions"))[0]? | throw (IO.userError "no row")
        check s!"{name} {method.name} {values}" row (fromEmpty methods position (values.foldl (· + ·) 0))
      -- Missing arguments are truncated; an extra Word is ignored.
      if method.arity > 0 then
        let input := raw method.selector []
        ensure (dispatches shapes input (.error StdDispatch.truncatedError))
          s!"{name}: the byte model accepts missing arguments"
        check s!"{name} {method.name} without arguments" (← runRaw plan.contract input fuel) truncated
      let extra := raw method.selector ((List.replicate method.arity 2) ++ [9])
      ensure (dispatches shapes extra (.ok position)) s!"{name}: the byte model rejects an extra Word"
      check s!"{name} {method.name} with an extra Word" (← runRaw plan.contract extra fuel)
        (fromEmpty methods position (2 * method.arity))
    -- The missing selector, short calldata and the empty calldata reach the fallback.
    for input in [raw missing [1], ByteArray.mk ((selectorBytes (methods.getD 0 P).selector).take 3).toArray,
        ByteArray.empty] do
      ensure (dispatches shapes input (.error StdDispatch.noSelectorError))
        s!"{name}: the byte model dispatches a missing selector"
      check s!"{name} missing selector" (← runRaw plan.contract input fuel) noSelector
  -- One sequence on four mixed methods [P, Q, R, S] shares slots zero and one.
  let methods := [P, Q, R, S]
  let some plan := ContractMethods.CheckedPlan.ofParts? (methods.map (·.shape)) (← methods.mapM (step ∘ constant))
    | throw (IO.userError "the four-method wrapper failed admission")
  let transactions : List Transaction := [⟨"tx-0", some 2, [w 2, w 4]⟩, ⟨"tx-1", some 0, [w 10]⟩,
    ⟨"tx-2", none, [w 1]⟩, ⟨"tx-3", some 3, [w 3]⟩, ⟨"tx-4", some 1, []⟩]
  let history := MethodsExecution.observe plan methods missing transactions StorageExecution.fixtureBindings fuel
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  -- R(2, 4): 6 + 0 + 3 = 9, result 9 + 1 + 9. P(10): 10 + 9 + 1 = 20, result 20 + 2 + 20.
  -- The missing selector and S(3), odd with 3 + 20 + 4 = 27 and result 57, commit nothing.
  -- Q(): 0 + 20 + 2 = 22, result 22 + 3 + 22.
  let expected : List Expected := [⟨"returned", 19, [9, 1, 0, 0, 9, 0]⟩, ⟨"returned", 42, [20, 2, 20, 0, 9, 0]⟩,
    ⟨"reverted", StdDispatch.noSelectorError, [20, 2, 20, 0, 9, 0]⟩, ⟨"reverted", 57, [20, 2, 20, 0, 9, 0]⟩,
    ⟨"returned", 47, [22, 3, 20, 22, 9, 0]⟩]
  ensure (rows.size == expected.length) "the shared sequence lost a row"
  for (row, golden) in rows.toList.zip expected do
    check "shared sequence" row golden

end Tests.SourceMethodsGolden
end

section
-- leanmerge: from Solcore.Test.SourceTraitCases
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
  "pragma solcore;", "import * from std;",
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
end
