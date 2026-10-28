import Solcore.Synthesis.Core.TraitPlan
import Solcore.Synthesis.Source.EnumEmitter

/-! Source emission of a trait plan: the declarations, the trait `Sc_Fold`
with `sc_fold` and `sc_both`, its impls, the constrained generic helpers,
one builder function per use, and `run`, which calls every use. No emitter
proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Traits

open Solcore.Synthesis.Core.Traits
open Solcore.Synthesis.Source.Enums (enumName constructorName declLines leafText)

def emitterVersion : String := "solcore-source-traits-v1"
def wrapperVersion : String := "solcore-word-traits-contract-v1"

def contractName : String := "SynthesizedTraits"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedTraitsDeploy"]
def runtimePath : List String := ["SynthesizedTraitsDeploy", "SynthesizedTraits"]

def traitName : String := "Sc_Fold"

def methodText : Method → String
  | .unary => "sc_fold"
  | .binary => "sc_both"

def instText : Inst → String
  | .word => "word"
  | .tuple left right => "(" ++ instText left ++ ", " ++ instText right ++ ")"
  | .sum left right => "sum<" ++ instText left ++ ", " ++ instText right ++ ">"
  | .enum index => enumName index
  | .applied index argument => enumName index ++ "<" ++ instText argument ++ ">"

private def indented (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def arguments (texts : List String) : String :=
  if texts.isEmpty then "" else "(" ++ ", ".intercalate texts ++ ")"

private def instIndex : Inst → Nat
  | .enum index | .applied index _ => index
  | _ => 0

def valueText (decls : List Solcore.Synthesis.Core.Enums.Decl) : Nat → Inst → Val → String
  | 0, _, _ => "sc_x"
  | _ + 1, .word, .leaf op constant => leafText op constant
  | fuel + 1, .tuple left right, .tuple first second =>
      "(" ++ valueText decls fuel left first ++ ", " ++ valueText decls fuel right second ++ ")"
  | fuel + 1, .sum left _, .inl value => "inl(" ++ valueText decls fuel left value ++ ")"
  | fuel + 1, .sum _ right, .inr value => "inr(" ++ valueText decls fuel right value ++ ")"
  | fuel + 1, type, value => match constructorsOf decls type, value.constructor? with
      | some constructors, some (ctor, fields, form) =>
          let index := instIndex type
          let name := match form with
            | .qualified => enumName index ++ "." ++ constructorName decls index ctor
            | .dot => "." ++ constructorName decls index ctor
            | .sameName => enumName index
          name ++ arguments (((constructors.getD ctor []).zip fields).map fun (fieldType, field) =>
            valueText decls fuel fieldType field)
      | _, _ => "sc_x"

/-- An arm's result: the operands folded, then the operator and constant. -/
def stepText (step : Step) : List String → String
  | [] => toString step.constant
  | first :: rest =>
      let folded := rest.foldl (fun folded operand => "(" ++ folded ++ " " ++ step.combine.token ++ " " ++ operand ++ ")")
        first
      "(" ++ folded ++ " " ++ step.op.token ++ " " ++ toString step.constant ++ ")"

private def xNames : List String := ["sc_a", "sc_b"]
private def yNames : List String := ["sc_c", "sc_d"]

def unaryCall (name : String) : String := traitName ++ ".sc_fold(" ++ name ++ ")"

def binaryCall (first second : String) : String := traitName ++ ".sc_both(" ++ first ++ ", " ++ second ++ ")"

/-- Constructor `ctor` of an impl's type binding its fields: a tuple's
components, a sum's side, or a declaration's constructor, unqualified when it
is a same-name constructor. -/
def ctorPattern (decls : List Solcore.Synthesis.Core.Enums.Decl) (head : Head) (ctor fields : Nat)
    (names : List String) : String :=
  let bound := names.take fields
  match head with
  | .tuple => "(" ++ ", ".intercalate bound ++ ")"
  | .sum => (if ctor = 0 then "inl" else "inr") ++ arguments bound
  | .decl index =>
      let name := if ctor = 0 && (decls[index]?.map (·.sameName)).getD false then enumName index
        else enumName index ++ "." ++ constructorName decls index ctor
      name ++ arguments bound
  | .word => "_"

def implType (decls : List Solcore.Synthesis.Core.Enums.Decl) : Head → String
  | .word => "word"
  | .tuple => "(f, g)"
  | .sum => "sum<f, g>"
  | .decl index => enumName index ++ (if (decls[index]?.map (·.generic)).getD false then "<a>" else "")

def implHeader (decls : List Solcore.Synthesis.Core.Enums.Decl) : Head → String
  | .word => "impl " ++ traitName ++ "<word> {"
  | .tuple => "impl<f, g> " ++ traitName ++ "<(f, g)> where f: " ++ traitName ++ ", g: " ++ traitName ++ " {"
  | .sum => "impl<f, g> " ++ traitName ++ "<sum<f, g>> where f: " ++ traitName ++ ", g: " ++ traitName ++ " {"
  | .decl index =>
      if (decls[index]?.map (·.generic)).getD false then
        "impl<a> " ++ traitName ++ "<" ++ enumName index ++ "<a>> where a: " ++ traitName ++ " {"
      else "impl " ++ traitName ++ "<" ++ enumName index ++ "> {"

private def arm (indent : Nat) (header : String) (body : List String) : List String :=
  [indented indent ("case " ++ header ++ " {")] ++ body ++ [indented indent "}"]

private def defaultArm (indent : Nat) (value : Nat) : List String :=
  [indented indent "default {", indented (indent + 4) ("return " ++ toString value ++ ";"), indented indent "}"]

private def returned (indent : Nat) (text : String) : String := indented indent ("return " ++ text ++ ";")

def unaryBody (decls : List Solcore.Synthesis.Core.Enums.Decl) (head : Head) (counts : List Nat)
    (steps : List Step) : List String :=
  match head with
  | .word => [returned 8 (stepText (steps.headD default) ["sc_x"])]
  | _ =>
      let names := fun (ctor : Nat) => if head == .sum && ctor = 1 then ["sc_b"] else xNames
      [indented 8 "match (sc_x) {"] ++
        (counts.zip steps).zipIdx.flatMap (fun ((fields, step), ctor) =>
          arm 12 (ctorPattern decls head ctor fields (names ctor))
            [returned 16 (stepText step (((names ctor).take fields).map unaryCall))]) ++
        [indented 8 "}"]

def binaryBody (decls : List Solcore.Synthesis.Core.Enums.Decl) (head : Head) (counts : List Nat) (impl : Impl) :
    List String :=
  let steps := impl.binary
  let pairs := fun (fields : Nat) (left right : List String) =>
    ((left.take fields).zip (right.take fields)).map fun (first, second) => binaryCall first second
  match head, impl.form with
  | .word, _ => [returned 8 (stepText (steps.headD default) ["sc_x", "sc_y"])]
  | .sum, _ =>
      let mismatch := fun (index : Nat) => toString (impl.mismatch.getD index 0)
      [indented 8 "match (sc_x) {"] ++
        arm 12 "inl(sc_a)" ([indented 16 "match (sc_y) {"] ++
          arm 20 "inl(sc_c)" [returned 24 (stepText (steps.getD 0 default) [binaryCall "sc_a" "sc_c"])] ++
          arm 20 "inr(_)" [returned 24 (mismatch 0)] ++ [indented 16 "}"]) ++
        arm 12 "inr(sc_b)" ([indented 16 "match (sc_y) {"] ++
          arm 20 "inl(_)" [returned 24 (mismatch 1)] ++
          arm 20 "inr(sc_d)" [returned 24 (stepText (steps.getD 1 default) [binaryCall "sc_b" "sc_d"])] ++
          [indented 16 "}"]) ++
        [indented 8 "}"]
  | _, .nested =>
      [indented 8 "match (sc_x) {"] ++
        (counts.zip steps).zipIdx.flatMap (fun ((fields, step), ctor) =>
          arm 12 (ctorPattern decls head ctor fields xNames) ([indented 16 "match (sc_y) {"] ++
            arm 20 (ctorPattern decls head ctor fields yNames) [returned 24 (stepText step (pairs fields xNames yNames))] ++
            (if head == .tuple then [] else defaultArm 20 (impl.mismatch.getD 0 0)) ++ [indented 16 "}"])) ++
        [indented 8 "}"]
  | _, .columns =>
      [indented 8 "match (sc_x, sc_y) {"] ++
        (counts.zip steps).zipIdx.flatMap (fun ((fields, step), ctor) =>
          arm 12 ("(" ++ ctorPattern decls head ctor fields xNames ++ ", " ++ ctorPattern decls head ctor fields yNames ++ ")")
            [returned 16 (stepText step (pairs fields xNames yNames))]) ++
        (if head == .tuple then [] else defaultArm 12 (impl.mismatch.getD 0 0)) ++
        [indented 8 "}"]

def implLines (plan : Plan) (impl : Impl) : List String :=
  let decls := plan.decls
  let type := implType decls impl.head
  let unary := match operandCounts decls .unary impl.head with
    | some counts => if plan.unary then
        [indented 4 ("function sc_fold(sc_x: " ++ type ++ ") returns (word) {")] ++
          unaryBody decls impl.head counts impl.unary ++ [indented 4 "}"]
      else []
    | none => []
  let binary := match operandCounts decls .binary impl.head with
    | some counts => if plan.binary then
        [indented 4 ("function sc_both(sc_x: " ++ type ++ ", sc_y: " ++ type ++ ") returns (word) {")] ++
          binaryBody decls impl.head counts impl ++ [indented 4 "}"]
      else []
    | none => []
  [implHeader decls impl.head] ++ unary ++ binary ++ ["}", ""]

def traitLines (plan : Plan) : List String :=
  ["trait " ++ traitName ++ "<a> {"] ++
    (if plan.unary then [indented 4 "function sc_fold(sc_x: a) returns (word);"] else []) ++
    (if plan.binary then [indented 4 "function sc_both(sc_x: a, sc_y: a) returns (word);"] else []) ++
    ["}", ""]

def helperName (call : Call) (method : Method) : String :=
  match call, method with
  | .lifted, .unary => "sc_lift"
  | .lifted, .binary => "sc_lift2"
  | _, .unary => "sc_once"
  | _, .binary => "sc_twice"

def helperLines (helper : Helper) : List String :=
  let step : Step := {combine := .add, op := helper.op, constant := helper.constant}
  let call := match helper.call, helper.method with
    | .lifted, .unary => unaryCall "(sc_x, sc_x)"
    | .lifted, .binary => binaryCall "(sc_x, sc_y)" "(sc_y, sc_x)"
    | _, .unary => unaryCall "sc_x"
    | _, .binary => binaryCall "sc_x" "sc_y"
  let parameters := if helper.method == .unary then "sc_x: t" else "sc_x: t, sc_y: t"
  ["function " ++ helperName helper.call helper.method ++ "<t>(" ++ parameters ++ ") returns (word) where t: " ++
    traitName ++ " {", returned 4 (stepText step [call]), "}", ""]

def builderName (index : Nat) : String := "sc_u" ++ toString index

def builderLines (decls : List Solcore.Synthesis.Core.Enums.Decl) (index : Nat) (use : Use) : List String :=
  let header := "function " ++ builderName index ++ "(sc_x: word) returns (" ++ instText use.type ++ ") {"
  let value := fun (indent : Nat) (tree : Val) =>
    returned indent (valueText decls Solcore.Synthesis.Core.Enums.valueFuel use.type tree)
  match use.builder.trees with
  | [tree] => [header, value 4 tree, "}", ""]
  | trees =>
      let count := trees.length
      [header, indented 4 ("let sc_k: word = ((sc_x + " ++ toString use.builder.offset ++ ") & 3);")] ++
        (trees.take (count - 1)).zipIdx.flatMap (fun (tree, residue) =>
          [indented 4 ("if (sc_k == " ++ toString residue ++ ") {"), value 8 tree, indented 4 "}"]) ++
        [value 4 (trees.getLastD default), "}", ""]

def useText (index : Nat) (use : Use) : String :=
  let first := builderName index ++ "(sc_input)"
  let second := builderName index ++ "((sc_input + " ++ toString use.shift ++ "))"
  let callee := if use.call == .direct then traitName ++ "." ++ methodText use.method
    else helperName use.call use.method
  callee ++ "(" ++ (if use.method == .unary then first else first ++ ", " ++ second) ++ ")"

def runLines (plan : Plan) : List String :=
  let callLines := plan.uses.zipIdx.map fun (use, index) =>
    indented 8 ("let sc_r" ++ toString index ++ ": word = " ++ useText index use ++ ";")
  let combined := (List.range plan.uses.length).foldl (fun accumulated index =>
      if index = 0 then "sc_r0"
      else "(" ++ accumulated ++ " + (sc_r" ++ toString index ++ " * " ++ toString (2 * index + 1) ++ "))") ""
  ["contract " ++ contractName ++ " {",
   indented 4 ("function " ++ methodName ++ "(input: uint256) public returns (uint256) {"),
   indented 8 "let sc_input: word = Typedef.rep(input);"] ++ callLines ++
    [indented 8 ("return uint256(" ++ combined ++ ");"), indented 4 "}", "}"]

def emit (plan : Plan) : Solcore.Synthesis.Source.EmittedProgram :=
  let lines := ["import * from std;", "import * from std.dispatch;", ""] ++
    plan.decls.zipIdx.flatMap (fun (decl, index) => declLines plan.decls index decl) ++
    traitLines plan ++ plan.impls.flatMap (implLines plan) ++ plan.helpers.flatMap helperLines ++
    plan.uses.zipIdx.flatMap (fun (use, index) => builderLines plan.decls index use) ++
    runLines plan
  { source := "\n".intercalate lines ++ "\n", contractName, methodName, methodSignature, deployPath, runtimePath }

end Solcore.Synthesis.Source.Traits
