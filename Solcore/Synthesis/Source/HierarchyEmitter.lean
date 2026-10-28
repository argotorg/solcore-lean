import Solcore.Synthesis.Core.HierarchyPlan
import Solcore.Synthesis.Source.TraitEmitter

/-! Source emission of a trait hierarchy plan: the declarations, the base
trait `Sc_Fold` and its impls as `TraitEmitter` emits them, the subclass
`Sc_Sub` and the chain `Sc_Top` with their impls, the helpers, one builder
function per use's receiver and argument, and `run`, which calls every use.
No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Hierarchies

open Solcore.Synthesis.Core.Hierarchies
open Solcore.Synthesis.Core.Traits (Inst Step Head)
open Solcore.Synthesis.Source.Enums (enumName declLines)

abbrev Decl := Solcore.Synthesis.Core.Enums.Decl

def emitterVersion : String := "solcore-source-trait-hierarchies-v1"
def wrapperVersion : String := "solcore-word-trait-hierarchies-contract-v1"

def contractName : String := "SynthesizedTraitHierarchies"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedTraitHierarchiesDeploy"]
def runtimePath : List String := ["SynthesizedTraitHierarchiesDeploy", "SynthesizedTraitHierarchies"]

def baseName : String := Traits.traitName
def subName : String := "Sc_Sub"
def topName : String := "Sc_Top"

/-- The subclass method's name: `sc_fold`, the superclass's, when shadowing. -/
def mixName : Sub → String
  | .shadow => "sc_fold"
  | _ => "sc_mix"

private def indented (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def returned (indent : Nat) (text : String) : String := indented indent ("return " ++ text ++ ";")

private def arm (indent : Nat) (header : String) (body : List String) : List String :=
  [indented indent ("case " ++ header ++ " {")] ++ body ++ [indented indent "}"]

/-- An impl header of a trait at a head, constrained by the same trait. -/
def implHeader (decls : List Decl) (trait : String) : Head → String
  | .word => "impl " ++ trait ++ "<word>"
  | .tuple => "impl<f, g> " ++ trait ++ "<(f, g)> where f: " ++ trait ++ ", g: " ++ trait
  | .sum => "impl<f, g> " ++ trait ++ "<sum<f, g>> where f: " ++ trait ++ ", g: " ++ trait
  | .decl index =>
      if (decls[index]?.map (·.generic)).getD false then
        "impl<a> " ++ trait ++ "<" ++ enumName index ++ "<a>> where a: " ++ trait
      else "impl " ++ trait ++ "<" ++ enumName index ++ ">"

def mixCall (sub : Sub) (receiver argument : String) : String :=
  subName ++ "." ++ mixName sub ++ "(" ++ receiver ++ ", " ++ argument ++ ")"

private def xNames : List String := ["sc_a", "sc_b"]

/-- The subclass method's body at a head: a Word combines `sc_x` with the
base fold of `sc_y`, any other head matches `sc_x` and calls the method at
its bound values. -/
def mixBody (plan : Plan) (head : Head) (counts : List Nat) (steps : List Step) : List String :=
  match head with
  | .word => [returned 8 (Traits.stepText (steps.headD default) ["sc_x", Traits.unaryCall "sc_y"])]
  | _ =>
      let names := fun (ctor : Nat) => if head == .sum && ctor = 1 then ["sc_b"] else xNames
      [indented 8 "match (sc_x) {"] ++
        (counts.zip steps).zipIdx.flatMap (fun ((fields, step), ctor) =>
          arm 12 (Traits.ctorPattern plan.decls head ctor fields (names ctor))
            [returned 16 (Traits.stepText step (((names ctor).take fields).map fun name => mixCall plan.sub name "sc_y"))]) ++
        [indented 8 "}"]

def subImplLines (plan : Plan) (impl : SubImpl) : List String :=
  let header := implHeader plan.decls subName impl.head
  match mixCounts plan.decls impl.head with
  | some counts => if plan.sub.method then
      [header ++ " {", indented 4 ("function " ++ mixName plan.sub ++ "<u>(sc_x: " ++ Traits.implType plan.decls impl.head ++
          ", sc_y: u) returns (word) where u: " ++ baseName ++ " {")] ++
        mixBody plan impl.head counts impl.steps ++ [indented 4 "}", "}", ""]
    else [header ++ " {}", ""]
  | none => []

def topImplLines (plan : Plan) (head : Head) : List String := [implHeader plan.decls topName head ++ " {}", ""]

def hierarchyLines (plan : Plan) : List String :=
  (if plan.sub.method then
    ["trait " ++ subName ++ "<a> where a: " ++ baseName ++ " {",
     indented 4 ("function " ++ mixName plan.sub ++ "<u>(sc_x: a, sc_y: u) returns (word) where u: " ++ baseName ++ ";"),
     "}", ""]
   else ["trait " ++ subName ++ "<a> where a: " ++ baseName ++ " {}", ""]) ++
    ["trait " ++ topName ++ "<a> where a: " ++ subName ++ " {}", ""]

def helperName (call : Call) (method : Method) : String :=
  match call, method with
  | .top, .mix => "sc_mixt"
  | _, .mix => "sc_mixv"
  | .sub, .unary => "sc_up"
  | .sub, _ => "sc_up2"
  | .top, .unary => "sc_top"
  | .top, _ => "sc_top2"
  | .value, .unary => "sc_val"
  | .value, _ => "sc_val2"
  | _, .unary => "sc_fun"
  | _, _ => "sc_fun2"

def helperLines (plan : Plan) (helper : Helper) : List String :=
  let step : Step := {combine := .add, op := helper.op, constant := helper.constant}
  let bound := if helper.call == .top then topName else subName
  let arguments := match helper.method with
    | .unary => "sc_x"
    | _ => "sc_x, sc_y"
  let parameters := match helper.method with
    | .unary => "<t>(sc_x: t)"
    | .binary => "<t>(sc_x: t, sc_y: t)"
    | .mix => "<t, u>(sc_x: t, sc_y: u)"
  let bounds := "t: " ++ bound ++ (if helper.method == .mix then ", u: " ++ baseName else "")
  let target := match helper.method, helper.call with
    | .mix, _ => subName ++ "." ++ mixName plan.sub
    | .unary, .function => "sc_up"
    | _, .function => "sc_up2"
    | .unary, _ => baseName ++ ".sc_fold"
    | _, _ => baseName ++ ".sc_both"
  let header := "function " ++ helperName helper.call helper.method ++ parameters ++ " returns (word) where " ++
    bounds ++ " {"
  let body := match helper.call with
    | .value | .function => [indented 4 ("let sc_f = " ++ target ++ ";"),
        returned 4 (Traits.stepText step ["sc_f(" ++ arguments ++ ")"])]
    | _ => [returned 4 (Traits.stepText step [target ++ "(" ++ arguments ++ ")"])]
  [header] ++ body ++ ["}", ""]

def builderName (prefix_ : String) (index : Nat) : String := prefix_ ++ toString index

/-- A builder returning one of its values, selected by the residue
`(sc_x + offset) & 3` when it has several, as `TraitEmitter`'s. -/
def builderLines (decls : List Decl) (name : String) (type : Inst) (builder : Solcore.Synthesis.Core.Traits.Builder) :
    List String :=
  let header := "function " ++ name ++ "(sc_x: word) returns (" ++ Traits.instText type ++ ") {"
  let value := fun (indent : Nat) (tree : Solcore.Synthesis.Core.Traits.Val) =>
    returned indent (Traits.valueText decls Solcore.Synthesis.Core.Enums.valueFuel type tree)
  match builder.trees with
  | [tree] => [header, value 4 tree, "}", ""]
  | trees =>
      let count := trees.length
      [header, indented 4 ("let sc_k: word = ((sc_x + " ++ toString builder.offset ++ ") & 3);")] ++
        (trees.take (count - 1)).zipIdx.flatMap (fun (tree, residue) =>
          [indented 4 ("if (sc_k == " ++ toString residue ++ ") {"), value 8 tree, indented 4 "}"]) ++
        [value 4 (trees.getLastD default), "}", ""]

def argumentPrefixes : List String := ["sc_v", "sc_w"]

def useBuilderLines (decls : List Decl) (index : Nat) (use : Use) : List String :=
  builderLines decls (builderName "sc_u" index) use.type use.builder ++
    (use.arguments.zip argumentPrefixes).flatMap fun (argument, prefix_) =>
      builderLines decls (builderName prefix_ index) argument.type argument.builder

def useText (plan : Plan) (index : Nat) (use : Use) : String :=
  let first := builderName "sc_u" index ++ "(sc_input)"
  let second := builderName "sc_u" index ++ "((sc_input + " ++ toString use.shift ++ "))"
  let callee := match use.call, use.method with
    | .direct, .unary => baseName ++ ".sc_fold"
    | .direct, .binary => baseName ++ ".sc_both"
    | .direct, .mix => subName ++ "." ++ mixName plan.sub
    | call, method => helperName call method
  match use.method with
  | .unary => callee ++ "(" ++ first ++ ")"
  | .binary => callee ++ "(" ++ first ++ ", " ++ second ++ ")"
  | .mix =>
      let calls := (argumentPrefixes.take use.arguments.length).map fun prefix_ =>
        callee ++ "(" ++ first ++ ", " ++ builderName prefix_ index ++ "(sc_input))"
      "(" ++ " + ".intercalate calls ++ ")"

def runLines (plan : Plan) : List String :=
  let callLines := plan.uses.zipIdx.map fun (use, index) =>
    indented 8 ("let sc_r" ++ toString index ++ ": word = " ++ useText plan index use ++ ";")
  let combined := (List.range plan.uses.length).foldl (fun accumulated index =>
      if index = 0 then "sc_r0"
      else "(" ++ accumulated ++ " + (sc_r" ++ toString index ++ " * " ++ toString (2 * index + 1) ++ "))") ""
  ["contract " ++ contractName ++ " {",
   indented 4 ("function " ++ methodName ++ "(input: uint256) public returns (uint256) {"),
   indented 8 "let sc_input: word = Typedef.rep(input);"] ++ callLines ++
    [indented 8 ("return uint256(" ++ combined ++ ");"), indented 4 "}", "}"]

def emit (plan : Plan) : Solcore.Synthesis.Source.EmittedProgram :=
  let base := plan.base
  let lines := ["import * from std;", "import * from std.dispatch;", ""] ++
    plan.decls.zipIdx.flatMap (fun (decl, index) => declLines plan.decls index decl) ++
    Traits.traitLines base ++ plan.impls.flatMap (Traits.implLines base) ++
    hierarchyLines plan ++ plan.subImpls.flatMap (subImplLines plan) ++ plan.tops.flatMap (topImplLines plan) ++
    plan.helpers.flatMap (helperLines plan) ++
    plan.uses.zipIdx.flatMap (fun (use, index) => useBuilderLines plan.decls index use) ++
    runLines plan
  { source := "\n".intercalate lines ++ "\n", contractName, methodName, methodSignature, deployPath, runtimePath }

end Solcore.Synthesis.Source.Hierarchies
