import Solcore.Synthesis.Core.EnumMatch
import Solcore.Synthesis.Source.ScalarRenderer

/-! Source emission of an enum plan: top-level `enum` declarations, one
function per view whose body is one `match`, one builder function per
scrutinee or instance, and `run`, which calls every view on its builders'
values. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Enums

open Solcore.Synthesis.Core.Enums

def emitterVersion : String := "solcore-source-enums-v1"
def wrapperVersion : String := "solcore-word-enums-contract-v1"

def contractName : String := "SynthesizedEnums"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedEnumsDeploy"]
def runtimePath : List String := ["SynthesizedEnumsDeploy", "SynthesizedEnums"]

def enumName (index : Nat) : String := "Sc_T" ++ toString index

/-- Constructor `ctor` of declaration `index`; a same-name constructor 0
carries the enum's name. -/
def constructorName (decls : List Decl) (index ctor : Nat) : String :=
  if ctor = 0 && (decls[index]?.map (·.sameName)).getD false then enumName index
  else enumName index ++ "_" ++ toString ctor

def typeText : Ty → String
  | .word => "word"
  | .param => "a"
  | .tuple left right => "(" ++ typeText left ++ ", " ++ typeText right ++ ")"
  | .enum index => enumName index
  | .applied index argument => enumName index ++ "<" ++ typeText argument ++ ">"

private def indented (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def arguments (texts : List String) : String :=
  if texts.isEmpty then "" else "(" ++ ", ".intercalate texts ++ ")"

def declLines (decls : List Decl) (index : Nat) (decl : Decl) : List String :=
  let count := decl.constructors.length
  ["enum " ++ enumName index ++ (if decl.generic then "<a>" else "") ++ " {"] ++
    decl.constructors.zipIdx.map (fun (fields, ctor) =>
      indented 4 (constructorName decls index ctor ++ arguments (fields.map typeText) ++
        (if ctor + 1 < count then "," else ""))) ++
    ["}", ""]

private def declIndex : Ty → Nat
  | .enum index | .applied index _ => index
  | _ => 0

def constructorText (decls : List Decl) (type : Ty) (ctor : Nat) : Form → String
  | .qualified => enumName (declIndex type) ++ "." ++ constructorName decls (declIndex type) ctor
  | .dot => "." ++ constructorName decls (declIndex type) ctor
  | .sameName => enumName (declIndex type)

def leafText : LeafOp → Nat → String
  | .input, _ => "sc_x"
  | .add, constant => "(sc_x + " ++ toString constant ++ ")"
  | .xor, constant => "(sc_x ^ " ++ toString constant ++ ")"
  | .mul, constant => "(sc_x * " ++ toString constant ++ ")"

def valueText (decls : List Decl) : Nat → Ty → Value → String
  | 0, _, _ => "sc_x"
  | _ + 1, .word, .leaf op constant => leafText op constant
  | fuel + 1, .tuple left right, .tuple first second =>
      "(" ++ valueText decls fuel left first ++ ", " ++ valueText decls fuel right second ++ ")"
  | fuel + 1, type, value => match constructorsOf decls type, value.constructor? with
      | some constructors, some (ctor, fields, form) =>
          let types := constructors.getD ctor []
          constructorText decls type ctor form ++
            arguments ((types.zip fields).map fun (fieldType, field) => valueText decls fuel fieldType field)
      | _, _ => "sc_x"

def patText (decls : List Decl) : Nat → Ty → Pat → String
  | 0, _, _ => "_"
  | _ + 1, _, .wild => "_"
  | _ + 1, _, .var name => names.getD name "_"
  | fuel + 1, .tuple left right, .tuple first second =>
      "(" ++ patText decls fuel left first ++ ", " ++ patText decls fuel right second ++ ")"
  | fuel + 1, type, pattern => match constructorsOf decls type, pattern.head, pattern.form? with
      | some constructors, some (ctor, fields), some form =>
          let types := constructors.getD ctor []
          constructorText decls type ctor form ++
            arguments ((types.zip fields).map fun (fieldType, field) => patText decls fuel fieldType field)
      | _, _, _ => "_"

def termText : Term → String
  | .name name => names.getD name "sc_w"
  | .constant value => toString value

def bodyLine (indent : Nat) (body : Body) : String :=
  let folded := body.rest.foldl
    (fun accumulated (op, term) => "(" ++ accumulated ++ " " ++ op.token ++ " " ++ termText term ++ ")")
    (termText body.first)
  indented indent ("return (" ++ folded ++ " + " ++ toString body.constant ++ ");")

def rowHeader (decls : List Decl) (types : List Ty) : List Pat → String
  | [] => "default {"
  | [pattern] => "case " ++ patText decls patFuel (types.headD .word) pattern ++ " {"
  | patterns => "case (" ++ ", ".intercalate ((types.zip patterns).map fun (type, pattern) =>
      patText decls patFuel type pattern) ++ ") {"

/-- The binding of a scrutinee name at an arm, as in the original Core. -/
private def scrutineeType (decls : List Decl) (types : List Ty) (row : List Pat) (name : Nat) : Ty :=
  (lookupType (rowBindings decls types row) name).getD .word

def armLines (decls : List Decl) (types : List Ty) (indent : Nat) (arm : Arm) : List String :=
  let body := match arm.body with
    | .expr body => [bodyLine (indent + 4) body]
    | .nested scrutinee arms =>
        let type := scrutineeType decls types arm.patterns scrutinee
        [indented (indent + 4) ("match (" ++ names.getD scrutinee "sc_w" ++ ") {")] ++
          arms.flatMap (fun inner =>
            [indented (indent + 8) (rowHeader decls [type] inner.patterns), bodyLine (indent + 12) inner.body,
             indented (indent + 8) "}"]) ++
          [indented (indent + 4) "}"]
  [indented indent (rowHeader decls types arm.patterns)] ++ body ++ [indented indent "}"]

def viewName (index : Nat) : String := "sc_view" ++ toString index

def builderName (view builder : Nat) : String := "sc_make" ++ toString view ++ "_" ++ toString builder

private def scrutineeNames : List String := ["sc_e", "sc_f"]

def viewLines (decls : List Decl) (index : Nat) (view : View) : List String :=
  let parameters := (view.scrutinees.zip scrutineeNames).map fun (type, name) => name ++ ": " ++ typeText type
  let header := "function " ++ viewName index ++ (if view.kind == .generic then "<a>" else "") ++ "(" ++
    ", ".intercalate (parameters ++ ["sc_w: word"]) ++ ") returns (word) {"
  [header, indented 4 ("match (" ++ ", ".intercalate (scrutineeNames.take view.scrutinees.length) ++ ") {")] ++
    view.arms.flatMap (armLines decls view.scrutinees 8) ++ [indented 4 "}", "}", ""]

def builderLines (decls : List Decl) (name : String) (type : Ty) (builder : Builder) : List String :=
  let header := "function " ++ name ++ "(sc_x: word) returns (" ++ typeText type ++ ") {"
  let returned := fun (indent : Nat) (tree : Value) =>
    indented indent ("return " ++ valueText decls valueFuel type tree ++ ";")
  match builder.trees with
  | [tree] => [header, returned 4 tree, "}", ""]
  | trees =>
      let count := trees.length
      [header, indented 4 ("let sc_k: word = ((sc_x + " ++ toString builder.offset ++ ") & 3);")] ++
        (trees.take (count - 1)).zipIdx.flatMap (fun (tree, residue) =>
          [indented 4 ("if (sc_k == " ++ toString residue ++ ") {"), returned 8 tree, indented 4 "}"]) ++
        [returned 4 (trees.getLastD default), "}", ""]

/-- Each call: the view, its builders and the view's Word offset. -/
def calls (plan : Plan) : List (Nat × List Nat × Nat) :=
  plan.views.zipIdx.flatMap fun (view, index) => match view.kind with
    | .generic => (List.range view.builders.length).map fun builder => (index, [builder], view.wordOffset)
    | _ => [(index, List.range view.builders.length, view.wordOffset)]

def runLines (plan : Plan) : List String :=
  let callLines := (calls plan).zipIdx.map fun ((view, builders, offset), index) =>
    indented 8 ("let sc_r" ++ toString index ++ ": word = " ++ viewName view ++ "(" ++
      ", ".intercalate (builders.map (fun builder => builderName view builder ++ "(sc_input)") ++
        ["(sc_input + " ++ toString offset ++ ")"]) ++ ");")
  let combined := (List.range (calls plan).length).foldl (fun accumulated index =>
      if index = 0 then "sc_r0"
      else "(" ++ accumulated ++ " + (sc_r" ++ toString index ++ " * " ++ toString (2 * index + 1) ++ "))") ""
  ["contract " ++ contractName ++ " {",
   indented 4 ("function " ++ methodName ++ "(input: uint256) public returns (uint256) {"),
   indented 8 "let sc_input: word = Typedef.rep(input);"] ++ callLines ++
    [indented 8 ("return uint256(" ++ combined ++ ");"), indented 4 "}", "}"]

def emit (plan : Plan) : EmittedProgram :=
  let lines := ["import * from std;", "import * from std.dispatch;", ""] ++
    plan.decls.zipIdx.flatMap (fun (decl, index) => declLines plan.decls index decl) ++
    plan.views.zipIdx.flatMap (fun (view, index) =>
      viewLines plan.decls index view ++
        (view.instanceTypes.zip view.builders).zipIdx.flatMap fun ((type, builder), builderIndex) =>
          builderLines plan.decls (builderName index builderIndex) type builder) ++
    runLines plan
  { source := "\n".intercalate lines ++ "\n", contractName, methodName, methodSignature, deployPath, runtimePath }

end Solcore.Synthesis.Source.Enums
