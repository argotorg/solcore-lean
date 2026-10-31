import Solcore.Synthesis.Core.RevertData
import Solcore.Synthesis.Source.MemoryValuesEmitter

/-! The Solcore source of a revert data plan: the helpers `sc_h<k>` that
raise, make, choose and forward std `Error` values, the enum `Sc_F` when a
plan uses it, and `SynthesizedRevertData.run(uint256)`, whose
`runtime-memory-values` actions keep that profile's text. The source is a
function of the plan; nothing here builds or reads the Core reference. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.RevertData

open Solcore.Synthesis.Core.RevertData
open Solcore.Synthesis.Core.MemoryValues (Ref Fold Operand)

def emitterVersion : String := "solcore-source-revert-data-v1"
def wrapperVersion : String := "solcore-word-revert-data-contract-v1"
def contractName : String := "SynthesizedRevertData"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def deployPath : List String := ["SynthesizedRevertDataDeploy"]
def runtimePath : List String := ["SynthesizedRevertDataDeploy", "SynthesizedRevertData"]

private def foldText : Fold → String
  | .add => " + "
  | .xor => " ^ "

private def indent (count : Nat) (lines : List String) : List String :=
  lines.map fun line => String.ofList (List.replicate count ' ') ++ line

def testText (word : String) : Test → String
  | .lt constant => "(" ++ word ++ " < " ++ toString constant ++ ")"
  | .gt constant => "(" ++ word ++ " > " ++ toString constant ++ ")"
  | .eq constant => "(" ++ word ++ " == " ++ toString constant ++ ")"
  | .ne constant => "(" ++ word ++ " != " ++ toString constant ++ ")"
  | .bits mask value => "((" ++ word ++ " & " ++ toString mask ++ ") == " ++ toString value ++ ")"

/-- A Word of `run`, its loop and match arms. -/
def runWord : Operand → String := Source.MemoryValues.operandText "sc_counter"

/-- A Word of a helper or closure over its parameter. -/
def localWord (base : String) : Operand → String
  | .add constant => "(" ++ base ++ " + " ++ toString constant ++ ")"
  | .mul constant => "(" ++ base ++ " * " ++ toString constant ++ ")"
  | .xor constant => "(" ++ base ++ " ^ " ++ toString constant ++ ")"
  | _ => base

def bytesName (value : Nat) : String := "sc_b" ++ toString value

def makeText (word : Operand → String) : Make → String
  | .selector selector => "Error(" ++ word selector ++ ")"
  | .empty => "Error.Empty"
  | .message value => "Error.Msg(memory(Typedef.rep(" ++ bytesName value ++ ")))"

def sourceText (word : Operand → String) : Source → String
  | .make made => makeText word made
  | .named number => "sc_e" ++ toString number
  | .param => "sc_e"

def literalText (text : Nat) : String := "\"" ++ (literals[text]?).getD "" ++ "\""

/-- A site's lines over the Words of its scope. -/
def siteLines (word : Operand → String) (site : Site) : List String :=
  let condition := testText (word site.cond.word) site.cond.test
  let guarded := fun (line : String) => ["if " ++ condition ++ " {", "    " ++ line, "}"]
  match site.form, site.payload with
  | .when, .error origin => guarded ("revertWithError(" ++ sourceText word origin ++ ");")
  | .require, .error origin => ["require(" ++ condition ++ ", " ++ sourceText word origin ++ ");"]
  | .when, .literal text => guarded ("revertLit(" ++ literalText text ++ ");")
  | .require, .literal text => ["require(" ++ condition ++ ", " ++ literalText text ++ ");"]
  | _, .none => guarded "revertEmpty();"

def helperName (index : Nat) : String := "sc_h" ++ toString index

def helperLines (index : Nat) : Helper → List String
  | .raise site fold constant =>
      ["function " ++ helperName index ++ "(sc_e: Error, sc_w: word) returns (word) {"] ++
      indent 4 (siteLines (localWord "sc_w") site) ++
      ["    return (sc_w" ++ foldText fold ++ toString constant ++ ");", "}"]
  | .make constant =>
      ["function " ++ helperName index ++ "(sc_w: word) returns (Error) {",
       "    return Error((sc_w + " ++ toString constant ++ "));", "}"]
  | .message =>
      ["function " ++ helperName index ++ "(sc_v: memory<bytes>) returns (Error) {",
       "    return Error.Msg(memory(Typedef.rep(sc_v)));", "}"]
  | .pick test =>
      ["function " ++ helperName index ++ "(sc_w: word, sc_a: Error, sc_b: Error) returns (Error) {",
       "    if " ++ testText "sc_w" test ++ " {", "        return sc_a;", "    }", "    return sc_b;", "}"]
  | .call callee constant =>
      ["function " ++ helperName index ++ "(sc_e: Error, sc_w: word) returns (word) {",
       "    return " ++ helperName callee ++ "(sc_e, (sc_w + " ++ toString constant ++ "));", "}"]

/-- Declaration numbers so far, by kind. -/
structure Names where
  values : Source.MemoryValues.Names := {}
  errors : Nat := 0
  pairs : Nat := 0
  sums : Nat := 0
  enums : Nat := 0
  closures : Nat := 0
  functions : Nat := 0

def foldLine (fold : Fold) (constant : Nat) (value : String) : String :=
  "sc_r = ((sc_r * " ++ toString constant ++ ")" ++ foldText fold ++ value ++ ");"

def declText : Decl → String
  | .make made => makeText runWord made
  | .helper helper word => helperName helper ++ "(" ++ runWord word ++ ")"
  | .message helper value => helperName helper ++ "(" ++ bytesName value ++ ")"
  | .pick helper word first second =>
      helperName helper ++ "(" ++ runWord word ++ ", " ++ sourceText runWord first ++ ", " ++
        sourceText runWord second ++ ")"

def takeLines (held : Held) (site : Site) (fold : Fold) (constant : Nat) : List String :=
  let arm := siteLines runWord site
  let folded := [foldLine fold constant "sc_w"]
  match held with
  | .pair number =>
      ["match (sc_t" ++ toString number ++ ") {", "    case (sc_e, sc_w) {"] ++ indent 8 (arm ++ folded) ++
      ["    }", "}"]
  | .sum number =>
      ["match (sc_u" ++ toString number ++ ") {", "    case inl(sc_e) {"] ++ indent 8 arm ++
      ["    }", "    case inr(sc_w) {"] ++ indent 8 folded ++ ["    }", "}"]
  | .enum number =>
      ["match (sc_g" ++ toString number ++ ") {", "    case Sc_F.Sc_F0(sc_e, sc_w) {"] ++ indent 8 (arm ++ folded) ++
      ["    }", "    case Sc_F.Sc_F1(sc_w) {"] ++ indent 8 folded ++ ["    }", "}"]

/-- A step's lines and the declaration numbers after it. -/
def stepLines (names : Names) : Step → List String × Names
  | .action action =>
      let (lines, values) := Source.MemoryValues.actionLines "sc_counter" names.values action
      (lines, {names with values})
  | .error decl =>
      (["let sc_e" ++ toString names.errors ++ ": Error = " ++ declText decl ++ ";"],
       {names with errors := names.errors + 1})
  | .data datum =>
      let error := fun (origin : Source) => sourceText runWord origin
      match datum with
      | .pair origin word =>
          (["let sc_t" ++ toString names.pairs ++ ": (Error, word) = (" ++ error origin ++ ", " ++ runWord word ++ ");"],
           {names with pairs := names.pairs + 1})
      | .inl origin =>
          (["let sc_u" ++ toString names.sums ++ ": sum<Error, word> = inl(" ++ error origin ++ ");"],
           {names with sums := names.sums + 1})
      | .inr word =>
          (["let sc_u" ++ toString names.sums ++ ": sum<Error, word> = inr(" ++ runWord word ++ ");"],
           {names with sums := names.sums + 1})
      | .first origin word =>
          (["let sc_g" ++ toString names.enums ++ ": Sc_F = Sc_F.Sc_F0(" ++ error origin ++ ", " ++ runWord word ++ ");"],
           {names with enums := names.enums + 1})
      | .second word =>
          (["let sc_g" ++ toString names.enums ++ ": Sc_F = Sc_F.Sc_F1(" ++ runWord word ++ ");"],
           {names with enums := names.enums + 1})
  | .site site => (siteLines runWord site, names)
  | .call helper origin word direct fold constant =>
      let arguments := "(" ++ sourceText runWord origin ++ ", " ++ runWord word ++ ")"
      if direct then ([foldLine fold constant (helperName helper ++ arguments)], names)
      else
        let name := "sc_f" ++ toString names.functions
        (["let " ++ name ++ ": function (Error, word) returns (word) = " ++ helperName helper ++ ";",
          foldLine fold constant (name ++ arguments)], {names with functions := names.functions + 1})
  | .take held site fold constant => (takeLines held site fold constant, names)
  | .closure site fold constant =>
      (["let sc_c" ++ toString names.closures ++ ": function (word) returns (word) = lam (sc_j: word) -> word {"] ++
        indent 4 (siteLines (localWord "sc_j") site) ++
        ["    return (sc_j" ++ foldText fold ++ toString constant ++ ");", "};"],
       {names with closures := names.closures + 1})
  | .apply closure word fold constant =>
      ([foldLine fold constant ("sc_c" ++ toString closure ++ "(" ++ runWord word ++ ")")], names)
  | .loop mask body =>
      let (inner, values) := body.foldl (fun (lines, values) item => match item with
        | .action action =>
            let (more, values) := Source.MemoryValues.actionLines "sc_counter" values action
            (lines ++ more, values)
        | .site site => (lines ++ siteLines runWord site, values)) ([], names.values)
      (["let sc_limit: word = (sc_x & " ++ toString mask ++ ");",
        "let sc_counter: word = 0;",
        "while (sc_limit > sc_counter) {"] ++ indent 4 inner ++
       ["    sc_counter = (sc_counter + 1);", "}"], {names with values})

def Step.actions : Step → List Solcore.Synthesis.Core.MemoryValues.Action
  | .action action => [action]
  | .loop _ body => body.filterMap fun item => match item with
      | .action action => some action
      | .site _ => none
  | _ => []

def usesEnum (plan : Plan) : Bool :=
  plan.steps.any fun step => match step with
    | .data (.first ..) | .data (.second _) => true
    | _ => false

def emit (plan : Plan) : EmittedProgram := Id.run do
  let mut names : Names := {}
  let mut lines : List String := []
  for step in plan.steps do
    let (more, next) := stepLines names step
    lines := lines ++ more
    names := next
  let used := plan.steps.flatMap fun step => (Step.actions step).flatMap Source.MemoryValues.actionHelpers
  let actionHelpers := Source.MemoryValues.helperNames.filter used.contains
  let enum := if usesEnum plan then ["enum Sc_F {", "    Sc_F0(Error, word),", "    Sc_F1(word)", "}", ""] else []
  let helpers := plan.helpers.zipIdx.flatMap fun (helper, index) => helperLines index helper ++ [""]
  let source := ["import * from std;", "import * from std.dispatch;",
      "import { mload, mstore, mstore8, shr, mod } from std.opcodes;", ""] ++
    actionHelpers.flatMap Source.MemoryValues.helperLines ++ enum ++ helpers ++
    ["contract " ++ contractName ++ " {",
     "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
     "        let sc_x: word = Typedef.rep(input);",
     "        let sc_r: word = 0;"] ++ indent 8 lines ++
    ["        return uint256(sc_r);", "    }", "}"]
  return {
    source := String.intercalate "\n" source ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.RevertData
