import Solcore.Synthesis.Core.MemoryCalls
import Solcore.Synthesis.Source.MemoryValuesEmitter

/-! The Solcore source of a memory call plan: the helpers `sc_h<k>(sc_v, sc_i,
sc_w)` over std's memory values and data values carrying them, the enum
`Sc_E` when a plan uses it, and `SynthesizedMemoryCalls.run(uint256)`, whose
`runtime-memory-values` actions keep that profile's text. The source is a
function of the plan; nothing here builds or reads the Core reference. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MemoryCalls

open Solcore.Synthesis.Core.MemoryCalls
open Solcore.Synthesis.Core.MemoryValues (Ref Fold Width Operand Index)

def emitterVersion : String := "solcore-source-memory-calls-v1"
def wrapperVersion : String := "solcore-word-memory-calls-contract-v1"
def contractName : String := "SynthesizedMemoryCalls"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def deployPath : List String := ["SynthesizedMemoryCallsDeploy"]
def runtimePath : List String := ["SynthesizedMemoryCallsDeploy", "SynthesizedMemoryCalls"]

def kindType : Kinded → String
  | .bytes => "memory<bytes>"
  | .slice => "memory_ref"
  | .array => "memory<DynArray<uint256>>"
  | .pair => "(memory<bytes>, word)"
  | .sum => "sum<memory<bytes>, word>"
  | .enum => "Sc_E"
  | .word => "word"

def paramType : Param → String
  | .bytes => "memory<bytes>"
  | .slice => "memory_ref"
  | .generic => "a"
  | .array => "memory<DynArray<uint256>>"
  | .pair => "(memory<bytes>, word)"
  | .sum => "sum<memory<bytes>, word>"
  | .enum => "Sc_E"

private def foldText : Fold → String
  | .add => " + "
  | .xor => " ^ "

/-- What a helper's base kind returns, given the text of the value it is
handed. -/
def baseResult (base : Helper) (value : String) : String :=
  match base.kind with
  | .read .. | .take .. => "word"
  | .write _ => value
  | .view _ => "memory_ref"
  | .copy => "memory<bytes>"
  | .pack _ => "(memory<bytes>, word)"
  | .call .. => value

def obsText (value index : String) : Obs → String
  | .length => "MemorySize.len(" ++ value ++ ")"
  | .word => "sc_word(" ++ value ++ ", " ++ index ++ ")"
  | .byte => "sc_byte(" ++ value ++ ", " ++ index ++ ")"
  | .hash => "Typedef.rep(keccak256_(" ++ value ++ "))"
  | .element => "Typedef.rep(" ++ value ++ "[uint256(" ++ index ++ ")])"

private def indent (count : Nat) (lines : List String) : List String :=
  lines.map fun line => String.ofList (List.replicate count ' ') ++ line

def helperName (index : Nat) : String := "sc_h" ++ toString index

def helperLines (helpers : List Helper) (index : Nat) (helper : Helper) : List String :=
  let value := paramType helper.param
  let result := match resolve helpers (maximumHelpers + 1) index with
    | some (base, _) => baseResult base value
    | none => "word"
  let name := helperName index
  let header := if helper.param == .generic then
      "function " ++ name ++ "<a>(sc_v: a, sc_i: word, sc_w: word) returns (" ++ result ++
        ") where a: MemorySize, a: MemoryPointer, a: MemoryEncode {"
    else "function " ++ name ++ "(sc_v: " ++ value ++ ", sc_i: word, sc_w: word) returns (" ++ result ++ ") {"
  let body := match helper.kind with
    | .read obs fold => ["return (" ++ obsText "sc_v" "sc_i" obs ++ foldText fold ++ "sc_w);"]
    | .write width =>
        (if helper.param == .array then ["IndexAccess.set(sc_v, uint256(sc_i), uint256(sc_w));"]
         else [(if width == .word then "sc_put" else "sc_put8") ++ "(sc_v, sc_i, sc_w);"]) ++ ["return sc_v;"]
    | .view start => ["return slice_(sc_v, " ++ toString start ++ ");"]
    | .copy => ["return concat(sc_v, bytes32(sc_w));"]
    | .call callee constant => ["return " ++ helperName callee ++ "(sc_v, sc_i, (sc_w + " ++ toString constant ++ "));"]
    | .pack constant => ["return (sc_v, (sc_w + " ++ toString constant ++ "));"]
    | .take obs fold written =>
        let memory := fun (writtenWord : String) =>
          (if written then ["sc_put8(sc_p, sc_i, " ++ writtenWord ++ ");"] else []) ++
            ["return (" ++ obsText "sc_p" "sc_i" obs ++ foldText fold ++ "sc_w);"]
        let wordArm := ["return (sc_q" ++ foldText fold ++ "sc_w);"]
        let arm := fun (pattern : String) (lines : List String) =>
          ["case " ++ pattern ++ " {"] ++ indent 4 lines ++ ["}"]
        let arms := match helper.param with
          | .pair => arm "(sc_p, sc_q)" (memory "sc_q")
          | .sum => arm "inl(sc_p)" (memory "sc_w") ++ arm "inr(sc_q)" wordArm
          | _ => arm "Sc_E.Sc_E0(sc_p, sc_q)" (memory "sc_q") ++ arm "Sc_E.Sc_E1(sc_q)" wordArm
        ["match (sc_v) {"] ++ indent 4 arms ++ ["}"]
  [header] ++ indent 4 body ++ ["}", ""]

/-- Declaration numbers so far: `runtime-memory-values`' kinds, then pairs,
sums, enums, closures and function values. -/
structure Names where
  memory : MemoryValues.Names := {}
  pairs : Nat := 0
  sums : Nat := 0
  enums : Nat := 0
  closures : Nat := 0
  values : Nat := 0

def declaration (names : Names) : Kinded → String × Names
  | .bytes => ("let sc_b" ++ toString names.memory.bytes ++ ": memory<bytes>",
      {names with memory := {names.memory with bytes := names.memory.bytes + 1}})
  | .slice => ("let sc_s" ++ toString names.memory.slices ++ ": memory_ref",
      {names with memory := {names.memory with slices := names.memory.slices + 1}})
  | .array => ("let sc_a" ++ toString names.memory.arrays ++ ": memory<DynArray<uint256>>",
      {names with memory := {names.memory with arrays := names.memory.arrays + 1}})
  | .pair => ("let sc_t" ++ toString names.pairs ++ ": (memory<bytes>, word)", {names with pairs := names.pairs + 1})
  | .sum => ("let sc_u" ++ toString names.sums ++ ": sum<memory<bytes>, word>", {names with sums := names.sums + 1})
  | .enum => ("let sc_e" ++ toString names.enums ++ ": Sc_E", {names with enums := names.enums + 1})
  | .word => ("", names)

def stepLines (helpers : List Helper) (names : Names) : Step → List String × Names
  | .action single =>
      let (lines, memory) := MemoryValues.actionLines "sc_counter" names.memory single
      (lines, {names with memory})
  | .call helper arg index word form fold constant =>
      let result := (resultAt helpers helper arg.kinded).getD .word
      let arguments := arg.name ++ ", " ++ MemoryValues.indexText "sc_counter" index ++ ", " ++
        MemoryValues.operandText "sc_counter" word
      let (lines, callee, names) := match form with
        | .direct => ([], helperName helper, names)
        | .value =>
            let name := "sc_f" ++ toString names.values
            (["let " ++ name ++ ": function (" ++ kindType arg.kinded ++ ", word, word) returns (" ++
              kindType result ++ ") = " ++ helperName helper ++ ";"], name, {names with values := names.values + 1})
      let call := callee ++ "(" ++ arguments ++ ")"
      if result == .word then
        (lines ++ ["sc_r = ((sc_r * " ++ toString constant ++ ")" ++ foldText fold ++ call ++ ");"], names)
      else
        let (declared, names) := declaration names result
        (lines ++ [declared ++ " = " ++ call ++ ";"], names)
  | .data datum =>
      let word := fun (operand : Operand) => MemoryValues.operandText "sc_counter" operand
      match datum with
      | .pair ref operand =>
          let (declared, names) := declaration names .pair
          ([declared ++ " = (" ++ refName ref ++ ", " ++ word operand ++ ");"], names)
      | .inl ref =>
          let (declared, names) := declaration names .sum
          ([declared ++ " = inl(" ++ refName ref ++ ");"], names)
      | .inr operand =>
          let (declared, names) := declaration names .sum
          ([declared ++ " = inr(" ++ word operand ++ ");"], names)
      | .first ref operand =>
          let (declared, names) := declaration names .enum
          ([declared ++ " = Sc_E.Sc_E0(" ++ refName ref ++ ", " ++ word operand ++ ");"], names)
      | .second operand =>
          let (declared, names) := declaration names .enum
          ([declared ++ " = Sc_E.Sc_E1(" ++ word operand ++ ");"], names)
  | .closure ref obs =>
      let name := "sc_c" ++ toString names.closures
      (["let " ++ name ++ ": function (word) returns (word) = lam (sc_j: word) -> word {",
        "    return " ++ obsText (refName ref) "sc_j" obs ++ ";", "};"], {names with closures := names.closures + 1})
  | .apply number index fold constant =>
      (["sc_r = ((sc_r * " ++ toString constant ++ ")" ++ foldText fold ++ "sc_c" ++ toString number ++ "(" ++
        MemoryValues.indexText "sc_counter" index ++ "));"], names)

/-- The memory helpers a plan uses: `runtime-memory-values`' through its
actions, and through the helpers' and closures' observations and writes. -/
def usedHelpers (plan : Plan) : List String :=
  let fromObs := fun (obs : Obs) => match obs with
    | .word => ["sc_word"]
    | .byte => ["sc_byte"]
    | _ => []
  let used := plan.steps.flatMap (fun step => match step with
      | .action single => MemoryValues.actionHelpers single
      | .closure _ obs => fromObs obs
      | _ => []) ++
    plan.helpers.flatMap fun helper => match helper.kind with
      | .read obs _ => fromObs obs
      | .write width => if helper.param == .array then [] else if width == .word then ["sc_put"] else ["sc_put8"]
      | .take obs _ written => fromObs obs ++ (if written then ["sc_put8"] else [])
      | _ => []
  MemoryValues.helperNames.filter used.contains

def usesEnum (plan : Plan) : Bool :=
  plan.helpers.any (·.param == .enum) || plan.steps.any fun step => match step with
    | .data (.first ..) | .data (.second _) => true
    | _ => false

def emit (plan : Plan) : EmittedProgram := Id.run do
  let mut names : Names := {}
  let mut lines : List String := []
  for step in plan.steps do
    let (more, next) := stepLines plan.helpers names step
    lines := lines ++ more
    names := next
  let enumLines := if usesEnum plan then
      ["enum Sc_E {", "    Sc_E0(memory<bytes>, word),", "    Sc_E1(word)", "}", ""] else []
  let source := ["import * from std;", "import * from std.dispatch;",
      "import { mload, mstore, mstore8, shr, mod } from std.opcodes;", ""] ++
    (usedHelpers plan).flatMap MemoryValues.helperLines ++ enumLines ++
    (plan.helpers.zipIdx.flatMap fun (helper, index) => helperLines plan.helpers index helper) ++
    ["contract " ++ contractName ++ " {",
     "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
     "        let sc_x: word = Typedef.rep(input);",
     "        let sc_r: word = 0;"] ++ indent 8 lines ++
    ["        return uint256(sc_r);", "    }", "}"]
  return {
    source := String.intercalate "\n" source ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.MemoryCalls
