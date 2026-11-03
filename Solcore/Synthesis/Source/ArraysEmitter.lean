import Solcore.Synthesis.Core.Arrays
import Solcore.Synthesis.Source.IntegersEmitter

/-! The Solcore source of an array plan: the helpers it uses, then
`SynthesizedMemoryArrays.run(uint256)`, with the storage array `sc_st` when
the plan uses it, or `SynthesizedArrayAbi.run` with its `T[]` and
`calldata<T[]>` parameters, which converts the input Word to its values and
indices, runs the steps and folds every observation into `sc_r`, then
returns it or a `T[]`. The source is a function of the plan; nothing here
builds or reads the Core reference. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Arrays

open Solcore.Synthesis.Core.Arrays
open Solcore.Synthesis.Core.Integers (IntType Op)
open Solcore.Synthesis.Source.Integers (convertText intText hexText opSymbol)

def memoryEmitterVersion : String := "solcore-source-memory-arrays-v1"
def memoryWrapperVersion : String := "solcore-memory-arrays-contract-v1"
def memoryContract : String := "SynthesizedMemoryArrays"
def abiEmitterVersion : String := "solcore-source-array-abi-v1"
def abiWrapperVersion : String := "solcore-array-abi-contract-v1"
def abiContract : String := "SynthesizedArrayAbi"

private def indent (count : Nat) (lines : List String) : List String :=
  lines.map fun line => String.ofList (List.replicate count ' ') ++ line

def offsetText (offset : Nat) : String := if offset = 0 then "sc_x" else "(sc_x + " ++ toString offset ++ ")"

def valueDeclaration (type : IntType) (input : ValueInput) (index : Nat) : String :=
  "let sc_v" ++ toString index ++ ": " ++ type.name ++ " = Typedef.abs(" ++
    (if input.raw then offsetText input.offset else convertText type (offsetText input.offset)) ++ ");"

def indexDeclaration (input : IndexInput) (index : Nat) : String :=
  let word := if input.flagged then "(sc_x & " ++ hexText (flag + input.mask) ++ ")"
    else if input.shift = 0 then "(sc_x & " ++ toString input.mask ++ ")"
    else "((sc_x >> " ++ toString input.shift ++ ") & " ++ toString input.mask ++ ")"
  "let sc_k" ++ toString index ++ ": uint256 = uint256(" ++ word ++ ");"

def indexText : Index → String
  | .literal value => toString value
  | .input index => "sc_k" ++ toString index
  | .counter => "sc_i"

/-- A literal index of a slice or a calldata parameter is typed: upstream's
inference leaves `Typedef.rep(s[0])` ambiguous there. -/
def elementIndexText (coll : Coll) (index : Index) : String :=
  match coll, index with
  | .slice _, .literal value | .calldata _, .literal value => "uint256(" ++ toString value ++ ")"
  | _, _ => indexText index

def valueText (type : IntType) : Value → String
  | .input index => "sc_v" ++ toString index
  | .literal index => intText (type.literals.getD index 0)

def lengthText : Length → String
  | .literal value => toString value
  | .input index => "sc_k" ++ toString index

def nameText : Name → String
  | .var index => "sc_a" ++ toString index
  | .param index => "sc_p" ++ toString index

def collText : Coll → String
  | .array name => nameText name
  | .slice index => "sc_s" ++ toString index
  | .storage => "sc_st"
  | .row grid index => "sc_g" ++ toString grid ++ "[" ++ indexText index ++ "]"
  | .calldata index => "sc_p" ++ toString index

def targetText : Target → String
  | .array name => nameText name
  | .storage => "sc_st"
  | .row grid index => "sc_g" ++ toString grid ++ "[" ++ indexText index ++ "]"

def cutText : Cut → String
  | .range start stop => "[" ++ indexText start ++ ":" ++ indexText stop ++ "]"
  | .start start => "[" ++ indexText start ++ ":]"
  | .stop stop => "[:" ++ indexText stop ++ "]"
  | .all => "[:]"

def observationText : Observation → String
  | .length coll => collText coll ++ ".length"
  | .element coll index => collText coll ++ "[" ++ elementIndexText coll index ++ "]"
  | .gridLength grid => "sc_g" ++ toString grid ++ ".length"
  | .sum name => "sc_sum(" ++ nameText name ++ ")"
  | .get coll index => "sc_get(" ++ collText coll ++ ", " ++ indexText index ++ ")"
  | .len coll => "sc_len(" ++ collText coll ++ ")"

def actionLines (type : IntType) : Action → List String
  | .write target index value form =>
      let target := targetText target
      let index := indexText index
      let value := valueText type value
      match form with
      | .plain => [target ++ "[" ++ index ++ "] = " ++ value ++ ";"]
      | .compound op false => [target ++ "[" ++ index ++ "] " ++ opSymbol op ++ "= " ++ value ++ ";"]
      | .compound op true => ["unchecked {", "    " ++ target ++ "[" ++ index ++ "] " ++ opSymbol op ++ "= " ++ value ++ ";", "}"]
      | .put => ["sc_put(lidx(" ++ target ++ ", " ++ index ++ "), " ++ value ++ ");"]
      | .inc => ["sc_inc(lidx(" ++ target ++ ", " ++ index ++ "), " ++ value ++ ");"]
  | .observe observation =>
      ["sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(" ++ observationText observation ++ "));"]

/-- A step's statements; `arrays`, `slices` and `grids` count the names
declared before it. -/
def stepLines (type : IntType) (arrays slices grids : Nat) : Step → List String
  | .alloc length => ["let sc_a" ++ toString arrays ++ ": " ++ type.name ++ "[] = new " ++ type.name ++ "[](" ++
      lengthText length ++ ");"]
  | .literal values => ["let sc_a" ++ toString arrays ++ ": " ++ type.name ++ "[] = [" ++
      ", ".intercalate (values.map (valueText type)) ++ "];"]
  | .alias source => ["let sc_a" ++ toString arrays ++ ": " ++ type.name ++ "[] = " ++ nameText source ++ ";"]
  | .copy slice => ["let sc_a" ++ toString arrays ++ ": " ++ type.name ++ "[] = toArray(sc_s" ++ toString slice ++ ");"]
  | .made left right => ["let sc_a" ++ toString arrays ++ ": " ++ type.name ++ "[] = sc_mk(" ++ valueText type left ++
      ", " ++ valueText type right ++ ");"]
  | .slice base cut => ["let sc_s" ++ toString slices ++ " = " ++ collText base ++ cutText cut ++ ";"]
  | .tail source start => ["let sc_s" ++ toString slices ++ " = sc_tail(" ++ nameText source ++ ", " ++
      indexText start ++ ");"]
  | .grid length => ["let sc_g" ++ toString grids ++ ": " ++ type.name ++ "[][] = new " ++ type.name ++ "[][](" ++
      lengthText length ++ ");"]
  | .gridOf sources => ["let sc_g" ++ toString grids ++ ": " ++ type.name ++ "[][] = [" ++
      ", ".intercalate (sources.map nameText) ++ "];"]
  | .gridLiteral rows => ["let sc_g" ++ toString grids ++ ": " ++ type.name ++ "[][] = [" ++
      ", ".intercalate (rows.map fun row => "[" ++ ", ".intercalate (row.map (valueText type)) ++ "]") ++ "];"]
  | .setRow grid index source => ["sc_g" ++ toString grid ++ "[" ++ indexText index ++ "] = " ++ nameText source ++ ";"]
  | .act action => actionLines type action
  | .fill target value => ["sc_fill(" ++ nameText target ++ ", " ++ valueText type value ++ ");"]
  | .push value => ["sc_st.push(" ++ valueText type value ++ ");"]
  | .pop => ["sc_st.pop();"]
  | .setLength length => ["sc_st.setLength(" ++ lengthText length ++ ");"]
  | .loop over body =>
      ["for (let sc_i: uint256 = 0; sc_i < " ++ collText over ++ ".length; sc_i += 1) {"] ++
        indent 4 (body.flatMap (actionLines type)) ++ ["}"]

def stepsLines (plan : Plan) : List String := Id.run do
  let mut lines : List String := []
  let mut arrays := 0
  let mut slices := 0
  let mut grids := 0
  for step in plan.steps do
    lines := lines ++ stepLines plan.element arrays slices grids step
    match step with
    | .alloc _ | .literal _ | .alias _ | .copy _ | .made .. => arrays := arrays + 1
    | .slice .. | .tail .. => slices := slices + 1
    | .grid _ | .gridOf _ | .gridLiteral _ => grids := grids + 1
    | _ => pure ()
  return lines

def actions (plan : Plan) : List Action := plan.steps.flatMap (·.actions)

def unchecked (plan : Plan) : Bool := (actions plan).any fun
  | .write _ _ _ (.compound _ true) => true
  | _ => false

def uses (plan : Plan) (helper : String) : Bool :=
  match helper with
  | "sc_put" => (actions plan).any (· matches .write _ _ _ .put)
  | "sc_inc" => (actions plan).any (· matches .write _ _ _ .inc)
  | "sc_sum" => (actions plan).any (· matches .observe (.sum _))
  | "sc_fill" => plan.steps.any (· matches .fill ..)
  | "sc_mk" => plan.steps.any (· matches .made ..)
  | "sc_tail" => plan.steps.any (· matches .tail ..)
  | "sc_get" => (actions plan).any (· matches .observe (.get ..))
  | "sc_len" => (actions plan).any (· matches .observe (.len _))
  | _ => false

def imports (plan : Plan) : List String :=
  let type := plan.element
  ["import * from std;", "import * from std.unsigned;"] ++
    (if type.signed then ["import * from std.signed;"] else []) ++
    (if unchecked plan then [if type.signed then "import * from std.unchecked.signed;" else
      "import * from std.unchecked.unsigned;"] else []) ++
    ["import * from std.dispatch;"] ++
    (if type.signed && type.bytes < 32 then ["import { signextend as sc_signextend } from std.opcodes;"] else [])

def helperLines (plan : Plan) : List String :=
  let name := plan.element.name
  let loop := "for (let sc_i: uint256 = 0; sc_i < sc_v.length; sc_i += 1) {"
  let helpers : List (String × List String) := [
    ("sc_put", ["function sc_put(sc_c: memref<" ++ name ++ ">, sc_w: " ++ name ++ ") {",
      "    CanStore.store(sc_c, sc_w);", "}"]),
    ("sc_inc", ["function sc_inc(sc_c: memref<" ++ name ++ ">, sc_w: " ++ name ++ ") {",
      "    CanStore.store(sc_c, (CanStore.load(sc_c) + sc_w));", "}"]),
    ("sc_sum", ["function sc_sum(sc_v: " ++ name ++ "[]) returns (" ++ name ++ ") {",
      "    let sc_t: " ++ name ++ " = 0;", "    " ++ loop, "        sc_t += sc_v[sc_i];", "    }",
      "    return sc_t;", "}"]),
    ("sc_fill", ["function sc_fill(sc_v: " ++ name ++ "[], sc_w: " ++ name ++ ") {", "    " ++ loop,
      "        sc_v[sc_i] = sc_w;", "    }", "}"]),
    ("sc_mk", ["function sc_mk(sc_p: " ++ name ++ ", sc_q: " ++ name ++ ") returns (" ++ name ++ "[]) {",
      "    return [sc_p, sc_q];", "}"]),
    ("sc_tail", ["function sc_tail(sc_v: " ++ name ++ "[], sc_s: uint256) returns (arraySlice<" ++ name ++ "[]>) {",
      "    return sc_v[sc_s:];", "}"]),
    ("sc_get", ["function sc_get<c>(sc_c: c, sc_i: uint256) returns (" ++ name ++ ") where (c, uint256): " ++
      "RValueIdxAccess<" ++ name ++ "> {", "    return ridx(sc_c, sc_i);", "}"]),
    ("sc_len", ["function sc_len<c>(sc_c: c) returns (uint256) where c: Length {", "    return sc_c.length;", "}"])]
  helpers.flatMap fun (helper, lines) => if uses plan helper then lines ++ [""] else []

def parameterText (type : IntType) (param : Param) (index : Nat) : String :=
  "sc_p" ++ toString index ++ ": " ++ (if param.calldata then "calldata<" ++ type.name ++ "[]>" else type.name ++ "[]")

def signature (plan : Plan) : String :=
  "run(" ++ ",".intercalate ((plan.params.map fun _ => plan.element.name ++ "[]") ++ ["uint256"]) ++ ")"

def resultLines (plan : Plan) : List String :=
  match plan.result with
  | .word => ["return uint256(sc_r);"]
  | .array name => ["return " ++ nameText name ++ ";"]
  | .copy slice => ["return toArray(sc_s" ++ toString slice ++ ");"]

def emitWith (contract : String) (plan : Plan) : EmittedProgram :=
  let type := plan.element
  let parameters := plan.params.zipIdx.map fun (param, index) => parameterText type param index
  let result := if plan.result == .word then "uint256" else type.name ++ "[]"
  let body := ["let sc_x: word = Typedef.rep(input);"] ++
    plan.values.zipIdx.map (fun (input, index) => valueDeclaration type input index) ++
    plan.indices.zipIdx.map (fun (input, index) => indexDeclaration input index) ++
    ["let sc_r: word = 0;"] ++ stepsLines plan ++ resultLines plan
  let field := if plan.usesStorage then ["    sc_st: " ++ type.name ++ "[];", ""] else []
  let lines := imports plan ++ [""] ++ helperLines plan ++ ["contract " ++ contract ++ " {"] ++ field ++
    ["    function run(" ++ ", ".intercalate (parameters ++ ["input: uint256"]) ++ ") public returns (" ++ result ++
      ") {"] ++ indent 8 body ++ ["    }", "}"]
  { source := String.intercalate "\n" lines ++ "\n", contractName := contract, methodName := "run",
    methodSignature := signature plan, deployPath := [contract ++ "Deploy"],
    runtimePath := [contract ++ "Deploy", contract] }

def emitMemory (plan : Plan) : EmittedProgram := emitWith memoryContract plan

def emitAbi (plan : Plan) : EmittedProgram := emitWith abiContract plan

end Solcore.Synthesis.Source.Arrays
