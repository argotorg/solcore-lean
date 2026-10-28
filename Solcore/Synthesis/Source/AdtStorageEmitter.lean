import Solcore.Synthesis.Core.AdtStorage
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the enum and struct storage contract. The module declares `ScPair`
when a variant carries it, the enum `ScChoice` and the record `ScRecord`, with
the shape's Word type for every Word field, and std's `StorageGeneric` derives
their layouts; the source never computes a slot. The contract declares the
accumulator, the enum and record fields and the two mappings, and the case's
methods in declaration order. A method converts its parameters, computes the
step of the input plus the accumulator, and branches on the variant and the
field in nested `if`/`else`. Its values are constructor applications of the
step result plus literal offsets; reads `match` the value with one arm per
variant and nested patterns. A mapping entry's field update matches the entry
and writes a whole record, since the pinned front end rejects a field
assignment through a mapping index. This implementation is separate from the
original Core contract's slot arithmetic. No emitter proof covers this
wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AdtStorage

open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.AdtStorage (CheckedPlan Method Shape Payload WordType payloadOffset offsetConstant multiplier)

def emitterVersion : String := "solcore-source-adt-storage-v1"
def wrapperVersion : String := "solcore-word-adt-storage-contract-v1"
def contractName : String := "SynthesizedAdtStorage"
def deployPath : List String := ["SynthesizedAdtStorageDeploy"]
def runtimePath : List String := ["SynthesizedAdtStorageDeploy", "SynthesizedAdtStorage"]

/-- The emitted source of an enum and struct storage contract; its methods are the case's. -/
structure EmittedAdtStorage where
  source : String
  contractName : String
  deployPath : List String
  runtimePath : List String
  deriving Repr, BEq

private def hexLiteral (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

/-- A Word expression as a field value of the shape's Word type. -/
private def wrapped (shape : Shape) (expression : String) : String :=
  match shape.wordType with
  | .word => expression
  | .uint256 => "uint256(" ++ expression ++ ")"

/-- A bound field value of the shape's Word type as a Word expression. -/
private def unwrapped (shape : Shape) (name : String) : String :=
  match shape.wordType with
  | .word => name
  | .uint256 => "Typedef.rep(" ++ name ++ ")"

/-- The value written at offset `offset` of the written value: `r + offset·K`. -/
private def valueAt (shape : Shape) (offset : Nat) : String :=
  wrapped shape (if offset == 0 then "sc_r" else "(sc_r + " ++ hexLiteral (offsetConstant offset) ++ ")")

/-- Variant `index` applied to its payload arguments, or as a pattern over names. -/
private def construct (shape : Shape) (index : Nat) (arguments : List String) : String :=
  let name := "ScChoice.V" ++ toString index
  match shape.variants.getD index (.words 0) with
  | .words 0 => name
  | .words _ => name ++ "(" ++ ", ".intercalate arguments ++ ")"
  | .pair => name ++ "(ScPair(" ++ ", ".intercalate arguments ++ "))"

/-- Variant `index` written as part of a value whose first slot lies `origin`
slots before the enum's first slot. -/
private def constructAt (shape : Shape) (index origin : Nat) : String :=
  construct shape index ((List.range (shape.width index)).map fun field =>
    valueAt shape (origin + payloadOffset shape.count index + field))

/-- The record written with its enum field's variant `index`. -/
private def recordValue (shape : Shape) (index : Nat) : String :=
  "ScRecord(" ++ ", ".intercalate ((List.range AdtStorage.recordFields).map fun field =>
    if field == shape.position then constructAt shape index (shape.fieldOffset field)
    else valueAt shape (shape.fieldOffset field)) ++ ")"

/-- Horner's rule over Word expressions with the multiplier, from zero. -/
private def digest (tokens : List String) : String :=
  match tokens with
  | [] => "0"
  | first :: rest => rest.foldl (fun total token => "((" ++ total ++ " * " ++ hexLiteral multiplier ++ ") + " ++ token ++ ")")
      first

/-- Nested `if`/`else` over `selector` for `count` branches, the last taking
every other Word. -/
private def branches (selector : String) (count indent : Nat) (branch : Nat → List String) : List String :=
  let pad := String.ofList (List.replicate indent ' ')
  let rec go (index fuel depth : Nat) : List String :=
    match fuel with
    | 0 => (branch index).map (pad ++ String.ofList (List.replicate (4 * depth) ' ') ++ ·)
    | fuel + 1 =>
        let inner := pad ++ String.ofList (List.replicate (4 * depth) ' ')
        [inner ++ "if (" ++ selector ++ " == " ++ toString index ++ ") {"] ++
          (branch index).map (inner ++ "    " ++ ·) ++ [inner ++ "} else {"] ++
          go (index + 1) fuel (depth + 1) ++ [inner ++ "}"]
  go 0 (count - 1) 0

private def completion (result : String) : List String :=
  ["        acc = " ++ result ++ ";",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, " ++ result ++ ");",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(" ++ result ++ ");"]

private def header (method : Method) : List String :=
  ["    function " ++ method.name ++ "(" ++ ", ".intercalate (method.parameters.map (· ++ ": uint256")) ++
      ") public returns (uint256) {"] ++
    ((method.parameters.filter (· != "input")).map fun parameter =>
      "        let sc_" ++ parameter ++ ": word = Typedef.rep(" ++ parameter ++ ");") ++
    (if method.reads then [] else ["        let sc_r: word = sc_step((Typedef.rep(input) + acc));"])

/-- The match arms of a decoded enum, each assigning its digest. -/
private def choiceArms (shape : Shape) (target : String) : List String :=
  ["        let sc_digest: word = 0;", "        match (" ++ target ++ ") {"] ++
    ((List.range shape.count).flatMap fun index =>
      let names := (List.range (shape.width index)).map fun field => "sc_a" ++ toString field
      ["            case " ++ construct shape index names ++ " {",
        "                sc_digest = " ++ digest ([toString index] ++ names.map (unwrapped shape)) ++ ";",
        "            }"]) ++ ["        }"]

/-- The match arms of a decoded record, one per variant of its enum field. -/
private def recordArms (shape : Shape) (target : String) : List String :=
  ["        let sc_digest: word = 0;", "        match (" ++ target ++ ") {"] ++
    ((List.range shape.count).flatMap fun index =>
      let names := (List.range (shape.width index)).map fun field => "sc_a" ++ toString field
      let fields := (List.range AdtStorage.recordFields).map fun field =>
        if field == shape.position then (construct shape index names, [toString index] ++ names.map (unwrapped shape))
        else ("sc_x" ++ toString field, [unwrapped shape ("sc_x" ++ toString field)])
      ["            case ScRecord(" ++ ", ".intercalate (fields.map Prod.fst) ++ ") {",
        "                sc_digest = " ++ digest (fields.flatMap Prod.snd) ++ ";",
        "            }"]) ++ ["        }"]

/-- The writes of field `field`, through `assign` of each new field value. -/
private def fieldUpdate (shape : Shape) (field : Nat) (assign : String → String) : List String :=
  let offset := shape.fieldOffset field
  if field == shape.position then
    branches "sc_variant" shape.count 0 fun index => [assign (constructAt shape index offset)]
  else [assign (valueAt shape offset)]

private def fieldBranches (shape : Shape) (indent : Nat) (assign : Nat → String → String) : List String :=
  branches "sc_field" AdtStorage.recordFields indent fun field => fieldUpdate shape field (assign field)

private def methodLines (shape : Shape) (method : Method) : List String :=
  let choice := if method.keyed then "choices[sc_key]" else "choice"
  let record := if method.keyed then "records[sc_key]" else "record"
  let body : List String :=
    match method with
    | .putChoice | .putChoiceAt =>
        branches "sc_variant" shape.count 8 (fun index => [choice ++ " = " ++ constructAt shape index 0 ++ ";"]) ++
          completion "sc_r"
    | .clearChoice | .clearChoiceAt =>
        ["        " ++ choice ++ " = " ++ construct shape shape.clearVariant [] ++ ";"] ++ completion "sc_r"
    | .getChoice | .getChoiceAt => choiceArms shape choice ++ completion "sc_digest"
    | .putRecord | .putRecordAt =>
        branches "sc_variant" shape.count 8 (fun index => [record ++ " = " ++ recordValue shape index ++ ";"]) ++
          completion "sc_r"
    | .setRecord =>
        fieldBranches shape 8 (fun field value => "record.f" ++ toString field ++ " = " ++ value ++ ";") ++
          completion "sc_r"
    | .setRecordAt =>
        let bound := (List.range AdtStorage.recordFields).map fun field => "sc_x" ++ toString field
        let replaced := fun (field : Nat) (value : String) =>
          record ++ " = ScRecord(" ++ ", ".intercalate (bound.zipIdx.map fun (name, index) =>
            if index == field then value else name) ++ ");"
        ["        match (" ++ record ++ ") {", "            case ScRecord(" ++ ", ".intercalate bound ++ ") {"] ++
          fieldBranches shape 16 replaced ++ ["            }", "        }"] ++ completion "sc_r"
    | .getRecord | .getRecordAt => recordArms shape record ++ completion "sc_digest"
  header method ++ body ++ ["    }"]

/-- The type declarations, the Word type for every Word field. -/
private def typeLines (shape : Shape) : List String :=
  let type := shape.wordType.name
  let pair := if shape.variants.contains .pair then
      ["struct ScPair {", "    a: " ++ type ++ ";", "    b: " ++ type ++ ";", "}", ""]
    else []
  let variants := (List.range shape.count).map fun index =>
    "    V" ++ toString index ++
      match shape.variants.getD index (.words 0) with
      | .words 0 => ""
      | .words count => "(" ++ ", ".intercalate (List.replicate count type) ++ ")"
      | .pair => "(ScPair)"
  pair ++ ["enum ScChoice {"] ++ (variants.zipIdx.map fun (line, index) =>
      if index + 1 < variants.length then line ++ "," else line) ++ ["}", "",
    "struct ScRecord {"] ++ ((List.range AdtStorage.recordFields).map fun field =>
      "    f" ++ toString field ++ ": " ++ (if field == shape.position then "ScChoice" else type) ++ ";") ++ ["}", ""]

def emit (plan : CheckedPlan) : Except EmitError EmittedAdtStorage := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", "import * from std.Generic;",
    "import * from std.StorageGeneric;",
    AggregateRenderer.opcodeImportWith ["mstore", "revert_"] (plan.step.helpers ++ [plan.step.entry]), ""] ++
    typeLines plan.shape
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    acc: word;",
    "    choice: ScChoice;",
    "    record: ScRecord;",
    "    choices: mapping(word => ScChoice);",
    "    records: mapping(word => ScRecord);"]
  for method in plan.methods do
    lines := lines ++ [""] ++ methodLines plan.shape method
  lines := lines ++ ["}"]
  return {source := String.intercalate "\n" lines ++ "\n", contractName, deployPath, runtimePath}

end Solcore.Synthesis.Source.AdtStorage
