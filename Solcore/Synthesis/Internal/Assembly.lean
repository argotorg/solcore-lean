import Solcore.Synthesis.Internal.Functions
import Solcore.Synthesis.Core.Shrink
import Solcore.Core.Wire.Conversions
import Solcore.Frontend.RustHull.Precompiles
import Solcore.Synthesis.Core.Generator
import Solcore.Synthesis.Core.Seed
import Solcore.Synthesis.Internal.Aggregates
import Solcore.Synthesis.Internal.StorageLoops
import Solcore.Synthesis.Internal.Loops

/-!
# Profiles: inline Yul

The profiles `runtime-assembly`, `runtime-assembly-memory`, `runtime-assembly-loops`,
`stateful-assembly-storage-loops` and `stateful-assembly-keccak-loops`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.AssemblyMemory
/-! The original Core reference of an inline Yul memory plan: a step function
and a schedule over the 96-byte window above the free-memory pointer. The
reference keeps no memory. The window is three let-bound Words with byte
placement as shifts and masks, and the optional hash is a let-bound closure
over two read Words built from the Core Keccak-f[1600] permutation and digest
builders of the Hull import path, the builders of the mapping profile's
closure. Nothing here reads the Yul text. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.AssemblyMemory

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Frontend.RustHull

def version : String := "core-assembly-memory-v1"

/-- The window's bytes; word accesses start in 0..64 and byte writes in 0..95. -/
def windowBytes : Nat := 96
def hashLengths : List Nat := [0, 1, 31, 32, 33, 64]
def maximumStages : Nat := 3

inductive Width where
  | word
  | byte
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Width

def name : Width → String
  | .word => "word"
  | .byte => "byte"

def ofString? : String → Option Width
  | "word" => some .word
  | "byte" => some .byte
  | _ => none

end Width

/-- Read a Word, then write the step's result on it as a Word or one byte. -/
structure Stage where
  read : Nat
  width : Width
  write : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

structure Hash where
  offset : Nat
  length : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

structure Schedule where
  stages : List Stage
  final : Nat
  hash : Option Hash
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Schedule

def admitted (schedule : Schedule) : Bool :=
  1 ≤ schedule.stages.length && schedule.stages.length ≤ maximumStages &&
  schedule.stages.all (fun stage => stage.read ≤ 64 &&
    match stage.width with
    | .word => stage.write ≤ 64
    | .byte => stage.write < windowBytes) &&
  schedule.final ≤ 64 &&
  match schedule.hash with
  | none => true
  | some hash => hashLengths.contains hash.length && hash.offset + hash.length ≤ windowBytes

/-- Zero without a hash, else one more than the length's position. -/
def hashRank (schedule : Schedule) : Nat :=
  match schedule.hash with
  | none => 0
  | some hash => hashLengths.idxOf hash.length + 1

def offsets (schedule : Schedule) : List Nat :=
  schedule.stages.flatMap (fun stage => [stage.read, stage.write]) ++ [schedule.final] ++
    (schedule.hash.map (·.offset)).toList

def deltaSum (schedule : Schedule) : Nat := (schedule.offsets.map (· % 32)).sum

end Schedule

/-- Byte `position` of the 64-byte message `first ++ second`, big-endian. -/
private def messageByte (first second : Solcore.Core.Expr) (position : Nat) : Solcore.Core.Expr :=
  if position < 32 then .binary .wordByte (Keccak.number position) first
  else .binary .wordByte (Keccak.number (position - 32)) second

/-- Lane `chunk` of the first `length` message bytes, little-endian as Keccak
absorbs it; bytes past the prefix are absent. -/
private def prefixLane (first second : Solcore.Core.Expr) (length chunk : Nat) : Solcore.Core.Expr :=
  (List.range 8).foldl (fun lane index =>
    if 8 * chunk + index < length then
      .binary .wordOr lane (Keccak.shift (messageByte first second (8 * chunk + index)) (8 * index))
    else lane) (Keccak.number 0)

/-- The absorbed state of one 136-byte rate block holding the first `length`
bytes of `first ++ second`, Ethereum's `0x01` domain byte at offset `length`
and the final `0x80` at offset 135. At length 64 this is the mapping profile's
block. -/
def prefixBlock (first second : Solcore.Core.Expr) (length : Nat) : Solcore.Core.Expr :=
  Keccak.packet ((List.range 25).map fun index =>
    let padding := (if index = length / 8 then 2 ^ (8 * (length % 8)) else 0) +
      (if index = 16 then 2 ^ 63 else 0)
    if 8 * index < length then
      if padding = 0 then prefixLane first second length index
      else .binary .wordOr (prefixLane first second length index) (Keccak.number padding)
    else Keccak.number padding)

/-- `fun (first, second) => keccak256(first ++ second)[..length]` in ordinary Core. -/
def coreHash (length : Nat) : Solcore.Core.Expr :=
  .lambda (.product .word .word) .word
    (.letE (.first (.var 0))
      (.letE (.second (.var 1))
        (.letE (Keccak.permute (prefixBlock (.var 1) (.var 0) length)) (Keccak.digest (.var 0)))))

/-- The closure as a Wire expression. A failed conversion would leave an
ill-typed `Unit` that full admission rejects, never a different hash. -/
def hashClosure (length : Nat) : Expr := (Expr.ofCore? (coreHash length)).getD .unit

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def shl (value : Expr) (bits : Nat) : Expr := .binary .wordShl value (word bits)
private def shr (value : Expr) (bits : Nat) : Expr := .binary .wordShr value (word bits)
private def band (left right : Expr) : Expr := .binary .wordAnd left right
private def bor (left right : Expr) : Expr := .binary .wordOr left right

/-- The first `count` bytes of a Word, and its last `count` bytes. -/
def high (count : Nat) : Nat := 2 ^ 256 - 2 ^ (8 * (32 - count))
def low (count : Nat) : Nat := 2 ^ (8 * count) - 1

/-- Let-bound values in binding order and the binding of each window Word. A
reference is valid in the next initializer or in the final body. -/
private structure Builder where
  bindings : Array Expr := #[]
  words : List Nat := []

namespace Builder

def ref (builder : Builder) (position : Nat) : Expr := .var (builder.bindings.size - 1 - position)

def bind (builder : Builder) (value : Expr) : Builder × Nat :=
  ({builder with bindings := builder.bindings.push value}, builder.bindings.size)

def close (builder : Builder) (body : Expr) : Expr :=
  builder.bindings.foldr (fun value rest => .letE value rest) body

/-- Words past the window are zero. -/
def wordAt (builder : Builder) (index : Nat) : Expr :=
  match builder.words[index]? with
  | some position => builder.ref position
  | none => word 0

def setWord (builder : Builder) (index position : Nat) : Builder :=
  {builder with words := builder.words.set index position}

/-- The big-endian Word at byte `offset` of the window. -/
def load (builder : Builder) (offset : Nat) : Expr :=
  let index := offset / 32
  let delta := offset % 32
  if delta = 0 then builder.wordAt index
  else if index + 1 < 3 then
    bor (shl (builder.wordAt index) (8 * delta)) (shr (builder.wordAt (index + 1)) (8 * (32 - delta)))
  else shl (builder.wordAt index) (8 * delta)

/-- A Word write of the value bound at `value`. -/
def store (builder : Builder) (offset value : Nat) : Builder :=
  let index := offset / 32
  let delta := offset % 32
  if delta = 0 then builder.setWord index value
  else
    let (builder, first) := builder.bind
      (bor (band (builder.wordAt index) (word (high delta))) (shr (builder.ref value) (8 * delta)))
    let builder := builder.setWord index first
    let (builder, second) := builder.bind
      (bor (band (builder.wordAt (index + 1)) (word (low (32 - delta))))
        (shl (builder.ref value) (8 * (32 - delta))))
    builder.setWord (index + 1) second

/-- A byte write of the low byte of the value bound at `value`. -/
def store8 (builder : Builder) (offset value : Nat) : Builder :=
  let index := offset / 32
  let bits := 8 * (31 - offset % 32)
  let (builder, updated) := builder.bind
    (bor (band (builder.wordAt index) (word (2 ^ 256 - 1 - 255 * 2 ^ bits)))
      (shl (band (builder.ref value) (word 255)) bits))
  builder.setWord index updated

end Builder

/-- The reference program of `step`, a closed Word-to-Word lambda, under a
schedule at an input: the closure first when the schedule hashes, then the
step, the input and the prologue Words, then each stage's read, its step
application and its write, and finally the step on the final read, plus the
hash of the Words read at the hash offset and 32 bytes later. -/
def program (step : Expr) (schedule : Schedule) (input : Word) : Program := Id.run do
  let mut builder : Builder := {}
  let mut closure : Option Nat := none
  if let some hash := schedule.hash then
    let (next, position) := builder.bind (hashClosure hash.length)
    builder := next
    closure := some position
  let (next, function) := builder.bind step
  builder := next
  let (next, argument) := builder.bind (.word input)
  builder := next
  let (next, applied) := builder.bind (.apply (builder.ref function) (builder.ref argument))
  builder := next
  let (next, complement) := builder.bind (.unary .wordNot (builder.ref argument))
  builder := {next with words := [argument, applied, complement]}
  for stage in schedule.stages do
    let (next, read) := builder.bind (builder.load stage.read)
    builder := next
    let (next, value) := builder.bind (.apply (builder.ref function) (builder.ref read))
    builder := next
    builder := match stage.width with
      | .word => builder.store stage.write value
      | .byte => builder.store8 stage.write value
  let (next, read) := builder.bind (builder.load schedule.final)
  builder := next
  let result : Expr := .apply (builder.ref function) (builder.ref read)
  let body := match schedule.hash, closure with
    | some hash, some position =>
        .binary .wordAdd result (.apply (builder.ref position)
          (.pair (builder.load hash.offset)
            (if hash.length > 32 then builder.load (hash.offset + 32) else word 0)))
    | _, _ => result
  return {resultType := .word, dataDefinitions := [], body := builder.close body}

end Solcore.Synthesis.Core.AssemblyMemory
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyRenderer
/-! Inline Yul for the checked scalar Word functions of the primitive profile.
`renderYul` prints a whole body as Yul statements inside one `assembly` block;
`renderOperations` keeps Solcore lets, conditionals, literals and `!` and puts
every other operation in its own `assembly` block assigning a fresh Solcore
Word local. Comparisons give Yul's Words 0 and 1, which correspond to Core's
Bools. This is a tested printer, not a source meaning-preservation theorem. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyRenderer

open Solcore.Core.Wire
open Solcore.Synthesis.Core (Target FeatureMask)
open ScalarRenderer (Rendered)

/-- How a function's Solcore and Yul parts mix. -/
inductive Form where
  /-- The whole body in Yul, each Core `if` as a `switch`. -/
  | switch
  /-- The whole body in Yul, each Core `if` as two Yul `if`s. -/
  | branches
  /-- Solcore control flow, each operation in its own `assembly` block. -/
  | operations
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Form

def all : List Form := [.switch, .branches, .operations]

def name : Form → String
  | .switch => "switch"
  | .branches => "if"
  | .operations => "operations"

def ofString? : String → Option Form
  | "switch" => some .switch
  | "if" => some .branches
  | "operations" => some .operations
  | _ => none

end Form

/-- The G0 features both renderers render: every operator and form. -/
def support : FeatureMask := PrimitiveRenderer.support

/-- The Yul builtin of a unary operation. -/
def unaryCall : UnaryOp → Option String
  | .boolNot => some "iszero"
  | .wordNot => some "not"
  | .wordClz => some "clz"
  | _ => none

/-- The Yul builtin of a binary operation, and whether it takes its Core operands
in reverse: Yul shifts take the shift amount first. -/
def binaryCall : BinaryOp → Option (String × Bool)
  | .wordAdd => some ("add", false)
  | .wordSub => some ("sub", false)
  | .wordMul => some ("mul", false)
  | .wordDiv => some ("div", false)
  | .wordMod => some ("mod", false)
  | .wordAnd => some ("and", false)
  | .wordOr => some ("or", false)
  | .wordXor => some ("xor", false)
  | .wordEq => some ("eq", false)
  | .wordGt => some ("gt", false)
  | .wordSgt => some ("sgt", false)
  | .wordShl => some ("shl", true)
  | .wordShr => some ("shr", true)
  | .wordSar => some ("sar", true)
  | .wordByte => some ("byte", false)
  | .wordPow => some ("exp", false)
  | .wordSignExtend => some ("signextend", false)
  | .wordSdiv => some ("sdiv", false)
  | .wordSmod => some ("smod", false)
  | _ => none

def ternaryCall : TernaryOp → String
  | .wordAddMod => "addmod"
  | .wordMulMod => "mulmod"

/-- Comparisons, whose Core results are Bools. -/
def comparison : BinaryOp → Bool
  | .wordEq | .wordGt | .wordSgt => true
  | _ => false

private def line (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def call (callee : String) (arguments : List String) : String :=
  callee ++ "(" ++ String.intercalate ", " arguments ++ ")"

private def yulName (index : Nat) : String := "sc_y" ++ toString index

private def unsupported (name : String) : EmitError := .unsupportedExpression name

/-- Yul statements and the Yul expression of a value. Bindings are nearest
first, as in the original Core function. A conditional's branches stay inside
their own blocks; an operation nests its operands' expressions after their
statements. Every operation is pure, so Yul's argument order cannot be
observed. -/
def renderYul (branches : Bool) (locals : List String) (indent nextId : Nat) :
    Expr → Except EmitError Rendered
  | .word value => .ok ⟨[], toString value.val, nextId⟩
  | .bool value => .ok ⟨[], if value then "1" else "0", nextId⟩
  | .var index => match locals[index]? with
      | some binding => .ok ⟨[], binding, nextId⟩
      | none => .error (.unboundLocal index)
  | .letE initializer body => do
      let value ← renderYul branches locals indent nextId initializer
      let binding := yulName value.nextId
      let rest ← renderYul branches (binding :: locals) indent (value.nextId + 1) body
      return ⟨value.lines ++ [line indent ("let " ++ binding ++ " := " ++ value.value)] ++ rest.lines,
        rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← renderYul branches locals indent nextId condition
      if branches then
        let held := yulName tested.nextId
        let result := yulName (tested.nextId + 1)
        let selected ← renderYul branches locals (indent + 4) (tested.nextId + 2) yes
        let fallback ← renderYul branches locals (indent + 4) selected.nextId no
        return ⟨tested.lines ++ [line indent ("let " ++ held ++ " := " ++ tested.value),
            line indent ("let " ++ result ++ " := 0"), line indent ("if " ++ held ++ " {")] ++
          selected.lines ++ [line (indent + 4) (result ++ " := " ++ selected.value), line indent "}",
            line indent ("if iszero(" ++ held ++ ") {")] ++
          fallback.lines ++ [line (indent + 4) (result ++ " := " ++ fallback.value), line indent "}"],
          result, fallback.nextId⟩
      else
        let result := yulName tested.nextId
        let selected ← renderYul branches locals (indent + 4) (tested.nextId + 1) yes
        let fallback ← renderYul branches locals (indent + 4) selected.nextId no
        return ⟨tested.lines ++ [line indent ("let " ++ result ++ " := 0"),
            line indent ("switch " ++ tested.value), line indent "case 0 {"] ++
          fallback.lines ++ [line (indent + 4) (result ++ " := " ++ fallback.value), line indent "}",
            line indent "default {"] ++
          selected.lines ++ [line (indent + 4) (result ++ " := " ++ selected.value), line indent "}"],
          result, fallback.nextId⟩
  | .unary operation operand => do
      let some callee := unaryCall operation | throw (.unsupportedUnary operation)
      let value ← renderYul branches locals indent nextId operand
      return ⟨value.lines, call callee [value.value], value.nextId⟩
  | .binary operation left right => do
      let some (callee, reversed) := binaryCall operation | throw (.unsupportedBinary operation)
      let first ← renderYul branches locals indent nextId left
      let second ← renderYul branches locals indent first.nextId right
      let arguments := if reversed then [second.value, first.value] else [first.value, second.value]
      return ⟨first.lines ++ second.lines, call callee arguments, second.nextId⟩
  | .ternary operation first second third => do
      let first ← renderYul branches locals indent nextId first
      let second ← renderYul branches locals indent first.nextId second
      let third ← renderYul branches locals indent second.nextId third
      return ⟨first.lines ++ second.lines ++ third.lines,
        call (ternaryCall operation) [first.value, second.value, third.value], third.nextId⟩
  | .unit => .error (unsupported "unit")
  | .integer _ => .error (unsupported "integer")
  | .pair _ _ => .error (unsupported "pair")
  | .first _ => .error (unsupported "first")
  | .second _ => .error (unsupported "second")
  | .lambda _ _ _ => .error (unsupported "lambda")
  | .apply _ _ => .error (unsupported "apply")
  | .inLeft _ _ => .error (unsupported "inLeft")
  | .inRight _ _ => .error (unsupported "inRight")
  | .caseE _ _ _ => .error (unsupported "caseE")
  | .newCell _ _ => .error (unsupported "newCell")
  | .loadCell _ => .error (unsupported "loadCell")
  | .storeCell _ _ => .error (unsupported "storeCell")
  | .construct _ _ => .error (unsupported "construct")
  | .matchData _ _ _ _ => .error (unsupported "matchData")

private def typeName : Target → String
  | .word => "word"
  | .bool => "bool"

private def zero : Target → String
  | .word => "0"
  | .bool => "false"

private def name (index : Nat) : String := "sc_v" ++ toString index

private def bindValue (target : Target) (indent nextId : Nat) (value : String) : Rendered :=
  ⟨[line indent ("let " ++ name nextId ++ ": " ++ typeName target ++ " = " ++ value ++ ";")],
    name nextId, nextId + 1⟩

/-- A fresh Solcore Word local that one `assembly` block assigns. -/
private def assemble (indent nextId : Nat) (expression : String) : Rendered :=
  ⟨[line indent ("let " ++ name nextId ++ ": word = 0;"), line indent "assembly {",
    line (indent + 4) (name nextId ++ " := " ++ expression), line indent "}"], name nextId, nextId + 1⟩

/-- Solcore lets, conditionals, literals and `!` as in the primitive renderer;
every other operation reads Solcore Word locals in its own `assembly` block. A
comparison's Word becomes a Bool through std's `tobool`. -/
def renderOperations (target : Target) (locals : List String) (indent nextId : Nat) :
    Expr → Except EmitError Rendered
  | .word value => .ok (bindValue .word indent nextId (toString value.val))
  | .bool value => .ok (bindValue .bool indent nextId (if value then "true" else "false"))
  | .var index => match locals[index]? with
      | some binding => .ok ⟨[], binding, nextId⟩
      | none => .error (.unboundLocal index)
  | .letE initializer body => do
      let value ← renderOperations .word locals indent nextId initializer
      let binding := bindValue .word indent value.nextId value.value
      let rest ← renderOperations target (binding.value :: locals) indent binding.nextId body
      return ⟨value.lines ++ binding.lines ++ rest.lines, rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← renderOperations .bool locals indent nextId condition
      let result := bindValue target indent tested.nextId (zero target)
      let selected ← renderOperations target locals (indent + 4) result.nextId yes
      let fallback ← renderOperations target locals (indent + 4) selected.nextId no
      return ⟨tested.lines ++ result.lines ++
        [line indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
        [line (indent + 4) (result.value ++ " = " ++ selected.value ++ ";"), line indent "} else {"] ++
        fallback.lines ++ [line (indent + 4) (result.value ++ " = " ++ fallback.value ++ ";"), line indent "}"],
        result.value, fallback.nextId⟩
  | .unary .boolNot operand => do
      let value ← renderOperations .bool locals indent nextId operand
      let result := bindValue .bool indent value.nextId ("(!" ++ value.value ++ ")")
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .unary operation operand => do
      let some callee := unaryCall operation | throw (.unsupportedUnary operation)
      let value ← renderOperations .word locals indent nextId operand
      let result := assemble indent value.nextId (call callee [value.value])
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .binary operation left right => do
      let some (callee, reversed) := binaryCall operation | throw (.unsupportedBinary operation)
      let first ← renderOperations .word locals indent nextId left
      let second ← renderOperations .word locals indent first.nextId right
      let arguments := if reversed then [second.value, first.value] else [first.value, second.value]
      let word := assemble indent second.nextId (call callee arguments)
      if comparison operation then
        let result := bindValue .bool indent word.nextId ("tobool(" ++ word.value ++ ")")
        return ⟨first.lines ++ second.lines ++ word.lines ++ result.lines, result.value, result.nextId⟩
      else
        return ⟨first.lines ++ second.lines ++ word.lines, word.value, word.nextId⟩
  | .ternary operation first second third => do
      let first ← renderOperations .word locals indent nextId first
      let second ← renderOperations .word locals indent first.nextId second
      let third ← renderOperations .word locals indent second.nextId third
      let result := assemble indent third.nextId
        (call (ternaryCall operation) [first.value, second.value, third.value])
      return ⟨first.lines ++ second.lines ++ third.lines ++ result.lines, result.value, result.nextId⟩
  | .unit => .error (unsupported "unit")
  | .integer _ => .error (unsupported "integer")
  | .pair _ _ => .error (unsupported "pair")
  | .first _ => .error (unsupported "first")
  | .second _ => .error (unsupported "second")
  | .lambda _ _ _ => .error (unsupported "lambda")
  | .apply _ _ => .error (unsupported "apply")
  | .inLeft _ _ => .error (unsupported "inLeft")
  | .inRight _ _ => .error (unsupported "inRight")
  | .caseE _ _ _ => .error (unsupported "caseE")
  | .newCell _ _ => .error (unsupported "newCell")
  | .loadCell _ => .error (unsupported "loadCell")
  | .storeCell _ _ => .error (unsupported "storeCell")
  | .construct _ _ => .error (unsupported "construct")
  | .matchData _ _ _ _ => .error (unsupported "matchData")

end Solcore.Synthesis.Source.AssemblyRenderer
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyEmitter
/-! Source emission of the checked scalar Word functions of the primitive
profile partly or wholly as inline Yul. The whole-body forms assign the Solcore
result local from one `assembly` block; the operations form keeps Solcore
control flow. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Assembly

open Solcore.Synthesis.Core (CheckedWordFunction)
open AssemblyRenderer (Form)

def emitterVersion : String := "solcore-source-assembly-v1"
def wrapperVersion : String := "solcore-word-assembly-contract-v1"

/-- The G0 features `emit` renders in every form: every operator and form. -/
def featureSupport := AssemblyRenderer.support
def contractName : String := "SynthesizedAssembly"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedAssemblyDeploy"]
def runtimePath : List String := ["SynthesizedAssemblyDeploy", "SynthesizedAssembly"]

/-- The function body's statements and the Solcore Word that `run` returns. -/
def body (form : Form) (function : CheckedWordFunction) : Except EmitError (List String × String) := do
  match form with
  | .operations =>
      let rendered ← AssemblyRenderer.renderOperations .word ["sc_input"] 8 0 function.body
      return (rendered.lines, rendered.value)
  | .switch | .branches =>
      let rendered ← AssemblyRenderer.renderYul (form == .branches) ["sc_input"] 12 0 function.body
      return (["        let sc_out: word = 0;", "        assembly {"] ++ rendered.lines ++
        ["            sc_out := " ++ rendered.value, "        }"], "sc_out")

def emit (form : Form) (function : CheckedWordFunction) : Except EmitError EmittedProgram := do
  let (statements, value) ← body form function
  let lines := ["import * from std;", "import * from std.dispatch;", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ statements ++
    ["        return uint256(" ++ value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Assembly
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyCases
/-! An inline Yul case retains the independently checked original Core
function of the primitive profile and the form that renders it. Generation
repeats the primitive profile's steps, so its Core reference is unchanged, and
draws the form from a hash of the seed. Saved observations never supply the
oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Assembly
open Lean Solcore.Core Solcore.Synthesis.Core
open AssemblyRenderer (Form)

def caseSchema : String := "solcore-lean.semantic-assembly-case.v1"
def planSchema : String := "solcore-lean.assembly-plan.v1"
def profileVersion : String := "runtime-assembly-v1/form-seed-v1"

/-- A checked primitive function and the form that renders it. -/
structure CheckedPlan where
  function : CheckedWordFunction
  form : Form

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.function.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("functionProgram", Wire.encodeProgram plan.function.program),
  ("form", toJson plan.form.name)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported assembly plan schema"
  let function ← Primitive.checkedFunction (← json.getObjVal? "functionProgram")
  let some form := Form.ofString? (← json.getObjValAs? String "form") |
    throw "assembly form must be switch, if or operations"
  let plan : CheckedPlan := ⟨function, form⟩
  unless json == planJson plan do
    throw "saved assembly plan differs from its canonical checked representation"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ 512 do
    throw "applied assembly function exceeds the 512-node case limit"
  return plan

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("assemblyPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionProfileVersion", toJson Primitive.profileVersion),
    ("functionVersion", toJson wordFunctionVersion),
    ("abstractionVersion", toJson abstractionVersion),
    ("generatorVersion", toJson (Primitive.generatorVersionFor revision)),
    ("baseGeneratorVersion", toJson revision.version),
    ("boundaryVersion", toJson Primitive.boundaryVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson ((features plan.function.body).map featureName))]),
  ("contract", Primitive.contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", Primitive.observe plan.function input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (plan.function.instantiate input) ≤ 512 do
    throw "applied assembly function exceeds the 512-node case limit"
  let emitted ← (emit plan.form plan.function).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Every origin keeps the canonical applied function of its plan. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic assembly case schema"
  let plan ← checkedPlan (← json.getObjVal? "assemblyPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.function.instantiate input) do
    throw "saved Core program differs from its assembly plan's function and runtime input"
  return ⟨plan, input⟩

/-- Separates the form stream from other uses of a case seed. -/
private def formDomain : UInt64 := 0x617373656d626c01

/-- A SplitMix64 hash of the seed, so that consecutive seeds vary in form
independently of the primitive function. -/
def formFor (seed : Seed) : Form :=
  Form.all[(GeneratorV2.mix (seed.toUInt64 ^^^ formDomain)).toNat % Form.all.length]?.getD .switch

/-- The steps of the primitive profile's generation, repeated: the same G0
program under the same swarm mask, then the same literal abstraction. A
registered test requires both profiles' functions to agree. -/
def primitiveFunction (seed : Seed) (nodes : Nat) (revision : GeneratorRevision) :
    Except String (GeneratedProgram × Nat × CheckedWordFunction) := do
  unless Primitive.minimumProgramNodes ≤ nodes && nodes ≤ 512 do
    throw "complete primitive program budget must be between the profile minimum and 512"
  let mask := revision.caseMask seed featureSupport
  let generated ← (generate {seed, maxProgramNodes := nodes - Primitive.appliedOverhead, revision, mask}).mapError reprStr
  let count := literalCount generated.program.body
  unless count > 0 do throw "generated body has no Word literal to abstract"
  let literalIndex := seed.toNat % count
  let some function := CheckedWordFunction.fromProgram? generated.checkedProgram literalIndex |
    throw "literal abstraction did not produce a checked Word function"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ nodes do
    throw "applied primitive function exceeds its complete program budget"
  return (generated, literalIndex, function)

/-- The generated origin before its input index, validation fuel, input
selection and acceptance filter. -/
private def generatedOrigin (seed : Seed) (nodes : Nat) (generated : GeneratedProgram)
    (literalIndex : Nat) (form : Form) : List (String × Json) := [
  ("kind", toJson "assembly-generated"), ("seed", toJson (toString seed.toNat)),
  ("finalSeed", toJson (toString generated.finalSeed.toNat)), ("maxProgramNodes", toJson nodes),
  ("baseProgramNodes", toJson generated.maxProgramNodes), ("literalIndex", toJson literalIndex),
  ("form", toJson form.name)]

/-- Attempt limits count functions; case limits count individual runtime inputs.
The exclusions are those of the primitive profile, in its order. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary)
    (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (generated, literalIndex, function) ← primitiveFunction seed nodes revision
        let plan : CheckedPlan := ⟨function, formFor seed⟩
        let emitted ← (emit plan.form plan.function).mapError
          (fun error => "unsupported source primitive: " ++ reprStr error)
        Primitive.inputSensitive function fuel acceptance
        return (generated, literalIndex, plan, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)),
            ("stage", toJson "assembly-profile"), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error.startsWith "unsupported source primitive:" then "unsupported-operation"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (generated, literalIndex, plan, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs Primitive.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := Json.mkObj (generatedOrigin seed nodes generated literalIndex plan.form ++
                [("inputIndex", toJson inputIndex), ("validationFuel", toJson fuel)])
              cases := cases.push
                (makeCase plan input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance "baseGeneratorVersion"
  for (name, expected) in [
      ("generatorVersion", Primitive.generatorVersionFor revision), ("profileVersion", profileVersion),
      ("functionProfileVersion", Primitive.profileVersion),
      ("baseGeneratorVersion", revision.version), ("boundaryVersion", Primitive.boundaryVersion),
      ("functionVersion", wordFunctionVersion), ("abstractionVersion", abstractionVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan.form admitted.plan.function).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the assembly plan"
  unless (← json.getObjVal? "contract") == Primitive.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the assembly wrapper"
  unless (← provenance.getObjVal? "features") ==
      toJson ((features admitted.plan.function.body).map featureName) do
    throw "saved features differ from the original Core function"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "assembly-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported assembly case origin"
  if kind = "assembly-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless Primitive.minimumProgramNodes ≤ nodes && nodes ≤ 512 do
      throw "saved generation budget exceeds profile limits"
    let (generated, literalIndex, function) ← primitiveFunction (Seed.ofNat seed) nodes revision
    unless admitted.plan.form == formFor (Seed.ofNat seed) do
      throw "saved assembly form differs from its generation seed"
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.plan.function.program do
      throw "saved function differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Primitive.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    Primitive.inputSensitive function validationFuel acceptance
    unless origin == acceptance.record (inputSelection.record (Json.mkObj (
        generatedOrigin (Seed.ofNat seed) nodes generated literalIndex admitted.plan.form ++
        [("inputIndex", toJson inputIndex), ("validationFuel", toJson validationFuel)]))) do
      throw "generated assembly provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported assembly provenance is not canonical"
  else
    let parentProgram ← origin.getObjVal? "parentProgram"
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent ← caseProgram (Json.mkObj [("schema", toJson caseSchema), ("assemblyPlan", parentPlan),
      ("program", parentProgram), ("input", toJson parentText)])
    unless parent.plan.form == admitted.plan.form do
      throw "saved assembly reduction changes its parent's form"
    unless (complexity admitted.program.body).isStrictlySmaller (complexity parent.program.body) do
      throw "saved assembly reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentProgram", parentProgram),
        ("parentPlan", parentPlan), ("parentInput", toJson parentText)] do
      throw "reduced assembly provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel revision mask
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "assembly provenance contains unexpected fields"
  return fresh

/-- A primitive reduction of the Core function, rendered in the parent's form. -/
structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameForm : candidate.plan.form = source.plan.form
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

/-- The primitive reductions: G0 shrinking under the abstraction and smaller
inputs, each sealed by the full checker and strictly smaller. Keeping the form
changes no Core node. -/
def reductions (source : CheckedInput) : List (Reduction source) :=
  (Primitive.reductions ⟨source.plan.function, source.input⟩).map fun reduced =>
    ⟨⟨⟨reduced.candidate.function, source.plan.form⟩, reduced.candidate.input⟩, rfl, reduced.strict⟩

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance "baseGeneratorVersion"
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Assembly
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyStorageForm
/-! The rendering forms shared by the inline Yul storage and Keccak loops. In
every form the loop is a Solcore `while` loop around one Solcore step call,
since a Yul block can call only builtins and its own Yul functions; the forms
differ in how the iteration's storage, hash and log work is split into
`assembly` blocks around that call. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyStorage

open Solcore.Core.Wire (Expr)
open Solcore.Synthesis.Core.Aggregates (CheckedDAG)

/-- How an iteration's Yul blocks surround the step call. -/
inductive Form where
  /-- A read block before the call and a write block after it, which computes
  the slot again; the counter advances in Solcore. -/
  | split
  /-- The read block assigns the slot to a Solcore local that the write block
  uses; the write block advances the counter. -/
  | carried
  /-- One block after the call writes, advances the counter and reads the next
  iteration; a block before the loop reads the first. -/
  | pipelined
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Form

def all : List Form := [.split, .carried, .pipelined]

def name : Form → String
  | .split => "split"
  | .carried => "carried"
  | .pipelined => "pipelined"

def ofString? : String → Option Form
  | "split" => some .split
  | "carried" => some .carried
  | "pipelined" => some .pipelined
  | _ => none

theorem ofString?_name (form : Form) : ofString? form.name = some form := by
  cases form <;> rfl

end Form

/-- A SplitMix64 hash of the seed in a profile's own domain, so that
consecutive seeds vary in form independently of the plan. -/
def formFor (domain : UInt64) (seed : Solcore.Synthesis.Core.Seed) : Form :=
  Form.all[(Solcore.Synthesis.Core.GeneratorV2.mix (seed.toUInt64 ^^^ domain)).toNat % Form.all.length]?.getD .split

/-- The step's helpers as `sc_fn<k>` and its entry as `sc_step`, rendered as
in the parent loop profiles. -/
def stepLines (step : CheckedDAG) : Except EmitError (List String) := do
  let mut names : List String := []
  let mut lines : List String := []
  for (body, index) in step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 step.entry
  let result ← AggregateRenderer.requireValue entry
  return lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", ""]

/-- The imports: std, its dispatch, and `std.opcodes` only for the step's
opcode aliases. -/
def importLines (step : CheckedDAG) : List String :=
  ["import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (step.helpers ++ [step.entry]) ++ [""]

end Solcore.Synthesis.Source.AssemblyStorage
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyKeccakLoopEmitter
/-! Emit the Keccak-loop protocol with every storage access, entry hash and log
in inline Yul. The contract keeps the Keccak-loop profile's fields, `acc` at
slot zero and `entries` at base slot one, which fix the layout the blocks
address directly: the entry of `key` lies at `keccak256(1 ++ key)`, hashed
from a 64-byte buffer that the first block reserves from the free-memory
pointer. The loop is the source while loop around one Solcore step call; each
iteration reads its entry and slot zero into the step argument, writes the
result to the entry and then to slot zero, and logs it from the buffer with
the counter and the key as topics. After the loop one block forms the result
and reverts it from the buffer for odd flags. This implementation is separate
from the finite ordinal guards of the checked Core reference. No emitter proof
covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyKeccakLoop

open Solcore.Synthesis.Core.KeccakLoop (CheckedPlan)
open Solcore.Synthesis.Source.AssemblyStorage (Form)

def emitterVersion : String := "solcore-source-assembly-keccak-loops-v1"
def wrapperVersion : String := "solcore-word-assembly-keccak-loops-contract-v1"
def contractName : String := "SynthesizedAssemblyKeccakLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedAssemblyKeccakLoopsDeploy"]
def runtimePath : List String := ["SynthesizedAssemblyKeccakLoopsDeploy", "SynthesizedAssemblyKeccakLoops"]

/-- The Word locals besides flags, input, limit and base, all declared before the loop. -/
def locals : Form → List String
  | .split => ["sc_counter", "sc_key", "sc_sum", "sc_value", "sc_result", "sc_ptr"]
  | .carried | .pipelined => ["sc_counter", "sc_key", "sc_slot", "sc_sum", "sc_value", "sc_result", "sc_ptr"]

/-- The key of the counter's iteration, then its entry slot hashed from the
buffer, at the given indentation. -/
def keyLines (indent : String) (keyMask : Nat) : List String := [
  indent ++ "sc_key := or(sc_base, and(sc_counter, " ++ toString keyMask ++ "))",
  indent ++ "mstore(sc_ptr, 1)",
  indent ++ "mstore(add(sc_ptr, 32), sc_key)"]

/-- The key, its entry slot in `sc_slot` and the step argument. -/
def readLines (indent : String) (keyMask : Nat) : List String :=
  keyLines indent keyMask ++ [
    indent ++ "sc_slot := keccak256(sc_ptr, 64)",
    indent ++ "sc_sum := add(add(sload(sc_slot), sload(0)), sc_input)"]

/-- The two writes and the log of the iteration's value. -/
def writeLines (indent slot : String) : List String := [
  indent ++ "sstore(" ++ slot ++ ", sc_value)",
  indent ++ "sstore(0, sc_value)",
  indent ++ "mstore(sc_ptr, sc_value)",
  indent ++ "log2(sc_ptr, 32, sc_counter, sc_key)"]

def loopLines (form : Form) (keyMask : Nat) : List String :=
  match form with
  | .split => [
      "        while (sc_limit > sc_counter) {",
      "            assembly {"] ++
      keyLines "                " keyMask ++ [
      "                sc_sum := add(add(sload(keccak256(sc_ptr, 64)), sload(0)), sc_input)",
      "            }",
      "            sc_value = sc_step(sc_sum);",
      "            assembly {",
      "                mstore(sc_ptr, 1)",
      "                mstore(add(sc_ptr, 32), sc_key)"] ++
      writeLines "                " "keccak256(sc_ptr, 64)" ++ [
      "            }",
      "            sc_counter = (sc_counter + 1);",
      "        }"]
  | .carried => [
      "        while (sc_limit > sc_counter) {",
      "            assembly {"] ++
      readLines "                " keyMask ++ [
      "            }",
      "            sc_value = sc_step(sc_sum);",
      "            assembly {"] ++
      writeLines "                " "sc_slot" ++ [
      "                sc_counter := add(sc_counter, 1)",
      "            }",
      "        }"]
  | .pipelined => [
      "        assembly {",
      "            if gt(sc_limit, sc_counter) {"] ++
      readLines "                " keyMask ++ [
      "            }",
      "        }",
      "        while (sc_limit > sc_counter) {",
      "            sc_value = sc_step(sc_sum);",
      "            assembly {"] ++
      writeLines "                " "sc_slot" ++ [
      "                sc_counter := add(sc_counter, 1)",
      "                if gt(sc_limit, sc_counter) {"] ++
      readLines "                    " keyMask ++ [
      "                }",
      "            }",
      "        }"]

def emit (form : Form) (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let steps ← AssemblyStorage.stepLines plan.step
  let lines := AssemblyStorage.importLines plan.step ++ steps ++ [
    "contract " ++ contractName ++ " {",
    "    acc: word;",
    "    entries: mapping(word => word);",
    "",
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_base: word = (sc_input & ~7);"] ++
    (locals form).map (fun name => "        let " ++ name ++ ": word = 0;") ++ [
    "        assembly {",
    "            sc_ptr := mload(64)",
    "            mstore(64, add(sc_ptr, 64))",
    "        }"] ++
    loopLines form plan.keyMask ++ [
    "        assembly {",
    "            sc_result := add(sload(0), sc_limit)",
    "            if and(sc_flags, 1) {",
    "                mstore(sc_ptr, sc_result)",
    "                revert(sc_ptr, 32)",
    "            }",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.AssemblyKeccakLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyKeccakLoopCases
/-! An inline Yul Keccak-loop case retains the Keccak-loop profile's checked
plan, transactions and original Core contract, and the form that renders them.
Generation repeats that profile's steps, so its Core reference, observation and
exclusions are unchanged, and draws the form from a hash of the seed.
Reductions are that profile's, each in the parent case's form. Saved outputs
are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyKeccakLoop
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Source.AssemblyStorage (Form)
open Solcore.Synthesis.Stateful.KeccakLoopExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-assembly-keccak-loop-case.v1"
def planSchema : String := "solcore-lean.assembly-keccak-loop-plan.v1"
def profileVersion : String := "stateful-assembly-keccak-loops-v1/form-seed-v1"
def corpusSchema : String := "solcore-lean.semantic-assembly-keccak-loop-corpus.v1"

/-- A checked Keccak-loop scenario and the form that renders it. -/
structure CheckedScenario where
  loop : KeccakLoop.CheckedScenario
  form : Form

def CheckedScenario.plan (scenario : CheckedScenario) : Solcore.Synthesis.Core.KeccakLoop.CheckedPlan :=
  scenario.loop.plan

def CheckedScenario.transactions (scenario : CheckedScenario) : List Transaction := scenario.loop.transactions

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.loop.program

def planJson (plan : Solcore.Synthesis.Core.KeccakLoop.CheckedPlan) (form : Form) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("mask", toJson plan.mask), ("keyMask", toJson plan.keyMask), ("form", toJson form.name)]

/-- The Keccak-loop profile checks the step and both masks; then the form and
the whole saved plan must be canonical. -/
def checkedPlan (json : Json) : Except String (Solcore.Synthesis.Core.KeccakLoop.CheckedPlan × Form) := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported assembly Keccak-loop plan schema"
  let plan ← KeccakLoop.checkedPlan (Json.mkObj [("schema", toJson KeccakLoop.planSchema),
    ("stepProgram", ← json.getObjVal? "stepProgram"), ("mask", ← json.getObjVal? "mask"),
    ("keyMask", ← json.getObjVal? "keyMask")])
  let some form := Form.ofString? (← json.getObjValAs? String "form") |
    throw "assembly Keccak-loop form must be split, carried or pipelined"
  unless json == planJson plan form do
    throw "saved assembly Keccak-loop plan differs from its canonical checked representation"
  return (plan, form)

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("keccakLoopPlan", planJson scenario.plan scenario.form),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", KeccakLoop.transactionsJson scenario.plan.mask scenario.transactions),
    ("initialState", KeccakLoop.initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson scenario.loop.observedSlots),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("loopProfileVersion", toJson KeccakLoop.profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.KeccakLoop.version),
      ("framingVersion", toJson Solcore.Synthesis.Core.EventLog.framingVersion),
      ("templateVersion", toJson KeccakLoop.templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", KeccakLoop.contractJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.form scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- The case in the Keccak-loop profile's shape must pass that profile's
checks: its transactions, the canonical Core program, the empty initial state,
the fuel and the derived observed slots. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic assembly Keccak-loop case schema"
  let (plan, form) ← checkedPlan (← json.getObjVal? "keccakLoopPlan")
  let loop ← KeccakLoop.caseProgram ((json.setObjVal! "schema" (toJson KeccakLoop.caseSchema)).setObjVal!
    "keccakLoopPlan" (KeccakLoop.planJson plan))
  return ⟨loop, form⟩

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  KeccakLoop.observe scenario.loop bindings fuel

/-- Separates the form stream from other uses of a case seed. -/
private def formDomain : UInt64 := 0x616b636c6f6f7001

def formFor (seed : Seed) : Form := AssemblyStorage.formFor formDomain seed

/-- The Keccak-loop profile's scenario and generated origin for the seed, with
the seed's form. A registered test requires both profiles to agree. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  let (loop, origin) ← KeccakLoop.generatedScenario seed nodes revision transactions
  let form := formFor seed
  return (⟨loop, form⟩,
    (origin.setObjVal! "kind" (toJson "assembly-keccak-loop-generated")).setObjVal! "form" (toJson form.name))

/-- Attempts count complete scenario candidates. The exclusions are those of
the Keccak-loop profile, in its order; fuel exhaustion is an inconclusive
exclusion. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.form scenario.plan).mapError reprStr
        KeccakLoop.validateGenerated scenario.loop fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "Keccak-loop history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "assembly-keccak-loop-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- A sealed Keccak-loop reduction of the source scenario, kept in its form. -/
structure Reduction (source : CheckedScenario) where private mk ::
  loop : KeccakLoop.Reduction source.loop

def Reduction.candidate {source : CheckedScenario} (reduced : Reduction source) : CheckedScenario :=
  ⟨reduced.loop.candidate, source.form⟩

/-- The Keccak-loop profile's reductions, in their order, each in the form of
the source case. -/
def reductions (source : CheckedScenario) : List (Reduction source) :=
  (KeccakLoop.reductions source.loop).map fun reduced => ⟨reduced⟩

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan parent.form),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentTransactions", KeccakLoop.transactionsJson parent.plan.mask parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("loopProfileVersion", KeccakLoop.profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.KeccakLoop.version),
      ("framingVersion", Solcore.Synthesis.Core.EventLog.framingVersion),
      ("templateVersion", KeccakLoop.templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.form admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from assembly Keccak-loop plan emission"
  unless (← json.getObjVal? "contract") == KeccakLoop.contractJson emitted do
    throw "saved contract metadata differs from assembly Keccak-loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "assembly-keccak-loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes")
      revision (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated assembly Keccak-loop provenance"
    unless planJson expected.plan expected.form == planJson admitted.plan admitted.form &&
        KeccakLoop.transactionsJson expected.plan.mask expected.transactions ==
          KeccakLoop.transactionsJson admitted.plan.mask admitted.transactions do
      throw "saved plan, form or transaction sequence differs from its generation seed"
    KeccakLoop.validateGenerated expected.loop validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let (parentPlan, parentForm) ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← KeccakLoop.decodeTransactions parentPlan.mask (← origin.getObjVal? "parentTransactions")
    let parent : CheckedScenario := ⟨← KeccakLoop.checkedScenario parentPlan parentTransactions, parentForm⟩
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its plan"
    unless parentForm == admitted.form do throw "reduction changes the parent case's form"
    unless (KeccakLoop.sealReduction parent.loop admitted.plan.step admitted.plan.mask admitted.plan.keyMask
        admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported assembly Keccak-loop case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced =>
    emitCase reduced.candidate (reducedOrigin source) fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.AssemblyKeccakLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyLoopRenderer
/-! Inline Yul for scalar call-graph steps: helpers become Yul functions and a
body becomes Yul statements. Expressions render as in the `switch` form of
`AssemblyRenderer.renderYul`, and a call names its helper's Yul function. With
`pairs`, every helper returns its result and its argument, and each call binds
both before its expression uses the first. `renderTail` assigns a function's
`sc_ret` and returns through `leave` after the then branch of every conditional
in tail position. This is a tested printer, not a source meaning-preservation
theorem. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyLoopRenderer

open Solcore.Core.Wire
open ScalarRenderer (Rendered)
open AssemblyRenderer (unaryCall binaryCall ternaryCall)

def line (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def call (callee : String) (arguments : List String) : String :=
  callee ++ "(" ++ String.intercalate ", " arguments ++ ")"

def yulName (index : Nat) : String := "sc_y" ++ toString index

private def unsupported (name : String) : EmitError := .unsupportedExpression name

/-- Yul statements and the Yul expression of a value. Word locals are nearest
first, and the helpers' Yul function names follow them, also nearest first, as
in the original Core graph. A conditional's branches stay inside their own
blocks, so a call in a branch runs only there. Every operation and helper is
pure, so Yul's argument order cannot be observed. -/
def render (functions : List String) (pairs : Bool) (locals : List String) (indent nextId : Nat) :
    Expr → Except EmitError Rendered
  | .word value => .ok ⟨[], toString value.val, nextId⟩
  | .bool value => .ok ⟨[], if value then "1" else "0", nextId⟩
  | .var index => match locals[index]? with
      | some binding => .ok ⟨[], binding, nextId⟩
      | none => .error (.unboundLocal index)
  | .letE initializer body => do
      let value ← render functions pairs locals indent nextId initializer
      let binding := yulName value.nextId
      let rest ← render functions pairs (binding :: locals) indent (value.nextId + 1) body
      return ⟨value.lines ++ [line indent ("let " ++ binding ++ " := " ++ value.value)] ++ rest.lines,
        rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← render functions pairs locals indent nextId condition
      let result := yulName tested.nextId
      let selected ← render functions pairs locals (indent + 4) (tested.nextId + 1) yes
      let fallback ← render functions pairs locals (indent + 4) selected.nextId no
      return ⟨tested.lines ++ [line indent ("let " ++ result ++ " := 0"),
          line indent ("switch " ++ tested.value), line indent "case 0 {"] ++
        fallback.lines ++ [line (indent + 4) (result ++ " := " ++ fallback.value), line indent "}",
          line indent "default {"] ++
        selected.lines ++ [line (indent + 4) (result ++ " := " ++ selected.value), line indent "}"],
        result, fallback.nextId⟩
  | .unary operation operand => do
      let some callee := unaryCall operation | throw (.unsupportedUnary operation)
      let value ← render functions pairs locals indent nextId operand
      return ⟨value.lines, call callee [value.value], value.nextId⟩
  | .binary operation left right => do
      let some (callee, reversed) := binaryCall operation | throw (.unsupportedBinary operation)
      let first ← render functions pairs locals indent nextId left
      let second ← render functions pairs locals indent first.nextId right
      let arguments := if reversed then [second.value, first.value] else [first.value, second.value]
      return ⟨first.lines ++ second.lines, call callee arguments, second.nextId⟩
  | .ternary operation first second third => do
      let first ← render functions pairs locals indent nextId first
      let second ← render functions pairs locals indent first.nextId second
      let third ← render functions pairs locals indent second.nextId third
      return ⟨first.lines ++ second.lines ++ third.lines,
        call (ternaryCall operation) [first.value, second.value, third.value], third.nextId⟩
  | .apply (.var index) argument => do
      if index < locals.length then throw (unsupported "apply")
      let some callee := functions[index - locals.length]? | throw (unsupported "apply")
      let value ← render functions pairs locals indent nextId argument
      if pairs then
        let result := yulName value.nextId
        return ⟨value.lines ++ [line indent ("let " ++ result ++ ", " ++ yulName (value.nextId + 1) ++ " := " ++
          call callee [value.value])], result, value.nextId + 2⟩
      else return ⟨value.lines, call callee [value.value], value.nextId⟩
  | .apply _ _ => .error (unsupported "apply")
  | .unit => .error (unsupported "unit")
  | .integer _ => .error (unsupported "integer")
  | .pair _ _ => .error (unsupported "pair")
  | .first _ => .error (unsupported "first")
  | .second _ => .error (unsupported "second")
  | .lambda _ _ _ => .error (unsupported "lambda")
  | .inLeft _ _ => .error (unsupported "inLeft")
  | .inRight _ _ => .error (unsupported "inRight")
  | .caseE _ _ _ => .error (unsupported "caseE")
  | .newCell _ _ => .error (unsupported "newCell")
  | .loadCell _ => .error (unsupported "loadCell")
  | .storeCell _ _ => .error (unsupported "storeCell")
  | .construct _ _ => .error (unsupported "construct")
  | .matchData _ _ _ _ => .error (unsupported "matchData")

/-- A function body that assigns `sc_ret` on every path. A conditional in tail
position becomes a Yul `if` whose then branch assigns and leaves, followed by
its else branch at the same depth; a `let` keeps its body in tail position.
Returns the statements and the next free temporary. -/
def renderTail (functions : List String) (locals : List String) (indent nextId : Nat) :
    Expr → Except EmitError (List String × Nat)
  | .letE initializer body => do
      let value ← render functions false locals indent nextId initializer
      let binding := yulName value.nextId
      let (rest, next) ← renderTail functions (binding :: locals) indent (value.nextId + 1) body
      return (value.lines ++ [line indent ("let " ++ binding ++ " := " ++ value.value)] ++ rest, next)
  | .ifE condition yes no => do
      let tested ← render functions false locals indent nextId condition
      let (selected, next) ← renderTail functions locals (indent + 4) tested.nextId yes
      let (fallback, next) ← renderTail functions locals indent next no
      return (tested.lines ++ [line indent ("if " ++ tested.value ++ " {")] ++ selected ++
        [line (indent + 4) "leave", line indent "}"] ++ fallback, next)
  | expression => do
      let value ← render functions false locals indent nextId expression
      return (value.lines ++ [line indent ("sc_ret := " ++ value.value)], value.nextId)

end Solcore.Synthesis.Source.AssemblyLoopRenderer
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyLoopEmitter
/-! Source emission of a scalar call-graph loop plan as one inline Yul block:
the step's helpers as Yul functions and the loop as a Yul `for` loop in one of
five forms. The Core reference stays the plan's finite ordinal guards; no
emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyLoop

open Solcore.Core.Wire (Expr)
open Solcore.Synthesis.Core.CallGraphLoop (CheckedPlan)
open AssemblyLoopRenderer (line)

def emitterVersion : String := "solcore-source-assembly-loops-v1"
def wrapperVersion : String := "solcore-word-assembly-loops-contract-v1"
def contractName : String := "SynthesizedAssemblyLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedAssemblyLoopsDeploy"]
def runtimePath : List String := ["SynthesizedAssemblyLoopsDeploy", "SynthesizedAssemblyLoops"]

/-- How the Yul `for` loop runs the step, and how helpers return. -/
inductive Form where
  /-- Bounded by the loop condition. -/
  | bounded
  /-- Exited by `break` from a constant condition. -/
  | breaks
  /-- Bounded by the mask from a zero-argument function, skipping the step with
  `continue` once the counter reaches the limit. -/
  | continues
  /-- Inside a two-argument function exited by `leave`; helpers return through
  `leave` from conditionals in tail position. -/
  | leaves
  /-- Helpers return two values, and a two-argument, two-result step function
  also advances the counter. -/
  | pair
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Form

def all : List Form := [.bounded, .breaks, .continues, .leaves, .pair]

def name : Form → String
  | .bounded => "for"
  | .breaks => "break"
  | .continues => "continue"
  | .leaves => "leave"
  | .pair => "pair"

def ofString? : String → Option Form
  | "for" => some .bounded
  | "break" => some .breaks
  | "continue" => some .continues
  | "leave" => some .leaves
  | "pair" => some .pair
  | _ => none

end Form

def helperName (index : Nat) : String := "sc_fn" ++ toString index

/-- The helpers as Yul functions in declaration order, their names nearest first
for later bodies, and the next free temporary. -/
def helperFunctions (form : Form) (bodies : List Expr) :
    Except EmitError (List String × List String × Nat) := do
  let mut names : List String := []
  let mut lines : List String := []
  let mut nextId := 0
  for (body, index) in bodies.zipIdx do
    let name := helperName index
    match form with
    | .leaves =>
        let (statements, next) ← AssemblyLoopRenderer.renderTail names ["sc_arg"] 16 nextId body
        lines := lines ++ [line 12 ("function " ++ name ++ "(sc_arg) -> sc_ret {")] ++ statements ++
          [line 12 "}"]
        nextId := next
    | .pair =>
        let rendered ← AssemblyLoopRenderer.render names true ["sc_arg"] 16 nextId body
        lines := lines ++ [line 12 ("function " ++ name ++ "(sc_arg) -> sc_ret, sc_aux {")] ++
          rendered.lines ++ [line 16 ("sc_ret := " ++ rendered.value), line 16 "sc_aux := sc_arg", line 12 "}"]
        nextId := rendered.nextId
    | _ =>
        let rendered ← AssemblyLoopRenderer.render names false ["sc_arg"] 16 nextId body
        lines := lines ++ [line 12 ("function " ++ name ++ "(sc_arg) -> sc_ret {")] ++ rendered.lines ++
          [line 16 ("sc_ret := " ++ rendered.value), line 12 "}"]
        nextId := rendered.nextId
    names := name :: names
  return (names, lines, nextId)

/-- The block after the helpers: the loop of the form around the entry, which
assigns `sc_out`. The Yul counter is independent of the Core ordinal guards. -/
def loopStatements (form : Form) (names : List String) (mask : Nat) (nextId : Nat) (entry : Expr) :
    Except EmitError (List String) := do
  let bound := toString mask
  let header := [line 12 ("let sc_limit := and(sc_input, " ++ bound ++ ")"), line 12 "let sc_acc := sc_input"]
  match form with
  | .leaves =>
      let step ← AssemblyLoopRenderer.render names false ["sc_ret"] 20 nextId entry
      return [line 12 "function sc_loop(sc_acc, sc_limit) -> sc_ret {", line 16 "sc_ret := sc_acc",
          line 16 "for { let sc_i := 0 } 1 { sc_i := add(sc_i, 1) } {",
          line 20 "if iszero(lt(sc_i, sc_limit)) { leave }"] ++ step.lines ++
        [line 20 ("sc_ret := " ++ step.value), line 16 "}", line 12 "}",
          line 12 ("sc_out := sc_loop(sc_input, and(sc_input, " ++ bound ++ "))")]
  | .pair =>
      let step ← AssemblyLoopRenderer.render names true ["sc_arg"] 16 nextId entry
      return [line 12 "function sc_iterate(sc_arg, sc_count) -> sc_ret, sc_next {"] ++ step.lines ++
        [line 16 ("sc_ret := " ++ step.value), line 16 "sc_next := add(sc_count, 1)", line 12 "}"] ++ header ++
        [line 12 "let sc_i := 0", line 12 "for { } lt(sc_i, sc_limit) { } {",
          line 16 "sc_acc, sc_i := sc_iterate(sc_acc, sc_i)", line 12 "}", line 12 "sc_out := sc_acc"]
  | _ =>
      let step ← AssemblyLoopRenderer.render names false ["sc_acc"] 16 nextId entry
      let (prelude, opening) := match form with
        | .breaks => ([], [line 12 "for { let sc_i := 0 } 1 { sc_i := add(sc_i, 1) } {",
            line 16 "if iszero(lt(sc_i, sc_limit)) { break }"])
        | .continues => ([line 12 "function sc_bound() -> sc_ret {", line 16 ("sc_ret := " ++ bound),
              line 12 "}"],
            [line 12 "for { let sc_i := 0 } lt(sc_i, sc_bound()) { sc_i := add(sc_i, 1) } {",
              line 16 "if iszero(lt(sc_i, sc_limit)) { continue }"])
        | _ => ([], [line 12 "for { let sc_i := 0 } lt(sc_i, sc_limit) { sc_i := add(sc_i, 1) } {"])
      return prelude ++ header ++ opening ++ step.lines ++
        [line 16 ("sc_acc := " ++ step.value), line 12 "}", line 12 "sc_out := sc_acc"]

def emit (form : Form) (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let (names, helpers, nextId) ← helperFunctions form plan.graph.helpers
  let statements ← loopStatements form names plan.mask nextId plan.graph.entry
  let lines := ["import * from std;", "import * from std.dispatch;", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_out: word = 0;",
    "        assembly {"] ++ helpers ++ statements ++
    ["        }", "        return uint256(sc_out);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.AssemblyLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyLoopCases
/-! An inline Yul loop case retains the independently checked plan of the
call-graph loop profile and the form that renders it. Generation repeats that
profile's steps, so its finite Core reference is unchanged, and draws the form
from a hash of the seed. Saved observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyLoop
open Lean Solcore.Core Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-assembly-loop-case.v1"
def planSchema : String := "solcore-lean.assembly-loop-plan.v1"
def profileVersion : String := "runtime-assembly-loops-v1/form-seed-v1"

/-- A checked call-graph loop plan and the form that renders it. -/
structure CheckedPlan where
  loop : Solcore.Synthesis.Core.CallGraphLoop.CheckedPlan
  form : Form

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.loop.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.loop.graph.program),
  ("mask", toJson plan.loop.mask), ("form", toJson plan.form.name)]

/-- The call-graph loop profile checks the step and mask, then the form and the
whole saved plan must be canonical. -/
def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported assembly loop plan schema"
  let loop ← CallGraphLoop.checkedPlan (Json.mkObj [("schema", toJson CallGraphLoop.planSchema),
    ("stepProgram", ← json.getObjVal? "stepProgram"), ("mask", ← json.getObjVal? "mask")])
  let some form := Form.ofString? (← json.getObjValAs? String "form") |
    throw "assembly loop form must be for, break, continue, leave or pair"
  let plan : CheckedPlan := ⟨loop, form⟩
  unless json == planJson plan do
    throw "saved assembly loop plan differs from its canonical checked representation"
  return plan

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("assemblyLoopPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.loop.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("loopProfileVersion", toJson CallGraphLoop.profileVersion),
    ("functionVersion", toJson CallGraphLoop.functionVersion), ("loopVersion", toJson BoundedLoop.version),
    ("stepFunctionVersion", toJson wordFunctionDAGVersion),
    ("aggregateVersion", toJson Aggregates.version),
    ("boundaryVersion", toJson CallGraphLoop.boundaryVersion),
    ("stepBoundaryVersion", toJson CallGraphLoop.stepBoundaryVersion),
    ("callShapeVersion", toJson CallGraphLoop.callShapeVersion),
    ("generatorVersion", toJson CallGraphLoop.generatorVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.loop.features),
    ("helperCount", toJson plan.loop.graph.helpers.length),
    ("callShapes", toJson (CallGraphLoop.callShapes plan.loop))]),
  ("contract", CallGraphLoop.contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", CallGraphLoop.observe plan.loop input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless Wire.programNodes (plan.loop.instantiate input) ≤ 512 do
    throw "canonical applied assembly loop exceeds the 512-node case limit"
  let emitted ← (emit plan.form plan.loop).mapError reprStr
  return makeCase plan input emitted origin fuel

/-- Even imported and reduced cases retain the exact canonical reference; no
origin makes a saved arbitrary Core program trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic assembly loop case schema"
  let plan ← checkedPlan (← json.getObjVal? "assemblyLoopPlan")
  let input ← CallGraphLoop.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.loop.instantiate input) do
    throw "saved Core program differs from its canonical assembly loop plan and runtime input"
  let admitted : CheckedInput := ⟨plan, input⟩
  unless Wire.encodeProgram admitted.program == (← json.getObjVal? "program") do
    throw "saved Core assembly loop application is not canonical"
  return admitted

/-- Separates the form stream from other uses of a case seed. -/
private def formDomain : UInt64 := 0x61736d6c6f6f7001

/-- A SplitMix64 hash of the seed, so that consecutive seeds vary in form
independently of the call-graph loop plan. -/
def formFor (seed : Seed) : Form :=
  Form.all[(GeneratorV2.mix (seed.toUInt64 ^^^ formDomain)).toNat % Form.all.length]?.getD .bounded

/-- The call-graph loop profile's plan and generated origin for the seed, with
the seed's form. A registered test requires both profiles to agree. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String (CheckedPlan × Json) := do
  let (loop, origin) ← CallGraphLoop.generatedPlan seed nodes
  let form := formFor seed
  return (⟨loop, form⟩,
    (origin.setObjVal! "kind" (toJson "assembly-loop-generated")).setObjVal! "form" (toJson form.name))

/-- Attempts count complete plan candidates. Accepted plans yield up to six
cases in fixed input order. The exclusions are those of the call-graph loop
profile, in its order; fuel exhaustion is an inconclusive exclusion. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "validation fuel exceeds profile limit"
        let (plan, origin) ← generatedPlan seed nodes
        let emitted ← (emit plan.form plan.loop).mapError reprStr
        CallGraphLoop.inputSensitive plan.loop fuel
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "assembly-loop-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs CallGraphLoop.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (inputSelection.record origin) fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  let admitted ← caseProgram json
  let savedFuel ← json.getObjValAs? Nat "executionFuel"
  unless savedFuel ≤ 10000000 do throw "saved execution fuel exceeds profile limit"
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("generatorVersion", CallGraphLoop.generatorVersion), ("profileVersion", profileVersion),
      ("loopProfileVersion", CallGraphLoop.profileVersion),
      ("functionVersion", CallGraphLoop.functionVersion), ("loopVersion", BoundedLoop.version),
      ("stepFunctionVersion", wordFunctionDAGVersion), ("aggregateVersion", Aggregates.version),
      ("boundaryVersion", CallGraphLoop.boundaryVersion),
      ("stepBoundaryVersion", CallGraphLoop.stepBoundaryVersion),
      ("callShapeVersion", CallGraphLoop.callShapeVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan.form admitted.plan.loop).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the assembly loop plan"
  unless (← json.getObjVal? "contract") == CallGraphLoop.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the assembly loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.loop.features do
    throw "saved features differ from the original Core call graph"
  unless (← provenance.getObjValAs? Nat "helperCount") = admitted.plan.loop.graph.helpers.length do
    throw "saved helper count differs from the original Core call graph"
  unless (← provenance.getObjVal? "callShapes") == toJson (CallGraphLoop.callShapes admitted.plan.loop) do
    throw "saved call shapes differ from the original Core call graph"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "assembly-loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes
    unless admitted.plan.form == plan.form do
      throw "saved assembly loop form differs from its generation seed"
    unless planJson plan == planJson admitted.plan do
      throw "saved assembly loop plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs CallGraphLoop.boundaryInputs (Seed.ofNat seed))[inputIndex]? =
        some admitted.input do
      throw "saved input differs from its loop boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    CallGraphLoop.inputSensitive plan.loop validationFuel
    let canonicalOrigin := (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
      "validationFuel" (toJson validationFuel)
    unless origin == inputSelection.record canonicalOrigin do
      throw "generated assembly loop provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported assembly loop provenance is not canonical"
  else if kind = "reduced" then
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← CallGraphLoop.inputWord parentText⟩
    unless parent.plan.form == admitted.plan.form do
      throw "saved assembly loop reduction changes its parent's form"
    unless admitted.plan.loop.graph.helpers.length = parent.plan.loop.graph.helpers.length do
      throw "saved loop reduction changes helper count"
    unless admitted.plan.loop.mask ≤ parent.plan.loop.mask do
      throw "saved loop reduction increases its mask"
    unless (complexity admitted.program.body).isStrictlySmaller (complexity parent.program.body) do
      throw "saved loop reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced assembly loop provenance is not canonical"
  else throw "unsupported assembly loop case origin"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "assembly loop provenance contains unexpected fields"
  -- Ignore the saved observation, but require the complete canonical envelope.
  let _ ← json.getObjVal? "directCore"
  let savedEnvelope := json.setObjVal! "directCore" .null
  let freshEnvelope := (fresh.setObjVal! "directCore" .null).setObjVal!
    "executionFuel" (toJson savedFuel)
  unless savedEnvelope == freshEnvelope do throw "saved assembly loop case envelope is not canonical"
  return fresh

/-- A call-graph loop reduction, rendered in the parent's form. -/
structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameForm : candidate.plan.form = source.plan.form
  sameHelperCount : candidate.plan.loop.graph.helpers.length = source.plan.loop.graph.helpers.length
  boundedMask : candidate.plan.loop.mask ≤ source.plan.loop.mask
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

/-- The call-graph loop reductions: typed graph reductions that keep every
helper binding, smaller masks and boundary inputs, each resealed and strictly
smaller. Keeping the form changes no Core node. -/
def reductions (source : CheckedInput) : List (Reduction source) :=
  (CallGraphLoop.reductions ⟨source.plan.loop, source.input⟩).map fun reduced =>
    ⟨⟨⟨reduced.candidate.plan, source.plan.form⟩, reduced.candidate.input⟩, rfl,
      reduced.sameHelperCount, reduced.boundedMask, reduced.strict⟩

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.AssemblyLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyMemoryEmitter
/-! Source emission of an inline Yul memory plan: one `assembly` block that
defines the step as a Yul function, takes its base from the free-memory
pointer without moving it, fills the 96-byte window, runs the schedule's
stages, final read and optional hash, and assigns the Solcore result local.
No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyMemory

open Solcore.Synthesis.Core (CheckedWordFunction)
open Solcore.Synthesis.Core.AssemblyMemory (Schedule Width)

def emitterVersion : String := "solcore-source-assembly-memory-v1"
def wrapperVersion : String := "solcore-word-assembly-memory-contract-v1"

/-- The G0 features the step's rendering supports: every operator and form. -/
def featureSupport := AssemblyRenderer.support
def contractName : String := "SynthesizedAssemblyMemory"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedAssemblyMemoryDeploy"]
def runtimePath : List String := ["SynthesizedAssemblyMemoryDeploy", "SynthesizedAssemblyMemory"]

private def line (text : String) : String := "            " ++ text

/-- The window byte at `offset` from the base. -/
private def address (offset : Nat) : String :=
  if offset = 0 then "sc_base" else "add(sc_base, " ++ toString offset ++ ")"

private def readName (index : Nat) : String := "sc_m" ++ toString index

/-- The block's statements: the step function in the `switch` form of
`runtime-assembly`, the base and the prologue, each stage, the final read and
the optional hash. -/
def block (function : CheckedWordFunction) (schedule : Schedule) : Except EmitError (List String) := do
  let step ← AssemblyRenderer.renderYul false ["sc_arg"] 16 0 function.body
  let stages := schedule.stages.zipIdx.flatMap fun (stage, index) =>
    [line ("let " ++ readName index ++ " := mload(" ++ address stage.read ++ ")"),
     line ((match stage.width with | .word => "mstore(" | .byte => "mstore8(") ++ address stage.write ++
       ", sc_step(" ++ readName index ++ "))")]
  let final := readName schedule.stages.length
  let result := match schedule.hash with
    | none => [line ("sc_out := sc_step(" ++ final ++ ")")]
    | some hash =>
        [line ("let sc_h := keccak256(" ++ address hash.offset ++ ", " ++ toString hash.length ++ ")"),
         line ("sc_out := add(sc_step(" ++ final ++ "), sc_h)")]
  return [line "function sc_step(sc_arg) -> sc_ret {"] ++ step.lines ++
    [line ("    sc_ret := " ++ step.value), line "}",
     line "let sc_base := mload(64)", line "mstore(sc_base, sc_input)",
     line "mstore(add(sc_base, 32), sc_step(sc_input))", line "mstore(add(sc_base, 64), not(sc_input))"] ++
    stages ++ [line ("let " ++ final ++ " := mload(" ++ address schedule.final ++ ")")] ++ result

def emit (function : CheckedWordFunction) (schedule : Schedule) : Except EmitError EmittedProgram := do
  let statements ← block function schedule
  let lines := ["import * from std;", "import * from std.dispatch;", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_out: word = 0;", "        assembly {"] ++ statements ++
    ["        }", "        return uint256(sc_out);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.AssemblyMemory
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyMemoryCases
/-! An inline Yul memory case retains the independently checked original Core
function of the primitive profile, the step, and the memory schedule drawn
from its seed. Generation repeats the primitive profile's steps for the step,
and the reference composes the step with the window model of
`Solcore.Synthesis.Core.AssemblyMemory`, which never reads the Yul text. Saved
observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyMemory
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.AssemblyMemory (Schedule Stage Hash Width)

def caseSchema : String := "solcore-lean.semantic-assembly-memory-case.v1"
def planSchema : String := "solcore-lean.assembly-memory-plan.v1"
def profileVersion : String := "runtime-assembly-memory-v1/schedule-seed-v1"

/-- The applied step's limit, as for `runtime-assembly`; the schedule and the
closure lie outside it. -/
def stepLimit : Nat := 512

/-- A checked step, an admitted schedule, and a full Core check of the
composed reference. The input is a literal, so its check does not depend on it. -/
structure CheckedPlan where private mk ::
  function : CheckedWordFunction
  schedule : Schedule
  admitted : schedule.admitted = true
  checked : (AssemblyMemory.program function.program.body schedule Word.zero).check = true

namespace CheckedPlan

def ofParts? (function : CheckedWordFunction) (schedule : Schedule) : Option CheckedPlan :=
  if admitted : schedule.admitted = true then
    if checked : (AssemblyMemory.program function.program.body schedule Word.zero).check = true then
      some ⟨function, schedule, admitted, checked⟩
    else none
  else none

def program (plan : CheckedPlan) (input : Word) : Wire.Program :=
  AssemblyMemory.program plan.function.program.body plan.schedule input

end CheckedPlan

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program := value.plan.program value.input

private def stageJson (stage : Stage) : Json := Json.mkObj [
  ("read", toJson stage.read), ("width", toJson stage.width.name), ("write", toJson stage.write)]

def scheduleJson (schedule : Schedule) : List (String × Json) := [
  ("stages", .arr (schedule.stages.map stageJson).toArray), ("finalRead", toJson schedule.final),
  ("hash", match schedule.hash with
    | none => Json.null
    | some hash => Json.mkObj [("offset", toJson hash.offset), ("length", toJson hash.length)])]

def planJson (plan : CheckedPlan) : Json := Json.mkObj ([
  ("schema", toJson planSchema), ("functionProgram", Wire.encodeProgram plan.function.program)] ++
  scheduleJson plan.schedule)

private def stageOf (json : Json) : Except String Stage := do
  let some width := Width.ofString? (← json.getObjValAs? String "width") |
    throw "assembly memory stage width must be word or byte"
  return ⟨← json.getObjValAs? Nat "read", width, ← json.getObjValAs? Nat "write"⟩

def scheduleOf (json : Json) : Except String Schedule := do
  let stages ← (← json.getObjValAs? (Array Json) "stages").toList.mapM stageOf
  let final ← json.getObjValAs? Nat "finalRead"
  let hash ← match ← json.getObjVal? "hash" with
    | .null => pure none
    | value => pure (some ⟨← value.getObjValAs? Nat "offset", ← value.getObjValAs? Nat "length"⟩)
  return ⟨stages, final, hash⟩

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported assembly memory plan schema"
  let function ← Primitive.checkedFunction (← json.getObjVal? "functionProgram")
  let schedule ← scheduleOf json
  unless schedule.admitted do
    throw "assembly memory schedule is outside the admitted stages, offsets and hashed lengths"
  let some plan := CheckedPlan.ofParts? function schedule |
    throw "assembly memory reference failed the full Core checker"
  unless json == planJson plan do
    throw "saved assembly memory plan differs from its canonical checked representation"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ stepLimit do
    throw "applied assembly memory step exceeds the 512-node step limit"
  return plan

/-- The reference on one input, with the observation fields of the primitive profile. -/
def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ =>
        [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Primitive.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("assemblyMemoryPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.program input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionProfileVersion", toJson Primitive.profileVersion),
    ("functionVersion", toJson wordFunctionVersion),
    ("abstractionVersion", toJson abstractionVersion),
    ("generatorVersion", toJson (Primitive.generatorVersionFor revision)),
    ("baseGeneratorVersion", toJson revision.version),
    ("boundaryVersion", toJson Primitive.boundaryVersion),
    ("memoryVersion", toJson AssemblyMemory.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson ((features plan.function.body).map featureName))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (plan.function.instantiate input) ≤ stepLimit do
    throw "applied assembly memory step exceeds the 512-node step limit"
  unless (plan.program input).check do
    throw "assembly memory reference failed the full Core checker"
  let emitted ← (emit plan.function plan.schedule).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- The decode bound of a saved reference: the step limit, the schedule's
largest overhead and the largest closure. -/
def caseLimit : Nat := 3282

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic assembly memory case schema"
  let plan ← checkedPlan (← json.getObjVal? "assemblyMemoryPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its assembly memory plan's reference and runtime input"
  return ⟨plan, input⟩

/-- Separates the schedule stream from other uses of a case seed. -/
private def scheduleDomain : UInt64 := 0x61736d6d656d6f01

private def gamma : UInt64 := 0x9e3779b97f4a7c15

/-- Value `index` of the seed's schedule stream, reduced to `[0, bound)` from its upper 32 bits. -/
private def draw (seed : Seed) (index bound : Nat) : Nat :=
  ((GeneratorV2.mix ((seed.toUInt64 ^^^ scheduleDomain) + UInt64.ofNat (index + 1) * gamma)).toNat / 2 ^ 32) % bound

/-- The delta classes 0, 1, 2–15, 16, 17–30 and 31. -/
def deltaClasses : List (Nat × Nat) := [(0, 0), (1, 1), (2, 15), (16, 16), (17, 30), (31, 31)]

/-- An offset from three stream values: its class, its delta in the class, and
its Word: 0, 32 or 64 for a byte or a delta of zero, else 0 or 32. -/
private def drawOffset (seed : Seed) (index : Nat) (byte : Bool) : Nat :=
  let (low, high) := deltaClasses.getD (draw seed index 6) (0, 0)
  let delta := low + draw seed (index + 1) (high - low + 1)
  32 * draw seed (index + 2) (if byte || delta = 0 then 3 else 2) + delta

/-- The schedule of a case seed: the stage count; per stage the read offset,
the width and the write offset; the final read offset; the hash, none or one
of the six lengths; then its offset. -/
def scheduleFor (seed : Seed) : Schedule := Id.run do
  let count := 1 + draw seed 0 AssemblyMemory.maximumStages
  let mut index := 1
  let mut stages : List Stage := []
  for _ in List.range count do
    let read := drawOffset seed index false
    let width := if draw seed (index + 3) 2 = 0 then Width.word else Width.byte
    let write := drawOffset seed (index + 4) (width == .byte)
    stages := stages ++ [⟨read, width, write⟩]
    index := index + 7
  let final := drawOffset seed index false
  let choice := draw seed (index + 3) (AssemblyMemory.hashLengths.length + 1)
  let hash := if choice = 0 then none else
    let length := AssemblyMemory.hashLengths.getD (choice - 1) 0
    some ⟨draw seed (index + 4) (AssemblyMemory.windowBytes - length + 1), length⟩
  return ⟨stages, final, hash⟩

/-- A generation filter on the composed reference, not a claim that this
finite bank covers a function. -/
def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) := do
  Primitive.boundaryInputs.mapM fun input =>
    match (plan.program input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (plan : CheckedPlan) (fuel : Nat) (acceptance : Acceptance := .profile) :
    Except String Unit := do
  let results ← boundaryResults plan fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all eight boundary inputs returned the same Word"
  acceptance.check Primitive.boundaryInputs results

/-- The generated origin before its input index, validation fuel, input
selection and acceptance filter. -/
private def generatedOrigin (seed : Seed) (nodes : Nat) (generated : GeneratedProgram)
    (literalIndex : Nat) : List (String × Json) := [
  ("kind", toJson "assembly-memory-generated"), ("seed", toJson (toString seed.toNat)),
  ("finalSeed", toJson (toString generated.finalSeed.toNat)), ("maxProgramNodes", toJson nodes),
  ("baseProgramNodes", toJson generated.maxProgramNodes), ("literalIndex", toJson literalIndex)]

/-- The step by the primitive profile's steps and the seed's schedule. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision) :
    Except String (GeneratedProgram × Nat × CheckedPlan) := do
  let (generated, literalIndex, function) ← Assembly.primitiveFunction seed nodes revision
  let some plan := CheckedPlan.ofParts? function (scheduleFor seed) |
    throw "assembly memory reference failed the full Core checker"
  return (generated, literalIndex, plan)

/-- Attempt limits count functions; case limits count individual runtime inputs. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary)
    (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (generated, literalIndex, plan) ← generatedPlan seed nodes revision
        let emitted ← (emit plan.function plan.schedule).mapError
          (fun error => "unsupported source primitive: " ++ reprStr error)
        inputSensitive plan fuel acceptance
        return (generated, literalIndex, plan, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)),
            ("stage", toJson "assembly-memory-profile"), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error.startsWith "unsupported source primitive:" then "unsupported-operation"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (generated, literalIndex, plan, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs Primitive.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := Json.mkObj (generatedOrigin seed nodes generated literalIndex ++
                [("inputIndex", toJson inputIndex), ("validationFuel", toJson fuel)])
              cases := cases.push
                (makeCase plan input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- The lexicographic shrink measure: stages, hash rank, delta sum, then the
applied step's nodes and literal weight. -/
structure Measure where
  stages : Nat
  hash : Nat
  deltas : Nat
  step : Complexity
  deriving Repr, BEq, DecidableEq

namespace Measure

def StrictlySmaller (candidate source : Measure) : Prop :=
  candidate.stages < source.stages ∨ (candidate.stages = source.stages ∧
    (candidate.hash < source.hash ∨ (candidate.hash = source.hash ∧
      (candidate.deltas < source.deltas ∨ (candidate.deltas = source.deltas ∧
        candidate.step.StrictlySmaller source.step)))))

instance (candidate source : Measure) : Decidable (candidate.StrictlySmaller source) := by
  unfold StrictlySmaller
  infer_instance

end Measure

def CheckedInput.measure (value : CheckedInput) : Measure :=
  ⟨value.plan.schedule.stages.length, value.plan.schedule.hashRank, value.plan.schedule.deltaSum,
    complexity (value.plan.function.instantiate value.input).body⟩

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance "baseGeneratorVersion"
  for (name, expected) in [
      ("generatorVersion", Primitive.generatorVersionFor revision), ("profileVersion", profileVersion),
      ("functionProfileVersion", Primitive.profileVersion),
      ("baseGeneratorVersion", revision.version), ("boundaryVersion", Primitive.boundaryVersion),
      ("functionVersion", wordFunctionVersion), ("abstractionVersion", abstractionVersion),
      ("memoryVersion", AssemblyMemory.version),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan.function admitted.plan.schedule).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the assembly memory plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the assembly memory wrapper"
  unless (← provenance.getObjVal? "features") ==
      toJson ((features admitted.plan.function.body).map featureName) do
    throw "saved features differ from the original Core step"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "assembly-memory-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported assembly memory case origin"
  if kind = "assembly-memory-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless Primitive.minimumProgramNodes ≤ nodes && nodes ≤ 512 do
      throw "saved generation budget exceeds profile limits"
    let (generated, literalIndex, plan) ← generatedPlan (Seed.ofNat seed) nodes revision
    unless admitted.plan.schedule == plan.schedule do
      throw "saved assembly memory schedule differs from its generation seed"
    unless Wire.encodeProgram plan.function.program == Wire.encodeProgram admitted.plan.function.program do
      throw "saved step differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Primitive.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    inputSensitive plan validationFuel acceptance
    unless origin == acceptance.record (inputSelection.record (Json.mkObj (
        generatedOrigin (Seed.ofNat seed) nodes generated literalIndex ++
        [("inputIndex", toJson inputIndex), ("validationFuel", toJson validationFuel)]))) do
      throw "generated assembly memory provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported assembly memory provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved assembly memory reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced assembly memory provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel revision mask
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "assembly memory provenance contains unexpected fields"
  return fresh

/-- Sealing includes the full Core check of the composed reference and a
strictly smaller measure. -/
structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  strict : candidate.measure.StrictlySmaller source.measure

private def sealReduction (source : CheckedInput) (function : CheckedWordFunction) (schedule : Schedule)
    (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? function schedule
  let candidate : CheckedInput := ⟨plan, input⟩
  if strict : candidate.measure.StrictlySmaller source.measure then some ⟨candidate, strict⟩ else none

private def aligned (offset : Nat) : Nat := offset - offset % 32

/-- One stage removed, keeping one; the hash removed or shortened at its
offset; one offset aligned within its Word. -/
def scheduleReductions (schedule : Schedule) : List Schedule :=
  let stages := schedule.stages
  let removed := if stages.length > 1 then
      (List.range stages.length).map fun index => {schedule with stages := stages.eraseIdx index}
    else []
  let hashes := match schedule.hash with
    | none => []
    | some hash => {schedule with hash := none} ::
        ((AssemblyMemory.hashLengths.filter (· < hash.length)).map fun length =>
          {schedule with hash := some ⟨hash.offset, length⟩})
  let stageAligned := stages.zipIdx.flatMap fun (stage, index) =>
    [{schedule with stages := stages.set index {stage with read := aligned stage.read}},
     {schedule with stages := stages.set index {stage with write := aligned stage.write}}]
  let finalAligned := [{schedule with final := aligned schedule.final}]
  let hashAligned := match schedule.hash with
    | none => []
    | some hash => [{schedule with hash := some ⟨aligned hash.offset, hash.length⟩}]
  removed ++ hashes ++ stageAligned ++ finalAligned ++ hashAligned

/-- The schedule reductions with the step and input kept, then the primitive
reductions of the step and input with the schedule kept. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let raw := (scheduleReductions source.plan.schedule).map
      (fun schedule => (source.plan.function, schedule, source.input)) ++
    (Primitive.reductions ⟨source.plan.function, source.input⟩).map fun reduced =>
      (reduced.candidate.function, source.plan.schedule, reduced.candidate.input)
  let mut seen : List String := []
  let mut result := []
  for (function, schedule, input) in raw do
    if let some reduced := sealReduction source function schedule input then
      let key := (planJson reduced.candidate.plan).compress ++ toString reduced.candidate.input.val
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

/-- A plan with a hash embeds the closure in every candidate, so its shrink
response holds at most eight. -/
def shrinkBatch (plan : CheckedPlan) (limit : Nat) : Nat :=
  if plan.schedule.hash.isSome then min limit 8 else limit

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance "baseGeneratorVersion"
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take (shrinkBatch source.plan limit) do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.AssemblyMemory
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyStorageLoopEmitter
/-! Emit the storage-loop protocol with every storage access in inline Yul. The
loop is the source while loop of the storage-loop profile around one Solcore
step call; the `assembly` blocks read the slots `0`, `1`, `1 + i` and `2 + i`
into the Solcore step argument, write the result to slot `2 + i` and then to
slot zero, and after the loop add the limit to slot one, form the result and
revert it from memory at zero for odd flags. This implementation is separate
from the finite ordinal guards with literal slots of the checked Core
reference. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyStorageLoop

open Solcore.Synthesis.Core.StorageLoop (CheckedPlan)
open Solcore.Synthesis.Source.AssemblyStorage (Form)

def emitterVersion : String := "solcore-source-assembly-storage-loops-v1"
def wrapperVersion : String := "solcore-word-assembly-storage-loops-contract-v1"
def contractName : String := "SynthesizedAssemblyStorageLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedAssemblyStorageLoopsDeploy"]
def runtimePath : List String := ["SynthesizedAssemblyStorageLoopsDeploy", "SynthesizedAssemblyStorageLoops"]

/-- The step argument of the iteration whose upper slot is `slot`. -/
def stepArgument (slot : String) : String :=
  "add(add(add(add(sload(0), sload(1)), sload(sub(" ++ slot ++ ", 1))), sload(" ++ slot ++ ")), sc_input)"

/-- The Word locals besides flags, input and limit, all declared before the loop. -/
def locals : Form → List String
  | .split => ["sc_counter", "sc_sum", "sc_value", "sc_result"]
  | .carried | .pipelined => ["sc_counter", "sc_slot", "sc_sum", "sc_value", "sc_result"]

def loopLines : Form → List String
  | .split => [
      "        while (sc_limit > sc_counter) {",
      "            assembly {",
      "                let sc_slot := add(sc_counter, 2)",
      "                sc_sum := " ++ stepArgument "sc_slot",
      "            }",
      "            sc_value = sc_step(sc_sum);",
      "            assembly {",
      "                sstore(add(sc_counter, 2), sc_value)",
      "                sstore(0, sc_value)",
      "            }",
      "            sc_counter = (sc_counter + 1);",
      "        }"]
  | .carried => [
      "        while (sc_limit > sc_counter) {",
      "            assembly {",
      "                sc_slot := add(sc_counter, 2)",
      "                sc_sum := " ++ stepArgument "sc_slot",
      "            }",
      "            sc_value = sc_step(sc_sum);",
      "            assembly {",
      "                sstore(sc_slot, sc_value)",
      "                sstore(0, sc_value)",
      "                sc_counter := add(sc_counter, 1)",
      "            }",
      "        }"]
  | .pipelined => [
      "        assembly {",
      "            if gt(sc_limit, sc_counter) {",
      "                sc_slot := add(sc_counter, 2)",
      "                sc_sum := " ++ stepArgument "sc_slot",
      "            }",
      "        }",
      "        while (sc_limit > sc_counter) {",
      "            sc_value = sc_step(sc_sum);",
      "            assembly {",
      "                sstore(sc_slot, sc_value)",
      "                sstore(0, sc_value)",
      "                sc_counter := add(sc_counter, 1)",
      "                if gt(sc_limit, sc_counter) {",
      "                    sc_slot := add(sc_counter, 2)",
      "                    sc_sum := " ++ stepArgument "sc_slot",
      "                }",
      "            }",
      "        }"]

def emit (form : Form) (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let steps ← AssemblyStorage.stepLines plan.step
  let lines := AssemblyStorage.importLines plan.step ++ steps ++ [
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");"] ++
    (locals form).map (fun name => "        let " ++ name ++ ": word = 0;") ++
    loopLines form ++ [
    "        assembly {",
    "            sstore(1, add(sload(1), sc_limit))",
    "            sc_result := add(sload(0), sload(1))",
    "            if and(sc_flags, 1) {",
    "                mstore(0, sc_result)",
    "                revert(0, 32)",
    "            }",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.AssemblyStorageLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.AssemblyStorageLoopCases
/-! An inline Yul storage-loop case retains the storage-loop profile's checked
plan, transactions and original Core contract, and the form that renders them.
Generation repeats that profile's steps, so its Core reference, observation and
exclusions are unchanged, and draws the form from a hash of the seed.
Reductions are that profile's, each in the parent case's form. Saved outputs
are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyStorageLoop
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Source.AssemblyStorage (Form)
open Solcore.Synthesis.Stateful.StorageLoopExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-assembly-storage-loop-case.v1"
def planSchema : String := "solcore-lean.assembly-storage-loop-plan.v1"
def profileVersion : String := "stateful-assembly-storage-loops-v1/form-seed-v1"
def corpusSchema : String := "solcore-lean.semantic-assembly-storage-loop-corpus.v1"

/-- A checked storage-loop scenario and the form that renders it. -/
structure CheckedScenario where
  loop : StorageLoop.CheckedScenario
  form : Form

def CheckedScenario.plan (scenario : CheckedScenario) : Solcore.Synthesis.Core.StorageLoop.CheckedPlan :=
  scenario.loop.plan

def CheckedScenario.transactions (scenario : CheckedScenario) : List Transaction := scenario.loop.transactions

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.loop.program

def planJson (plan : Solcore.Synthesis.Core.StorageLoop.CheckedPlan) (form : Form) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("mask", toJson plan.mask), ("form", toJson form.name)]

/-- The storage-loop profile checks the step and the mask; then the form and
the whole saved plan must be canonical. -/
def checkedPlan (json : Json) : Except String (Solcore.Synthesis.Core.StorageLoop.CheckedPlan × Form) := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported assembly storage-loop plan schema"
  let plan ← StorageLoop.checkedPlan (Json.mkObj [("schema", toJson StorageLoop.planSchema),
    ("stepProgram", ← json.getObjVal? "stepProgram"), ("mask", ← json.getObjVal? "mask")])
  let some form := Form.ofString? (← json.getObjValAs? String "form") |
    throw "assembly storage-loop form must be split, carried or pipelined"
  unless json == planJson plan form do
    throw "saved assembly storage-loop plan differs from its canonical checked representation"
  return (plan, form)

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("storageLoopPlan", planJson scenario.plan scenario.form),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", StorageLoop.transactionsJson scenario.plan.mask scenario.transactions),
    ("initialState", StorageLoop.initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.StorageLoopExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("loopProfileVersion", toJson StorageLoop.profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.StorageLoop.version),
      ("templateVersion", toJson StorageLoop.templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", StorageLoop.contractJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.form scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- The case in the storage-loop profile's shape must pass that profile's
checks: its transactions, the canonical Core program, the empty initial state,
slots zero through eight and the fuel. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic assembly storage-loop case schema"
  let (plan, form) ← checkedPlan (← json.getObjVal? "storageLoopPlan")
  let loop ← StorageLoop.caseProgram ((json.setObjVal! "schema" (toJson StorageLoop.caseSchema)).setObjVal!
    "storageLoopPlan" (StorageLoop.planJson plan))
  return ⟨loop, form⟩

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  StorageLoop.observe scenario.loop bindings fuel

/-- Separates the form stream from other uses of a case seed. -/
private def formDomain : UInt64 := 0x6173746c6f6f7001

def formFor (seed : Seed) : Form := AssemblyStorage.formFor formDomain seed

/-- The storage-loop profile's scenario and generated origin for the seed, with
the seed's form. A registered test requires both profiles to agree. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  let (loop, origin) ← StorageLoop.generatedScenario seed nodes revision transactions
  let form := formFor seed
  return (⟨loop, form⟩,
    (origin.setObjVal! "kind" (toJson "assembly-storage-loop-generated")).setObjVal! "form" (toJson form.name))

/-- Attempts count complete scenario candidates. The exclusions are those of
the storage-loop profile, in its order; fuel exhaustion is an inconclusive
exclusion. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.form scenario.plan).mapError reprStr
        StorageLoop.validateGenerated scenario.loop fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "storage-loop history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "assembly-storage-loop-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- A sealed storage-loop reduction of the source scenario, kept in its form. -/
structure Reduction (source : CheckedScenario) where private mk ::
  loop : StorageLoop.Reduction source.loop

def Reduction.candidate {source : CheckedScenario} (reduced : Reduction source) : CheckedScenario :=
  ⟨reduced.loop.candidate, source.form⟩

/-- The storage-loop profile's reductions, in their order, each in the form of
the source case. -/
def reductions (source : CheckedScenario) : List (Reduction source) :=
  (StorageLoop.reductions source.loop).map fun reduced => ⟨reduced⟩

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan parent.form),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentTransactions", StorageLoop.transactionsJson parent.plan.mask parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("loopProfileVersion", StorageLoop.profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.StorageLoop.version),
      ("templateVersion", StorageLoop.templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.form admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from assembly storage-loop plan emission"
  unless (← json.getObjVal? "contract") == StorageLoop.contractJson emitted do
    throw "saved contract metadata differs from assembly storage-loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "assembly-storage-loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes")
      revision (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated assembly storage-loop provenance"
    unless planJson expected.plan expected.form == planJson admitted.plan admitted.form &&
        StorageLoop.transactionsJson expected.plan.mask expected.transactions ==
          StorageLoop.transactionsJson admitted.plan.mask admitted.transactions do
      throw "saved plan, form or transaction sequence differs from its generation seed"
    StorageLoop.validateGenerated expected.loop validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let (parentPlan, parentForm) ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← StorageLoop.decodeTransactions parentPlan.mask (← origin.getObjVal? "parentTransactions")
    let parent : CheckedScenario := ⟨← StorageLoop.checkedScenario parentPlan parentTransactions, parentForm⟩
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its plan"
    unless parentForm == admitted.form do throw "reduction changes the parent case's form"
    unless (StorageLoop.sealReduction parent.loop admitted.plan.step admitted.plan.mask admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported assembly storage-loop case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced =>
    emitCase reduced.candidate (reducedOrigin source) fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.AssemblyStorageLoop
end
