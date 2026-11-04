import Solcore.Synthesis.Internal.EnumAbi

/-!
# Profile: constructor arguments

The profile `stateful-constructor-arguments`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.ConstructorArguments
/-! Two checked contracts for a constructor that takes arguments. The
initializer is the deployment phase: its input data are the constructor's
argument bytes, which it decodes itself as the pinned std does after the
compiler's generated copy, through a memory reader bounded by the argument
size and without std's code. Reading starts at offset 0, there is no up-front
head check, every read and advance past the end is `ABIInputTruncated()`
(`0x08638556`), and an unknown tag is empty revert data, written as the Word
zero. The parameters are none, one Word, two Words, a Word and a `bytes` value
of up to 64 bytes, or a Word and a value of a user enum of two to four
constructors as for `stateful-enum-arguments`. On success the initializer
writes the decoded record `d1` to `d5` to slots 1 to 5 and returns the Word
zero; a rejection reverts with its Word.

The runtime is one method `run(uint256 flags, uint256 input)`: it applies a
closed aggregate step to `slot 0 + input + slot 1 + ... + slot 5`, writes the
result `r` to slot 0, and odd flags revert with `r`; even flags return it. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.ConstructorArguments

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.StdDispatch
open Solcore.Synthesis.Core.EnumArgument (Constructor Payload Shape)

def initializerVersion : String := "core-constructor-argument-initializer-v1"
def runtimeVersion : String := "core-constructor-argument-runtime-v1"

/-- Both contracts return one Word or revert with one Word. -/
def resultType : Ty := .sum .word (.sum .word .word)

/-- Slot zero, then the decoded record in slots 1 to 5. -/
def slotCount : Nat := 6

/-- The Word that stands for an unknown tag's empty revert data. -/
def emptyRevert : Nat := 0

/-- The constructor's parameters. -/
inductive Parameters where
  | none
  | word
  | words
  | bytes
  | enum (shape : Shape)
  deriving Repr, BEq, DecidableEq

namespace Parameters

/-- The parameters' name, as the plan records them. -/
def name : Parameters → String
  | .none => "none"
  | .word => "uint256"
  | .words => "uint256,uint256"
  | .bytes => "uint256,bytes"
  | .enum _ => "uint256,enum"

def Valid : Parameters → Prop
  | .enum shape => shape.Valid
  | _ => True

instance (parameters : Parameters) : Decidable parameters.Valid := by
  cases parameters <;> unfold Valid <;> infer_instance

/-- Whether the arguments' head holds an offset Word at 32: a `bytes` value or
a dynamic enum. -/
def hasOffset : Parameters → Bool
  | .bytes => true
  | .enum shape => shape.dynamic
  | _ => false

end Parameters

/-- The decoded record: five Words. -/
def recordType : Ty := .product .word (.product .word (.product .word (.product .word .word)))

private def failed (error : Nat) : Expr := .inRight recordType (word error)

private def record (first second third fourth fifth : Expr) : Expr :=
  .inLeft .word (.pair first (.pair second (.pair third (.pair fourth fifth))))

/-- Arguments shorter than `bytes`, at the size Word `size`, are truncated. -/
private def short (size : Expr) (bytes : Nat) (continuation : Expr) : Expr :=
  .ifE (gt (word bytes) size) (failed truncatedError) continuation

/-- Keeps the first `remaining` bytes of a big-endian Word: all of them from 32
on, where the shift reaches 256, and none for zero. -/
private def mask (remaining : Expr) : Expr :=
  .unary .wordNot (.binary .wordShr (word (2 ^ 256 - 1)) (mul (word 8) remaining))

/-- Payload chunk `index` in a frame of `locals` binders whose newest is the
payload start `d` and the next the length `L`: the payload Word at
`d + 32 index` masked to the payload when all its bytes exist, otherwise the
Word that ends at the last payload byte shifted to the chunk's start. -/
private def chunk (locals index : Nat) : Expr :=
  .ifE (gt (.var 1) (word (32 * index)))
    (.caseE (host 8 locals (add (.var 0) (word (32 * index))))
      (.binary .wordShl (readAt (locals + 1) (sub (add (.var 1) (.var 2)) (word 32)))
        (mul (word 8) (sub (word (32 * (index + 1))) (.var 2))))
      (.binary .wordAnd (.var 0) (mask (sub (.var 2) (word (32 * index))))))
    (word 0)

/-- The leading Word `a` at offset 0, read once the size admits it. -/
private def leading (locals : Nat) : Expr := readAt locals (word 0)

/-- A `bytes` value at the head offset 32, in a frame of one binder, the size:
the offset `t <= size`, a length Word at `t`, and a length `L` that fits after
it. -/
private def bytesValue : Expr :=
  short (.var 0) 64
    (.letE (readAt 1 (word 32))
      (.ifE (gt (.var 0) (.var 1)) (failed truncatedError)
        (.ifE (gt (word 32) (sub (.var 1) (.var 0))) (failed truncatedError)
          (.letE (readAt 2 (.var 0))
            (.ifE (gt (.var 0) (sub (sub (.var 2) (.var 1)) (word 32))) (failed truncatedError)
              (.letE (add (.var 1) (word 32))
                (record (leading 4) (.var 1) (chunk 4 0) (chunk 4 1) (word 0))))))))

/-- Constructor `index`'s fields of a static enum, inline after the tag at 32,
in a frame of two binders: the tag and the size. -/
private def staticFields (index : Nat) : Payload → Expr
  | .noWords | .bytes => record (leading 2) (word index) (word 0) (word 0) (word 0)
  | .oneWord => short (.var 1) 96 (record (leading 2) (word index) (readAt 2 (word 64)) (word 0) (word 0))
  | .twoWords | .pair =>
      short (.var 1) 128 (record (leading 2) (word index) (readAt 2 (word 64)) (readAt 2 (word 96)) (word 0))

/-- Constructor `index`'s fields of a dynamic enum relative to its body `p`, in
a frame of three binders: the tag, `p` and the size. Each Word must exist; a
`bytes` value's tail offset `t` must satisfy `t <= size - p`, its length Word
must exist at `p + t` and its length must fit after it. -/
private def dynamicFields (index : Nat) : Payload → Expr
  | .noWords => record (leading 3) (word index) (word 0) (word 0) (word 0)
  | .oneWord =>
      .ifE (gt (word 64) (sub (.var 2) (.var 1))) (failed truncatedError)
        (record (leading 3) (word index) (readAt 3 (add (.var 1) (word 32))) (word 0) (word 0))
  | .twoWords | .pair =>
      .ifE (gt (word 96) (sub (.var 2) (.var 1))) (failed truncatedError)
        (record (leading 3) (word index) (readAt 3 (add (.var 1) (word 32))) (readAt 3 (add (.var 1) (word 64)))
          (word 0))
  | .bytes =>
      .ifE (gt (word 64) (sub (.var 2) (.var 1))) (failed truncatedError)
        (.letE (readAt 3 (add (.var 1) (word 32)))
          (.ifE (gt (.var 0) (sub (.var 3) (.var 2))) (failed truncatedError)
            (.letE (add (.var 2) (.var 0))
              (.ifE (gt (word 32) (sub (.var 4) (.var 0))) (failed truncatedError)
                (.letE (readAt 5 (.var 0))
                  (.ifE (gt (.var 0) (sub (.var 5) (add (.var 1) (word 32)))) (failed truncatedError)
                    (.letE (add (.var 1) (word 32))
                      (record (leading 7) (word index) (.var 1) (chunk 7 0) (chunk 7 1)))))))))

/-- The tag at 0 against each constructor's tag in declaration order; no match
is the unknown tag. -/
private def dispatch (fields : Nat → Payload → Expr) : Nat → List Constructor → Expr
  | _, [] => failed emptyRevert
  | index, constructor :: rest =>
      .ifE (.binary .wordEq (.var 0) (.word (EnumArgument.tag constructor))) (fields index constructor.payload)
        (dispatch fields (index + 1) rest)

/-- An enum value at the head offset 32, in a frame of one binder, the size: a
static body inline at 32, or a dynamic one at the offset `o <= size` read at
32; the tag Word must exist at the body. -/
private def enumValue (shape : Shape) : Expr :=
  if shape.dynamic then
    short (.var 0) 64
      (.letE (readAt 1 (word 32))
        (.ifE (gt (.var 0) (.var 1)) (failed truncatedError)
          (.ifE (gt (word 32) (sub (.var 1) (.var 0))) (failed truncatedError)
            (.letE (readAt 2 (.var 0)) (dispatch dynamicFields 1 shape.constructors)))))
  else
    short (.var 0) 64 (.letE (readAt 1 (word 32)) (dispatch staticFields 1 shape.constructors))

/-- The decoded record or the revert Word, in a frame of one binder, the size. -/
def decoder : Parameters → Expr
  | .none => record (word 1) (word 0) (word 0) (word 0) (word 0)
  | .word => short (.var 0) 32 (record (leading 1) (word 0) (word 0) (word 0) (word 0))
  | .words => short (.var 0) 64 (record (leading 1) (readAt 1 (word 32)) (word 0) (word 0) (word 0))
  | .bytes => bytesValue
  | .enum shape => enumValue shape

/-- After the record `d` at 0 and the size at 1: the five writes, then the
Word zero. -/
private def writes : Expr :=
  .letE (host 1 2 (.pair (word 1) (.first (.var 0))))
    (.letE (host 1 3 (.pair (word 2) (.first (.second (.var 1)))))
      (.letE (host 1 4 (.pair (word 3) (.first (.second (.second (.var 2))))))
        (.letE (host 1 5 (.pair (word 4) (.first (.second (.second (.second (.var 3)))))))
          (.letE (host 1 6 (.pair (word 5) (.second (.second (.second (.second (.var 4)))))))
            (.inLeft (.sum .word .word) (word 0))))))

private def initializerExpression (parameters : Parameters) : Expr :=
  .letE (host 7 0 .unit)
    (.caseE (decoder parameters) writes (.inRight .word (.inLeft .word (.var 0))))

def initializerProgram (parameters : Parameters) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := initializerExpression parameters
}

def initializerNodes (parameters : Parameters) : Nat := programNodes (initializerProgram parameters)

/-- In a frame of four binders: `r` at 0, the sum, the input, the flags and
the step. Odd flags revert with `r` after its write; otherwise `r` returns. -/
private def runtimeExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readAt 1 (word 4))
      (.letE (readAt 2 (word 36))
        (.letE (add (add (add (add (add (add (host 0 3 (word 0)) (.var 0)) (host 0 3 (word 1)))
            (host 0 3 (word 2))) (host 0 3 (word 3))) (host 0 3 (word 4))) (host 0 3 (word 5)))
          (.letE (.apply (.var 3) (.var 0))
            (.letE (host 1 5 (.pair (word 0) (.var 0)))
              (.ifE (.binary .wordEq (.binary .wordAnd (.var 4) (word 1)) (word 1))
                (.inRight .word (.inLeft .word (.var 1)))
                (.inLeft (.sum .word .word) (.var 1))))))))

def runtimeProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := runtimeExpression step.program.body
}

def runtimeNodes (step : Aggregates.CheckedDAG) : Nat := programNodes (runtimeProgram step)

/-- Syntax-only size of the runtime without the step, measured with a one-node
placeholder step that is never admitted or run. It lies inside a case's node
budget; the initializer lies outside it. -/
def shellNodes : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := runtimeExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  parameters : Parameters
  valid : parameters.Valid
  initializerChecked : (initializerProgram parameters).check = true
  runtimeChecked : (runtimeProgram step).check = true

namespace CheckedPlan

def initializerProgram (plan : CheckedPlan) : Program := ConstructorArguments.initializerProgram plan.parameters
def runtimeProgram (plan : CheckedPlan) : Program := ConstructorArguments.runtimeProgram plan.step

def ofParts? (step : Aggregates.CheckedDAG) (parameters : Parameters) : Option CheckedPlan :=
  if valid : parameters.Valid then
    if initializerChecked : (ConstructorArguments.initializerProgram parameters).check = true then
      if runtimeChecked : (ConstructorArguments.runtimeProgram step).check = true then
        some ⟨step, parameters, valid, initializerChecked, runtimeChecked⟩
      else none
    else none
  else none

theorem initializerWellTyped (plan : CheckedPlan) : plan.initializerProgram.WellTyped :=
  Program.check_full_sound plan.initializerChecked

theorem runtimeWellTyped (plan : CheckedPlan) : plan.runtimeProgram.WellTyped :=
  Program.check_full_sound plan.runtimeChecked

def initializerCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.initializerProgram.toCore, Program.check_promotes_current plan.initializerChecked⟩

def runtimeCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.runtimeProgram.toCore, Program.check_promotes_current plan.runtimeChecked⟩

def initializer (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.initializerCode rfl

def runtime (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.runtimeCode rfl

theorem initializer_program (plan : CheckedPlan) :
    plan.initializer.code.program = plan.initializerProgram.toCore := rfl

theorem runtime_program (plan : CheckedPlan) : plan.runtime.code.program = plan.runtimeProgram.toCore := rfl

end CheckedPlan
end Solcore.Synthesis.Core.ConstructorArguments
end

section
-- leanmerge: from Solcore.Synthesis.Source.ConstructorArgumentsEmitter
/-! Emit the constructor-argument protocol as a contract with one constructor
and one public method. The constructor takes the plan's parameters, which the
compiler's generated deployment code copies from the init code's suffix and
std decodes before the body runs, and writes the decoded record to slots 1 to
5: the marker 1, the leading Word, the second Word, a `bytes` value's length
and its chunks, or an enum's one-based constructor index and decoded Words.
An enum is declared, and matched with one arm per constructor, as for the
enum-argument profile; a `bytes` value's chunks are read with `mload` only when
its length exceeds their start, since std zeroes the decoded payload's padding
but nothing past it. The method `run(uint256 flags, uint256 input)` follows
the original Core runtime in order: the step over slot 0, the input and slots 1
to 5, the write of slot 0 and the odd-flags revert. Memory at zero is touched
only before the terminal revert. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ConstructorArguments

open Solcore.Synthesis.Core.ConstructorArguments (CheckedPlan Parameters)
open Solcore.Synthesis.Source.EnumArgument (enumName typeLines armLines)

def emitterVersion : String := "solcore-source-constructor-arguments-v1"
def wrapperVersion : String := "solcore-constructor-arguments-contract-v1"
def contractName : String := "SynthesizedConstructorArguments"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedConstructorArgumentsDeploy"]
def runtimePath : List String := ["SynthesizedConstructorArgumentsDeploy", "SynthesizedConstructorArguments"]

/-- The constructor and its writes of the record. -/
def constructorLines : Parameters → List String
  | .none => ["    constructor() {", "        sstore(1, 1);", "    }"]
  | .word => ["    constructor(a: uint256) {", "        sstore(1, Typedef.rep(a));", "    }"]
  | .words => ["    constructor(a: uint256, b: uint256) {", "        sstore(1, Typedef.rep(a));",
      "        sstore(2, Typedef.rep(b));", "    }"]
  | .bytes => ["    constructor(a: uint256, payload: memory<bytes>) {",
      "        sstore(1, Typedef.rep(a));",
      "        let sc_data: word = Typedef.rep(payload);",
      "        let sc_length: word = mload(sc_data);",
      "        sstore(2, sc_length);",
      "        if (sc_length > 0) {",
      "            sstore(3, mload((sc_data + 32)));",
      "        }",
      "        if (sc_length > 32) {",
      "            sstore(4, mload((sc_data + 64)));",
      "        }",
      "    }"]
  | .enum shape => ["    constructor(a: uint256, value: " ++ enumName ++ ") {",
      "        sstore(1, Typedef.rep(a));",
      "        let sc_index: word = 0;",
      "        let sc_w0: word = 0;",
      "        let sc_w1: word = 0;",
      "        let sc_w2: word = 0;",
      "        match (value) {"] ++
      (shape.constructors.zipIdx.map fun (constructor, index) => armLines index constructor).flatten ++
      ["        }",
      "        sstore(2, sc_index);",
      "        sstore(3, sc_w0);",
      "        sstore(4, sc_w1);",
      "        sstore(5, sc_w2);",
      "    }"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let enumLines := match plan.parameters with
    | .enum shape => ["import * from std.Generic;", "import * from std.ABIGeneric;"] ++
        [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"]
          (plan.step.helpers ++ [plan.step.entry]), ""] ++ typeLines shape
    | _ => [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"]
          (plan.step.helpers ++ [plan.step.entry]), ""]
  let mut lines := ["import * from std;", "import * from std.dispatch;"] ++ enumLines
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
    "contract " ++ contractName ++ " {"] ++ constructorLines plan.parameters ++ ["",
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_result: word = sc_step(((((((sload(0) + sc_input) + sload(1)) + sload(2)) + sload(3)) + sload(4)) + sload(5)));",
    "        sstore(0, sc_result);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.ConstructorArguments
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.ConstructorArgumentsExecution
/-! Execute the original checked constructor-argument contracts over an account
world. The deployment phase installs the initializer at the bound address and
runs it as one top-level invocation whose input data are the constructor's
argument bytes: canonical, or with one malformation. On return the account's
code becomes the runtime contract's through `Account.withCode`, which keeps
the storage the initializer wrote; a revert installs nothing and ends the
scenario. Runtime transactions then run as for the storage profiles, each
invocation with a fresh Core heap, and only the public terminal `finalWorld`
becomes the next transaction's world. Observations report the deployment row,
then each transaction's whole return data, slots zero to five and the
contract's whole committed storage.

`stdDecide` is a second model of the pinned std's decision on the argument
bytes, written over the bytes instead of in Core: the compiler's generated copy
and std's `MemoryWordReader`, reading from 0 with no up-front head check, each
read and advance bounded by the argument size. `model` reads the emitted
source on its decision, with the step evaluated alone in Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.ConstructorArgumentsExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ConstructorArguments (CheckedPlan Parameters)
open Solcore.Synthesis.Core.EnumArgument (Constructor Payload Shape)
open Solcore.Synthesis.Core.StdDispatch (truncatedError)

def historySchema : String := "solcore-lean.constructor-argument-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- The longest canonical `bytes` payload. -/
def maxLength : Nat := 64

/-- How the arguments depart from their canonical encoding: a cut, trailing
bytes, the head's offset Word, a `bytes` length Word, an unknown tag (whole, or
cut right after it), a dynamic enum's `bytes` tail offset, or a static enum cut
to the chosen constructor's head. -/
inductive Malformation where
  | none
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | offset (value : Word)
  | length (value : Word)
  | tag (value : Word)
  | tagCut (value : Word)
  | tail (value : Word)
  | narrow
  deriving BEq, Repr

/-- The deployment record: the leading Word `a`, the enum choice, the second
Word or field Words `first` and `second`, a `bytes` length, and the
malformation. -/
structure Deployment where
  a : Word
  choice : Nat
  first : Word
  second : Word
  length : Nat
  malformation : Malformation
  deriving BEq

structure Transaction where
  id : String
  flags : Word
  input : Word
  deriving BEq

/-- The enum choice as an argument-profile transaction, whose body encoder and
decoder are reused. -/
def enumTransaction (deployment : Deployment) : EnumArgumentExecution.Transaction :=
  ⟨"deployment", Word.zero, deployment.choice, deployment.first, deployment.second, deployment.length, .none⟩

/-- A `bytes` payload: the first `length` bytes of `first · K` and
`second · K`. -/
def payload (deployment : Deployment) : ByteArray :=
  EnumArgumentExecution.payload deployment.first deployment.second deployment.length

private def zeros (count : Nat) : ByteArray := ByteArray.mk (Array.replicate count 0)

private def w (value : Nat) : ByteArray := encodeWordBytesBE (Word.ofNatModulo value)

/-- Where an enum's body starts: inline at 32 for a static enum, at the
canonical offset 64 for a dynamic one. -/
def bodyStart (shape : Shape) : Nat := if shape.dynamic then 64 else 32

/-- The canonical argument bytes. -/
def canonicalBytes (parameters : Parameters) (deployment : Deployment) : ByteArray :=
  match parameters with
  | .none => ByteArray.empty
  | .word => encodeWordBytesBE deployment.a
  | .words => encodeWordBytesBE deployment.a ++ encodeWordBytesBE deployment.first
  | .bytes => encodeWordBytesBE deployment.a ++ w 64 ++ w deployment.length ++ payload deployment ++
      zeros (EnumArgumentExecution.paddedLength deployment.length - deployment.length)
  | .enum shape => encodeWordBytesBE deployment.a ++ (if shape.dynamic then w 64 else ByteArray.empty) ++
      EnumArgumentExecution.body shape (enumTransaction deployment)

def canonicalSize (parameters : Parameters) (deployment : Deployment) : Nat :=
  (canonicalBytes parameters deployment).size

def chosen (shape : Shape) (deployment : Deployment) : Constructor :=
  EnumArgumentExecution.constructorAt shape deployment.choice

/-- Whether the arguments carry a `bytes` length Word: the parameter, or the
chosen constructor of an enum. -/
def carriesBytes (parameters : Parameters) (deployment : Deployment) : Bool :=
  match parameters with
  | .bytes => true
  | .enum shape => (chosen shape deployment).payload == .bytes
  | _ => false

/-- The position of the `bytes` length Word. -/
def lengthPosition (parameters : Parameters) : Nat :=
  match parameters with
  | .enum shape => bodyStart shape + shape.bodyHead
  | _ => 64

/-- The chosen constructor's head, after which a static enum's padding is
cut. -/
def narrowedSize (shape : Shape) (deployment : Deployment) : Nat :=
  64 + EnumArgument.headSize (chosen shape deployment).payload

/-- The argument bytes the deployment sends. -/
def argumentBytes (parameters : Parameters) (deployment : Deployment) : ByteArray :=
  let canonical := canonicalBytes parameters deployment
  let start := match parameters with
    | .enum shape => bodyStart shape
    | _ => 32
  let change : StdCalldata.Change := match deployment.malformation with
    | .none => .none
    | .truncate kept => .truncate kept
    | .trailing count pattern => .trailing count pattern
    | .offset value => .word 32 value
    | .length value => .word (lengthPosition parameters) value
    | .tag value => .word start value
    | .tagCut value => .word start value
    | .tail value => .word (start + 32) value
    | .narrow => match parameters with
        | .enum shape => .truncate (narrowedSize shape deployment)
        | _ => .none
  let changed := change.apply canonical
  match deployment.malformation with
  | .tagCut _ => changed.extract 0 (start + 32)
  | _ => changed

/-- A malformation within its bounds, where it applies: cuts inside the
arguments, the trailing bounds, the offset Word of a `bytes` value or a dynamic
enum, the length Word of a `bytes` value, unknown tags of an enum, the tail
offset of a dynamic enum's `bytes` constructor, and a static enum's narrower
constructor. -/
def Malformation.valid (parameters : Parameters) (deployment : Deployment) : Malformation → Bool
  | .none => true
  | .truncate kept => kept < canonicalSize parameters deployment
  | .trailing count pattern => 1 ≤ count && count ≤ 64 && pattern < 3
  | .offset value => parameters.hasOffset && value.val != 64
  | .length value => carriesBytes parameters deployment && value.val != deployment.length
  | .tag value | .tagCut value => match parameters with
      | .enum shape => !shape.constructors.any (EnumArgument.tag · == value)
      | _ => false
  | .tail value => match parameters with
      | .enum shape => shape.dynamic && carriesBytes parameters deployment && value.val != shape.bodyHead
      | _ => false
  | .narrow => match parameters with
      | .enum shape => !shape.dynamic && narrowedSize shape deployment < canonicalSize parameters deployment
      | _ => false

/-- The record the constructor writes to slots 1 to 5. -/
structure Record where
  words : Word × Word × Word × Word × Word
  deriving BEq, Repr

def Record.toList (record : Record) : List Word :=
  let (d1, d2, d3, d4, d5) := record.words
  [d1, d2, d3, d4, d5]

/-- The revert data of a std rejection, or the decoded record. -/
abbrev Decision := Except ByteArray Record

private def selectorBytes (selector : Nat) : ByteArray :=
  ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

private def wordAt (input : ByteArray) (offset : Nat) : Word := Word.ofNatModulo (StdCalldata.wordAt input offset)

/-- The payload's zero-padded Word at `offset`, from the bytes that exist, as
std's copy leaves it in memory. -/
private def chunkAt (input : ByteArray) (start length offset : Nat) : Word :=
  let bytes := (input.extract (start + offset) (start + length)).extract 0 32
  Word.ofNatModulo ((bytes.data.toList ++ List.replicate (32 - bytes.size) (0 : UInt8)).foldl
    (fun total byte => total * 256 + byte.toNat) 0)

/-- A `bytes` value whose tail offset Word lies at `head` relative to `base`:
the offset `t <= size - base`, a length Word at `base + t` and a length that
fits after it. Returns the length and its two zero-padded chunks. -/
private def bytesAt (input : ByteArray) (base head : Nat) : Option (Word × Word × Word) :=
  let size := input.size
  if size - base < head + 32 then none
  else
    let tail := StdCalldata.wordAt input (base + head)
    if tail > size - base then none
    else if size - (base + tail) < 32 then none
    else
      let length := StdCalldata.wordAt input (base + tail)
      if length > size - (base + tail + 32) then none
      else
        let data := base + tail + 32
        some (Word.ofNatModulo length, if length > 0 then chunkAt input data length 0 else Word.zero,
          if length > 32 then chunkAt input data length 32 else Word.zero)

/-- An enum value's body at `start`: the tag compared with each constructor's
tag in declaration order before any field is read, then the chosen
constructor's fields, each Word required to exist. -/
private def enumAt (shape : Shape) (input : ByteArray) (start : Nat) : Except ByteArray (Nat × Word × Word × Word) :=
  let size := input.size
  let trunc : Except ByteArray (Nat × Word × Word × Word) := .error (selectorBytes truncatedError)
  if size - start < 32 then trunc
  else
    let found := wordAt input start
    match (shape.constructors.zipIdx.find? fun (constructor, _) => EnumArgument.tag constructor == found) with
    | none => .error ByteArray.empty
    | some (constructor, index) =>
        match constructor.payload with
        | .noWords => pure (index + 1, Word.zero, Word.zero, Word.zero)
        | .oneWord => if size - start < 64 then trunc else pure (index + 1, wordAt input (start + 32), Word.zero, Word.zero)
        | .twoWords | .pair =>
            if size - start < 96 then trunc
            else pure (index + 1, wordAt input (start + 32), wordAt input (start + 64), Word.zero)
        | .bytes => match bytesAt input start 32 with
            | some (length, first, second) => pure (index + 1, length, first, second)
            | none => trunc

/-- The pinned std's decision on the argument bytes, written from the
compiler's generated copy, `MemoryWordReader` and the derived decoders: `a`
first, then the parameters' values, every check comparing before it adds, as
std's do not wrap. A failure is `0x08638556`, an unknown tag empty data. -/
def stdDecide (parameters : Parameters) (input : ByteArray) : Decision := do
  let size := input.size
  let trunc : Decision := .error (selectorBytes truncatedError)
  let record := fun (d1 d2 d3 d4 d5 : Word) => (pure ⟨(d1, d2, d3, d4, d5)⟩ : Decision)
  match parameters with
  | .none => record (Word.ofNatModulo 1) Word.zero Word.zero Word.zero Word.zero
  | .word => if size < 32 then trunc else record (wordAt input 0) Word.zero Word.zero Word.zero Word.zero
  | .words => if size < 64 then trunc else record (wordAt input 0) (wordAt input 32) Word.zero Word.zero Word.zero
  | .bytes =>
      if size < 32 then trunc
      else match bytesAt input 0 32 with
        | some (length, first, second) => record (wordAt input 0) length first second Word.zero
        | none => trunc
  | .enum shape =>
      if size < 32 then trunc
      else
        let start? : Option Nat :=
          if shape.dynamic then
            if size < 64 then none
            else
              let offset := StdCalldata.wordAt input 32
              if offset > size then none else some offset
          else some 32
        match start? with
        | none => trunc
        | some start =>
            match enumAt shape input start with
            | .error data => .error data
            | .ok (index, w0, w1, w2) => record (wordAt input 0) (Word.ofNatModulo index) w0 w1 w2

/-- std's revert data for a rejected deployment, or none when it deploys. -/
def stdRejection? (parameters : Parameters) (deployment : Deployment) : Option ByteArray :=
  match stdDecide parameters (argumentBytes parameters deployment) with
  | .error data => some data
  | .ok _ => none

def arguments (parameters : Parameters) (deployment : Deployment) : String :=
  encodeBytesText (argumentBytes parameters deployment)

/-- The selector of `run(uint256,uint256)`, then the flags and input Words. -/
def inputData (flags input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input : Word) : String := encodeBytesText (inputData flags input).bytes

/-- Slot zero holds the accumulator and slots one to five the record. -/
def observedSlots : List Word := (List.range ConstructorArguments.slotCount).map Word.ofNatModulo

def slotsJson : Json := toJson (observedSlots.map fun slot => toString slot.val)

def storageJson (account : Account) : Json := toJson (observedSlots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)),
  ("value", toJson (toString (account.storageRead slot).val))])

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => storageJson account
  | none => storageJson Account.empty

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- One top-level invocation of `contract` at the bound address over `world`:
none when the code does not resolve, `some none` when fuel runs out, and
otherwise the outcome and the final world. -/
private def invoke (contract : CheckedCoreContract) (world : WorldState) (bindings : Bindings)
    (input : HostStorageDriver.InputData) (fuel : Nat) : Option (Option (FrameOutcome Word × WorldState)) :=
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  match registry.resolve? world bindings.address with
  | none => none
  | some ⟨resolved, installed⟩ =>
      match TopLevelExecution.run resolved
          { target := bindings.address, caller := bindings.caller, callValue := Word.zero, inputData := input }
          installed fuel with
      | .completed terminal => some (some (terminal.outcome, terminal.finalWorld))
      | .outOfFuel .. => some none

/-- Independent original-Core observation of the deployment phase, then of
the runtime transactions over the deployed world. -/
def observeContracts (initializer runtime : CheckedCoreContract) (argumentInput : ByteArray)
    (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let installed := StorageExecution.initialWorldForContract initializer bindings
  let mut world := installed
  let mut rows : Array Json := #[]
  let mut stopped : Option String := some "deployment"
  let mut deployment : Json := Json.null
  if bounded : argumentInput.size < wordModulus then
    match invoke initializer installed bindings ⟨argumentInput, bounded⟩ fuel with
    | none => deployment := Json.mkObj [("status", toJson "resolution-failure")]
    | some none => deployment := Json.mkObj [("status", toJson "out-of-fuel")]
    | some (some (outcome, final)) =>
        world := final
        match outcome, final.account? bindings.address with
        | .returned _, some account =>
            world := final.putAccount bindings.address (account.withCode runtime.code)
            stopped := none
        | _, _ => pure ()
        deployment := Json.mkObj (outcomeFields outcome)
  else
    deployment := Json.mkObj [("status", toJson "input-limit")]
  deployment := deployment.setObjVal! "committedStorage" (worldStorage world bindings)
    |>.setObjVal! "accountStorage" (AccountStorage.contractJson world bindings.address)
  let initial := worldStorage world bindings
  let initialWhole := AccountStorage.contractJson world bindings.address
  if stopped.isNone then
    for (transaction, index) in transactions.zipIdx do
      if stopped.isNone then
        let prior := world
        let common := [("id", toJson transaction.id), ("index", toJson index)]
        match invoke runtime prior bindings (inputData transaction.flags transaction.input) fuel with
        | none =>
            rows := rows.push (Json.mkObj (common ++ [
              ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings),
              ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
            stopped := some transaction.id
        | some none =>
            rows := rows.push (Json.mkObj (common ++ [
              ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings),
              ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
            stopped := some transaction.id
        | some (some (outcome, final)) =>
            world := final
            rows := rows.push (Json.mkObj (common ++ outcomeFields outcome ++ [
              ("committedStorage", worldStorage world bindings),
              ("accountStorage", AccountStorage.contractJson world bindings.address)]))
  let deployed := (deployment.getObjValAs? String "status").toOption == some "returned"
  let complete := (deployed && stopped.isNone) ||
    (!deployed && (deployment.getObjValAs? String "status").toOption == some "reverted" && transactions.isEmpty)
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", slotsJson), ("deployment", deployment),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if complete then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (deployment : Deployment) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContracts plan.initializer plan.runtime (argumentBytes plan.parameters deployment) transactions bindings fuel

/-- The step's own Core result at one argument. -/
def stepResult (step : Aggregates.CheckedDAG) (fuel : Nat) (argument : Word) : Option Word :=
  match (step.instantiate argument).toCore.runStateful fuel with
  | .done (.word value) _ => some value
  | _ => none

/-- One modelled row: whether it reverts, its whole output (std's revert data
for a rejected deployment, the one returned or reverted Word otherwise) and
slots zero to five. -/
structure ModelRow where
  reverted : Bool
  output : ByteArray
  slots : List Word

/-- The modelled deployment and transaction rows. The deployment follows
std's decision on the argument bytes and the constructor's writes; each
transaction follows the source: `sc_result = sc_step(sload(0) + input +
sload(1) + ... + sload(5))`, the write of slot zero, then the odd-flags revert,
which keeps the prior slots. A rejected deployment ends the rows. -/
def model (step : Aggregates.CheckedDAG) (fuel : Nat) (parameters : Parameters) (deployment : Deployment)
    (transactions : List Transaction) : Option (ModelRow × List ModelRow) := Id.run do
  match stdDecide parameters (argumentBytes parameters deployment) with
  | .error data =>
      return some (⟨true, data, List.replicate ConstructorArguments.slotCount Word.zero⟩, [])
  | .ok record =>
      let mut slots : List Word := Word.zero :: record.toList
      let deployed : ModelRow := ⟨false, encodeWordBytesBE Word.zero, slots⟩
      let mut rows : Array ModelRow := #[]
      for transaction in transactions do
        let total := slots.foldl (· + ·) Word.zero + transaction.input
        match stepResult step fuel total with
        | none => return none
        | some result =>
            if transaction.flags.val % 2 == 1 then
              rows := rows.push ⟨true, encodeWordBytesBE result, slots⟩
            else
              slots := slots.set 0 result
              rows := rows.push ⟨false, encodeWordBytesBE result, slots⟩
      return some (deployed, rows.toList)

end Solcore.Synthesis.Stateful.ConstructorArgumentsExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.ConstructorArgumentsCases
/-! Constructor-argument cases retain the original host-aware initializer and
runtime contracts, the constructor's parameters, one deployment record with
its malformation, and an ordered history of `(flags, input)` runtime
transactions, none when std rejects the deployment. Each case records std's
prescribed decision on its argument bytes. Reductions remove transactions,
drop or simplify the malformation, shorten a `bytes` length, simplify the
parameters, drop and narrow enum constructors, reduce the step and simplify
the record Words, flags and inputs. Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ConstructorArguments
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ConstructorArguments (CheckedPlan Parameters)
open Solcore.Synthesis.Core.EnumArgument (Constructor Payload Shape)
open Solcore.Synthesis.Stateful.ConstructorArgumentsExecution (Deployment Malformation Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-constructor-argument-case.v1"
def planSchema : String := "solcore-lean.constructor-argument-plan.v1"
def profileVersion : String := "stateful-constructor-arguments-v1/constructor-sequence-seed-v1"
def templateVersion : String := "std-constructor-decode-record-step-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-constructor-argument-corpus.v1"

/-- Flags values, inputs and record Words; the bank of the two-slot storage
profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- `bytes` lengths drawn with probability one half: empty, the Word boundaries
and the bound. -/
def lengthBank : List Nat := [0, 1, 31, 32, 33, 63, 64]

/-- The runtime, shell included, stays within the largest step budget. -/
def maxProgramNodes : Nat := 512

/-- The initializer lies outside the step budget. -/
def maxInitializerNodes : Nat := 1024

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The record Words a deployment's parameters and choice use: `first` for
`b`, one Word or two, and `second` for two Words or a payload. -/
private def usesFirst (parameters : Parameters) (deployment : Deployment) : Bool :=
  match parameters with
  | .words | .bytes => true
  | .enum shape => (Stateful.ConstructorArgumentsExecution.chosen shape deployment).payload != .noWords
  | _ => false

private def usesSecond (parameters : Parameters) (deployment : Deployment) : Bool :=
  match parameters with
  | .bytes => true
  | .enum shape => [Payload.twoWords, .pair, .bytes].contains
      (Stateful.ConstructorArgumentsExecution.chosen shape deployment).payload
  | _ => false

/-- A canonical record: a choice below the constructor count, a length of at
most 64 only where a `bytes` value is sent, and zero in every Word the
parameters do not send. -/
def admitsRecord (parameters : Parameters) (deployment : Deployment) : Bool :=
  let choiceOk := match parameters with
    | .enum shape => deployment.choice < shape.constructors.length
    | _ => deployment.choice == 0
  choiceOk && deployment.length ≤ Stateful.ConstructorArgumentsExecution.maxLength &&
    (Stateful.ConstructorArgumentsExecution.carriesBytes parameters deployment || deployment.length == 0) &&
    (parameters != .none || deployment.a == Word.zero) &&
    (usesFirst parameters deployment || deployment.first == Word.zero) &&
    (usesSecond parameters deployment || deployment.second == Word.zero) &&
    deployment.malformation.valid parameters deployment

def rejected (parameters : Parameters) (deployment : Deployment) : Bool :=
  (Stateful.ConstructorArgumentsExecution.stdRejection? parameters deployment).isSome

def validTransactions (parameters : Parameters) (deployment : Deployment) (transactions : List Transaction) : Prop :=
  transactions.length ≤ Stateful.Sequence.maxTransactions ∧ (transactions.map (·.id)).Nodup ∧
    transactions.all (fun tx => Storage.validId tx.id) = true ∧ admitsRecord parameters deployment = true ∧
    (rejected parameters deployment = false ∨ transactions = [])

instance (parameters : Parameters) (deployment : Deployment) (transactions : List Transaction) :
    Decidable (validTransactions parameters deployment transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  deployment : Deployment
  transactions : List Transaction
  valid : validTransactions plan.parameters deployment transactions
  bounded : Wire.programNodes plan.runtimeProgram ≤ maxProgramNodes
  initializerBounded : Wire.programNodes plan.initializerProgram ≤ maxInitializerNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.runtimeProgram

private def transactionRule : String :=
  s!"constructor-argument scenario requires a canonical deployment record with an applicable malformation, at most {Stateful.Sequence.maxTransactions} runtime transactions with distinct valid IDs, and none after a rejected deployment"

def checkedScenario (plan : CheckedPlan) (deployment : Deployment) (transactions : List Transaction) :
    Except String CheckedScenario := do
  if valid : validTransactions plan.parameters deployment transactions then
    if bounded : Wire.programNodes plan.runtimeProgram ≤ maxProgramNodes then
      if initializerBounded : Wire.programNodes plan.initializerProgram ≤ maxInitializerNodes then
        return ⟨plan, deployment, transactions, valid, bounded, initializerBounded⟩
      else throw "constructor-argument initializer exceeds its case limit"
    else throw "canonical constructor-argument runtime exceeds its case limit"
  else throw transactionRule

def malformationKinds : List String :=
  ["none", "truncate", "trailing", "offset", "length", "tag", "tagCut", "tail", "narrow"]

def kindOf : Malformation → String
  | .none => "none"
  | .truncate _ => "truncate"
  | .trailing _ _ => "trailing"
  | .offset _ => "offset"
  | .length _ => "length"
  | .tag _ => "tag"
  | .tagCut _ => "tagCut"
  | .tail _ => "tail"
  | .narrow => "narrow"

abbrev patternNames := Stateful.StdCalldata.patternNames

def malformationJson : Malformation → Json
  | .none => Json.mkObj [("kind", toJson "none")]
  | .truncate kept => Json.mkObj [("kind", toJson "truncate"), ("kept", toJson kept)]
  | .trailing count pattern => Json.mkObj [("kind", toJson "trailing"), ("count", toJson count),
      ("pattern", toJson (patternNames.getD pattern "ramp"))]
  | .offset value => Json.mkObj [("kind", toJson "offset"), ("value", toJson (toString value.val))]
  | .length value => Json.mkObj [("kind", toJson "length"), ("value", toJson (toString value.val))]
  | .tag value => Json.mkObj [("kind", toJson "tag"), ("value", toJson (toString value.val))]
  | .tagCut value => Json.mkObj [("kind", toJson "tagCut"), ("value", toJson (toString value.val))]
  | .tail value => Json.mkObj [("kind", toJson "tail"), ("value", toJson (toString value.val))]
  | .narrow => Json.mkObj [("kind", toJson "narrow")]

/-- std's revert data as text: an error selector, `0x` for an unknown tag, or
null when the deployment succeeds. -/
def prescribed (parameters : Parameters) (deployment : Deployment) : Option String :=
  (Stateful.ConstructorArgumentsExecution.stdRejection? parameters deployment).map
    Solcore.ContractRuntime.encodeBytesText

def deploymentJson (parameters : Parameters) (deployment : Deployment) : Json := Json.mkObj [
  ("a", toJson (toString deployment.a.val)), ("choice", toJson deployment.choice),
  ("first", toJson (toString deployment.first.val)), ("second", toJson (toString deployment.second.val)),
  ("length", toJson deployment.length), ("malformation", malformationJson deployment.malformation),
  ("arguments", toJson (Stateful.ConstructorArgumentsExecution.arguments parameters deployment)),
  ("stdRejection", match prescribed parameters deployment with
    | some data => toJson data
    | none => Json.null)]

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("calldata", toJson (Stateful.ConstructorArgumentsExecution.calldata tx.flags tx.input)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json :=
  toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "deployment or transaction Word exceeds 78 digits"
  Input.inputWord text

private def natural (json : Json) (key : String) : Except String Nat := do
  let value ← json.getObjValAs? Nat key
  unless value < 2 ^ 32 do throw s!"{key} is out of range"
  return value

private def nameIndex (names : List String) (json : Json) (key : String) : Except String Nat := do
  let name ← json.getObjValAs? String key
  match names.idxOf? name with
  | some index => return index
  | none => throw s!"unknown malformation {key}"

def decodeMalformation (json : Json) : Except String Malformation := do
  match ← json.getObjValAs? String "kind" with
  | "none" => return .none
  | "truncate" => return .truncate (← natural json "kept")
  | "trailing" => return .trailing (← natural json "count") (← nameIndex patternNames json "pattern")
  | "offset" => return .offset (← word (← json.getObjValAs? String "value"))
  | "length" => return .length (← word (← json.getObjValAs? String "value"))
  | "tag" => return .tag (← word (← json.getObjValAs? String "value"))
  | "tagCut" => return .tagCut (← word (← json.getObjValAs? String "value"))
  | "tail" => return .tail (← word (← json.getObjValAs? String "value"))
  | "narrow" => return .narrow
  | _ => throw "unknown malformation kind"

def decodeDeployment (parameters : Parameters) (json : Json) : Except String Deployment := do
  let deployment : Deployment := ⟨← word (← json.getObjValAs? String "a"), ← natural json "choice",
    ← word (← json.getObjValAs? String "first"), ← word (← json.getObjValAs? String "second"),
    ← natural json "length", ← decodeMalformation (← json.getObjVal? "malformation")⟩
  unless admitsRecord parameters deployment do throw transactionRule
  unless json == deploymentJson parameters deployment do
    throw "deployment differs from its canonical record, malformation, arguments or std outcome"
  return deployment

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be at most {Stateful.Sequence.maxTransactions}"
  rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← word (← row.getObjValAs? String "input")⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, input, calldata or zero-value metadata"
    return transaction

private def payloadOf? (fields : String) : Option Payload :=
  [Payload.noWords, .oneWord, .twoWords, .pair, .bytes].find? (EnumArgument.fieldsName · == fields)

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("parameters", toJson plan.parameters.name),
  ("constructors", toJson (match plan.parameters with
    | .enum shape => shape.constructors.map EnumArgument.constructorJson
    | _ => [])),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def parametersOf? (name : String) (constructors : List Constructor) : Option Parameters :=
  match name, constructors with
  | "none", [] => some .none
  | "uint256", [] => some .word
  | "uint256,uint256", [] => some .words
  | "uint256,bytes", [] => some .bytes
  | "uint256,enum", list => (EnumArgument.Shape.ofList? list).map Parameters.enum
  | _, _ => none

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported constructor-argument plan schema"
  let rows ← (← json.getObjVal? "constructors").getArr?
  unless rows.size ≤ Solcore.Synthesis.Core.EnumArgument.maxConstructors do
    throw "an enum has at most four constructors"
  let constructors ← rows.toList.mapM fun row => do
    let some payload := payloadOf? (← row.getObjValAs? String "fields") | throw "unsupported constructor fields"
    return ({name := ← row.getObjValAs? String "name", payload} : Constructor)
  let some parameters := parametersOf? (← json.getObjValAs? String "parameters") constructors
    | throw "unsupported constructor parameters"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step parameters
    | throw "constructor-argument plan needs valid parameters, an enum of two to four constructors with distinct bank names and at most two with bytes, and full host-Core admission of both contracts"
  unless json == planJson plan do throw "constructor-argument plan differs from its canonical checked representation"
  unless Wire.programNodes plan.runtimeProgram ≤ maxProgramNodes do throw "constructor-argument runtime exceeds its case limit"
  unless Wire.programNodes plan.initializerProgram ≤ maxInitializerNodes do
    throw "constructor-argument initializer exceeds its case limit"
  return plan

def contractJson (parameters : Parameters) (deployment : Deployment) (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson (Stateful.ConstructorArgumentsExecution.arguments parameters deployment))]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("constructorArgumentsPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.plan.runtimeProgram),
    ("initializerProgram", Wire.encodeProgram scenario.plan.initializerProgram),
    ("source", toJson emitted.source),
    ("deployment", deploymentJson scenario.plan.parameters scenario.deployment),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Stateful.ConstructorArgumentsExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.ConstructorArguments.runtimeVersion),
      ("initializerVersion", toJson Solcore.Synthesis.Core.ConstructorArguments.initializerVersion),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson scenario.plan.parameters scenario.deployment emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

private def decodeProgram (json : Json) (budget : Nat) : Except String Wire.Program :=
  (Wire.decodeProgramWithBudget {maxDepth := 512, maxNodes := budget, maxIntegerBytes := 4096} json).mapError (fun
    | .protocol error => error.toJson.compress
    | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)

/-- Every origin must reconstruct the fixed host contracts, including imports
and reductions. Arbitrary well-typed programs are not admissible
replacements. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic constructor-argument case schema"
  let plan ← checkedPlan (← json.getObjVal? "constructorArgumentsPlan")
  let deployment ← decodeDeployment plan.parameters (← json.getObjVal? "deployment")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let runtime ← decodeProgram (← json.getObjVal? "program") maxProgramNodes
  unless Wire.encodeProgram runtime == Wire.encodeProgram plan.runtimeProgram do
    throw "saved original Core runtime differs from the canonical constructor-argument plan"
  let initializer ← decodeProgram (← json.getObjVal? "initializerProgram") maxInitializerNodes
  unless Wire.encodeProgram initializer == Wire.encodeProgram plan.initializerProgram do
    throw "saved original Core initializer differs from the canonical constructor-argument plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Stateful.ConstructorArgumentsExecution.slotsJson do
    throw "observed slots must be zero through five"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan deployment transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Stateful.ConstructorArgumentsExecution.observe scenario.plan scenario.deployment scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- SplitMix64's finalizer. The generator's draws are affine in its start, so
consecutive seeds would otherwise start streams whose draws step by a fixed
residue. -/
private def mixed (value : Nat) : Nat :=
  let z := value % 2 ^ 64
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9 % 2 ^ 64
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb % 2 ^ 64
  z ^^^ (z >>> 31)

/-- High halves of successive draws from the stream that starts at the mixed
`seed` xor `domain`, each below its bound. -/
private def boundedDraws (seed : Seed) (domain : Nat) (bounds : List Nat) : List Nat := Id.run do
  let mut state := Seed.ofNat (mixed (seed.toNat ^^^ domain))
  let mut values : Array Nat := #[]
  for bound in bounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- The parameters, `a`, `first` and `second`, the choice, a `bytes` length
selector and uniform length, then the malformation's canonical selector, its
kind and its bank entry. -/
def shapeBounds : List Nat := [8, 6, 6, 6, 12, 14, 65, 3, 12, 16]

def shapeChoices (seed : Seed) : List Nat := boundedDraws seed 0x6374722d73686170 shapeBounds

/-- `none`, `uint256` and `uint256,uint256` once each of eight, `uint256,bytes`
twice and an enum three times, its shape drawn as for the enum-argument
profile. -/
def generatedParameters (seed : Seed) : Parameters :=
  match (shapeChoices seed).getD 0 0 with
  | 0 => .none
  | 1 => .word
  | 2 => .words
  | 3 | 4 => .bytes
  | _ => .enum (Solcore.Synthesis.Source.EnumArgument.generatedShape seed)

/-- The record with every Word the parameters do not send set to zero, and no
length where no `bytes` value is sent. -/
def canonicalRecord (parameters : Parameters) (deployment : Deployment) : Deployment :=
  let choice := match parameters with
    | .enum shape => deployment.choice % shape.constructors.length
    | _ => 0
  let base := {deployment with choice}
  {base with
    a := if parameters == .none then Word.zero else base.a
    first := if usesFirst parameters base then base.first else Word.zero
    second := if usesSecond parameters base then base.second else Word.zero
    length := if Stateful.ConstructorArgumentsExecution.carriesBytes parameters base then base.length else 0}

private def uniqueNats (values : List Nat) : List Nat := values.eraseDups

/-- The kinds that apply to a record, in catalog order. -/
def malformationBank (parameters : Parameters) (deployment : Deployment) (kind : String) : List Malformation :=
  let n := Stateful.ConstructorArgumentsExecution.canonicalSize parameters deployment
  let valid := fun (malformation : Malformation) => malformation.valid parameters deployment
  let words := fun (values : List Nat) => (uniqueNats values).map w
  (match kind with
    | "truncate" =>
        let boundaries := (List.range ((n + 31) / 32)).filterMap fun index =>
          if 0 < index && 32 * index < n then some index else none
        (uniqueNats (0 :: (boundaries.flatMap fun index => [32 * index - 1, 32 * index]) ++ [n - 1])).map Malformation.truncate
    | "trailing" => [1, 31, 32, 33].flatMap fun count => [0, 1, 2].map (Malformation.trailing count)
    | "offset" => (words [0, 32, n - 31, n, 2 ^ 255, 2 ^ 256 - 32]).map Malformation.offset
    | "length" =>
        let length := deployment.length
        let fits := n - (Stateful.ConstructorArgumentsExecution.lengthPosition parameters + 32)
        (words ([0] ++ (if length > 0 then [length - 1] else []) ++ [length + 1, fits, fits + 1, 2 ^ 256 - 1])).map Malformation.length
    | "tag" | "tagCut" =>
        let tag := match parameters with
          | .enum shape => (EnumArgument.tag (Stateful.ConstructorArgumentsExecution.chosen shape deployment)).val
          | _ => 0
        let values := words [0, tag + 1, tag ^^^ 2 ^ 255, 2 ^ 256 - 1]
        if kind == "tag" then values.map Malformation.tag else values.map Malformation.tagCut
    | "tail" =>
        let body := match parameters with
          | .enum shape => Stateful.ConstructorArgumentsExecution.bodyStart shape
          | _ => 0
        (words [0, 32, n - body + 1, 2 ^ 256 - 1]).map Malformation.tail
    | "narrow" => [.narrow]
    | _ => []).filter valid

def applicableKinds (parameters : Parameters) (deployment : Deployment) : List String :=
  (malformationKinds.drop 1).filter fun kind => !(malformationBank parameters deployment kind).isEmpty

/-- Canonical when the selector draw is 0, otherwise a kind uniformly among
those that apply, then an entry of its bank uniformly. -/
def generatedDeployment (seed : Seed) (parameters : Parameters) : Deployment :=
  let choices := shapeChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  let selector := choices.getD 5 0
  let length := if selector < lengthBank.length then lengthBank.getD selector 0 else choices.getD 6 0
  let record := canonicalRecord parameters ⟨bank 1, choices.getD 4 0, bank 2, bank 3, length, .none⟩
  if choices.getD 7 0 == 0 then record
  else
    let kinds := applicableKinds parameters record
    match kinds with
    | [] => record
    | _ =>
        let kind := kinds.getD (choices.getD 8 0 % kinds.length) "none"
        let entries := malformationBank parameters record kind
        {record with malformation := entries.getD (choices.getD 9 0 % entries.length) .none}

/-- Three flags, three inputs, then the completion pattern. -/
def sequenceBounds : List Nat := [6, 6, 6, 6, 6, 6, 4]

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x6374722d73657173 sequenceBounds

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 6 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), parityInput odd (bank index), bank (3 + index)⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The shell lies inside the budget, and the complete runtime is remeasured
as the final budget authority. A rejected deployment ends the scenario, so it
keeps no transactions. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.ConstructorArguments.shellNodes < nodes do
    throw "node budget is too small for the constructor-argument runtime or exceeds 512"
  let parameters := generatedParameters seed
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - Solcore.Synthesis.Core.ConstructorArguments.shellNodes) revision
  let some plan := CheckedPlan.ofParts? step parameters | throw "generated constructor-argument plan failed full Core admission"
  let deployment := generatedDeployment seed parameters
  let sequence := if rejected parameters deployment then [] else generatedTransactions seed transactions
  let scenario ← checkedScenario plan deployment sequence
  unless Wire.programNodes scenario.program ≤ nodes do
    throw "constructor-argument runtime exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "constructor-argument-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("shapeChoices", toJson (shapeChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "constructor-argument history exhausted Core fuel"
  let deployment ← observed.getObjVal? "deployment"
  let expected := if rejected scenario.plan.parameters scenario.deployment then "reverted" else "returned"
  unless rowStatus deployment == some expected do
    throw "constructor-argument deployment did not follow its prescribed std outcome"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map rowStatus == scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "constructor-argument history did not follow its prescribed flags parities"

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
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "constructor-argument history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "constructor-argument-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- `none` 0, `uint256` 1, `uint256,uint256` 2, `uint256,bytes` 3 and an enum
4. -/
def parametersWeight : Parameters → Nat
  | .none => 0
  | .word => 1
  | .words => 2
  | .bytes => 3
  | .enum _ => 4

def shapeWeight : Parameters → Nat
  | .enum shape => Solcore.Synthesis.Source.EnumArgument.shapeWeight shape
  | _ => 0

/-- Nothing for no malformation, otherwise one plus its position in its kind's
bank, or one plus the bank's size outside it. -/
def malformationWeight (parameters : Parameters) (deployment : Deployment) : Nat :=
  match deployment.malformation with
  | .none => 0
  | malformation =>
      let bank := malformationBank parameters deployment (kindOf malformation)
      1 + (bank.idxOf? malformation).getD bank.length

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.deployment.a.val + scenario.deployment.first.val + scenario.deployment.second.val +
    scenario.transactions.foldl (fun total tx => total + tx.flags.val + tx.input.val) 0

/-- Transaction count, the parameters, the enum's shape, the malformation's
weight, the `bytes` length, complete program size/literals, then the record
Words, flags and inputs. Every axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (parametersWeight candidate.plan.parameters < parametersWeight source.plan.parameters ∨
    (parametersWeight candidate.plan.parameters = parametersWeight source.plan.parameters ∧
      (shapeWeight candidate.plan.parameters < shapeWeight source.plan.parameters ∨
      (shapeWeight candidate.plan.parameters = shapeWeight source.plan.parameters ∧
        (malformationWeight candidate.plan.parameters candidate.deployment <
            malformationWeight source.plan.parameters source.deployment ∨
        (malformationWeight candidate.plan.parameters candidate.deployment =
            malformationWeight source.plan.parameters source.deployment ∧
          (candidate.deployment.length < source.deployment.length ∨
          (candidate.deployment.length = source.deployment.length ∧
            ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
            (complexity candidate.program.body = complexity source.program.body ∧
              valueWeight candidate < valueWeight source)))))))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (parameters : Parameters)
    (deployment : Deployment) (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step parameters
  let candidate ← (checkedScenario plan deployment transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) : List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- New parameters' record and transactions: the record made canonical, a
malformation that no longer applies dropped, and no transactions after a
rejected deployment. -/
def reanchor (parameters : Parameters) (deployment : Deployment) (transactions : List Transaction) :
    Deployment × List Transaction :=
  let record := canonicalRecord parameters {deployment with malformation := .none}
  let kept := if deployment.malformation.valid parameters record then {record with malformation := deployment.malformation}
    else record
  (kept, if rejected parameters kept then [] else transactions)

private def moveDown (index value : Nat) : Nat := if value > index then value - 1 else value

/-- The next narrower fields: the struct to two Words, two Words to one, one
Word to none and `bytes` to none. -/
private def narrower : Payload → Option Payload
  | .pair => some .twoWords
  | .twoWords => some .oneWord
  | .oneWord => some .noWords
  | .bytes => some .noWords
  | .noWords => none

/-- Simpler parameters: a static enum, `uint256,bytes` and `uint256,uint256`
become `uint256`, which becomes `none`. -/
private def simpler : Parameters → Option Parameters
  | .enum shape => if shape.dynamic then none else some .word
  | .bytes | .words => some .word
  | .word => some .none
  | .none => none

/-- One-transaction removals, a dropped or earlier malformation, a shorter
length, simpler parameters, dropped and narrowed enum constructors, step
reductions, zero record Words, then the flags' parity bit and the input's low
byte. Candidates still need execution to establish that they preserve a
finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let parameters := source.plan.parameters
  let deployment := source.deployment
  let mut raw : List (Aggregates.CheckedDAG × Parameters × Deployment × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, parameters, deployment,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  let bank := malformationBank parameters deployment (kindOf deployment.malformation)
  let earlier := match bank.idxOf? deployment.malformation with
    | some position => bank.take position
    | none => bank
  for malformation in Malformation.none :: earlier do
    if malformation != deployment.malformation then
      let (kept, transactions) := reanchor parameters {deployment with malformation} source.transactions
      raw := raw ++ [(source.plan.step, parameters, kept, transactions)]
  -- A shorter length, empty or halved.
  for shorter in [0, deployment.length / 2] do
    if shorter < deployment.length then
      let (kept, transactions) := reanchor parameters {deployment with length := shorter} source.transactions
      raw := raw ++ [(source.plan.step, parameters, kept, transactions)]
  if let some smaller := simpler parameters then
    let (kept, transactions) := reanchor smaller deployment source.transactions
    raw := raw ++ [(source.plan.step, smaller, kept, transactions)]
  if let .enum shape := parameters then
    for index in List.range shape.constructors.length do
      if index != deployment.choice then
        if let some smaller := EnumArgument.Shape.ofList? (shape.constructors.eraseIdx index) then
          let (kept, transactions) := reanchor (.enum smaller)
            {deployment with choice := moveDown index deployment.choice} source.transactions
          raw := raw ++ [(source.plan.step, .enum smaller, kept, transactions)]
    for index in List.range shape.constructors.length do
      if let some constructor := shape.constructors[index]? then
        if let some payload := narrower constructor.payload then
          if let some smaller := EnumArgument.Shape.ofList? (shape.constructors.set index {constructor with payload}) then
            let (kept, transactions) := reanchor (.enum smaller) deployment source.transactions
            raw := raw ++ [(source.plan.step, .enum smaller, kept, transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, parameters, deployment, source.transactions)]
  for change in [fun (record : Deployment) => {record with a := Word.zero},
      fun (record : Deployment) => {record with first := Word.zero},
      fun (record : Deployment) => {record with second := Word.zero}] do
    let (kept, transactions) := reanchor parameters (change deployment) source.transactions
    raw := raw ++ [(source.plan.step, parameters, kept, transactions)]
  for index in List.range source.transactions.length do
    raw := raw ++ [(source.plan.step, parameters, deployment, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(source.plan.step, parameters, deployment, replaceAt source.transactions index fun tx =>
      {tx with input := tx.input.bitAnd (Word.ofNatModulo 255)})]
  let mut seen : List String := []
  let mut result := []
  for (step, parameters, deployment, transactions) in raw do
    if let some reduced := sealReduction source step parameters deployment transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("deployment", deploymentJson reduced.candidate.plan.parameters reduced.candidate.deployment),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentDeployment", deploymentJson parent.plan.parameters parent.deployment),
  ("parentTransactions", transactionsJson parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.ConstructorArguments.runtimeVersion),
      ("initializerVersion", Solcore.Synthesis.Core.ConstructorArguments.initializerVersion),
      ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from constructor-argument plan emission"
  unless (← json.getObjVal? "contract") == contractJson admitted.plan.parameters admitted.deployment emitted do
    throw "saved contract metadata differs from constructor-argument wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "constructor-argument-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated constructor-argument provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        deploymentJson expected.plan.parameters expected.deployment ==
          deploymentJson admitted.plan.parameters admitted.deployment &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan, deployment or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentDeployment ← decodeDeployment parentPlan.parameters (← origin.getObjVal? "parentDeployment")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentDeployment parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.parameters admitted.deployment
        admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported constructor-argument case origin"
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

end Solcore.Synthesis.Source.ConstructorArguments
end
