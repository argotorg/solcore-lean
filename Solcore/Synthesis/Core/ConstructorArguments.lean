import Solcore.Synthesis.Core.EnumArgument

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
