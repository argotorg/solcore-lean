import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Synthesis.Core.EnumReturn
import Solcore.Synthesis.Core.StdDispatch
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract
import Solcore.Abi.Keccak256

/-! A checked protocol that takes a value of a user enum of two to four
constructors as an argument and decodes it from the calldata itself, as the
pinned std's dispatcher and derived ABI decoder do, without std's decoder code.
The ABI supplies `run(uint256 flags, E value)`. Calldata shorter than four
bytes or with another selector reaches the default fallback; calldata shorter
than the arguments' head is truncated. The value's body starts at 36 for a
static enum, and for a dynamic one at `4 + o`, where `o` is the head offset
Word, with `o <= size - 4`. The tag Word must exist there and equal one
constructor's `keccak256("Name(fields)")`; otherwise the call reverts with empty
data, which the contract writes as the Word zero. The constructor's fields
follow the tag: one or two Words, the struct's two Words, or a `bytes` value
behind a tail offset relative to the body, each read only when its bytes exist.
The protocol then writes the step result `r = step(prior + index + w0 + w1 +
w2)` to slot 0, the constructor's one-based index to slot 1 and the decoded
Words to slots 2 to 4, and odd flags revert with `r`. A std rejection reverts
with its error selector as the Word payload. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.EnumArgument

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.StdDispatch

def version : String := "core-enum-argument-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- Slot zero, the constructor index and three decoded Words. -/
def slotCount : Nat := 5

/-- std's bound on a decoded `bytes` length, `~0 - 63`. -/
def maxPayloadLength : Nat := 2 ^ 256 - 64

/-- The Word that stands for an unknown tag's empty revert data. -/
def emptyRevert : Nat := 0

/-- A constructor's fields: none, one or two Words, the struct `ScPair` of two
Words, or one `bytes` value. -/
inductive Payload where
  | noWords
  | oneWord
  | twoWords
  | pair
  | bytes
  deriving Repr, BEq, DecidableEq

/-- The ABI signature of a constructor's fields, as std's `sigStr` writes
them. A struct's signature is its fields', without parentheses. -/
def fieldSignature : Payload → String
  | .noWords => ""
  | .oneWord => "uint256"
  | .twoWords => "uint256,uint256"
  | .pair => "uint256,uint256"
  | .bytes => "bytes"

/-- A constructor's head footprint after its tag. -/
def headSize : Payload → Nat
  | .noWords => 0
  | .oneWord => 32
  | .twoWords => 64
  | .pair => 64
  | .bytes => 32

/-- Names, drawn without repetition, as for the returned enums. -/
abbrev nameBank : List String := EnumReturn.nameBank

def minConstructors : Nat := 2
def maxConstructors : Nat := 4
def maxBytesConstructors : Nat := 2

structure Constructor where
  name : String
  payload : Payload
  deriving Repr, BEq, DecidableEq

private def hashWord (text : String) : Word :=
  (decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash text.toUTF8)).getD Word.zero

/-- std's variant tag: `keccak256("Name(fields)")` as a big-endian Word. -/
def tag (constructor : Constructor) : Word :=
  hashWord (constructor.name ++ "(" ++ fieldSignature constructor.payload ++ ")")

structure Shape where
  first : Constructor
  second : Constructor
  rest : List Constructor
  deriving Repr, BEq, DecidableEq

namespace Shape

def constructors (shape : Shape) : List Constructor := shape.first :: shape.second :: shape.rest

def payloads (shape : Shape) : List Payload := shape.constructors.map Constructor.payload

/-- Two to four constructors with distinct names from the bank, at most two of
which carry `bytes`. -/
def Valid (shape : Shape) : Prop :=
  shape.rest.length + 2 ≤ maxConstructors ∧ (shape.constructors.map (·.name)).Nodup ∧
    shape.constructors.all (fun constructor => nameBank.contains constructor.name) = true ∧
    (shape.payloads.filter (· == .bytes)).length ≤ maxBytesConstructors

instance (shape : Shape) : Decidable shape.Valid := by
  unfold Valid
  infer_instance

/-- A `bytes` constructor makes the enum dynamic. -/
def dynamic (shape : Shape) : Bool := shape.payloads.contains .bytes

/-- The body's head: the tag and the widest constructor's fields. -/
def bodyHead (shape : Shape) : Nat := 32 + shape.payloads.foldr (fun payload widest => max (headSize payload) widest) 0

/-- The head of `(uint256 flags, E value)`: the flags, then the inline body of
a static enum or one offset Word. -/
def argumentsHead (shape : Shape) : Nat := 32 + if shape.dynamic then 32 else shape.bodyHead

/-- std's structural signature of the enum: the field signatures nested to the
right in `sum(left,right)`. -/
def sumSignature : List Constructor → String
  | [] => ""
  | [last] => fieldSignature last.payload
  | constructor :: rest => "sum(" ++ fieldSignature constructor.payload ++ "," ++ sumSignature rest ++ ")"

def signature (shape : Shape) : String := "run(uint256," ++ sumSignature shape.constructors ++ ")"

/-- The method selector: the first four bytes of the signature's hash. -/
def selector (shape : Shape) : Nat := (hashWord shape.signature).val / 2 ^ 224

end Shape

/-- The decoded value: the one-based index and the three Words. -/
def fieldsType : Ty := .product .word (.product .word (.product .word .word))

private def failed (error : Nat) : Expr := .inRight fieldsType (word error)

private def decoded (index : Nat) (first second third : Expr) : Expr :=
  .inLeft .word (.pair (word index) (.pair first (.pair second third)))

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

/-- Constructor `index`'s fields of a static enum, read inside the checked
head, in a frame of four binders. -/
private def staticFields (index : Nat) : Payload → Expr
  | .noWords | .bytes => decoded index (word 0) (word 0) (word 0)
  | .oneWord => decoded index (readAt 4 (word 68)) (word 0) (word 0)
  | .twoWords | .pair => decoded index (readAt 4 (word 68)) (readAt 4 (word 100)) (word 0)

/-- Constructor `index`'s fields of a dynamic enum in a frame of six binders:
the tag at 0, the body start `p` at 1 and the size at 4. Each Word must exist;
a `bytes` value's tail offset `t` must satisfy `t <= size - p`, its length Word
must exist at `p + t` and its length `L` must fit after it. -/
private def dynamicFields (index : Nat) : Payload → Expr
  | .noWords => decoded index (word 0) (word 0) (word 0)
  | .oneWord =>
      .ifE (gt (word 64) (sub (.var 4) (.var 1))) (failed truncatedError)
        (decoded index (readAt 6 (add (.var 1) (word 32))) (word 0) (word 0))
  | .twoWords | .pair =>
      .ifE (gt (word 96) (sub (.var 4) (.var 1))) (failed truncatedError)
        (decoded index (readAt 6 (add (.var 1) (word 32))) (readAt 6 (add (.var 1) (word 64))) (word 0))
  | .bytes =>
      .ifE (gt (word 64) (sub (.var 4) (.var 1))) (failed truncatedError)
        (.letE (readAt 6 (add (.var 1) (word 32)))
          (.ifE (gt (.var 0) (sub (.var 5) (.var 2))) (failed truncatedError)
            (.letE (add (.var 2) (.var 0))
              (.ifE (gt (word 32) (sub (.var 6) (.var 0))) (failed truncatedError)
                (.letE (readAt 8 (.var 0))
                  (.ifE (gt (.var 0) (sub (.var 7) (add (.var 1) (word 32)))) (failed truncatedError)
                    (.ifE (gt (.var 0) (word maxPayloadLength)) (failed truncatedError)
                      (.letE (add (.var 1) (word 32))
                        (decoded index (.var 1) (chunk 10 0) (chunk 10 1))))))))))

/-- The tag at 0 against each constructor's tag in declaration order; no match
is the unknown tag. -/
private def dispatch (fields : Nat → Payload → Expr) : Nat → List Constructor → Expr
  | _, [] => failed emptyRevert
  | index, constructor :: rest =>
      .ifE (.binary .wordEq (.var 0) (.word (tag constructor))) (fields index constructor.payload)
        (dispatch fields (index + 1) rest)

/-- The decoded value or the revert Word, in a frame of three binders: the
flags, the size and the step. -/
private def decode (shape : Shape) : Expr :=
  if shape.dynamic then
    .letE (readAt 3 (word 36))
      (.ifE (gt (.var 0) (sub (.var 2) (word 4))) (failed truncatedError)
        (.letE (add (word 4) (.var 0))
          (.ifE (gt (word 32) (sub (.var 3) (.var 0))) (failed truncatedError)
            (.letE (readAt 5 (.var 0)) (dispatch dynamicFields 1 shape.constructors)))))
  else
    .letE (readAt 3 (word 36)) (dispatch staticFields 1 shape.constructors)

/-- After the decoded value `v` at 0, the flags at 1 and the step at 3: the
step result of `prior + index + w0 + w1 + w2`, the five writes and the
completion. -/
private def completion : Expr :=
  .letE (add (add (add (add (host 0 4 (word 0)) (.first (.var 0))) (.first (.second (.var 0))))
      (.first (.second (.second (.var 0))))) (.second (.second (.second (.var 0)))))
    (.letE (.apply (.var 4) (.var 0))
      (.letE (host 1 6 (.pair (word 0) (.var 0)))
        (.letE (host 1 7 (.pair (word 1) (.first (.var 3))))
          (.letE (host 1 8 (.pair (word 2) (.first (.second (.var 4)))))
            (.letE (host 1 9 (.pair (word 3) (.first (.second (.second (.var 5))))))
              (.letE (host 1 10 (.pair (word 4) (.second (.second (.second (.var 6))))))
                (.ifE (.binary .wordEq (.binary .wordAnd (.var 8) (word 1)) (word 1))
                  (.inRight .word (.inLeft .word (.var 5)))
                  (.inLeft (.sum .word .word) (.var 5)))))))))

/-- std's dispatch and head checks, the flags, then `decoder` and the completion. -/
private def contractExpressionWith (stepBody : Expr) (shape : Shape) (decoder : Expr) : Expr :=
  .letE stepBody
    (.letE (host 7 1 .unit)
      (.ifE (gt (word 4) (.var 0)) (reject noSelectorError)
        (.ifE (.binary .wordEq (selectorWord 2) (word shape.selector))
          (.ifE (gt (word (4 + shape.argumentsHead)) (.var 0)) (reject truncatedError)
            (.letE (readAt 2 (word 4))
              (.caseE decoder completion (.inRight .word (.inLeft .word (.var 0))))))
          (reject noSelectorError))))

private def contractExpression (stepBody : Expr) (shape : Shape) : Expr :=
  contractExpressionWith stepBody shape (decode shape)

def canonicalProgram (step : Aggregates.CheckedDAG) (shape : Shape) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body shape
}

def canonicalNodes (step : Aggregates.CheckedDAG) (shape : Shape) : Nat :=
  programNodes (canonicalProgram step shape)

/-- Syntax-only size of the wrapper without the step, measured with a one-node
placeholder step that is never admitted or run. -/
def shellNodes (shape : Shape) : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0) shape} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

/-- The wrapper without the step and the shape's decoder: the dispatch, the
head check, the flags and the completion, around a decoder of no
constructors. It lies inside a case's node budget. -/
def programOverhead (shape : Shape) : Nat :=
  let wrapper := contractExpressionWith (word 0) shape (failed emptyRevert)
  programNodes {resultType := resultType, dataDefinitions := [], body := wrapper} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

/-- The shape's decoder, the tag lookup and the field decoders, which lies
outside the step budget. -/
def decoderNodes (shape : Shape) : Nat := shellNodes shape - programOverhead shape

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  shape : Shape
  valid : shape.Valid
  checked : (canonicalProgram step shape).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.shape

def ofParts? (step : Aggregates.CheckedDAG) (shape : Shape) : Option CheckedPlan :=
  if valid : shape.Valid then
    if checked : (canonicalProgram step shape).check = true then some ⟨step, shape, valid, checked⟩
    else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

theorem hostChecked (plan : CheckedPlan) : plan.program.toCore.checkHost = true :=
  Program.check_promotes_current plan.checked

def code (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.program.toCore, plan.hostChecked⟩

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.code rfl

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

end CheckedPlan
end Solcore.Synthesis.Core.EnumArgument
