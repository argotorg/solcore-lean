import Solcore.Synthesis.Core.EnumArgument

/-! A checked protocol that takes a calldata array of values of a user enum and
two indices, and decodes the array's head and the two indexed elements from the
calldata itself, as the pinned std's dispatcher, lazy calldata-array decoder,
`abiArrayGet` and derived ABI decoder do, without std's decoder code. The ABI
supplies `run(uint256 flags, E[] items, uint256 first, uint256 second)`.
Calldata shorter than four bytes or with another selector reaches the default
fallback; calldata shorter than the arguments' 128-byte head is truncated. The
array's offset `o` at 36 must satisfy `o <= size - 4`, its length Word `L` must
exist at `p = 4 + o`, and its `L` elements of stride `s` must fit after it,
with `L <= ~0 / s`; `s` is the body head of a static enum and 32 for a dynamic
one. Each index `i` must be below `L`, else the call reverts with
`ArrayOutOfBounds()`. A static element's body is inline at `R + i s`, where
`R = p + 32`; a dynamic one's is at `R + e` for the offset `e` at `R + 32 i`,
with `e <= size - R` and its tag Word present. The tag must equal one
constructor's `keccak256("Name(fields)")`, otherwise the call reverts with
empty data, which the contract writes as the Word zero; the fields follow as
for one enum argument. The protocol then writes
`r = step(prior + L + index + w0 + w1 + w2 + index' + w0' + w1' + w2')` to slot
0, the length to slot 1 and each element's one-based index and Words to slots 2
to 5 and 6 to 9, and odd flags revert with `r`. A std rejection reverts with its
error selector as the Word payload. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.EnumArray

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.StdDispatch
open Solcore.Synthesis.Core.EnumArgument (Payload Constructor Shape fieldsType maxPayloadLength emptyRevert tag)

def version : String := "core-enum-array-argument-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- Slot zero, the length and two elements' index and three Words. -/
def slotCount : Nat := 10

/-- std's `ArrayOutOfBounds()` selector. -/
def outOfBoundsError : Nat := 0x7f52b2bf

/-- The flags, the array's offset and the two indices. -/
def argumentsHead : Nat := 128

/-- The share of the wrapper that lies inside the node budget: the wrapper of
`stateful-enum-arguments`, so that both profiles give the step one budget. -/
def reservedNodes : Nat := 168

private def hashWord (text : String) : Word :=
  (decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash text.toUTF8)).getD Word.zero

/-- std's structural signature: the enum's `sum(...)` signature, then `[]`. -/
def signature (shape : Shape) : String :=
  "run(uint256," ++ Shape.sumSignature shape.constructors ++ "[],uint256,uint256)"

/-- The method selector: the first four bytes of the signature's hash. -/
def selector (shape : Shape) : Nat := (hashWord (signature shape)).val / 2 ^ 224

/-- `ABIAttribs.headSize` of an element: the whole body of a static enum, one
offset Word of a dynamic one. -/
def stride (shape : Shape) : Nat := if shape.dynamic then 32 else shape.bodyHead

/-- The binder at `position`, counted from the outermost, in a frame of
`locals` binders. -/
private def binder (locals position : Nat) : Expr := .var (locals - 1 - position)

/- Binder positions: the step 0, the size 1, the flags 2, the array's offset 3,
the length Word's position `p` 4, the length 5, the element region `R` 6, the
indices 7 and 8 and the element decoder 9. In the decoder's body the index is
at 9 instead. -/
private def size (locals : Nat) : Expr := binder locals 1
private def length (locals : Nat) : Expr := binder locals 5
private def region (locals : Nat) : Expr := binder locals 6

private def failed (error : Nat) : Expr := .inRight fieldsType (word error)

private def decoded (index : Nat) (first second third : Expr) : Expr :=
  .inLeft .word (.pair (word index) (.pair first (.pair second third)))

/-- Keeps the first `remaining` bytes of a big-endian Word: all of them from 32
on, where the shift reaches 256, and none for zero. -/
private def mask (remaining : Expr) : Expr :=
  .unary .wordNot (.binary .wordShr (word (2 ^ 256 - 1)) (mul (word 8) remaining))

/-- Payload chunk `index` with the payload length at `lengthAt` and its start
at `startAt`: the payload Word masked to the payload when all its bytes exist,
otherwise the Word that ends at the last payload byte shifted to the chunk's
start. -/
private def chunk (locals lengthAt startAt index : Nat) : Expr :=
  .ifE (gt (binder locals lengthAt) (word (32 * index)))
    (.caseE (host 8 locals (add (binder locals startAt) (word (32 * index))))
      (.binary .wordShl
        (readAt (locals + 1) (sub (add (binder (locals + 1) lengthAt) (binder (locals + 1) startAt)) (word 32)))
        (mul (word 8) (sub (word (32 * (index + 1))) (binder (locals + 1) lengthAt))))
      (.binary .wordAnd (.var 0) (mask (sub (binder (locals + 1) lengthAt) (word (32 * index))))))
    (word 0)

/-- Constructor `index`'s fields of a static element whose body starts at
`startAt`, inside the checked region. -/
private def staticFields (locals startAt index : Nat) : Payload → Expr
  | .noWords | .bytes => decoded index (word 0) (word 0) (word 0)
  | .oneWord => decoded index (readAt locals (add (binder locals startAt) (word 32))) (word 0) (word 0)
  | .twoWords | .pair => decoded index (readAt locals (add (binder locals startAt) (word 32)))
      (readAt locals (add (binder locals startAt) (word 64))) (word 0)

/-- Constructor `index`'s fields of a dynamic element whose body starts at
`start`. Each Word must exist; a `bytes` value's tail offset `t` must satisfy
`t <= size - start`, its length Word must exist at `q = start + t` and its
length must fit after it. -/
private def dynamicFields (locals start index : Nat) : Payload → Expr
  | .noWords => decoded index (word 0) (word 0) (word 0)
  | .oneWord =>
      .ifE (gt (word 64) (sub (size locals) (binder locals start))) (failed truncatedError)
        (decoded index (readAt locals (add (binder locals start) (word 32))) (word 0) (word 0))
  | .twoWords | .pair =>
      .ifE (gt (word 96) (sub (size locals) (binder locals start))) (failed truncatedError)
        (decoded index (readAt locals (add (binder locals start) (word 32)))
          (readAt locals (add (binder locals start) (word 64))) (word 0))
  | .bytes =>
      -- The tail offset at `locals`, `q` at `locals + 1`, the length at
      -- `locals + 2` and the payload start at `locals + 3`.
      .ifE (gt (word 64) (sub (size locals) (binder locals start))) (failed truncatedError)
        (.letE (readAt locals (add (binder locals start) (word 32)))
          (.ifE (gt (binder (locals + 1) locals) (sub (size (locals + 1)) (binder (locals + 1) start))) (failed truncatedError)
            (.letE (add (binder (locals + 1) start) (binder (locals + 1) locals))
              (.ifE (gt (word 32) (sub (size (locals + 2)) (binder (locals + 2) (locals + 1)))) (failed truncatedError)
                (.letE (readAt (locals + 2) (binder (locals + 2) (locals + 1)))
                  (.ifE (gt (binder (locals + 3) (locals + 2))
                      (sub (size (locals + 3)) (add (binder (locals + 3) (locals + 1)) (word 32)))) (failed truncatedError)
                    (.ifE (gt (binder (locals + 3) (locals + 2)) (word maxPayloadLength)) (failed truncatedError)
                      (.letE (add (binder (locals + 3) (locals + 1)) (word 32))
                        (decoded index (binder (locals + 4) (locals + 2))
                          (chunk (locals + 4) (locals + 2) (locals + 3) 0)
                          (chunk (locals + 4) (locals + 2) (locals + 3) 1))))))))))

/-- The tag at `tagAt` against each constructor's tag in declaration order; no
match is the unknown tag. -/
private def dispatch (fields : Nat → Payload → Expr) (locals tagAt : Nat) : Nat → List Constructor → Expr
  | _, [] => failed emptyRevert
  | index, constructor :: rest =>
      .ifE (.binary .wordEq (binder locals tagAt) (.word (tag constructor))) (fields index constructor.payload)
        (dispatch fields locals tagAt (index + 1) rest)

/-- The decoder's body at the index (at 9), in a frame of ten binders, with
`lookup` the tag lookup and the fields. A static element's body start is at 10
and its tag at 11; a dynamic element's offset is at 10, its body start at 11 and
its tag at 12. -/
private def elementBodyWith (shape : Shape) (lookup : Option Expr) : Expr :=
  let decode :=
    if shape.dynamic then
      .letE (readAt 10 (add (region 10) (mul (word 32) (binder 10 9))))
        (.ifE (gt (binder 11 10) (sub (size 11) (region 11))) (failed truncatedError)
          (.letE (add (region 11) (binder 11 10))
            (.ifE (gt (word 32) (sub (size 12) (binder 12 11))) (failed truncatedError)
              (.letE (readAt 12 (binder 12 11))
                (lookup.getD (dispatch (dynamicFields 13 11) 13 12 1 shape.constructors))))))
    else
      .letE (add (region 10) (mul (binder 10 9) (word (stride shape))))
        (.letE (readAt 11 (binder 11 10)) (lookup.getD (dispatch (staticFields 12 10) 12 11 1 shape.constructors)))
  .ifE (gt (length 10) (binder 10 9)) decode (failed outOfBoundsError)

/-- An element's index or one of its three Words. -/
private def field (element : Expr) : Nat → Expr
  | 0 => .first element
  | 1 => .first (.second element)
  | 2 => .first (.second (.second element))
  | _ => .second (.second (.second element))

/-- After both elements (at 10 and 11): the step result of the prior slot zero,
the length and both elements' index and Words (the sum at 12, the result at
13), the ten writes (at 14 to 23) and the completion. -/
private def completion : Expr :=
  let element := fun (position : Nat) (locals : Nat) (index : Nat) => field (binder locals position) index
  let summands := [length 12] ++ (List.range 4).map (element 10 12) ++ (List.range 4).map (element 11 12)
  let values : List (Nat → Expr) := [fun locals => binder locals 13, length] ++
    (List.range 4).map (fun index locals => element 10 locals index) ++
    (List.range 4).map (fun index locals => element 11 locals index)
  let writes := values.zipIdx.foldr (fun (value, slot) rest =>
      .letE (host 1 (14 + slot) (.pair (word slot) (value (14 + slot)))) rest)
    (.ifE (.binary .wordEq (.binary .wordAnd (binder 24 2) (word 1)) (word 1))
      (.inRight .word (.inLeft .word (binder 24 13)))
      (.inLeft (.sum .word .word) (binder 24 13)))
  .letE (summands.foldl add (host 0 12 (word 0))) (.letE (.apply (binder 13 0) (binder 13 12)) writes)

/-- std's dispatch, head and array checks, the indices, then the decoder `body`
applied to each index in turn and the completion. -/
private def contractExpressionWith (stepBody : Expr) (shape : Shape) (body : Expr) : Expr :=
  let width := stride shape
  .letE stepBody
    (.letE (host 7 1 .unit)
      (.ifE (gt (word 4) (size 2)) (reject noSelectorError)
        (.ifE (.binary .wordEq (selectorWord 2) (word (selector shape)))
          (.ifE (gt (word (4 + argumentsHead)) (size 2)) (reject truncatedError)
            (.letE (readAt 2 (word 4))
              (.letE (readAt 3 (word 36))
                (.ifE (gt (binder 4 3) (sub (size 4) (word 4))) (reject truncatedError)
                  (.letE (add (word 4) (binder 4 3))
                    (.ifE (gt (word 32) (sub (size 5) (binder 5 4))) (reject truncatedError)
                      (.letE (readAt 5 (binder 5 4))
                        (.ifE (gt (binder 6 5) (word ((2 ^ 256 - 1) / width))) (reject truncatedError)
                          (.ifE (gt (mul (binder 6 5) (word width)) (sub (size 6) (add (binder 6 4) (word 32))))
                              (reject truncatedError)
                            (.letE (add (binder 6 4) (word 32))
                              (.letE (readAt 7 (word 68))
                                (.letE (readAt 8 (word 100))
                                  (.letE (.lambda .word (.sum fieldsType .word) body)
                                    (.caseE (.apply (binder 10 9) (binder 10 7))
                                      (.caseE (.apply (binder 11 9) (binder 11 8))
                                        completion
                                        (.inRight .word (.inLeft .word (.var 0))))
                                      (.inRight .word (.inLeft .word (.var 0)))))))))))))))))
          (reject noSelectorError))))

private def contractExpression (stepBody : Expr) (shape : Shape) : Expr :=
  contractExpressionWith stepBody shape (elementBodyWith shape none)

def canonicalProgram (step : Aggregates.CheckedDAG) (shape : Shape) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body shape
}

def canonicalNodes (step : Aggregates.CheckedDAG) (shape : Shape) : Nat :=
  programNodes (canonicalProgram step shape)

private def placeholderNodes : Nat :=
  programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

/-- Syntax-only size of the contract without the step, measured with a one-node
placeholder step that is never admitted or run. -/
def shellNodes (shape : Shape) : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0) shape} -
    placeholderNodes

/-- The array wrapper without the step and the tag lookup: the dispatch, the
head and array checks, the indices, the decoder's bounds check and element
start, both applications and the completion, around a lookup of no
constructors. -/
def wrapperNodes (shape : Shape) : Nat :=
  let wrapper := contractExpressionWith (word 0) shape (elementBodyWith shape (some (failed emptyRevert)))
  programNodes {resultType := resultType, dataDefinitions := [], body := wrapper} - placeholderNodes

/-- The shape's tag lookup and field decoders. -/
def decoderNodes (shape : Shape) : Nat := shellNodes shape - wrapperNodes shape

/-- The nodes outside a case's budget: the wrapper beyond the reservation and
the decoder. -/
def outsideNodes (shape : Shape) : Nat := shellNodes shape - reservedNodes

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
end Solcore.Synthesis.Core.EnumArray
