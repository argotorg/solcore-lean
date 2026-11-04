import Solcore.Synthesis.Internal.Aggregates
import Solcore.Synthesis.Internal.AbiReturns
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract
import Solcore.Abi.Keccak256
import Solcore.Synthesis.Core.StdDispatch
import Solcore.Synthesis.Stateful.Sequence
import Solcore.Synthesis.Internal.Storage

/-!
# Profiles: enums across the ABI

The profiles `stateful-enum-returns`, `stateful-enum-arguments` and `stateful-enum-array-arguments`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.EnumReturn
/-! A checked protocol that returns a value of a user enum of two to four
constructors. The ABI supplies
`run(uint256 flags, uint256 input, uint256 choice, uint256 length)`; the
contract reads `prior`, slot 0, and `last`, slot 2, applies a closed aggregate
step to `prior + input`, writes the result `r` to slot 0, slot 1 plus one to
slot 1 and the input to slot 2, then rereads slot 1 as `count`. Odd flags revert
with `r`. Even flags return constructor `choice mod n` with its tag Word and its
fields: none, `d0 = r · K`, `(d0, d1)` with `d1 = (count · K) xor last`, or the
first `length mod 65` bytes of `d0` and `d1`, under the enum entry convention.
Each constructor's tag is `keccak256("Name(fields)")`, std's variant tag. The
public contract runtime commits or rolls back the resulting working world. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.EnumReturn

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-enum-return-contract-v1"

/-- Slot zero, the call count and the last input. -/
def slotCount : Nat := 3

/-- The longest returned `bytes` field; the contract reads its length Word
modulo one more. -/
def maxLength : Nat := CoreContractEntryProfile.boundedBytesLimit

def lengthModulus : Nat := maxLength + 1

/-- The bytes-return profile's odd constant. -/
def multiplier : Nat := BytesReturn.multiplier

/-- Constructor names, drawn without repetition. They avoid std's own names and
vary in length. -/
def nameBank : List String :=
  ["Idle", "Ready", "Pair", "Blob", "Settled", "Q", "Rejected", "OverflowedAccumulator"]

/-- The smallest and largest constructor counts. -/
def minConstructors : Nat := 2
def maxConstructors : Nat := 4

/-- The most constructors that carry `bytes`. -/
def maxBytesConstructors : Nat := 2

/-- One constructor: its name and its fields. -/
structure Constructor where
  name : String
  payload : EnumPayload
  deriving Repr, BEq, DecidableEq

/-- The ABI signature of a constructor's fields, as std's `sigStr` writes them. -/
def fieldSignature : EnumPayload → String
  | .noWords => ""
  | .oneWord => "uint256"
  | .twoWords => "uint256,uint256"
  | .boundedBytes => "bytes"

/-- std's variant tag: `keccak256("Name(fields)")` as a big-endian Word. The
digest always has 32 bytes, so the fallback is unreachable. -/
def tag (constructor : Constructor) : Word :=
  (decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash
    (constructor.name ++ "(" ++ fieldSignature constructor.payload ++ ")").toUTF8)).getD Word.zero

/-- The returned enum's constructors in declaration order. -/
structure Shape where
  first : Constructor
  second : Constructor
  rest : List Constructor
  deriving Repr, BEq, DecidableEq

namespace Shape

def constructors (shape : Shape) : List Constructor := shape.first :: shape.second :: shape.rest

def payloads (shape : Shape) : List EnumPayload := shape.constructors.map Constructor.payload

/-- Two to four constructors with distinct names from the bank, at most two of
which carry `bytes`. -/
def Valid (shape : Shape) : Prop :=
  shape.rest.length + 2 ≤ maxConstructors ∧ (shape.constructors.map (·.name)).Nodup ∧
    shape.constructors.all (fun constructor => nameBank.contains constructor.name) = true ∧
    (shape.payloads.filter (· == .boundedBytes)).length ≤ maxBytesConstructors

instance (shape : Shape) : Decidable shape.Valid := by
  unfold Valid
  infer_instance

/-- Whether some constructor carries `bytes`, which makes the enum dynamic. -/
def dynamic (shape : Shape) : Bool := shape.payloads.contains .boundedBytes

def profile (shape : Shape) : CoreContractEntryProfile :=
  .enumOutcomeV1 shape.first.payload shape.second.payload (shape.rest.map Constructor.payload)

end Shape

/-- The Wire type of one constructor's value, its tag paired with its fields. -/
def payloadType : EnumPayload → Ty
  | .noWords => .product .word .unit
  | .oneWord => .product .word .word
  | .twoWords => .product .word (.product .word .word)
  | .boundedBytes => .product .word BytesReturn.bytesType

theorem payloadType_toCore (payload : EnumPayload) :
    (payloadType payload).toCore = CoreContractEntryProfile.enumPayloadType payload := by
  cases payload <;> rfl

/-- The right-nested Wire sum of the constructors from `first` on. -/
def enumType (first : EnumPayload) : List EnumPayload → Ty
  | [] => payloadType first
  | next :: rest => .sum (payloadType first) (enumType next rest)

theorem enumType_toCore (first : EnumPayload) (rest : List EnumPayload) :
    (enumType first rest).toCore = CoreContractEntryProfile.enumType first rest := by
  induction rest generalizing first with
  | nil => exact payloadType_toCore first
  | cons next rest ih =>
      simp [enumType, Ty.toCore, payloadType_toCore, ih, CoreContractEntryProfile.enumType]

def returnedType (shape : Shape) : Ty :=
  enumType shape.first.payload (shape.second.payload :: shape.rest.map Constructor.payload)

def resultType (shape : Shape) : Ty := .sum (returnedType shape) (.sum .word .word)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

/-- The binders the completion adds before it builds the value: `c`, the
constructor index, at 0, then the `bytes` value when one is bound, then `d1`
and `d0`. -/
private structure Fields where
  bytes : Nat
  second : Nat
  first : Nat

/-- One constructor's value: its tag Word and its fields. -/
private def fieldsOf (indices : Fields) (constructor : Constructor) : Expr :=
  .pair (.word (tag constructor)) (match constructor.payload with
    | .noWords => .unit
    | .oneWord => .var indices.first
    | .twoWords => .pair (.var indices.first) (.var indices.second)
    | .boundedBytes => .var indices.bytes)

/-- Constructor `index` from `constructor` on, chosen by the Word at 0: each
test injects its constructor left of the remaining ones, or passes right. -/
private def build (indices : Fields) (index : Nat) (constructor : Constructor) :
    List Constructor → Expr
  | [] => fieldsOf indices constructor
  | next :: rest =>
      .ifE (.binary .wordEq (.var 0) (word index))
        (.inLeft (enumType next.payload (rest.map Constructor.payload)) (fieldsOf indices constructor))
        (.inRight (payloadType constructor.payload) (build indices (index + 1) next rest))

/-- The bounded `bytes` value of `length mod 65` bytes of `d0` and `d1`, at 2
and 1 inside its own length binder: the empty value, or the tag `length - 1`
with both data Words. -/
private def bytesValue (length : Nat) : Expr :=
  .letE (.binary .wordMod (.var length) (word lengthModulus))
    (.ifE (.binary .wordEq (.var 0) (word 0))
      (.inLeft BytesReturn.dataType .unit)
      (.inRight .unit (.pair (.binary .wordSub (.var 0) (word 1)) (.pair (.var 2) (.var 1)))))

/-- In a frame of twelve binders: `count` at 0, three Unit writes, then `r`,
`last`, `prior`, the length Word, the choice Word, the input, the flags and the
step at 4 to 11. Odd flags revert with `r`. Otherwise the completion binds
`d0 = r · K` and `d1 = (count · K) xor last`, the `bytes` value when some
constructor carries one, and `c = choice mod n`, then builds constructor `c`. -/
private def completion (shape : Shape) : Expr :=
  let count := shape.constructors.length
  let choose (bound : Nat) (indices : Fields) :=
    .letE (.binary .wordMod (.var (8 + bound)) (word count))
      (.inLeft (.sum .word .word) (build indices 0 shape.first (shape.second :: shape.rest)))
  .ifE (.binary .wordEq (.binary .wordAnd (.var 10) (word 1)) (word 1))
    (.inRight (returnedType shape) (.inLeft .word (.var 4)))
    (.letE (.binary .wordMul (.var 4) (word multiplier))
      (.letE (.binary .wordXor (.binary .wordMul (.var 1) (word multiplier)) (.var 6))
        (if shape.dynamic then
          .letE (bytesValue 9) (choose 3 ⟨1, 2, 3⟩)
        else choose 2 ⟨0, 1, 2⟩)))

private def contractExpression (stepBody : Expr) (shape : Shape) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (readInput 3 68)
          (.letE (readInput 4 100)
            (.letE (host 0 5 (word 0))
              (.letE (host 0 6 (word 2))
                (.letE (.apply (.var 6) (.binary .wordAdd (.var 1) (.var 4)))
                  (.letE (host 1 8 (.pair (word 0) (.var 0)))
                    (.letE (host 1 9 (.pair (word 1) (.binary .wordAdd (host 0 9 (word 1)) (word 1))))
                      (.letE (host 1 10 (.pair (word 2) (.var 7)))
                        (.letE (host 0 11 (word 1))
                          (completion shape))))))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) (shape : Shape) : Program := {
  resultType := resultType shape
  dataDefinitions := []
  body := contractExpression step.program.body shape
}

def canonicalNodes (step : Aggregates.CheckedDAG) (shape : Shape) : Nat :=
  programNodes (canonicalProgram step shape)

/-- Syntax-only measurement of the shell, the wrapper without the step, using a
one-node placeholder step that is never admitted or run. The shell lies inside
a case's node budget. -/
def shellNodes (shape : Shape) : Nat :=
  programNodes {resultType := resultType shape, dataDefinitions := [], body := contractExpression (word 0) shape} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

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

theorem resultType_eq (plan : CheckedPlan) :
    plan.code.program.resultType = plan.shape.profile.resultType := by
  change (resultType plan.shape).toCore = _
  simp [resultType, returnedType, Ty.toCore, enumType_toCore, Shape.profile,
    CoreContractEntryProfile.resultType]

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.enumOutcomeV1 plan.code plan.shape.first.payload plan.shape.second.payload
    (plan.shape.rest.map Constructor.payload) plan.resultType_eq

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

theorem contract_entryProfile (plan : CheckedPlan) :
    plan.contract.entryProfile = plan.shape.profile := rfl

end CheckedPlan
end Solcore.Synthesis.Core.EnumReturn
end

section
-- leanmerge: from Solcore.Synthesis.Core.EnumArgument
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
end

section
-- leanmerge: from Solcore.Synthesis.Core.EnumArray
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
one. Each index `i` must be below `L`, else std panics with `Panic(0x32)`.
A static element's body is inline at `R + i s`, where
`R = p + 32`; a dynamic one's is at `R + e` for the offset `e` at `R + 32 i`,
with `e <= size - R` and its tag Word present. The tag must equal one
constructor's `keccak256("Name(fields)")`, otherwise the call reverts with
empty data, which the contract writes as the Word zero; the fields follow as
for one enum argument. The protocol then writes
`r = step(prior + L + index + w0 + w1 + w2 + index' + w0' + w1' + w2')` to slot
0, the length to slot 1 and each element's one-based index and Words to slots 2
to 5 and 6 to 9, and odd flags revert with `r`. A std rejection reverts with its
error selector, or for the panic the panic's selector, as the Word payload. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.EnumArray

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.StdDispatch
open Solcore.Synthesis.Core.EnumArgument (Payload Constructor Shape fieldsType maxPayloadLength emptyRevert tag)

def version : String := "core-enum-array-argument-contract-v2"
def resultType : Ty := .sum .word (.sum .word .word)

/-- Slot zero, the length and two elements' index and three Words. -/
def slotCount : Nat := 10

/-- std's `Panic(uint256)` selector: since solcore-rs `e2eef194`, an index past
the length is `out_of_bounds()`, which panics with `outOfBoundsPanic`. -/
def outOfBoundsError : Nat := 0x4e487b71

/-- The panic code of an array index past the length. -/
def outOfBoundsPanic : Nat := 0x32

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
end

section
-- leanmerge: from Solcore.Synthesis.Source.EnumArgumentEmitter
/-! Emit the enum-argument protocol as a public method taking a user enum. The
source declares the struct `ScPair` when a constructor carries it, then
`SynthesizedEnum` with the shape's constructors; std derives their `Generic`
and ABI instances, and its dispatcher decodes the argument before the body
runs. The method matches the value with one arm per constructor in declaration
order, each setting the one-based index and the decoded Words; a struct's
fields are bound through `ScPair(a, b)`. A `bytes` arm reads the length with
`mload` from `Typedef.rep` and each of its two chunks only when the length
exceeds the chunk's start, since std zeroes the decoded payload's padding but
nothing past it. The step, the five writes and the odd-flags revert follow the
original Core contract in order. Memory at zero is touched only before the
terminal revert. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EnumArgument

open Solcore.Synthesis.Core.EnumArgument (CheckedPlan Constructor Shape)

def emitterVersion : String := "solcore-source-enum-arguments-v1"
def wrapperVersion : String := "solcore-enum-arguments-contract-v1"
def contractName : String := "SynthesizedEnumArguments"
def enumName : String := "SynthesizedEnum"
def structName : String := "ScPair"
def methodName : String := "run"
def deployPath : List String := ["SynthesizedEnumArgumentsDeploy"]
def runtimePath : List String := ["SynthesizedEnumArgumentsDeploy", "SynthesizedEnumArguments"]

/-- The method selector as `0x` and eight hexadecimal digits. -/
def selectorText (shape : Shape) : String :=
  let digits := Nat.toDigits 16 shape.selector
  "0x" ++ String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

/-- A constructor's declaration: its name and its fields' types. -/
def declaration (constructor : Constructor) : String :=
  constructor.name ++ match constructor.payload with
    | .noWords => ""
    | .oneWord => "(uint256)"
    | .twoWords => "(uint256, uint256)"
    | .pair => "(" ++ structName ++ ")"
    | .bytes => "(memory<bytes>)"

/-- The arm of constructor `index`: its pattern, the one-based index and the
decoded Words. -/
def armLines (index : Nat) (constructor : Constructor) : List String :=
  let value := "            case " ++ enumName ++ "." ++ constructor.name
  let marker := "                sc_index = " ++ toString (index + 1) ++ ";"
  let words := ["                sc_w0 = Typedef.rep(sc_a0);", "                sc_w1 = Typedef.rep(sc_a1);"]
  (match constructor.payload with
    | .noWords => [value ++ " {", marker]
    | .oneWord => [value ++ "(sc_a0) {", marker, words.getD 0 ""]
    | .twoWords => [value ++ "(sc_a0, sc_a1) {", marker] ++ words
    | .pair => [value ++ "(" ++ structName ++ "(sc_a0, sc_a1)) {", marker] ++ words
    | .bytes => [value ++ "(sc_b) {", marker,
        "                let sc_data: word = Typedef.rep(sc_b);",
        "                sc_w0 = mload(sc_data);",
        "                if (sc_w0 > 0) {",
        "                    sc_w1 = mload((sc_data + 32));",
        "                }",
        "                if (sc_w0 > 32) {",
        "                    sc_w2 = mload((sc_data + 64));",
        "                }"]) ++ ["            }"]

/-- The struct, when a constructor carries it, then the enum. -/
def typeLines (shape : Shape) : List String :=
  let constructors := shape.constructors
  (if shape.payloads.contains .pair then
      ["struct " ++ structName ++ " {", "    a: uint256;", "    b: uint256;", "}", ""]
    else []) ++
    ["enum " ++ enumName ++ " {"] ++
    constructors.zipIdx.map (fun (constructor, index) =>
      "    " ++ declaration constructor ++ if index + 1 = constructors.length then "" else ",") ++
    ["}", ""]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let constructors := plan.shape.constructors
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", "import * from std.Generic;",
    "import * from std.ABIGeneric;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), ""] ++ typeLines plan.shape
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
    "    function " ++ methodName ++ "(flags: uint256, value: " ++ enumName ++ ") public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_index: word = 0;",
    "        let sc_w0: word = 0;",
    "        let sc_w1: word = 0;",
    "        let sc_w2: word = 0;",
    "        match (value) {"] ++
    (constructors.zipIdx.map fun (constructor, index) => armLines index constructor).flatten ++
    ["        }",
    "        let sc_result: word = sc_step(((((sload(0) + sc_index) + sc_w0) + sc_w1) + sc_w2));",
    "        sstore(0, sc_result);",
    "        sstore(1, sc_index);",
    "        sstore(2, sc_w0);",
    "        sstore(3, sc_w1);",
    "        sstore(4, sc_w2);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature := plan.shape.signature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.EnumArgument
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.EnumArgumentExecution
/-! Execute the original checked enum-argument contract over a persistent
account world. A transaction is a canonical call of
`run(uint256 flags, SynthesizedEnum value)`, a constructor with its field Words
or `bytes` payload, together with one malformation of its calldata; the
contract receives the malformed bytes. `stdDecode` is a second model of the
pinned std's dispatcher and derived enum decoder, written over the bytes
instead of in Core, which prescribes each transaction's outcome and the Words
the body decodes. `model` runs the protocol on its decisions with the step
evaluated alone in Core. Observations report slots zero to four and the
contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.EnumArgumentExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (CheckedPlan Constructor Payload Shape)
open Solcore.Synthesis.Core.StdDispatch (noSelectorError truncatedError)

def historySchema : String := "solcore-lean.enum-argument-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- The longest canonical `bytes` payload. -/
def maxLength : Nat := 64

/-- How a transaction's calldata departs from the canonical encoding of its
constructor: the malformed-calldata kinds; an unknown tag, another
constructor's tag, a head offset, the offset zero with the flags replaced by a
constructor's tag, an unread head Word, a `bytes` tail offset or length Word,
or nonzero padding. Padding patterns are `0xff` (0), the ramp `1, 2, 3, ...` (1)
or a single `0x01` in the last padding byte (2). -/
inductive Malformation where
  | none
  | short (bytes : Nat)
  | selector (mask : Nat)
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | tag (value : Word)
  | retag (index : Nat)
  | offset (value : Word)
  | aliased (index : Nat)
  | unused (value : Word)
  | tail (value : Word)
  | length (value : Word)
  | padding (pattern : Nat)
  deriving BEq, Repr

structure Transaction where
  id : String
  flags : Word
  choice : Nat
  first : Word
  second : Word
  length : Nat
  malformation : Malformation
  deriving BEq

/-- The bytes profile's odd constant. -/
def multiplier : Nat := Solcore.Synthesis.Core.BytesReturn.multiplier

/-- A `bytes` payload: the first `length` bytes of `first · K` and
`second · K`. -/
def payload (first second : Word) (length : Nat) : ByteArray :=
  (encodeWordBytesBE (first * Word.ofNatModulo multiplier) ++
    encodeWordBytesBE (second * Word.ofNatModulo multiplier)).extract 0 length

def paddedLength (length : Nat) : Nat := (length + 31) / 32 * 32

private def zeros (count : Nat) : ByteArray := ByteArray.mk (Array.replicate count 0)

/-- Where the body starts: inline at 36 for a static enum, at the canonical
offset 64 past the arguments' start for a dynamic one. -/
def bodyStart (shape : Shape) : Nat := if shape.dynamic then 68 else 36

/-- The chosen constructor, the first for an index outside the shape. -/
def constructorAt (shape : Shape) (index : Nat) : Constructor := shape.constructors.getD index shape.first

def constructor (shape : Shape) (tx : Transaction) : Constructor := constructorAt shape tx.choice

/-- The canonical body: the tag, the fields, zero Words up to the body's head,
then a `bytes` field's length Word and zero-padded payload behind the tail
offset, which is the body's head. -/
def body (shape : Shape) (tx : Transaction) : ByteArray :=
  let chosen := constructor shape tx
  let head := match chosen.payload with
    | .noWords => ByteArray.empty
    | .oneWord => encodeWordBytesBE tx.first
    | .twoWords | .pair => encodeWordBytesBE tx.first ++ encodeWordBytesBE tx.second
    | .bytes => encodeWordBytesBE (Word.ofNatModulo shape.bodyHead)
  let tail := match chosen.payload with
    | .bytes => encodeWordBytesBE (Word.ofNatModulo tx.length) ++ payload tx.first tx.second tx.length ++
        zeros (paddedLength tx.length - tx.length)
    | _ => ByteArray.empty
  encodeWordBytesBE (EnumArgument.tag chosen) ++ head ++
    zeros (shape.bodyHead - 32 - EnumArgument.headSize chosen.payload) ++ tail

private def selectorBytes (selector : Nat) : ByteArray :=
  ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

def canonicalBytes (shape : Shape) (tx : Transaction) : ByteArray :=
  selectorBytes shape.selector ++ encodeWordBytesBE tx.flags ++
    (if shape.dynamic then encodeWordBytesBE (Word.ofNatModulo 64) else ByteArray.empty) ++ body shape tx

def canonicalSize (shape : Shape) (tx : Transaction) : Nat := (canonicalBytes shape tx).size

/-- The payload start of a canonical `bytes` constructor. -/
def payloadStart (shape : Shape) : Nat := bodyStart shape + shape.bodyHead + 32

def paddingCount (length : Nat) : Nat := paddedLength length - length

/-- The last payload Word with its padding replaced by the pattern. -/
private def paddedWord (bytes : ByteArray) (length pattern : Nat) : Word :=
  let start := length / 32 * 32
  let count := paddingCount length
  let padding := (List.range count).map fun position =>
    match pattern with
    | 0 => (0xff : UInt8)
    | 1 => (position + 1).toUInt8
    | _ => if position + 1 = count then 1 else 0
  Word.ofNatModulo (((bytes.extract start length).data.toList ++ padding).foldl
    (fun total byte => total * 256 + byte.toNat) 0)

/-- The first head Word a narrower constructor leaves unread. -/
def unusedPosition (shape : Shape) (tx : Transaction) : Nat :=
  bodyStart shape + 32 + EnumArgument.headSize (constructor shape tx).payload

/-- Whether the chosen constructor's head is narrower than the body's head. -/
def hasUnused (shape : Shape) (tx : Transaction) : Bool :=
  32 + EnumArgument.headSize (constructor shape tx).payload < shape.bodyHead

def carriesBytes (shape : Shape) (tx : Transaction) : Bool := (constructor shape tx).payload == .bytes

/-- The calldata a transaction sends. -/
def inputBytes (shape : Shape) (tx : Transaction) : ByteArray :=
  let canonical := canonicalBytes shape tx
  let start := bodyStart shape
  let change : StdCalldata.Change := match tx.malformation with
    | .none => .none
    | .short bytes => .short bytes
    | .selector mask => .selector mask
    | .truncate kept => .truncate kept
    | .trailing count pattern => .trailing count pattern
    | .tag value => .word start value
    | .retag index => .word start (EnumArgument.tag (constructorAt shape index))
    | .offset value => .word 36 value
    | .aliased _ => .word 36 Word.zero
    | .unused value => .word (unusedPosition shape tx) value
    | .tail value => .word (start + 32) value
    | .length value => .word (start + shape.bodyHead) value
    | .padding pattern => .word (payloadStart shape + tx.length / 32 * 32)
        (paddedWord (payload tx.first tx.second tx.length) tx.length pattern)
  let changed := change.apply canonical
  match tx.malformation with
  | .aliased index => StdCalldata.replaceWord changed 4 (EnumArgument.tag (constructorAt shape index))
  | _ => changed

/-- A malformation within its bounds, where it applies: cuts inside the
calldata past the selector, the malformed-calldata bounds, another
constructor's tag, offsets and aliases of a dynamic enum, an unread head Word
of a narrower constructor, and `bytes` changes of a `bytes` constructor, its
padding only when there is some. -/
def Malformation.valid (shape : Shape) (tx : Transaction) : Malformation → Bool
  | .none => true
  | .short bytes => bytes < 4
  | .selector mask => 0 < mask && mask < 2 ^ 32
  | .truncate kept => 4 ≤ kept && kept < canonicalSize shape tx
  | .trailing count pattern => 1 ≤ count && count ≤ 64 && pattern < 3
  | .tag value => !shape.constructors.any (EnumArgument.tag · == value)
  | .retag index => index < shape.constructors.length && index != tx.choice
  | .offset value => shape.dynamic && value.val != 64
  | .aliased index => shape.dynamic && index < shape.constructors.length
  | .unused value => hasUnused shape tx && value != Word.zero
  | .tail value => carriesBytes shape tx && value.val != shape.bodyHead
  | .length value => carriesBytes shape tx && value.val != tx.length
  | .padding pattern => carriesBytes shape tx && paddingCount tx.length != 0 && pattern < 3

/-- The Words std decodes: the flags, the one-based index and the three
protocol Words. -/
structure Decoded where
  flags : Word
  index : Nat
  words : Word × Word × Word
  deriving BEq, Repr

/-- The revert data of a std rejection, or the decoded value. -/
abbrev Decision := Except ByteArray Decoded

private def wordAt (input : ByteArray) (offset : Nat) : Word := Word.ofNatModulo (StdCalldata.wordAt input offset)

/-- The payload's zero-padded Word at `offset`, from the bytes that exist. -/
private def chunkAt (input : ByteArray) (start length offset : Nat) : Word :=
  let bytes := (input.extract (start + offset) (start + length)).extract 0 32
  Word.ofNatModulo ((bytes.data.toList ++ List.replicate (32 - bytes.size) (0 : UInt8)).foldl
    (fun total byte => total * 256 + byte.toNat) 0)

/-- The pinned std's decision for `run(uint256 flags, E value)` over raw
calldata, written from `do_exec`, the bounded calldata reader, `abiSumReader`
and the derived decoder. The fallback reverts with `0x4924aef0`, a missing or
out-of-range read with `0x08638556`, and an unknown tag with empty data; the
tag is compared before any field is read. Natural arithmetic cannot wrap, as
std's checks do not. -/
def stdDecode (shape : Shape) (input : ByteArray) : Decision := do
  let size := input.size
  let fail := fun (error : Nat) => (Except.error (selectorBytes error) : Decision)
  if size < 4 || StdCalldata.bigEndian input 0 4 != shape.selector then fail noSelectorError
  else if size < 4 + shape.argumentsHead then fail truncatedError
  else
    let flags := wordAt input 4
    let start? : Option Nat :=
      if shape.dynamic then
        let offset := StdCalldata.wordAt input 36
        if offset > size - 4 then none else some (4 + offset)
      else some 36
    match start? with
    | none => fail truncatedError
    | some start =>
      if size - start < 32 then fail truncatedError
      else
        let found := wordAt input start
        match (shape.constructors.zipIdx.find? fun (constructor, _) => EnumArgument.tag constructor == found) with
        | none => throw ByteArray.empty
        | some (constructor, index) =>
          let decoded := fun (words : Word × Word × Word) => (pure ⟨flags, index + 1, words⟩ : Decision)
          match constructor.payload with
          | .noWords => decoded (Word.zero, Word.zero, Word.zero)
          | .oneWord =>
              if size - start < 64 then fail truncatedError
              else decoded (wordAt input (start + 32), Word.zero, Word.zero)
          | .twoWords | .pair =>
              if size - start < 96 then fail truncatedError
              else decoded (wordAt input (start + 32), wordAt input (start + 64), Word.zero)
          | .bytes =>
              if size - start < 64 then fail truncatedError
              else
                let tail := StdCalldata.wordAt input (start + 32)
                if tail > size - start then fail truncatedError
                else if size - (start + tail) < 32 then fail truncatedError
                else
                  let length := StdCalldata.wordAt input (start + tail)
                  if length > size - (start + tail + 32) then fail truncatedError
                  else if length > EnumArgument.maxPayloadLength then fail truncatedError
                  else
                    let data := start + tail + 32
                    decoded (Word.ofNatModulo length,
                      if length > 0 then chunkAt input data length 0 else Word.zero,
                      if length > 32 then chunkAt input data length 32 else Word.zero)

/-- std's revert data for a rejected transaction, or none when the body runs. -/
def stdRejection? (shape : Shape) (tx : Transaction) : Option ByteArray :=
  match stdDecode shape (inputBytes shape tx) with
  | .error data => some data
  | .ok _ => none

def calldata (shape : Shape) (tx : Transaction) : String := encodeBytesText (inputBytes shape tx)

def inputData? (shape : Shape) (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes shape tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

/-- Slot zero holds the accumulator, slot one the decoded index and slots two
to four the decoded Words. -/
def observedSlots : List Word := (List.range EnumArgument.slotCount).map Word.ofNatModulo

def slotsJson : Json := toJson (observedSlots.map fun slot => toString slot.val)

def storageJson (account : Account) : Json := toJson (observedSlots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)),
  ("value", toJson (toString (account.storageRead slot).val))])

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation, as for the malformed-calldata
profiles, with each transaction's malformed calldata as the input. -/
def observeContract (contract : CheckedCoreContract) (shape : Shape) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match inputData? shape transaction, registry.resolve? prior bindings.address with
      | none, _ =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "input-limit"), ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | _, none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some input, some ⟨resolved, installed⟩ =>
          let invocation : TopLevelInvocation := {
            target := bindings.address, caller := bindings.caller,
            callValue := Word.zero, inputData := input }
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings),
                ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", slotsJson),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract plan.shape transactions bindings fuel

/-- The step's own Core result at one argument. -/
def stepResult (step : Aggregates.CheckedDAG) (fuel : Nat) (argument : Word) : Option Word :=
  match (step.instantiate argument).toCore.runStateful fuel with
  | .done (.word value) _ => some value
  | _ => none

/-- One modelled transaction: whether it reverts, its whole output and the
slots it leaves committed. -/
structure ModelRow where
  reverted : Bool
  output : ByteArray
  slots : List Word

/-- std's decision, then the protocol: `r = step(prior + index + w0 + w1 + w2)`,
the five writes, and the flags' parity. A rejection outputs std's revert data
and keeps the prior slots. -/
def modelTransaction (step : Aggregates.CheckedDAG) (shape : Shape) (fuel : Nat)
    (prior : List Word) (transaction : Transaction) : Option ModelRow := do
  match stdDecode shape (inputBytes shape transaction) with
  | .error data => return ⟨true, data, prior⟩
  | .ok decoded =>
      let (w0, w1, w2) := decoded.words
      let index := Word.ofNatModulo decoded.index
      let result ← stepResult step fuel (prior.getD 0 Word.zero + index + w0 + w1 + w2)
      if decoded.flags.val % 2 == 1 then return ⟨true, encodeWordBytesBE result, prior⟩
      return ⟨false, encodeWordBytesBE result, [result, index, w0, w1, w2]⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (shape : Shape) (fuel : Nat)
    (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate EnumArgument.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step shape fuel slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

end Solcore.Synthesis.Stateful.EnumArgumentExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.EnumArgumentCases
/-! Enum-argument cases retain one original host-aware Core contract, its enum's
constructors, and an ordered history of transactions, each a constructor with
its field Words or `bytes` length and one malformation of its calldata.
Reductions remove transactions, simplify malformations, shorten lengths, drop
unused constructors, narrow fields, reduce the step and simplify the Words.
Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EnumArgument
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (CheckedPlan Constructor Payload Shape)
open Solcore.Synthesis.Stateful.EnumArgumentExecution (Transaction Malformation Bindings maxLength carriesBytes
  inputBytes stdRejection? calldata slotsJson hasUnused paddingCount canonicalSize bodyStart payloadStart stdDecode)

private def chosenConstructor (shape : Shape) (tx : Transaction) : Constructor :=
  Solcore.Synthesis.Stateful.EnumArgumentExecution.constructor shape tx

def caseSchema : String := "solcore-lean.semantic-enum-argument-case.v1"
def planSchema : String := "solcore-lean.enum-argument-plan.v1"
def profileVersion : String := "stateful-enum-arguments-v1/enum-argument-sequence-seed-v1"
def templateVersion : String := "std-enum-decode-index-words-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-enum-argument-corpus.v1"

/-- Flags values and field Words; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- Lengths drawn with probability one half: empty, the Word boundaries and the
bound. -/
def lengthBank : List Nat := [0, 1, 31, 32, 33, 63, 64]

/-- The largest decoder of a valid shape, four constructors of which two carry
`bytes` and two Words; the tests check it against every shape class. -/
def maxDecoderNodes : Nat := 500

/-- Complete contracts may exceed the step budget by their shape's decoder. -/
def maxProgramNodes : Nat := 512 + maxDecoderNodes

/-- A transaction encodes an existing constructor; only a `bytes` constructor
keeps a length, of at most 64 bytes; its malformation applies, and its calldata
stays within one KiB. -/
def admits (shape : Shape) (tx : Transaction) : Bool :=
  Storage.validId tx.id && tx.choice < shape.constructors.length &&
    tx.length ≤ maxLength && (carriesBytes shape tx || tx.length == 0) &&
    tx.malformation.valid shape tx &&
    (inputBytes shape tx).size ≤ Stateful.StdCalldata.maxCalldata

def validTransactions (shape : Shape) (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (admits shape) = true

instance (shape : Shape) (transactions : List Transaction) : Decidable (validTransactions shape transactions) := by
  unfold validTransactions
  infer_instance

/-- The step's budget is at most 512 nodes; the shape's decoder lies outside it. -/
def contractBound (plan : CheckedPlan) : Nat := 512 + EnumArgument.decoderNodes plan.shape

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions plan.shape transactions
  bounded : Wire.programNodes plan.program ≤ contractBound plan

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

private def transactionRule : String :=
  s!"enum-argument scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, a constructor of the shape, a length of at most {maxLength} that only a bytes constructor's transaction may set, a malformation that applies to it, and calldata of at most 1 KiB"

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions plan.shape transactions then
    if bounded : Wire.programNodes plan.program ≤ contractBound plan then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical enum-argument contract exceeds its case limit"
  else throw transactionRule

/-- Every malformation kind, in catalog order. -/
def malformationKinds : List String :=
  ["none", "short", "selector", "truncate", "trailing", "tag", "retag", "offset", "aliased", "unused",
    "tail", "length", "padding"]

def kindOf : Malformation → String
  | .none => "none"
  | .short _ => "short"
  | .selector _ => "selector"
  | .truncate _ => "truncate"
  | .trailing _ _ => "trailing"
  | .tag _ => "tag"
  | .retag _ => "retag"
  | .offset _ => "offset"
  | .aliased _ => "aliased"
  | .unused _ => "unused"
  | .tail _ => "tail"
  | .length _ => "length"
  | .padding _ => "padding"

abbrev patternNames := Stateful.StdCalldata.patternNames
def paddingNames : List String := ["ones", "ramp", "last-byte"]

def malformationJson : Malformation → Json
  | .none => Json.mkObj [("kind", toJson "none")]
  | .short bytes => Json.mkObj [("kind", toJson "short"), ("bytes", toJson bytes)]
  | .selector mask => Json.mkObj [("kind", toJson "selector"), ("mask", toJson (toString mask))]
  | .truncate kept => Json.mkObj [("kind", toJson "truncate"), ("kept", toJson kept)]
  | .trailing count pattern => Json.mkObj [("kind", toJson "trailing"), ("count", toJson count),
      ("pattern", toJson (patternNames.getD pattern "ramp"))]
  | .tag value => Json.mkObj [("kind", toJson "tag"), ("value", toJson (toString value.val))]
  | .retag index => Json.mkObj [("kind", toJson "retag"), ("constructor", toJson index)]
  | .offset value => Json.mkObj [("kind", toJson "offset"), ("value", toJson (toString value.val))]
  | .aliased index => Json.mkObj [("kind", toJson "aliased"), ("constructor", toJson index)]
  | .unused value => Json.mkObj [("kind", toJson "unused"), ("value", toJson (toString value.val))]
  | .tail value => Json.mkObj [("kind", toJson "tail"), ("value", toJson (toString value.val))]
  | .length value => Json.mkObj [("kind", toJson "length"), ("value", toJson (toString value.val))]
  | .padding pattern => Json.mkObj [("kind", toJson "padding"),
      ("pattern", toJson (paddingNames.getD pattern "last-byte"))]

/-- std's revert data as text: an error selector, `0x` for an unknown tag, or
null when the body runs. -/
def prescribed (shape : Shape) (tx : Transaction) : Option String :=
  (stdRejection? shape tx).map Solcore.ContractRuntime.encodeBytesText

def transactionJson (shape : Shape) (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("choice", toJson tx.choice),
  ("first", toJson (toString tx.first.val)), ("second", toJson (toString tx.second.val)),
  ("length", toJson tx.length), ("malformation", malformationJson tx.malformation),
  ("calldata", toJson (calldata shape tx)),
  ("stdRejection", match prescribed shape tx with
    | some data => toJson data
    | none => Json.null),
  ("value", toJson "0")]

def transactionsJson (shape : Shape) (transactions : List Transaction) : Json :=
  toJson (transactions.map (transactionJson shape))

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

private def natural (json : Json) (key : String) : Except String Nat := do
  let value ← json.getObjValAs? Nat key
  unless value < 2 ^ 32 do throw s!"malformation {key} is out of range"
  return value

private def nameIndex (names : List String) (json : Json) (key : String) : Except String Nat := do
  let name ← json.getObjValAs? String key
  match names.idxOf? name with
  | some index => return index
  | none => throw s!"unknown malformation {key}"

def decodeMalformation (json : Json) : Except String Malformation := do
  match ← json.getObjValAs? String "kind" with
  | "none" => return .none
  | "short" => return .short (← natural json "bytes")
  | "selector" => return .selector (← (← word (← json.getObjValAs? String "mask")).val |> pure)
  | "truncate" => return .truncate (← natural json "kept")
  | "trailing" => return .trailing (← natural json "count") (← nameIndex patternNames json "pattern")
  | "tag" => return .tag (← word (← json.getObjValAs? String "value"))
  | "retag" => return .retag (← natural json "constructor")
  | "offset" => return .offset (← word (← json.getObjValAs? String "value"))
  | "aliased" => return .aliased (← natural json "constructor")
  | "unused" => return .unused (← word (← json.getObjValAs? String "value"))
  | "tail" => return .tail (← word (← json.getObjValAs? String "value"))
  | "length" => return .length (← word (← json.getObjValAs? String "value"))
  | "padding" => return .padding (← nameIndex paddingNames json "pattern")
  | _ => throw "unknown malformation kind"

def decodeTransactions (shape : Shape) (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← natural row "choice",
      ← word (← row.getObjValAs? String "first"), ← word (← row.getObjValAs? String "second"),
      ← natural row "length", ← decodeMalformation (← row.getObjVal? "malformation")⟩
    unless validTransactions shape [transaction] do throw transactionRule
    unless row == transactionJson shape transaction do
      throw "transaction differs from canonical ID, flags, choice, Words, length, malformation, calldata, std outcome or zero-value metadata"
    return transaction
  unless validTransactions shape transactions do throw transactionRule
  return transactions

/-- A constructor's declared field types: none, `uint256`, two of them, the
struct or `bytes`. -/
def fieldsName : Payload → String
  | .noWords => ""
  | .oneWord => "uint256"
  | .twoWords => "uint256,uint256"
  | .pair => structName
  | .bytes => "bytes"

def constructorJson (constructor : Constructor) : Json := Json.mkObj [
  ("name", toJson constructor.name), ("fields", toJson (fieldsName constructor.payload))]

private def payloadOf? (fields : String) : Option Payload :=
  [Payload.noWords, .oneWord, .twoWords, .pair, .bytes].find? (fieldsName · == fields)

/-- The constructors of a list of two or more, in order. -/
def Shape.ofList? : List Constructor → Option Shape
  | first :: second :: rest => some ⟨first, second, rest⟩
  | _ => none

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("constructors", toJson (plan.shape.constructors.map constructorJson)),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported enum-argument plan schema"
  let rows ← (← json.getObjVal? "constructors").getArr?
  unless rows.size ≤ EnumArgument.maxConstructors do throw "an enum has at most four constructors"
  let constructors ← rows.toList.mapM fun row => do
    let some payload := payloadOf? (← row.getObjValAs? String "fields") | throw "unsupported constructor fields"
    return ({name := ← row.getObjValAs? String "name", payload} : Constructor)
  let some shape := Shape.ofList? constructors | throw "an enum needs at least two constructors"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step shape
    | throw "enum-argument plan needs two to four constructors with distinct bank names, at most two with bytes, and full host-Core admission"
  unless json == planJson plan do throw "enum-argument plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ contractBound plan do throw "enum-argument contract exceeds its case limit"
  return plan

def contractJson (shape : Shape) (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson (selectorText shape)),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("enumArgumentPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.plan.shape scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson EnumArgument.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson scenario.plan.shape emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic enum-argument case schema"
  let plan ← checkedPlan (← json.getObjVal? "enumArgumentPlan")
  let transactions ← decodeTransactions plan.shape (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical enum-argument plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == slotsJson do
    throw "observed slots must be zero through four"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.EnumArgumentExecution.observe scenario.plan scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- SplitMix64's finalizer: the generator's draws are affine in its start, so
consecutive seeds would otherwise start streams whose draws follow each other. -/
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

/-- The constructor count, the `bytes` count, four other fields, two `bytes`
positions and four name indices into the shrinking bank. -/
def shapeBounds : List Nat := [3, 4, 4, 4, 4, 4, 4, 4, 8, 7, 6, 5]

def shapeChoices (seed : Seed) : List Nat := boundedDraws seed 0x6172677368617065 shapeBounds

/-- Names drawn from the bank without repetition: each index picks among the
names still left. -/
private def drawNames (indices : List Nat) : List String := Id.run do
  let mut left := EnumArgument.nameBank
  let mut names : Array String := #[]
  for index in indices do
    names := names.push (left.getD index "")
    left := left.eraseIdx index
  return names.toList

/-- Two to four constructors; none carries `bytes` for a `bytes` draw below 2,
otherwise one or two do, at distinct positions. The other fields are none, one
Word, two Words or the struct. -/
def generatedShape (seed : Seed) : Shape :=
  let choices := shapeChoices seed
  let count := 2 + choices.getD 0 0
  let bytesCount := choices.getD 1 0 - 1
  let firstBytes := choices.getD 6 0 % count
  let secondBytes := (firstBytes + 1 + choices.getD 7 0 % (count - 1)) % count
  let payloads := (List.range count).map fun index =>
    if (bytesCount ≥ 1 && index == firstBytes) || (bytesCount ≥ 2 && index == secondBytes) then
      Payload.bytes
    else [Payload.noWords, .oneWord, .twoWords, .pair].getD (choices.getD (2 + index) 0) .noWords
  let names := drawNames ((choices.drop 8).take count)
  let constructors := (names.zip payloads).map fun (name, payload) => ({name, payload} : Constructor)
  (Shape.ofList? constructors).getD ⟨⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩, []⟩

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The kinds that apply to a transaction, in catalog order. -/
def applicableKinds (shape : Shape) (tx : Transaction) : List String :=
  ["short", "selector", "truncate", "trailing", "tag", "retag"] ++
    (if shape.dynamic then ["offset", "aliased"] else []) ++
    (if hasUnused shape tx then ["unused"] else []) ++
    (if carriesBytes shape tx then ["tail", "length"] else []) ++
    (if carriesBytes shape tx && paddingCount tx.length != 0 then ["padding"] else [])

/-- The generation bank of one kind for a transaction, without the entries
that do not apply to it. -/
def malformationBank (shape : Shape) (tx : Transaction) (kind : String) : List Malformation :=
  let size := canonicalSize shape tx
  let start := bodyStart shape
  let head := shape.bodyHead
  let data := payloadStart shape
  let tag := EnumArgument.tag (chosenConstructor shape tx)
  let others := (List.range shape.constructors.length).filter (· != tx.choice)
  let bank : List Malformation := match kind with
    | "short" => [.short 0, .short 1, .short 2, .short 3]
    | "selector" => [.selector 1, .selector (2 ^ 31), .selector (2 ^ 32 - 1)]
    | "truncate" =>
        let cuts := if shape.dynamic then
            [4, 36, 67, 68, 99, 100, 131, 132, 163, 164, start + head - 1, start + head, start + head + 31] ++
              (if carriesBytes shape tx && tx.length > 0 then [data + tx.length - 1] else []) ++
              (if carriesBytes shape tx && paddingCount tx.length != 0 then
                [data + tx.length] else []) ++ [size - 1]
          else [4, 35, 36, 67, size - 32, size - 1]
        (cuts.eraseDups.filter fun kept => 4 ≤ kept && kept < size).map .truncate
    | "trailing" => [.trailing 1 0, .trailing 31 1, .trailing 32 2, .trailing 33 0, .trailing 64 1, .trailing 64 2]
    | "tag" =>
        [w 0, tag + w 1, tag ^^^ w (2 ^ 255), w (2 ^ 256 - 1),
          EnumArgument.tag ⟨(chosenConstructor shape tx).name ++ "(uint256,bytes)", .noWords⟩].eraseDups.map .tag
    | "retag" => others.map .retag
    | "offset" => ([size - 3, size - 4, size - 35, 2 ^ 255, 2 ^ 256 - 4, 2 ^ 256 - 1, 0, 16, 32, 96].map w).eraseDups.map .offset
    | "aliased" => (List.range shape.constructors.length).map .aliased
    | "unused" => [w 1, w (2 ^ 255), w (2 ^ 256 - 1)].map .unused
    | "tail" => ([size - start + 1, size - start, size - start - 31, 0, 32, 2 ^ 255, 2 ^ 256 - 1].map w).eraseDups.map .tail
    | "length" =>
        let fits := size - data
        ([tx.length + 1, fits, fits + 1, EnumArgument.maxPayloadLength + 1, 2 ^ 256 - 1, 2 ^ 255,
          tx.length - 1, 0].map w).eraseDups.map .length
    | "padding" => [.padding 0, .padding 1, .padding 2]
    | _ => []
  bank.filter (·.valid shape tx)

/-- Three flags and the completion pattern, then per transaction a choice, two
field Words, a length selector, a uniform length, whether it is malformed, a
kind and a bank entry. The last two bounds divide by every count up to 16. -/
def sequenceBounds : List Nat :=
  [6, 6, 6, 4] ++ (List.range 3).flatMap fun _ => [12, 6, 6, 14, 65, 3, 720720, 720720]

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x6172677365716e63 sequenceBounds

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 3 0) [false, false, false]

/-- A selector below seven picks that entry of the length bank; otherwise the
uniform draw from 0 to 64 is the length. -/
def generatedLength (selector uniform : Nat) : Nat :=
  if selector < lengthBank.length then lengthBank.getD selector 0 else uniform

/-- A choice draw below 12 is uniform below any count from 2 to 4; only a
`bytes` constructor's transaction keeps its length. A third of the transactions
are canonical; the others draw a kind uniformly from those that apply, then an
entry of its bank. -/
def blockTransactions (shape : Shape) (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD index Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    let draw := fun (offset : Nat) => choices.getD (4 + 8 * index + offset) 0
    let choice := draw 0 % shape.constructors.length
    let base : Transaction := ⟨"tx-" ++ toString (first + index),
      parityInput odd (bank (choices.getD index 0)), choice, bank (draw 1), bank (draw 2), 0, .none⟩
    let base := if carriesBytes shape base then {base with length := generatedLength (draw 3) (draw 4)} else base
    if draw 5 == 0 then base
    else
      let kinds := applicableKinds shape base
      let entries := malformationBank shape base (kinds.getD (draw 6 % max kinds.length 1) "none")
      {base with malformation := entries.getD (draw 7 % max entries.length 1) .none}

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (shape : Shape) (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks (blockTransactions shape) seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The prescribed completion: std's rejection, or the decoded flags' parity. -/
def completionName (shape : Shape) (tx : Transaction) : String :=
  match stdDecode shape (inputBytes shape tx) with
  | .error data => "rejected:" ++ Solcore.ContractRuntime.encodeBytesText data
  | .ok decoded => statusName (decoded.flags.val % 2 == 1)

/-- Whether the decoded flags or a rejection make a transaction revert. -/
def reverts (shape : Shape) (tx : Transaction) : Bool := completionName shape tx != "returned"

/-- The fixed wrapper lies inside the budget and the shape's decoder outside
it; the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let shape := generatedShape seed
  let overhead := EnumArgument.programOverhead shape
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the enum-argument wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step shape | throw "generated enum-argument plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions shape seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + EnumArgument.decoderNodes shape do
    throw "enum-argument contract exceeds its requested node budget and decoder"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "enum-argument-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("shapeChoices", toJson (shapeChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson (scenario.transactions.map (completionName shape)))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "enum-argument history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map rowStatus == scenario.transactions.map (fun tx =>
      some (if reverts scenario.plan.shape tx then "reverted" else "returned")) do
    throw "enum-argument history did not follow its prescribed outcomes"

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
            error == "enum-argument history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "enum-argument-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def payloadWeight : Payload → Nat
  | .noWords => 0
  | .oneWord => 1
  | .twoWords => 2
  | .pair => 3
  | .bytes => 4

/-- One per constructor and its fields' weight. -/
def shapeWeight (shape : Shape) : Nat :=
  shape.constructors.foldl (fun total constructor => total + 1 + payloadWeight constructor.payload) 0

/-- Nothing for no malformation, otherwise one plus its position in its kind's
bank, or one plus the bank's size outside it. -/
def malformationWeight (shape : Shape) (tx : Transaction) : Nat :=
  match tx.malformation with
  | .none => 0
  | malformation =>
      let bank := malformationBank shape tx (kindOf malformation)
      1 + (bank.idxOf? malformation).getD bank.length

def totalMalformationWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total tx => total + malformationWeight scenario.plan.shape tx) 0

def totalLength (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.length) 0

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total tx => total + tx.first.val + tx.second.val + tx.flags.val) 0

/-- Transaction count, the shape's weight, the malformations' weight, the total
length, complete program size/literals, then the field Words and flags. Every
axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (shapeWeight candidate.plan.shape < shapeWeight source.plan.shape ∨
    (shapeWeight candidate.plan.shape = shapeWeight source.plan.shape ∧
      (totalMalformationWeight candidate < totalMalformationWeight source ∨
      (totalMalformationWeight candidate = totalMalformationWeight source ∧
        (totalLength candidate < totalLength source ∨
        (totalLength candidate = totalLength source ∧
          ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
          (complexity candidate.program.body = complexity source.program.body ∧
            valueWeight candidate < valueWeight source)))))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (shape : Shape)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step shape
  let candidate ← (checkedScenario plan transactions).toOption
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

/-- The constructor indices a transaction names: its choice, and a retag's or an
alias's constructor. -/
def namedConstructors (tx : Transaction) : List Nat :=
  tx.choice :: match tx.malformation with
    | .retag index | .aliased index => [index]
    | _ => []

/-- A shape change's transactions: a malformation that no longer applies
becomes none. -/
private def reanchor (shape : Shape) (transactions : List Transaction) : List Transaction :=
  transactions.map fun tx => if tx.malformation.valid shape tx then tx else {tx with malformation := .none}

private def moveDown (index value : Nat) : Nat := if value > index then value - 1 else value

/-- The shape without constructor `index`, and the indices above it moved down. -/
private def dropConstructor (shape : Shape) (transactions : List Transaction) (index : Nat) :
    Option (Shape × List Transaction) := do
  let smaller ← Shape.ofList? (shape.constructors.eraseIdx index)
  return (smaller, reanchor smaller (transactions.map fun tx =>
    {tx with choice := moveDown index tx.choice, malformation := match tx.malformation with
      | .retag other => .retag (moveDown index other)
      | .aliased other => .aliased (moveDown index other)
      | malformation => malformation}))

/-- The next narrower fields: the struct to two Words, two Words to one, one
Word to none and `bytes` to none. -/
private def narrower : Payload → Option Payload
  | .pair => some .twoWords
  | .twoWords => some .oneWord
  | .oneWord => some .noWords
  | .bytes => some .noWords
  | .noWords => none

/-- Constructor `index` with narrower fields; a `bytes` constructor's
transactions lose their lengths. -/
private def narrowConstructor (shape : Shape) (transactions : List Transaction) (index : Nat) :
    Option (Shape × List Transaction) := do
  let constructor ← shape.constructors[index]?
  let payload ← narrower constructor.payload
  let smaller ← Shape.ofList? (shape.constructors.set index {constructor with payload})
  return (smaller, reanchor smaller (transactions.map fun tx =>
    if tx.choice == index then {tx with length := 0} else tx))

/-- One-transaction removals, simpler malformations, shorter lengths, dropped
and narrowed constructors, step reductions, then per transaction zero field
Words and the flags' parity bit. Candidates still need execution to establish
that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let shape := source.plan.shape
  let mut raw : List (Aggregates.CheckedDAG × Shape × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, shape,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for (transaction, index) in source.transactions.zipIdx do
    let bank := malformationBank shape transaction (kindOf transaction.malformation)
    let earlier := match bank.idxOf? transaction.malformation with
      | some position => bank.take position
      | none => bank
    for simpler in Malformation.none :: earlier do
      if simpler != transaction.malformation then
        raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
          {tx with malformation := simpler})]
  -- A shorter length, empty or halved, keeps every other part of its transaction.
  for (transaction, index) in source.transactions.zipIdx do
    for shorter in [0, transaction.length / 2] do
      if shorter < transaction.length then
        raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
          {tx with length := shorter})]
  -- A constructor no transaction names can go while two others remain.
  for index in List.range shape.constructors.length do
    unless source.transactions.any (fun tx => (namedConstructors tx).contains index) do
      if let some (smaller, transactions) := dropConstructor shape source.transactions index then
        raw := raw ++ [(source.plan.step, smaller, transactions)]
  for index in List.range shape.constructors.length do
    if let some (smaller, transactions) := narrowConstructor shape source.transactions index then
      raw := raw ++ [(source.plan.step, smaller, transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, shape, source.transactions)]
  for index in List.range source.transactions.length do
    raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
      {tx with first := Word.zero, second := Word.zero})]
    raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
  let mut seen : List String := []
  let mut result := []
  for (step, shape, transactions) in raw do
    if let some reduced := sealReduction source step shape transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.plan.shape reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentTransactions", transactionsJson parent.plan.shape parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", EnumArgument.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from enum-argument plan emission"
  unless (← json.getObjVal? "contract") == contractJson admitted.plan.shape emitted do
    throw "saved contract metadata differs from enum-argument wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "enum-argument-generated" then
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
      throw "saved origin differs from generated enum-argument provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.plan.shape expected.transactions ==
          transactionsJson admitted.plan.shape admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions parentPlan.shape (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.shape admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported enum-argument case origin"
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

end Solcore.Synthesis.Source.EnumArgument
end

section
-- leanmerge: from Solcore.Synthesis.Source.EnumArrayEmitter
/-! Emit the enum-array protocol as a public method taking a calldata array of
a user enum and two indices. The source declares the struct and the enum as
for one enum argument; std derives their `Generic` and ABI instances, its
dispatcher checks the array's head before the body runs, and `items[first]`
and `items[second]` decode one element each on demand through std's
`abiArrayGet`. Each read matches its element with one arm per constructor in
declaration order, setting that element's one-based index and decoded Words as
for one enum argument. The step, the ten writes and the odd-flags revert follow
the original Core contract in order. Memory at zero is touched only before the
terminal revert. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EnumArray

open Solcore.Synthesis.Core.EnumArgument (Constructor Shape)
open Solcore.Synthesis.Core.EnumArray (CheckedPlan)
open Solcore.Synthesis.Source.EnumArgument (enumName structName typeLines)

def emitterVersion : String := "solcore-source-enum-array-arguments-v1"
def wrapperVersion : String := "solcore-enum-array-arguments-contract-v1"
def contractName : String := "SynthesizedEnumArrays"
def methodName : String := "run"
def deployPath : List String := ["SynthesizedEnumArraysDeploy"]
def runtimePath : List String := ["SynthesizedEnumArraysDeploy", "SynthesizedEnumArrays"]

/-- The method selector as `0x` and eight hexadecimal digits. -/
def selectorText (shape : Shape) : String :=
  let digits := Nat.toDigits 16 (Solcore.Synthesis.Core.EnumArray.selector shape)
  "0x" ++ String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

/-- Element `k`'s arm of constructor `index`: its pattern, the one-based index
and the decoded Words, in names suffixed by `k`. -/
def armLines (element index : Nat) (constructor : Constructor) : List String :=
  let k := toString element
  let value := "            case " ++ enumName ++ "." ++ constructor.name
  let marker := "                sc_index" ++ k ++ " = " ++ toString (index + 1) ++ ";"
  let words := ["                sc_x" ++ k ++ " = Typedef.rep(sc_a" ++ k ++ ");",
    "                sc_y" ++ k ++ " = Typedef.rep(sc_b" ++ k ++ ");"]
  (match constructor.payload with
    | .noWords => [value ++ " {", marker]
    | .oneWord => [value ++ "(sc_a" ++ k ++ ") {", marker, words.getD 0 ""]
    | .twoWords => [value ++ "(sc_a" ++ k ++ ", sc_b" ++ k ++ ") {", marker] ++ words
    | .pair => [value ++ "(" ++ structName ++ "(sc_a" ++ k ++ ", sc_b" ++ k ++ ")) {", marker] ++ words
    | .bytes => [value ++ "(sc_d" ++ k ++ ") {", marker,
        "                let sc_data" ++ k ++ ": word = Typedef.rep(sc_d" ++ k ++ ");",
        "                sc_x" ++ k ++ " = mload(sc_data" ++ k ++ ");",
        "                if (sc_x" ++ k ++ " > 0) {",
        "                    sc_y" ++ k ++ " = mload((sc_data" ++ k ++ " + 32));",
        "                }",
        "                if (sc_x" ++ k ++ " > 32) {",
        "                    sc_z" ++ k ++ " = mload((sc_data" ++ k ++ " + 64));",
        "                }"]) ++ ["            }"]

/-- The read of element `k` at the method's argument `argument`. -/
def readLines (shape : Shape) (element : Nat) (argument : String) : List String :=
  let k := toString element
  ["        let sc_index" ++ k ++ ": word = 0;", "        let sc_x" ++ k ++ ": word = 0;",
    "        let sc_y" ++ k ++ ": word = 0;", "        let sc_z" ++ k ++ ": word = 0;",
    "        let sc_value" ++ k ++ ": " ++ enumName ++ " = items[" ++ argument ++ "];",
    "        match (sc_value" ++ k ++ ") {"] ++
    (shape.constructors.zipIdx.map fun (constructor, index) => armLines element index constructor).flatten ++
    ["        }"]

/-- The step's argument after the prior slot zero, left to right as original
Core adds them: the length, then each element's index and three Words. -/
def summands : List String :=
  ["sc_count", "sc_index0", "sc_x0", "sc_y0", "sc_z0", "sc_index1", "sc_x1", "sc_y1", "sc_z1"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", "import * from std.Generic;",
    "import * from std.ABIGeneric;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), ""] ++ typeLines plan.shape
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
    "    function " ++ methodName ++ "(flags: uint256, items: calldata<array<" ++ enumName ++
      ">>, first: uint256, second: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_count: word = Typedef.rep(items.length());"] ++
    readLines plan.shape 0 "first" ++ readLines plan.shape 1 "second" ++
    ["        let sc_result: word = sc_step(" ++ summands.foldl (fun sum term => "(" ++ sum ++ " + " ++ term ++ ")")
      "sload(0)" ++ ");",
    "        sstore(0, sc_result);",
    "        sstore(1, sc_count);",
    "        sstore(2, sc_index0);",
    "        sstore(3, sc_x0);",
    "        sstore(4, sc_y0);",
    "        sstore(5, sc_z0);",
    "        sstore(6, sc_index1);",
    "        sstore(7, sc_x1);",
    "        sstore(8, sc_y1);",
    "        sstore(9, sc_z1);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature := Solcore.Synthesis.Core.EnumArray.signature plan.shape,
    deployPath, runtimePath
  }

end Solcore.Synthesis.Source.EnumArray
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.EnumArrayExecution
/-! Execute the original checked enum-array contract over a persistent account
world. A transaction is a canonical call of
`run(uint256 flags, SynthesizedEnum[] items, uint256 first, uint256 second)`:
up to three elements, each a constructor with its field Words or `bytes`
payload, and two indices, together with one malformation of its calldata; the
contract receives the malformed bytes. `stdDecode` is a second model of the
pinned std's dispatcher, lazy calldata-array decoder, `abiArrayGet` and derived
enum decoder, written over the bytes instead of in Core, which prescribes each
transaction's outcome and the Words the body decodes. `model` runs the protocol
on its decisions with the step evaluated alone in Core. Observations report
slots zero to nine and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.EnumArrayExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (Constructor Payload Shape)
open Solcore.Synthesis.Core.EnumArray (CheckedPlan outOfBoundsError outOfBoundsPanic)
open Solcore.Synthesis.Core.StdDispatch (noSelectorError truncatedError)

def historySchema : String := "solcore-lean.enum-array-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- The longest canonical `bytes` payload. -/
abbrev maxLength : Nat := EnumArgumentExecution.maxLength

/-- The most elements a canonical array carries. -/
def maxElements : Nat := 3

/-- A canonical element: a constructor, its field Words and a `bytes` length. -/
structure Element where
  choice : Nat
  a : Word
  b : Word
  length : Nat
  deriving BEq, Repr

/-- How a transaction's calldata departs from the canonical encoding: the
malformed-calldata kinds; the array's offset or length Word; and, for element
`target`, an unknown tag, another constructor's tag, its offset Word in a
dynamic array's table, another element's offset there, an unread head Word, a
`bytes` tail offset or length Word, or nonzero padding. Padding patterns are
`0xff` (0), the ramp `1, 2, 3, ...` (1) or a single `0x01` in the last padding
byte (2). -/
inductive Malformation where
  | none
  | short (bytes : Nat)
  | selector (mask : Nat)
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | offset (value : Word)
  | count (value : Word)
  | tag (target : Nat) (value : Word)
  | retag (target index : Nat)
  | entry (target : Nat) (value : Word)
  | share (target source : Nat)
  | unused (target : Nat) (value : Word)
  | tail (target : Nat) (value : Word)
  | length (target : Nat) (value : Word)
  | padding (target pattern : Nat)
  deriving BEq, Repr

structure Transaction where
  id : String
  flags : Word
  elements : List Element
  first : Word
  second : Word
  malformation : Malformation
  deriving BEq

/-- A `bytes` payload: the first `length` bytes of `a · K` and `b · K`. -/
def payload (element : Element) : ByteArray := EnumArgumentExecution.payload element.a element.b element.length

abbrev paddedLength := EnumArgumentExecution.paddedLength

private def zeros (count : Nat) : ByteArray := ByteArray.mk (Array.replicate count 0)

/-- The chosen constructor, the first for an index outside the shape. -/
def constructorAt (shape : Shape) (index : Nat) : Constructor := shape.constructors.getD index shape.first

def elementConstructor (shape : Shape) (element : Element) : Constructor := constructorAt shape element.choice

/-- The canonical body: the tag, the fields, zero Words up to the body's head,
then a `bytes` field's length Word and zero-padded payload behind the tail
offset, which is the body's head. -/
def body (shape : Shape) (element : Element) : ByteArray :=
  let chosen := elementConstructor shape element
  let head := match chosen.payload with
    | .noWords => ByteArray.empty
    | .oneWord => encodeWordBytesBE element.a
    | .twoWords | .pair => encodeWordBytesBE element.a ++ encodeWordBytesBE element.b
    | .bytes => encodeWordBytesBE (Word.ofNatModulo shape.bodyHead)
  let tail := match chosen.payload with
    | .bytes => encodeWordBytesBE (Word.ofNatModulo element.length) ++ payload element ++
        zeros (paddedLength element.length - element.length)
    | _ => ByteArray.empty
  encodeWordBytesBE (EnumArgument.tag chosen) ++ head ++
    zeros (shape.bodyHead - 32 - EnumArgument.headSize chosen.payload) ++ tail

/-- The canonical array's offset, the arguments' head. -/
def arrayOffset : Nat := EnumArray.argumentsHead

/-- The canonical length Word, right after the head. -/
def lengthPosition : Nat := 4 + arrayOffset

/-- The element region, right after the canonical length Word. -/
def regionStart : Nat := lengthPosition + 32

/-- A dynamic array's table: element `k`'s offset from the region, past the
table and the bodies before it. -/
def tableOffsets (shape : Shape) (tx : Transaction) : List Nat :=
  let sizes := tx.elements.map fun element => (body shape element).size
  (List.range tx.elements.length).map fun index => 32 * tx.elements.length + (sizes.take index).foldl (· + ·) 0

/-- Where element `k`'s canonical body starts. -/
def bodyStart (shape : Shape) (tx : Transaction) (index : Nat) : Nat :=
  if shape.dynamic then regionStart + (tableOffsets shape tx).getD index 0
  else regionStart + index * EnumArray.stride shape

private def selectorBytes (selector : Nat) : ByteArray :=
  ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

/-- std's `Panic(code)` revert data: the panic's selector, then the code as a Word. -/
private def panicBytes (code : Nat) : ByteArray :=
  selectorBytes outOfBoundsError ++ encodeWordBytesBE (Word.ofNatModulo code)

private def words (values : List Nat) : ByteArray :=
  values.foldl (fun bytes value => bytes ++ encodeWordBytesBE (Word.ofNatModulo value)) ByteArray.empty

/-- The selector, the flags, the array's offset, the two indices, the length,
then a dynamic array's offset table and the bodies in order. -/
def canonicalBytes (shape : Shape) (tx : Transaction) : ByteArray :=
  selectorBytes (EnumArray.selector shape) ++ encodeWordBytesBE tx.flags ++
    encodeWordBytesBE (Word.ofNatModulo arrayOffset) ++ encodeWordBytesBE tx.first ++ encodeWordBytesBE tx.second ++
    encodeWordBytesBE (Word.ofNatModulo tx.elements.length) ++
    (if shape.dynamic then words (tableOffsets shape tx) else ByteArray.empty) ++
    tx.elements.foldl (fun bytes element => bytes ++ body shape element) ByteArray.empty

def canonicalSize (shape : Shape) (tx : Transaction) : Nat := (canonicalBytes shape tx).size

def elementAt? (tx : Transaction) (index : Nat) : Option Element := tx.elements[index]?

/-- The payload start of element `k`, when it carries `bytes`. -/
def payloadStart (shape : Shape) (tx : Transaction) (index : Nat) : Nat :=
  bodyStart shape tx index + shape.bodyHead + 32

abbrev paddingCount := EnumArgumentExecution.paddingCount

/-- The last payload Word of an element with its padding replaced by the
pattern. -/
private def paddedWord (bytes : ByteArray) (length pattern : Nat) : Word :=
  let start := length / 32 * 32
  let count := paddingCount length
  let padding := (List.range count).map fun position =>
    match pattern with
    | 0 => (0xff : UInt8)
    | 1 => (position + 1).toUInt8
    | _ => if position + 1 = count then 1 else 0
  Word.ofNatModulo (((bytes.extract start length).data.toList ++ padding).foldl
    (fun total byte => total * 256 + byte.toNat) 0)

/-- Whether element `k` exists and its constructor's head is narrower than the
body's head. -/
def hasUnused (shape : Shape) (tx : Transaction) (index : Nat) : Bool :=
  match elementAt? tx index with
  | some element => 32 + EnumArgument.headSize (elementConstructor shape element).payload < shape.bodyHead
  | none => false

def carriesBytes (shape : Shape) (tx : Transaction) (index : Nat) : Bool :=
  match elementAt? tx index with
  | some element => (elementConstructor shape element).payload == .bytes
  | none => false

private def elementLength (tx : Transaction) (index : Nat) : Nat := ((elementAt? tx index).map (·.length)).getD 0

/-- The calldata a transaction sends. -/
def inputBytes (shape : Shape) (tx : Transaction) : ByteArray :=
  let start := bodyStart shape tx
  let entryAt := fun (index : Nat) => regionStart + 32 * index
  let change : StdCalldata.Change := match tx.malformation with
    | .none => .none
    | .short bytes => .short bytes
    | .selector mask => .selector mask
    | .truncate kept => .truncate kept
    | .trailing extra pattern => .trailing extra pattern
    | .offset value => .word 36 value
    | .count value => .word lengthPosition value
    | .tag target value => .word (start target) value
    | .retag target index => .word (start target) (EnumArgument.tag (constructorAt shape index))
    | .entry target value => .word (entryAt target) value
    | .share target source => .word (entryAt target) (Word.ofNatModulo ((tableOffsets shape tx).getD source 0))
    | .unused target value =>
        let width := ((elementAt? tx target).map fun element =>
          EnumArgument.headSize (elementConstructor shape element).payload).getD 0
        .word (start target + 32 + width) value
    | .tail target value => .word (start target + 32) value
    | .length target value => .word (start target + shape.bodyHead) value
    | .padding target pattern =>
        let element := (elementAt? tx target).getD ⟨0, Word.zero, Word.zero, 0⟩
        .word (payloadStart shape tx target + element.length / 32 * 32)
          (paddedWord (payload element) element.length pattern)
  change.apply (canonicalBytes shape tx)

/-- A malformation within its bounds, where it applies: cuts inside the
calldata past the selector, the malformed-calldata bounds, another offset or
length, an existing target element, another constructor's tag, table changes
of a dynamic array, an unread head Word of a narrower constructor, and `bytes`
changes of a `bytes` element, its padding only when there is some. -/
def Malformation.valid (shape : Shape) (tx : Transaction) : Malformation → Bool
  | .none => true
  | .short bytes => bytes < 4
  | .selector mask => 0 < mask && mask < 2 ^ 32
  | .truncate kept => 4 ≤ kept && kept < canonicalSize shape tx
  | .trailing extra pattern => 1 ≤ extra && extra ≤ 64 && pattern < 3
  | .offset value => value.val != arrayOffset
  | .count value => value.val != tx.elements.length
  | .tag target value => target < tx.elements.length && !shape.constructors.any (EnumArgument.tag · == value)
  | .retag target index => match elementAt? tx target with
      | some element => index < shape.constructors.length && index != element.choice
      | _ => false
  | .entry target value => shape.dynamic && target < tx.elements.length &&
      value.val != (tableOffsets shape tx).getD target 0
  | .share target source => shape.dynamic && target < tx.elements.length && source < tx.elements.length &&
      source != target
  | .unused target value => hasUnused shape tx target && value != Word.zero
  | .tail target value => carriesBytes shape tx target && value.val != shape.bodyHead
  | .length target value => carriesBytes shape tx target && value.val != elementLength tx target
  | .padding target pattern => carriesBytes shape tx target && paddingCount (elementLength tx target) != 0 &&
      pattern < 3

/-- An element as std decodes it: the one-based index and the three protocol
Words. -/
structure DecodedElement where
  index : Nat
  words : Word × Word × Word
  deriving BEq, Repr

/-- The Words std decodes: the flags, the length and both elements. -/
structure Decoded where
  flags : Word
  length : Word
  first : DecodedElement
  second : DecodedElement
  deriving BEq, Repr

/-- The revert data of a std rejection, or the decoded value. -/
abbrev Decision := Except ByteArray Decoded

private def wordAt (input : ByteArray) (offset : Nat) : Word := Word.ofNatModulo (StdCalldata.wordAt input offset)

/-- The payload's zero-padded Word at `offset`, from the bytes that exist. -/
private def chunkAt (input : ByteArray) (start length offset : Nat) : Word :=
  let bytes := (input.extract (start + offset) (start + length)).extract 0 32
  Word.ofNatModulo ((bytes.data.toList ++ List.replicate (32 - bytes.size) (0 : UInt8)).foldl
    (fun total byte => total * 256 + byte.toNat) 0)

/-- `abiArrayGet` of element `i` of an array whose region `R` follows a length
`L` that std accepted: `i >= L` is out of bounds; a static element's body is at
`R + i s`; a dynamic element's offset `e` at `R + 32 i` must satisfy
`e <= size - R` and its tag Word must exist at `R + e`; then the tag and the
fields as for one enum argument. Natural arithmetic cannot wrap, as std's
checks do not. -/
def decodeElement (shape : Shape) (input : ByteArray) (region length index : Nat) :
    Except ByteArray DecodedElement := do
  let size := input.size
  let fail := fun (error : Nat) => (Except.error (selectorBytes error) : Except ByteArray DecodedElement)
  if index ≥ length then .error (panicBytes outOfBoundsPanic)
  else
    let start? : Option Nat :=
      if shape.dynamic then
        let offset := StdCalldata.wordAt input (region + 32 * index)
        if offset > size - region then none else some (region + offset)
      else some (region + index * EnumArray.stride shape)
    match start? with
    | none => fail truncatedError
    | some start =>
      if size - start < 32 then fail truncatedError
      else
        let found := wordAt input start
        match (shape.constructors.zipIdx.find? fun (constructor, _) => EnumArgument.tag constructor == found) with
        | none => throw ByteArray.empty
        | some (constructor, position) =>
          let decoded := fun (words : Word × Word × Word) =>
            (pure ⟨position + 1, words⟩ : Except ByteArray DecodedElement)
          match constructor.payload with
          | .noWords => decoded (Word.zero, Word.zero, Word.zero)
          | .oneWord =>
              if size - start < 64 then fail truncatedError
              else decoded (wordAt input (start + 32), Word.zero, Word.zero)
          | .twoWords | .pair =>
              if size - start < 96 then fail truncatedError
              else decoded (wordAt input (start + 32), wordAt input (start + 64), Word.zero)
          | .bytes =>
              if size - start < 64 then fail truncatedError
              else
                let tail := StdCalldata.wordAt input (start + 32)
                if tail > size - start then fail truncatedError
                else if size - (start + tail) < 32 then fail truncatedError
                else
                  let count := StdCalldata.wordAt input (start + tail)
                  if count > size - (start + tail + 32) then fail truncatedError
                  else if count > EnumArgument.maxPayloadLength then fail truncatedError
                  else
                    let data := start + tail + 32
                    decoded (Word.ofNatModulo count,
                      if count > 0 then chunkAt input data count 0 else Word.zero,
                      if count > 32 then chunkAt input data count 32 else Word.zero)

/-- The pinned std's decision for `run(uint256 flags, E[] items, uint256 first,
uint256 second)` over raw calldata, written from `do_exec`, the bounded calldata
reader, the lazy calldata-array decoder, `checkArrayHead`, `abiArrayGet` and
the derived decoder. The fallback reverts with `0x4924aef0`, a missing or
out-of-range read with `0x08638556`, an index past the length with
`Panic(0x32)` and an unknown tag with empty data. The array's head is checked at
dispatch, then `first` and `second` are decoded in turn; unread elements are
never checked. -/
def stdDecode (shape : Shape) (input : ByteArray) : Decision := do
  let size := input.size
  let fail := fun (error : Nat) => (Except.error (selectorBytes error) : Decision)
  let width := EnumArray.stride shape
  if size < 4 || StdCalldata.bigEndian input 0 4 != EnumArray.selector shape then fail noSelectorError
  else if size < 4 + EnumArray.argumentsHead then fail truncatedError
  else
    let offset := StdCalldata.wordAt input 36
    if offset > size - 4 then fail truncatedError
    else
      let position := 4 + offset
      if size - position < 32 then fail truncatedError
      else
        let length := StdCalldata.wordAt input position
        if length > (2 ^ 256 - 1) / width || length * width > size - (position + 32) then fail truncatedError
        else
          let region := position + 32
          let first ← decodeElement shape input region length (StdCalldata.wordAt input 68)
          let second ← decodeElement shape input region length (StdCalldata.wordAt input 100)
          return ⟨wordAt input 4, Word.ofNatModulo length, first, second⟩

/-- std's revert data for a rejected transaction, or none when the body runs. -/
def stdRejection? (shape : Shape) (tx : Transaction) : Option ByteArray :=
  match stdDecode shape (inputBytes shape tx) with
  | .error data => some data
  | .ok _ => none

def calldata (shape : Shape) (tx : Transaction) : String := encodeBytesText (inputBytes shape tx)

def inputData? (shape : Shape) (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes shape tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

/-- Slot zero holds the accumulator, slot one the length and slots two to nine
both decoded elements. -/
def observedSlots : List Word := (List.range EnumArray.slotCount).map Word.ofNatModulo

def slotsJson : Json := toJson (observedSlots.map fun slot => toString slot.val)

def storageJson (account : Account) : Json := toJson (observedSlots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)),
  ("value", toJson (toString (account.storageRead slot).val))])

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation, as for the enum arguments, with each
transaction's malformed calldata as the input. -/
def observeContract (contract : CheckedCoreContract) (shape : Shape) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match inputData? shape transaction, registry.resolve? prior bindings.address with
      | none, _ =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "input-limit"), ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | _, none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some input, some ⟨resolved, installed⟩ =>
          let invocation : TopLevelInvocation := {
            target := bindings.address, caller := bindings.caller,
            callValue := Word.zero, inputData := input }
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings),
                ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", slotsJson),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract plan.shape transactions bindings fuel

/-- One modelled transaction: whether it reverts, its whole output and the
slots it leaves committed. -/
abbrev ModelRow := EnumArgumentExecution.ModelRow

private def elementWords (element : DecodedElement) : List Word :=
  let (w0, w1, w2) := element.words
  [Word.ofNatModulo element.index, w0, w1, w2]

/-- std's decision, then the protocol: `r = step(prior + L + both elements'
index and Words)`, the ten writes, and the flags' parity. A rejection outputs
std's revert data and keeps the prior slots. -/
def modelTransaction (step : Aggregates.CheckedDAG) (shape : Shape) (fuel : Nat)
    (prior : List Word) (transaction : Transaction) : Option ModelRow := do
  match stdDecode shape (inputBytes shape transaction) with
  | .error data => return ⟨true, data, prior⟩
  | .ok decoded =>
      let decodedWords := decoded.length :: elementWords decoded.first ++ elementWords decoded.second
      let result ← EnumArgumentExecution.stepResult step fuel
        (decodedWords.foldl (· + ·) (prior.getD 0 Word.zero))
      if decoded.flags.val % 2 == 1 then return ⟨true, encodeWordBytesBE result, prior⟩
      return ⟨false, encodeWordBytesBE result, result :: decodedWords⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (shape : Shape) (fuel : Nat)
    (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate EnumArray.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step shape fuel slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

end Solcore.Synthesis.Stateful.EnumArrayExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.EnumArrayCases
/-! Enum-array cases retain one original host-aware Core contract, its enum's
constructors, and an ordered history of transactions, each up to three elements
with their field Words or `bytes` lengths, two indices and one malformation of
its calldata. Reductions remove transactions, simplify malformations, drop the
last element, shorten lengths, drop unused constructors, narrow fields, reduce
the step and simplify the Words. Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EnumArray
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (Constructor Payload Shape)
open Solcore.Synthesis.Core.EnumArray (CheckedPlan)
open Solcore.Synthesis.Stateful.EnumArrayExecution (Element Transaction Malformation Bindings maxLength maxElements
  carriesBytes hasUnused inputBytes stdRejection? calldata slotsJson paddingCount canonicalSize bodyStart
  tableOffsets regionStart stdDecode elementConstructor)

def caseSchema : String := "solcore-lean.semantic-enum-array-case.v1"
def planSchema : String := "solcore-lean.enum-array-plan.v1"
def profileVersion : String := "stateful-enum-array-arguments-v1/enum-array-sequence-seed-v1"
def templateVersion : String := "std-enum-array-decode-two-elements-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-enum-array-corpus.v1"

/-- Flags values and field Words; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

abbrev lengthBank := EnumArgument.lengthBank

/-- The largest decoder of a valid shape, four constructors of which two carry
`bytes` and two Words; the tests check it against every shape class. -/
def maxDecoderNodes : Nat := 452

/-- The largest array wrapper, that of a dynamic element type. -/
def maxWrapperNodes : Nat := 397

/-- Complete contracts may exceed the step budget by the wrapper beyond the
reservation and by their shape's decoder. -/
def maxProgramNodes : Nat := 512 + maxWrapperNodes - Solcore.Synthesis.Core.EnumArray.reservedNodes + maxDecoderNodes

/-- An element encodes an existing constructor; only a `bytes` constructor
keeps a length, of at most 64 bytes. -/
def admitsElement (shape : Shape) (element : Element) : Bool :=
  element.choice < shape.constructors.length && element.length ≤ maxLength &&
    ((elementConstructor shape element).payload == .bytes || element.length == 0)

/-- A transaction has at most three admitted elements, its malformation
applies, and its calldata stays within one KiB. -/
def admits (shape : Shape) (tx : Transaction) : Bool :=
  Storage.validId tx.id && tx.elements.length ≤ maxElements && tx.elements.all (admitsElement shape) &&
    tx.malformation.valid shape tx &&
    (inputBytes shape tx).size ≤ Stateful.StdCalldata.maxCalldata

def validTransactions (shape : Shape) (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (admits shape) = true

instance (shape : Shape) (transactions : List Transaction) : Decidable (validTransactions shape transactions) := by
  unfold validTransactions
  infer_instance

/-- The step's budget is at most 512 nodes less the reservation; the rest of
the wrapper and the shape's decoder lie outside it. -/
def contractBound (plan : CheckedPlan) : Nat := 512 + Solcore.Synthesis.Core.EnumArray.outsideNodes plan.shape

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions plan.shape transactions
  bounded : Wire.programNodes plan.program ≤ contractBound plan

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

private def transactionRule : String :=
  s!"enum-array scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, at most {maxElements} elements of constructors of the shape, lengths of at most {maxLength} that only bytes constructors' elements may set, a malformation that applies to it, and calldata of at most 1 KiB"

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions plan.shape transactions then
    if bounded : Wire.programNodes plan.program ≤ contractBound plan then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical enum-array contract exceeds its case limit"
  else throw transactionRule

/-- Every malformation kind, in catalog order. -/
def malformationKinds : List String :=
  ["none", "short", "selector", "truncate", "trailing", "offset", "count", "tag", "retag", "entry", "share",
    "unused", "tail", "length", "padding"]

def kindOf : Malformation → String
  | .none => "none"
  | .short _ => "short"
  | .selector _ => "selector"
  | .truncate _ => "truncate"
  | .trailing _ _ => "trailing"
  | .offset _ => "offset"
  | .count _ => "count"
  | .tag _ _ => "tag"
  | .retag _ _ => "retag"
  | .entry _ _ => "entry"
  | .share _ _ => "share"
  | .unused _ _ => "unused"
  | .tail _ _ => "tail"
  | .length _ _ => "length"
  | .padding _ _ => "padding"

/-- The element a malformation changes, zero for the others. -/
def targetOf : Malformation → Nat
  | .tag target _ | .retag target _ | .entry target _ | .share target _ | .unused target _
  | .tail target _ | .length target _ | .padding target _ => target
  | _ => 0

abbrev patternNames := Stateful.StdCalldata.patternNames
abbrev paddingNames := EnumArgument.paddingNames

private def valueJson (kind : String) (target : Nat) (value : Word) : Json :=
  Json.mkObj [("kind", toJson kind), ("element", toJson target), ("value", toJson (toString value.val))]

def malformationJson : Malformation → Json
  | .none => Json.mkObj [("kind", toJson "none")]
  | .short bytes => Json.mkObj [("kind", toJson "short"), ("bytes", toJson bytes)]
  | .selector mask => Json.mkObj [("kind", toJson "selector"), ("mask", toJson (toString mask))]
  | .truncate kept => Json.mkObj [("kind", toJson "truncate"), ("kept", toJson kept)]
  | .trailing extra pattern => Json.mkObj [("kind", toJson "trailing"), ("count", toJson extra),
      ("pattern", toJson (patternNames.getD pattern "ramp"))]
  | .offset value => Json.mkObj [("kind", toJson "offset"), ("value", toJson (toString value.val))]
  | .count value => Json.mkObj [("kind", toJson "count"), ("value", toJson (toString value.val))]
  | .tag target value => valueJson "tag" target value
  | .retag target index => Json.mkObj [("kind", toJson "retag"), ("element", toJson target),
      ("constructor", toJson index)]
  | .entry target value => valueJson "entry" target value
  | .share target source => Json.mkObj [("kind", toJson "share"), ("element", toJson target),
      ("source", toJson source)]
  | .unused target value => valueJson "unused" target value
  | .tail target value => valueJson "tail" target value
  | .length target value => valueJson "length" target value
  | .padding target pattern => Json.mkObj [("kind", toJson "padding"), ("element", toJson target),
      ("pattern", toJson (paddingNames.getD pattern "last-byte"))]

/-- std's revert data as text: an error selector, `0x` for an unknown tag, or
null when the body runs. -/
def prescribed (shape : Shape) (tx : Transaction) : Option String :=
  (stdRejection? shape tx).map Solcore.ContractRuntime.encodeBytesText

def elementJson (element : Element) : Json := Json.mkObj [
  ("choice", toJson element.choice), ("a", toJson (toString element.a.val)),
  ("b", toJson (toString element.b.val)), ("length", toJson element.length)]

def transactionJson (shape : Shape) (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)),
  ("elements", toJson (tx.elements.map elementJson)),
  ("first", toJson (toString tx.first.val)), ("second", toJson (toString tx.second.val)),
  ("malformation", malformationJson tx.malformation),
  ("calldata", toJson (calldata shape tx)),
  ("stdRejection", match prescribed shape tx with
    | some data => toJson data
    | none => Json.null),
  ("value", toJson "0")]

def transactionsJson (shape : Shape) (transactions : List Transaction) : Json :=
  toJson (transactions.map (transactionJson shape))

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
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
  let value := fun _ : Unit => do word (← json.getObjValAs? String "value")
  match ← json.getObjValAs? String "kind" with
  | "none" => return .none
  | "short" => return .short (← natural json "bytes")
  | "selector" => return .selector (← word (← json.getObjValAs? String "mask")).val
  | "truncate" => return .truncate (← natural json "kept")
  | "trailing" => return .trailing (← natural json "count") (← nameIndex patternNames json "pattern")
  | "offset" => return .offset (← value ())
  | "count" => return .count (← value ())
  | "tag" => return .tag (← natural json "element") (← value ())
  | "retag" => return .retag (← natural json "element") (← natural json "constructor")
  | "entry" => return .entry (← natural json "element") (← value ())
  | "share" => return .share (← natural json "element") (← natural json "source")
  | "unused" => return .unused (← natural json "element") (← value ())
  | "tail" => return .tail (← natural json "element") (← value ())
  | "length" => return .length (← natural json "element") (← value ())
  | "padding" => return .padding (← natural json "element") (← nameIndex paddingNames json "pattern")
  | _ => throw "unknown malformation kind"

private def decodeElement (json : Json) : Except String Element :=
  return ⟨← natural json "choice", ← word (← json.getObjValAs? String "a"),
    ← word (← json.getObjValAs? String "b"), ← natural json "length"⟩

def decodeTransactions (shape : Shape) (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let elements ← (← row.getObjVal? "elements").getArr?
    unless elements.size ≤ maxElements do throw transactionRule
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← elements.toList.mapM decodeElement,
      ← word (← row.getObjValAs? String "first"), ← word (← row.getObjValAs? String "second"),
      ← decodeMalformation (← row.getObjVal? "malformation")⟩
    unless validTransactions shape [transaction] do throw transactionRule
    unless row == transactionJson shape transaction do
      throw "transaction differs from canonical ID, flags, elements, indices, malformation, calldata, std outcome or zero-value metadata"
    return transaction
  unless validTransactions shape transactions do throw transactionRule
  return transactions

private def payloadOf? (fields : String) : Option Payload :=
  [Payload.noWords, .oneWord, .twoWords, .pair, .bytes].find? (EnumArgument.fieldsName · == fields)

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("constructors", toJson (plan.shape.constructors.map EnumArgument.constructorJson)),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported enum-array plan schema"
  let rows ← (← json.getObjVal? "constructors").getArr?
  unless rows.size ≤ Solcore.Synthesis.Core.EnumArgument.maxConstructors do throw "an enum has at most four constructors"
  let constructors ← rows.toList.mapM fun row => do
    let some payload := payloadOf? (← row.getObjValAs? String "fields") | throw "unsupported constructor fields"
    return ({name := ← row.getObjValAs? String "name", payload} : Constructor)
  let some shape := EnumArgument.Shape.ofList? constructors | throw "an enum needs at least two constructors"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step shape
    | throw "enum-array plan needs two to four constructors with distinct bank names, at most two with bytes, and full host-Core admission"
  unless json == planJson plan do throw "enum-array plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ contractBound plan do throw "enum-array contract exceeds its case limit"
  return plan

def contractJson (shape : Shape) (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson (selectorText shape)),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("enumArrayPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.plan.shape scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.EnumArray.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson scenario.plan.shape emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic enum-array case schema"
  let plan ← checkedPlan (← json.getObjVal? "enumArrayPlan")
  let transactions ← decodeTransactions plan.shape (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical enum-array plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == slotsJson do
    throw "observed slots must be zero through nine"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.EnumArrayExecution.observe scenario.plan scenario.transactions bindings fuel

abbrev parityInput := EnumArgument.parityInput
abbrev parityPatterns := EnumArgument.parityPatterns

/-- SplitMix64's finalizer: the generator's draws are affine in its start, so
consecutive seeds would otherwise start streams whose draws follow each other. -/
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

/-- The shape draws of the enum arguments, from this profile's own stream. -/
abbrev shapeBounds := EnumArgument.shapeBounds

def shapeChoices (seed : Seed) : List Nat := boundedDraws seed 0x6172726173686170 shapeBounds

/-- Names drawn from the bank without repetition: each index picks among the
names still left. -/
private def drawNames (indices : List Nat) : List String := Id.run do
  let mut left := Solcore.Synthesis.Core.EnumArgument.nameBank
  let mut names : Array String := #[]
  for index in indices do
    names := names.push (left.getD index "")
    left := left.eraseIdx index
  return names.toList

/-- Two to four constructors; none carries `bytes` for a `bytes` draw below 2,
otherwise one or two do, at distinct positions. The other fields are none, one
Word, two Words or the struct. -/
def generatedShape (seed : Seed) : Shape :=
  let choices := shapeChoices seed
  let count := 2 + choices.getD 0 0
  let bytesCount := choices.getD 1 0 - 1
  let firstBytes := choices.getD 6 0 % count
  let secondBytes := (firstBytes + 1 + choices.getD 7 0 % (count - 1)) % count
  let payloads := (List.range count).map fun index =>
    if (bytesCount ≥ 1 && index == firstBytes) || (bytesCount ≥ 2 && index == secondBytes) then
      Payload.bytes
    else [Payload.noWords, .oneWord, .twoWords, .pair].getD (choices.getD (2 + index) 0) .noWords
  let names := drawNames ((choices.drop 8).take count)
  let constructors := (names.zip payloads).map fun (name, payload) => ({name, payload} : Constructor)
  (EnumArgument.Shape.ofList? constructors).getD ⟨⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩, []⟩

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The kinds that apply to a transaction with target element `target`, in
catalog order. -/
def applicableKinds (shape : Shape) (tx : Transaction) (target : Nat) : List String :=
  ["short", "selector", "truncate", "trailing", "offset", "count"] ++
    (if target < tx.elements.length then
      ["tag", "retag"] ++
        (if shape.dynamic then ["entry"] ++ (if tx.elements.length ≥ 2 then ["share"] else []) else []) ++
        (if hasUnused shape tx target then ["unused"] else []) ++
        (if carriesBytes shape tx target then ["tail", "length"] else []) ++
        (if carriesBytes shape tx target &&
            paddingCount ((tx.elements[target]?.map (·.length)).getD 0) != 0 then ["padding"] else [])
    else [])

/-- The generation bank of one kind for a transaction and target element,
without the entries that do not apply to it. -/
def malformationBank (shape : Shape) (tx : Transaction) (kind : String) (target : Nat) : List Malformation :=
  let size := canonicalSize shape tx
  let count := tx.elements.length
  let start := bodyStart shape tx target
  let head := shape.bodyHead
  let width := Solcore.Synthesis.Core.EnumArray.stride shape
  let element := (tx.elements[target]?).getD ⟨0, Word.zero, Word.zero, 0⟩
  let tag := Solcore.Synthesis.Core.EnumArgument.tag (elementConstructor shape element)
  let others := (List.range shape.constructors.length).filter (· != element.choice)
  let bank : List Malformation := match kind with
    | "short" => [.short 0, .short 1, .short 2, .short 3]
    | "selector" => [.selector 1, .selector (2 ^ 31), .selector (2 ^ 32 - 1)]
    | "truncate" =>
        let cuts := [4, 36, 68, 100, 131, 132, 163, 164] ++
          (List.range count).map (fun index => bodyStart shape tx index + 32) ++ [size - 1]
        (cuts.eraseDups.filter fun kept => 4 ≤ kept && kept < size).map .truncate
    | "trailing" => [.trailing 1 0, .trailing 31 1, .trailing 32 2, .trailing 33 0, .trailing 64 1, .trailing 64 2]
    | "offset" => ([size - 3, size - 4, size - 35, 2 ^ 255, 2 ^ 256 - 4, 0, 32, 64, 96].map w).eraseDups.map .offset
    | "count" =>
        ([count + 1, count - 1, 0, (size - regionStart) / width + 1, (2 ^ 256 - 1) / width + 1, 2 ^ 256 - 1].map w).eraseDups.map
          .count
    | "tag" => [w 0, tag + w 1, tag ^^^ w (2 ^ 255), w (2 ^ 256 - 1)].eraseDups.map (.tag target)
    | "retag" => others.map (.retag target)
    | "entry" => ([size - regionStart + 1, size - regionStart, 2 ^ 256 - 32, 0, 32].map w).eraseDups.map (.entry target)
    | "share" => ((List.range count).filter (· != target)).map (.share target)
    | "unused" => [w 1, w (2 ^ 256 - 1)].map (.unused target)
    | "tail" => ([size - start + 1, 0, 32, 2 ^ 256 - 1].map w).eraseDups.map (.tail target)
    | "length" =>
        let fits := size - (start + head + 32)
        ([element.length + 1, fits, fits + 1, 2 ^ 256 - 1, element.length - 1, 0].map w).eraseDups.map (.length target)
    | "padding" => [.padding target 0, .padding target 1, .padding target 2]
    | _ => []
  bank.filter (·.valid shape tx)

/-- Three flags and the completion pattern, then per transaction an element
count, three elements' choice, two field Words, a length selector and a uniform
length, both indices' inside draw and position, whether it is malformed, a
target element, a kind and a bank entry. The last two bounds divide by every
count up to 16. -/
def transactionBounds : List Nat :=
  [4] ++ (List.range maxElements).flatMap (fun _ => [12, 6, 6, 14, 65]) ++ [8, 6, 8, 6, 3, 6, 720720, 720720]

def sequenceBounds : List Nat := [6, 6, 6, 4] ++ (List.range 3).flatMap fun _ => transactionBounds

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x6172726173657173 sequenceBounds

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 3 0) [false, false, false]

abbrev generatedLength := EnumArgument.generatedLength

/-- An index inside `count` elements with probability 7/8, uniformly;
otherwise, and always for no element, the length itself or `2^256 - 1`. -/
def generatedIndex (count inside position : Nat) : Word :=
  if count > 0 && inside != 0 then w (position % count)
  else if position % 2 == 0 then w count else w (2 ^ 256 - 1)

/-- A choice draw below 12 is uniform below any count from 2 to 4; only a
`bytes` element keeps its length. A third of the transactions are canonical;
the others draw a target element, then a kind uniformly from those that apply,
then an entry of its bank. -/
def blockTransactions (shape : Shape) (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD index Word.zero
  let width := transactionBounds.length
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    let draw := fun (offset : Nat) => choices.getD (4 + width * index + offset) 0
    let count := draw 0
    let elements := (List.range count).map fun slot =>
      let pick := fun (offset : Nat) => draw (1 + 5 * slot + offset)
      let element : Element := ⟨pick 0 % shape.constructors.length, bank (pick 1), bank (pick 2), 0⟩
      if (elementConstructor shape element).payload == .bytes then
        {element with length := generatedLength (pick 3) (pick 4)}
      else element
    let indices := 1 + 5 * maxElements
    let base : Transaction := ⟨"tx-" ++ toString (first + index),
      parityInput odd (bank (choices.getD index 0)), elements,
      generatedIndex count (draw indices) (draw (indices + 1)),
      generatedIndex count (draw (indices + 2)) (draw (indices + 3)), .none⟩
    if draw (indices + 4) == 0 then base
    else
      let target := draw (indices + 5) % max count 1
      let kinds := applicableKinds shape base target
      let entries := malformationBank shape base (kinds.getD (draw (indices + 6) % max kinds.length 1) "none") target
      {base with malformation := entries.getD (draw (indices + 7) % max entries.length 1) .none}

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (shape : Shape) (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks (blockTransactions shape) seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The prescribed completion: std's rejection, or the decoded flags' parity. -/
def completionName (shape : Shape) (tx : Transaction) : String :=
  match stdDecode shape (inputBytes shape tx) with
  | .error data => "rejected:" ++ Solcore.ContractRuntime.encodeBytesText data
  | .ok decoded => statusName (decoded.flags.val % 2 == 1)

/-- Whether the decoded flags or a rejection make a transaction revert. -/
def reverts (shape : Shape) (tx : Transaction) : Bool := completionName shape tx != "returned"

/-- The reservation lies inside the budget and the rest of the wrapper and the
shape's decoder outside it; the complete contract is remeasured as the final
budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let shape := generatedShape seed
  let reserved := Solcore.Synthesis.Core.EnumArray.reservedNodes
  unless nodes ≤ 512 && reserved < nodes do
    throw "node budget is too small for the enum-array reservation or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - reserved) revision
  let some plan := CheckedPlan.ofParts? step shape | throw "generated enum-array plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions shape seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + Solcore.Synthesis.Core.EnumArray.outsideNodes shape do
    throw "enum-array contract exceeds its requested node budget, wrapper and decoder"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "enum-array-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("shapeChoices", toJson (shapeChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson (scenario.transactions.map (completionName shape)))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "enum-array history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map rowStatus == scenario.transactions.map (fun tx =>
      some (if reverts scenario.plan.shape tx then "reverted" else "returned")) do
    throw "enum-array history did not follow its prescribed outcomes"

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
            error == "enum-array history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "enum-array-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

abbrev shapeWeight := EnumArgument.shapeWeight

/-- Nothing for no malformation, otherwise one plus its position in its kind's
bank for its target, or one plus the bank's size outside it. -/
def malformationWeight (shape : Shape) (tx : Transaction) : Nat :=
  match tx.malformation with
  | .none => 0
  | malformation =>
      let bank := malformationBank shape tx (kindOf malformation) (targetOf malformation)
      1 + (bank.idxOf? malformation).getD bank.length

def totalMalformationWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total tx => total + malformationWeight scenario.plan.shape tx) 0

def elementCount (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total tx => total + tx.elements.length) 0

def totalLength (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total tx => total + tx.elements.foldl (fun sum element => sum + element.length) 0) 0

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total tx => total + tx.flags.val + tx.first.val + tx.second.val +
    tx.elements.foldl (fun sum element => sum + element.a.val + element.b.val) 0) 0

/-- Transaction count, element count, the shape's weight, the malformations'
weight, the total length, complete program size/literals, then the Words, the
indices and the flags. Every axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (elementCount candidate < elementCount source ∨
    (elementCount candidate = elementCount source ∧
      (shapeWeight candidate.plan.shape < shapeWeight source.plan.shape ∨
      (shapeWeight candidate.plan.shape = shapeWeight source.plan.shape ∧
        (totalMalformationWeight candidate < totalMalformationWeight source ∨
        (totalMalformationWeight candidate = totalMalformationWeight source ∧
          (totalLength candidate < totalLength source ∨
          (totalLength candidate = totalLength source ∧
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

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (shape : Shape)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step shape
  let candidate ← (checkedScenario plan transactions).toOption
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

/-- The constructor indices a transaction names: its elements' choices and a
retag's constructor. -/
def namedConstructors (tx : Transaction) : List Nat :=
  tx.elements.map (·.choice) ++ match tx.malformation with
    | .retag _ index => [index]
    | _ => []

/-- A changed transaction's malformation that no longer applies becomes none. -/
private def reanchor (shape : Shape) (transactions : List Transaction) : List Transaction :=
  transactions.map fun tx => if tx.malformation.valid shape tx then tx else {tx with malformation := .none}

private def moveDown (index value : Nat) : Nat := if value > index then value - 1 else value

/-- The shape without constructor `index`, and the indices above it moved down. -/
private def dropConstructor (shape : Shape) (transactions : List Transaction) (index : Nat) :
    Option (Shape × List Transaction) := do
  let smaller ← EnumArgument.Shape.ofList? (shape.constructors.eraseIdx index)
  let moved := fun (element : Element) => ({element with choice := moveDown index element.choice} : Element)
  let renamed := fun (malformation : Malformation) => match malformation with
    | .retag target other => Malformation.retag target (moveDown index other)
    | other => other
  return (smaller, reanchor smaller (transactions.map fun tx =>
    {tx with elements := tx.elements.map moved, malformation := renamed tx.malformation}))

/-- The next narrower fields: the struct to two Words, two Words to one, one
Word to none and `bytes` to none. -/
private def narrower : Payload → Option Payload
  | .pair => some .twoWords
  | .twoWords => some .oneWord
  | .oneWord => some .noWords
  | .bytes => some .noWords
  | .noWords => none

/-- Constructor `index` with narrower fields; its `bytes` elements lose their
lengths. -/
private def narrowConstructor (shape : Shape) (transactions : List Transaction) (index : Nat) :
    Option (Shape × List Transaction) := do
  let constructor ← shape.constructors[index]?
  let payload ← narrower constructor.payload
  let smaller ← EnumArgument.Shape.ofList? (shape.constructors.set index {constructor with payload})
  let shortened := fun (element : Element) =>
    if element.choice == index then ({element with length := 0} : Element) else element
  return (smaller, reanchor smaller (transactions.map fun tx => {tx with elements := tx.elements.map shortened}))

/-- One-transaction removals, simpler malformations, dropped last elements,
shorter lengths, dropped and narrowed constructors, step reductions, then per
transaction zero field Words and the flags' parity bit. Candidates still need
execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let shape := source.plan.shape
  let mut raw : List (Aggregates.CheckedDAG × Shape × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, shape,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for (transaction, index) in source.transactions.zipIdx do
    let bank := malformationBank shape transaction (kindOf transaction.malformation) (targetOf transaction.malformation)
    let earlier := match bank.idxOf? transaction.malformation with
      | some position => bank.take position
      | none => bank
    for simpler in Malformation.none :: earlier do
      if simpler != transaction.malformation then
        raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
          {tx with malformation := simpler})]
  -- The last element goes, with a malformation that no longer applies.
  for (transaction, index) in source.transactions.zipIdx do
    if transaction.elements.length > 0 then
      raw := raw ++ [(source.plan.step, shape, reanchor shape (replaceAt source.transactions index fun tx =>
        {tx with elements := tx.elements.dropLast}))]
  -- A shorter length, empty or halved, keeps every other part of its element.
  for (transaction, index) in source.transactions.zipIdx do
    for (element, slot) in transaction.elements.zipIdx do
      for shorter in [0, element.length / 2] do
        if shorter < element.length then
          let changed : Element := {element with length := shorter}
          raw := raw ++ [(source.plan.step, shape, reanchor shape (replaceAt source.transactions index fun tx =>
            {tx with elements := tx.elements.set slot changed}))]
  -- A constructor no transaction names can go while two others remain.
  for index in List.range shape.constructors.length do
    unless source.transactions.any (fun tx => (namedConstructors tx).contains index) do
      if let some (smaller, transactions) := dropConstructor shape source.transactions index then
        raw := raw ++ [(source.plan.step, smaller, transactions)]
  for index in List.range shape.constructors.length do
    if let some (smaller, transactions) := narrowConstructor shape source.transactions index then
      raw := raw ++ [(source.plan.step, smaller, transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, shape, source.transactions)]
  for index in List.range source.transactions.length do
    let cleared := fun (element : Element) => ({element with a := Word.zero, b := Word.zero} : Element)
    raw := raw ++ [(source.plan.step, shape, reanchor shape (replaceAt source.transactions index fun tx =>
      {tx with elements := tx.elements.map cleared}))]
    raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
  let mut seen : List String := []
  let mut result := []
  for (step, shape, transactions) in raw do
    if let some reduced := sealReduction source step shape transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.plan.shape reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentTransactions", transactionsJson parent.plan.shape parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.EnumArray.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from enum-array plan emission"
  unless (← json.getObjVal? "contract") == contractJson admitted.plan.shape emitted do
    throw "saved contract metadata differs from enum-array wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "enum-array-generated" then
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
      throw "saved origin differs from generated enum-array provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.plan.shape expected.transactions ==
          transactionsJson admitted.plan.shape admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions parentPlan.shape (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.shape admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported enum-array case origin"
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

end Solcore.Synthesis.Source.EnumArray
end

section
-- leanmerge: from Solcore.Synthesis.Source.EnumReturnEmitter
/-! Emit the enum-return protocol as a public method returning a user enum. The
source declares `SynthesizedEnum` with the shape's constructors, and the method
tests the choice against each constructor index but the last and returns that
constructor; std derives the enum's `Generic` and ABI instances, and its
dispatcher encodes the value with `abi_encode`. A `bytes` constructor allocates
three Words with std's `allocate_memory`, stores the length and the two data
Words and passes the pointer as a `memory<bytes>` local. The second data Word
rereads slot one after the writes. Memory at zero is touched only before the
terminal revert. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EnumReturn

open Solcore.Synthesis.Core.EnumReturn (CheckedPlan Constructor)
open Solcore.ContractRuntime (EnumPayload)

def emitterVersion : String := "solcore-source-enum-returns-v1"
def wrapperVersion : String := "solcore-enum-returns-contract-v1"
def contractName : String := "SynthesizedEnumReturns"
def enumName : String := "SynthesizedEnum"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256,uint256,uint256)"
def selector : String := "0x15509d2b"
def deployPath : List String := ["SynthesizedEnumReturnsDeploy"]
def runtimePath : List String := ["SynthesizedEnumReturnsDeploy", "SynthesizedEnumReturns"]

/-- The multiplier `K` as a hexadecimal literal. -/
def multiplierLiteral : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 Solcore.Synthesis.Core.EnumReturn.multiplier)

/-- A constructor's declaration: its name and its fields' types. -/
def declaration (constructor : Constructor) : String :=
  constructor.name ++ match constructor.payload with
    | .noWords => ""
    | .oneWord => "(uint256)"
    | .twoWords => "(uint256, uint256)"
    | .boundedBytes => "(memory<bytes>)"

/-- The statements that return constructor `index`, indented by `indent`. A
`bytes` constructor's locals carry its index. -/
def returnLines (indent : String) (index : Nat) (constructor : Constructor) : List String :=
  let value := enumName ++ "." ++ constructor.name
  match constructor.payload with
  | .noWords => [indent ++ "return " ++ value ++ ";"]
  | .oneWord => [indent ++ "return " ++ value ++ "(uint256(sc_first));"]
  | .twoWords => [indent ++ "return " ++ value ++ "(uint256(sc_first), uint256(sc_second));"]
  | .boundedBytes =>
      let pointer := "sc_pointer" ++ toString index
      let bytes := "sc_bytes" ++ toString index
      [indent ++ "let " ++ pointer ++ ": word = allocate_memory(96);",
        indent ++ "mstore(" ++ pointer ++ ", sc_length);",
        indent ++ "mstore((" ++ pointer ++ " + 32), sc_first);",
        indent ++ "mstore((" ++ pointer ++ " + 64), sc_second);",
        indent ++ "let " ++ bytes ++ ": memory<bytes> = Typedef.abs(" ++ pointer ++ ");",
        indent ++ "return " ++ value ++ "(" ++ bytes ++ ");"]

/-- Each constructor but the last returns under its choice test; the last
returns unconditionally. -/
def completionLines (constructors : List Constructor) : List String :=
  (constructors.zipIdx.map fun (constructor, index) =>
    if index + 1 = constructors.length then returnLines "        " index constructor
    else ["        if (sc_choice == " ++ toString index ++ ") {"] ++
      returnLines "            " index constructor ++ ["        }"]).flatten

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let constructors := plan.shape.constructors
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", "import * from std.Generic;",
    "import * from std.ABIGeneric;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), "",
    "enum " ++ enumName ++ " {"] ++
    constructors.zipIdx.map (fun (constructor, index) =>
      "    " ++ declaration constructor ++ if index + 1 = constructors.length then "" else ",") ++
    ["}", ""]
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
    "    function " ++ methodName ++ "(flags: uint256, input: uint256, choice: uint256, length: uint256) " ++
      "public returns (" ++ enumName ++ ") {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_choice: word = (Typedef.rep(choice) % " ++ toString constructors.length ++ ");",
    "        let sc_length: word = (Typedef.rep(length) % 65);",
    "        let sc_prior: word = sload(0);",
    "        let sc_last: word = sload(2);",
    "        let sc_result: word = sc_step((sc_prior + sc_input));",
    "        sstore(0, sc_result);",
    "        sstore(1, (sload(1) + 1));",
    "        sstore(2, sc_input);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        let sc_first: word = (sc_result * " ++ multiplierLiteral ++ ");",
    "        let sc_second: word = ((sload(1) * " ++ multiplierLiteral ++ ") ^ sc_last);"] ++
    completionLines constructors ++ ["    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.EnumReturn
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.EnumReturnExecution
/-! Execute the original checked enum-return contract over a persistent account
world. Each invocation starts a fresh Core heap and only the public terminal
`finalWorld` becomes the next transaction's world. Calldata is the selector of
`run(uint256,uint256,uint256,uint256)` with the flags, input, choice and length
Words. Observations report the whole return data, the three declared slots and
the contract's whole committed storage.

`model` is an independent reading of the emitted source and of std's encoder:
a slot map, the step evaluated alone in Core, the method's choice of
constructor and its 96 bytes of `bytes` data, then std's `abi_encode` of the
enum written out over a zeroed byte memory. The encoder is `encodeVariant` with
the head sizes of `ABIAttribs`, the unit, `uint256` and pair encoders and
`encodeIntoFromBytesLike`. A reverted transaction keeps the prior slots. It
shares nothing with the Core contract but that step and the tags. Tests compare
the two; neither is an oracle for the differential paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.EnumReturnExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumReturn (CheckedPlan Constructor Shape)

def historySchema : String := "solcore-lean.enum-return-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  choice : Word
  length : Word
  deriving BEq

/-- The selector of `run(uint256,uint256,uint256,uint256)`, then the flags,
input, choice and length Words. -/
def inputData (flags input choice length : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x15, 0x50, 0x9d, 0x2b] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input ++
    encodeWordBytesBE choice ++ encodeWordBytesBE length
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input choice length : Word) : String :=
  encodeBytesText (inputData flags input choice length).bytes

/-- Slot zero holds the accumulator, slot one the committed call count and slot
two the last committed input. -/
def observedSlots : List Word := (List.range EnumReturn.slotCount).map Word.ofNatModulo

def slotsJson : Json := toJson (observedSlots.map fun slot => toString slot.val)

def storageJson (account : Account) : Json := toJson (observedSlots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)),
  ("value", toJson (toString (account.storageRead slot).val))])

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation. The code registry is resolved again
against each current committed world, so persistence cannot install a different
contract or retain one invocation's local heap. A reverted invocation keeps the
prior committed world through the public runtime, not through this observer.
The output is the decoded convention's whole return data. -/
def observeContract (contract : CheckedCoreContract) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          let invocation : TopLevelInvocation := {
            target := bindings.address, caller := bindings.caller, callValue := Word.zero,
            inputData := inputData transaction.flags transaction.input transaction.choice transaction.length }
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings),
                ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", slotsJson),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

/-- The step's own Core result at one argument. -/
def stepResult (step : Aggregates.CheckedDAG) (fuel : Nat) (argument : Word) : Option Word :=
  match (step.instantiate argument).toCore.runStateful fuel with
  | .done (.word value) _ => some value
  | _ => none

/-- One modelled transaction: whether it reverts, its whole output (the encoded
returned value, or the one reverted Word) and the slots it leaves committed. -/
structure ModelRow where
  reverted : Bool
  output : ByteArray
  slots : List Word

private def slotAt (slots : List Word) (slot : Nat) : Word := slots.getD slot Word.zero

/-- The memory std's encoder writes, zeroed beforehand. -/
private def memorySize : Nat := 512

/-- `mstore`: one big-endian Word at `offset`. -/
private def store (memory : ByteArray) (offset : Nat) (value : Word) : ByteArray :=
  (encodeWordBytesBE value).copySlice 0 memory offset 32

/-- The fields' head size of `ABIAttribs`: unit 0, `uint256` 32, a pair the sum
of its two, and `memory<bytes>` one offset Word. -/
private def headSize : EnumPayload → Nat
  | .noWords => 0
  | .oneWord => 32
  | .twoWords => 32 + 32
  | .boundedBytes => 32

/-- The derived instance's `innerHead`: 32 plus the widest constructor's head. -/
private def innerHead (constructors : List Constructor) : Nat :=
  32 + constructors.foldl (fun widest constructor => max widest (headSize constructor.payload)) 0

/-- `encodeIntoFromBytesLike` of the method's 96 bytes at `source`: the offset
Word, `length + 32` bytes copied from the length Word on, then zeros up to a
multiple of 32. It returns the memory and the new tail. -/
private def encodeBytes (memory source : ByteArray) (basePtr offset tail : Nat) : ByteArray × Nat :=
  let length := (decodeWordBytesBE? (source.extract 0 32)).getD Word.zero |>.val
  let total := length + 32
  let rounded := (total + 31) / 32 * 32
  let written := store memory (basePtr + offset) (Word.ofNatModulo (tail - basePtr))
  let copied := source.copySlice 0 written tail total
  (ByteArray.mk (Array.replicate (rounded - total) 0) |>.copySlice 0 copied (tail + total) (rounded - total),
    tail + rounded)

/-- std's `abi_encode` of constructor `constructor` with the fields `first`,
`second` and the `bytes` source, from address 0: the derived `encodeVariant`
writes the tag inline for a static enum, or the offset to a body in the tail for
a dynamic one, then the fields' encoders run. The return data is the memory
from 0 to the final tail. -/
def stdEncoding (constructors : List Constructor) (constructor : Constructor)
    (first second : Word) (source : ByteArray) : ByteArray :=
  let static := constructors.all (·.payload != .boundedBytes)
  let inner := innerHead constructors
  -- `abi_encode`: the head starts at `start`, the tail after the enum's head,
  -- the whole body for a static enum and one offset Word otherwise.
  let start := 0
  let tail := start + if static then inner else 32
  let tag := EnumReturn.tag constructor
  let memory := ByteArray.mk (Array.replicate memorySize 0)
  -- `encodeVariant`: the tag at the head, or the offset to a new base in the
  -- tail that holds the tag; the fields follow the tag.
  let (memory, basePtr, offset, tail) :=
    if static then (store memory start tag, start, 32, tail)
    else (store (store memory start (Word.ofNatModulo (tail - start))) tail tag, tail, 32, tail + inner)
  let (memory, final) := match constructor.payload with
    | .noWords => (memory, tail)
    | .oneWord => (store memory (basePtr + offset) first, tail)
    | .twoWords => (store (store memory (basePtr + offset) first) (basePtr + offset + 32) second, tail)
    | .boundedBytes => encodeBytes memory source basePtr offset tail
  memory.extract 0 final

/-- It follows the source: `sc_choice = choice % n`, `sc_length = length % 65`,
`sc_prior = sload(0)`, `sc_last = sload(2)`, `sc_result = sc_step(sc_prior +
sc_input)`, the three writes, then `sc_first = sc_result * K` and `sc_second =
(sload(1) * K) ^ sc_last`, and the constructor `sc_choice` with its fields; a
`bytes` constructor's 96 bytes are `sc_length`, `sc_first` and `sc_second`. -/
def modelTransaction (step : Aggregates.CheckedDAG) (constructors : List Constructor) (fuel : Nat)
    (prior : List Word) (transaction : Transaction) : Option ModelRow := do
  let before := slotAt prior 0
  let last := slotAt prior 2
  let result ← stepResult step fuel (before + transaction.input)
  let written := ((prior.set 0 result).set 1 (slotAt prior 1 + Word.ofNatModulo 1)).set 2 transaction.input
  if transaction.flags.val % 2 == 1 then
    return ⟨true, encodeWordBytesBE result, prior⟩
  let constructor ← constructors[transaction.choice.val % constructors.length]?
  let multiplier := Word.ofNatModulo EnumReturn.multiplier
  let first := result * multiplier
  let second := (slotAt written 1 * multiplier) ^^^ last
  let source := encodeWordBytesBE (Word.ofNatModulo (transaction.length.val % 65)) ++
    encodeWordBytesBE first ++ encodeWordBytesBE second
  return ⟨false, stdEncoding constructors constructor first second source, written⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (constructors : List Constructor) (fuel : Nat)
    (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate EnumReturn.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step constructors fuel slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

end Solcore.Synthesis.Stateful.EnumReturnExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.EnumReturnCases
/-! Enum-return cases retain one original host-aware Core contract, its enum's
constructors, and an ordered history of `(flags, input, choice, length)`
transactions. Reductions remove transactions, shorten lengths, drop unchosen
constructors, narrow fields, reduce the step and simplify flags and inputs.
Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EnumReturn
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (EnumPayload)
open Solcore.Synthesis.Core.EnumReturn (CheckedPlan Constructor Shape)
open Solcore.Synthesis.Stateful.EnumReturnExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-enum-return-case.v1"
def planSchema : String := "solcore-lean.enum-return-plan.v1"
def profileVersion : String := "stateful-enum-returns-v1/enum-sequence-seed-v1"
def templateVersion : String := "enum-result-count-last-choice-length-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-enum-return-corpus.v1"

/-- Flags values and inputs; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- Lengths drawn with probability one half: empty, the Word boundaries and the
bound. -/
def lengthBank : List Nat := [0, 1, 31, 32, 33, 63, 64]

/-- Complete contracts, shell included, stay within the largest step budget. -/
def maxProgramNodes : Nat := 512

/-- Whether constructor `choice` of the shape exists and a nonzero length names
its `bytes` field. -/
def admits (shape : Shape) (transaction : Transaction) : Bool :=
  match shape.constructors[transaction.choice.val]? with
  | some constructor =>
      transaction.length.val ≤ Solcore.Synthesis.Core.EnumReturn.maxLength &&
        (constructor.payload == .boundedBytes || transaction.length.val == 0)
  | none => false

def validTransactions (shape : Shape) (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (admits shape) = true

instance (shape : Shape) (transactions : List Transaction) : Decidable (validTransactions shape transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions plan.shape transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

private def transactionRule : String :=
  s!"enum-return scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, a choice below the constructor count, and a length of at most {Solcore.Synthesis.Core.EnumReturn.maxLength} that only a bytes constructor's transaction may set"

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions plan.shape transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical enum-return contract exceeds its case limit"
  else throw transactionRule

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("choice", toJson (toString tx.choice.val)), ("length", toJson (toString tx.length.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.EnumReturnExecution.calldata tx.flags tx.input tx.choice
    tx.length)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json :=
  toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

def decodeTransactions (shape : Shape) (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← word (← row.getObjValAs? String "input"),
      ← word (← row.getObjValAs? String "choice"), ← word (← row.getObjValAs? String "length")⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, input, choice, length, calldata or zero-value metadata"
    return transaction
  unless validTransactions shape transactions do throw transactionRule
  return transactions

def constructorJson (constructor : Constructor) : Json := Json.mkObj [
  ("name", toJson constructor.name),
  ("fields", toJson (Solcore.Synthesis.Core.EnumReturn.fieldSignature constructor.payload))]

private def payloadOf? (fields : String) : Option EnumPayload :=
  [EnumPayload.noWords, .oneWord, .twoWords, .boundedBytes].find?
    (Solcore.Synthesis.Core.EnumReturn.fieldSignature · == fields)

/-- The constructors of a list of two or more, in order. -/
def Shape.ofList? : List Constructor → Option Shape
  | first :: second :: rest => some ⟨first, second, rest⟩
  | _ => none

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("constructors", toJson (plan.shape.constructors.map constructorJson)),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported enum-return plan schema"
  let rows ← (← json.getObjVal? "constructors").getArr?
  let constructors ← rows.toList.mapM fun row => do
    let some payload := payloadOf? (← row.getObjValAs? String "fields") | throw "unsupported constructor fields"
    return ({name := ← row.getObjValAs? String "name", payload} : Constructor)
  let some shape := Shape.ofList? constructors | throw "an enum needs at least two constructors"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step shape
    | throw "enum-return plan needs two to four constructors with distinct bank names, at most two with bytes, and full host-Core admission"
  unless json == planJson plan do throw "enum-return plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "enum-return contract exceeds its case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("enumReturnPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.EnumReturnExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.EnumReturn.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic enum-return case schema"
  let plan ← checkedPlan (← json.getObjVal? "enumReturnPlan")
  let transactions ← decodeTransactions plan.shape (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical enum-return plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.EnumReturnExecution.slotsJson do
    throw "observed slots must be zero through two"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.EnumReturnExecution.observe scenario.plan scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- SplitMix64's finalizer. The generator's draws are affine in its start, so
consecutive seeds would otherwise start streams whose low draw bits follow each
other: a raw shape stream alternates between two `bytes` counts. -/
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

/-- The constructor count, the `bytes` count, four Word fields, two `bytes`
positions and four name indices into the shrinking bank. -/
def shapeBounds : List Nat := [3, 4, 3, 3, 3, 3, 4, 4, 8, 7, 6, 5]

def shapeChoices (seed : Seed) : List Nat := boundedDraws seed 0x656e756d2d736870 shapeBounds

/-- Names drawn from the bank without repetition: each index picks among the
names still left. -/
private def drawNames (indices : List Nat) : List String := Id.run do
  let mut left := Solcore.Synthesis.Core.EnumReturn.nameBank
  let mut names : Array String := #[]
  for index in indices do
    names := names.push (left.getD index "")
    left := left.eraseIdx index
  return names.toList

/-- Two to four constructors; none carries `bytes` for a `bytes` draw below 2,
otherwise one or two do, at distinct positions. The other fields are none, one
or two Words. -/
def generatedShape (seed : Seed) : Shape :=
  let choices := shapeChoices seed
  let count := 2 + choices.getD 0 0
  let bytesCount := choices.getD 1 0 - 1
  let firstBytes := choices.getD 6 0 % count
  let secondBytes := (firstBytes + 1 + choices.getD 7 0 % (count - 1)) % count
  let payloads := (List.range count).map fun index =>
    if (bytesCount ≥ 1 && index == firstBytes) || (bytesCount ≥ 2 && index == secondBytes) then
      EnumPayload.boundedBytes
    else [EnumPayload.noWords, .oneWord, .twoWords].getD (choices.getD (2 + index) 0) .noWords
  let names := drawNames ((choices.drop 8).take count)
  let constructors := (names.zip payloads).map fun (name, payload) => ({name, payload} : Constructor)
  (Shape.ofList? constructors).getD ⟨⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩, []⟩

/-- Three flags, three inputs, the completion pattern, three choices, then per
transaction a length selector and a uniform length. -/
def sequenceBounds : List Nat := [6, 6, 6, 6, 6, 6, 4, 12, 12, 12, 14, 14, 14, 65, 65, 65]

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x656e756d732d7371 sequenceBounds

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 6 0) [false, false, false]

/-- A selector below seven picks that entry of the length bank; otherwise the
uniform draw from 0 to 64 is the length. -/
def generatedLength (choices : List Nat) (index : Nat) : Nat :=
  let selector := choices.getD (10 + index) 0
  if selector < lengthBank.length then lengthBank.getD selector 0 else choices.getD (13 + index) 0

/-- A choice draw below 12 is uniform below any count from 2 to 4; only a
`bytes` constructor's transaction keeps its length. -/
def blockTransactions (shape : Shape) (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    let choice := choices.getD (7 + index) 0 % shape.constructors.length
    let carries := shape.constructors[choice]?.any (·.payload == .boundedBytes)
    ⟨"tx-" ++ toString (first + index), parityInput odd (bank index), bank (3 + index),
      Word.ofNatModulo choice, Word.ofNatModulo (if carries then generatedLength choices index else 0)⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (shape : Shape) (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks (blockTransactions shape) seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The shell lies inside the budget, and the complete contract is remeasured as
the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let shape := generatedShape seed
  let shell := Solcore.Synthesis.Core.EnumReturn.shellNodes shape
  unless nodes ≤ 512 && shell < nodes do
    throw "node budget is too small for the enum-return wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - shell) revision
  let some plan := CheckedPlan.ofParts? step shape | throw "generated enum-return plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions shape seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do
    throw "enum-return contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "enum-return-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("shapeChoices", toJson (shapeChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "enum-return history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "enum-return history did not follow its prescribed flags parities"

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
            error == "enum-return history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "enum-return-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- One per constructor and its fields' weight: none 0, one Word 1, two Words 2
and `bytes` 3. -/
def shapeWeight (shape : Shape) : Nat :=
  shape.constructors.foldl (fun total constructor => total + 1 + match constructor.payload with
    | .noWords => 0
    | .oneWord => 1
    | .twoWords => 2
    | .boundedBytes => 3) 0

def totalLength (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.length.val) 0

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.flags.val + transaction.input.val) 0

/-- Transaction count, the shape's weight, the total length, complete program
size/literals, then flags and input values. Every axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (shapeWeight candidate.plan.shape < shapeWeight source.plan.shape ∨
    (shapeWeight candidate.plan.shape = shapeWeight source.plan.shape ∧
      (totalLength candidate < totalLength source ∨
      (totalLength candidate = totalLength source ∧
        ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
        (complexity candidate.program.body = complexity source.program.body ∧
          valueWeight candidate < valueWeight source)))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (shape : Shape)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step shape
  let candidate ← (checkedScenario plan transactions).toOption
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

/-- The shape without constructor `index`, and the transactions' choices above
it moved down. -/
private def dropConstructor (shape : Shape) (transactions : List Transaction) (index : Nat) :
    Option (Shape × List Transaction) := do
  let shape ← Shape.ofList? (shape.constructors.eraseIdx index)
  return (shape, transactions.map fun tx =>
    if tx.choice.val > index then {tx with choice := Word.ofNatModulo (tx.choice.val - 1)} else tx)

/-- The next narrower fields: two Words to one, one Word to none and `bytes`
to none. -/
private def narrower : EnumPayload → Option EnumPayload
  | .twoWords => some .oneWord
  | .oneWord => some .noWords
  | .boundedBytes => some .noWords
  | .noWords => none

/-- Constructor `index` with narrower fields; a `bytes` constructor's
transactions lose their lengths. -/
private def narrowConstructor (shape : Shape) (transactions : List Transaction) (index : Nat) :
    Option (Shape × List Transaction) := do
  let constructor ← shape.constructors[index]?
  let payload ← narrower constructor.payload
  let shape ← Shape.ofList? (shape.constructors.set index {constructor with payload})
  return (shape, transactions.map fun tx =>
    if tx.choice.val == index then {tx with length := Word.zero} else tx)

/-- One-transaction removals, shorter lengths, dropped and narrowed
constructors, step reductions, then per transaction the flags' parity bit and
the input's low byte. Candidates still need execution to establish that they
preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let shape := source.plan.shape
  let mut raw : List (Aggregates.CheckedDAG × Shape × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, shape,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  -- A shorter length, empty or halved, keeps every effect of its transaction.
  for (transaction, index) in source.transactions.zipIdx do
    for shorter in [0, transaction.length.val / 2] do
      if shorter < transaction.length.val then
        raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
          {tx with length := Word.ofNatModulo shorter})]
  -- A constructor no transaction chooses can go while two others remain.
  for index in List.range shape.constructors.length do
    unless source.transactions.any (·.choice.val == index) do
      if let some (smaller, transactions) := dropConstructor shape source.transactions index then
        raw := raw ++ [(source.plan.step, smaller, transactions)]
  for index in List.range shape.constructors.length do
    if let some (smaller, transactions) := narrowConstructor shape source.transactions index then
      raw := raw ++ [(source.plan.step, smaller, transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, shape, source.transactions)]
  for index in List.range source.transactions.length do
    raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
      {tx with input := tx.input.bitAnd (Word.ofNatModulo 255)})]
  let mut seen : List String := []
  let mut result := []
  for (step, shape, transactions) in raw do
    if let some reduced := sealReduction source step shape transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentTransactions", transactionsJson parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.EnumReturn.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from enum-return plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from enum-return wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "enum-return-generated" then
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
      throw "saved origin differs from generated enum-return provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions parentPlan.shape (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.shape admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported enum-return case origin"
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

end Solcore.Synthesis.Source.EnumReturn
end
