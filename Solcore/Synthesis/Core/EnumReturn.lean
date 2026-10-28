import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Synthesis.Core.BytesReturn
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract
import Solcore.Abi.Keccak256

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
