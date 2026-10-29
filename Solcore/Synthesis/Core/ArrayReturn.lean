import Solcore.Synthesis.Core.TupleReturn

/-! A checked protocol that returns std's ABI encoding of a memory array as a
static tuple of Words. The ABI supplies `run(uint256 flags, uint256 input,
uint256 choice, uint256 length)`; the contract reads `prior`, slot 0, and
`last`, slot 2, applies a closed aggregate step to `prior + input`, writes the
result `r` to slot 0, slot 1 plus one to slot 1 and the input to slot 2, then
rereads slot 1 as `count`. Odd flags revert with `r`. Even flags return the
Words of std's encoding of the plan's array, element `i` built from
`a = r · K + i` and `b = ((count · K) xor last) + i`, under the static
Word-tuple entry convention: the offset 32, the length, then inline Words
(`uint256` and left-aligned `bytes4` elements) or one offset per element and
the element tails (`bytes` and `uint256[]` elements).

The array's shape is the plan's constant. The contract reads only the flags
and the input; the emitted source reads the count from `length` and the inner
lengths from `choice`, which every transaction sets to the plan's values. The
public contract runtime commits or rolls back the resulting working world. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.ArrayReturn

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-array-return-contract-v1"

/-- Slot zero, the call count and the last input. -/
def slotCount : Nat := 3

/-- The odd constant of the bytes-return profile. -/
def multiplier : Nat := 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95

/-- The memory array's element type: `uint256`, `bytes4`, `memory<bytes>` or
`memory<DynArray<uint256>>`. -/
inductive Element where
  | words
  | fourBytes
  | bytes
  | nested
  deriving Repr, BEq, DecidableEq

namespace Element

/-- The element's ABI type name, as the plan records it. -/
def name : Element → String
  | .words => "uint256"
  | .fourBytes => "bytes4"
  | .bytes => "bytes"
  | .nested => "uint256[]"

def ofName? (text : String) : Option Element :=
  [Element.words, .fourBytes, .bytes, .nested].find? (·.name == text)

/-- Whether each element has its own length: a dynamic element. -/
def dynamic : Element → Bool
  | .bytes | .nested => true
  | _ => false

/-- The longest inner length: 64 bytes, or two Words. -/
def maxLength : Element → Nat
  | .bytes => 64
  | .nested => 2
  | _ => 0

/-- The digit base of the inner lengths in the `choice` argument. -/
def base : Element → Nat
  | .bytes => 65
  | .nested => 3
  | _ => 1

end Element

/-- The largest element count. -/
def maxCount : Nat := 3

/-- An element type, a count and, for dynamic elements, one inner length per
element. -/
structure Shape where
  element : Element
  count : Nat
  lengths : List Nat
  deriving Repr, BEq, DecidableEq

namespace Shape

def Valid (shape : Shape) : Prop :=
  shape.count ≤ maxCount ∧
    shape.lengths.length = (if shape.element.dynamic then shape.count else 0) ∧
    shape.lengths.all (· ≤ shape.element.maxLength) = true

instance (shape : Shape) : Decidable shape.Valid := by
  unfold Valid
  infer_instance

/-- The run-time `length` argument: the count. -/
def lengthArgument (shape : Shape) : Nat := shape.count

/-- The run-time `choice` argument: the inner lengths as digits of the element
type's base, element zero lowest; zero for inline elements. -/
def choiceArgument (shape : Shape) : Nat :=
  shape.lengths.zipIdx.foldl (fun total (length, index) => total + length * shape.element.base ^ index) 0

/-- One element's tail Words: its length Word and its data Words. -/
def tailWords (shape : Shape) (length : Nat) : Nat :=
  match shape.element with
  | .bytes => 1 + (length + 31) / 32
  | .nested => 1 + length
  | _ => 0

/-- The Words after the offset and the length: the element heads, then the
dynamic elements' tails. -/
def bodyWords (shape : Shape) : Nat :=
  shape.count + shape.lengths.foldl (fun total length => total + shape.tailWords length) 0

/-- The whole return data's Words. -/
def wordCount (shape : Shape) : Nat := 2 + shape.bodyWords

/-- The offsets of the dynamic elements' tails, relative to the element region. -/
def offsets (shape : Shape) : List Nat :=
  (shape.lengths.foldl (fun (acc : List Nat × Nat) length =>
    (acc.1 ++ [acc.2], acc.2 + 32 * shape.tailWords length)) ([], 32 * shape.count)).1

end Shape

/-- The right-nested Wire product of the return data's Words. -/
def resultType (shape : Shape) : Ty := .sum (TupleReturn.wordTuple (shape.bodyWords + 1)) (.sum .word .word)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

/-- Right-nested pairs of the listed Words; one Word stands alone. -/
private def tupleOf : List Expr → Expr
  | [] => .unit
  | [last] => last
  | head :: rest => .pair head (tupleOf rest)

/-- `base + index`; element zero's Word is `base` itself. -/
private def offsetBy (base : Expr) (index : Nat) : Expr :=
  if index = 0 then base else .binary .wordAdd base (word index)

/-- The leading `kept` bytes of a Word, the rest zero. -/
private def leading (value : Expr) (kept : Nat) : Expr :=
  if kept ≥ 32 then value else .binary .wordAnd value (word (2 ^ 256 - 2 ^ (8 * (32 - kept))))

/-- The Words after the offset and the length, over `a` = `r · K` and the mix
`b` = `(count · K) xor last`: inline element Words, or the offsets and then each
element's length and data. -/
def bodyExpressions (shape : Shape) (a b : Expr) : List Expr :=
  match shape.element with
  | .words => (List.range shape.count).map (offsetBy a)
  | .fourBytes => (List.range shape.count).map fun index =>
      .binary .wordMul (.binary .wordAnd (offsetBy a index) (word 0xffffffff)) (word (2 ^ 224))
  | .bytes => shape.offsets.map word ++ (shape.lengths.zipIdx.map fun (length, index) =>
      [word length] ++ (if length > 0 then [leading (offsetBy a index) length] else []) ++
        (if length > 32 then [leading (offsetBy b index) (length - 32)] else [])).flatten
  | .nested => shape.offsets.map word ++ (shape.lengths.zipIdx.map fun (length, index) =>
      [word length] ++ [offsetBy a index, offsetBy b index].take length).flatten

/-- In a frame of ten binders: `count` at 0, three Unit writes, then `r`,
`last`, `prior`, the input, the flags and the step at 4 to 9. Odd flags revert
with `r`; otherwise `a = r · K` and `b = (count · K) xor last` are bound and
the encoding's Words return. -/
private def completion (shape : Shape) : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 8) (word 1)) (word 1))
    (.inRight (TupleReturn.wordTuple (shape.bodyWords + 1)) (.inLeft .word (.var 4)))
    (.letE (.binary .wordMul (.var 4) (word multiplier))
      (.letE (.binary .wordXor (.binary .wordMul (.var 1) (word multiplier)) (.var 6))
        (.inLeft (.sum .word .word)
          (tupleOf ([word 32, word shape.count] ++ bodyExpressions shape (.var 1) (.var 0))))))

private def contractExpression (stepBody : Expr) (shape : Shape) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (host 0 3 (word 0))
          (.letE (host 0 4 (word 2))
            (.letE (.apply (.var 4) (.binary .wordAdd (.var 1) (.var 2)))
              (.letE (host 1 6 (.pair (word 0) (.var 0)))
                (.letE (host 1 7 (.pair (word 1) (.binary .wordAdd (host 0 7 (word 1)) (word 1))))
                  (.letE (host 1 8 (.pair (word 2) (.var 5)))
                    (.letE (host 0 9 (word 1))
                      (completion shape))))))))))

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
    if checked : (canonicalProgram step shape).check = true then some ⟨step, shape, valid, checked⟩ else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

theorem hostChecked (plan : CheckedPlan) : plan.program.toCore.checkHost = true :=
  Program.check_promotes_current plan.checked

def code (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.program.toCore, plan.hostChecked⟩

theorem count_le (plan : CheckedPlan) : plan.shape.count ≤ maxCount := plan.valid.1

/-- The tuple convention's `extraWords + 2` Words are the encoding's Words. -/
theorem resultType_eq (plan : CheckedPlan) :
    plan.code.program.resultType =
      (CoreContractEntryProfile.wordTupleOutcomeV1 plan.shape.bodyWords).resultType := by
  change (resultType plan.shape).toCore = _
  simp [resultType, Ty.toCore, TupleReturn.wordTuple_toCore, CoreContractEntryProfile.resultType]

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 plan.code plan.shape.bodyWords plan.resultType_eq

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

theorem contract_entryProfile (plan : CheckedPlan) :
    plan.contract.entryProfile = .wordTupleOutcomeV1 plan.shape.bodyWords := rfl

end CheckedPlan
end Solcore.Synthesis.Core.ArrayReturn
