import Solcore.Synthesis.Internal.Aggregates
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract
import Solcore.Synthesis.Internal.Storage
import Solcore.Synthesis.Stateful.Sequence

/-!
# Profiles: ABI returns

The profiles `stateful-bytes-returns`, `stateful-tuple-returns` and `stateful-array-returns`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.TupleReturn
/-! A checked protocol that returns a static tuple of two to four Words. The ABI
supplies `run(uint256 flags, uint256 input)`; the contract reads `prior`, slot
0, and `last`, slot 2, applies a closed aggregate step to `prior + input`,
writes the result `r` to slot 0, slot 1 plus one to slot 1 and the input to
slot 2, then rereads slot 1 as `count`. Odd flags revert with `r`; even flags
return the first `arity` Words of `(r, count, prior, last)` under the static
Word-tuple entry convention. The public contract runtime commits or rolls back
the resulting working world. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.TupleReturn

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-tuple-return-contract-v1"

def AllowedArity (arity : Nat) : Prop := arity = 2 ∨ arity = 3 ∨ arity = 4

instance (arity : Nat) : Decidable (AllowedArity arity) := inferInstanceAs
  (Decidable (arity = 2 ∨ arity = 3 ∨ arity = 4))

/-- The largest admitted arity, which returns every protocol Word. -/
def maxArity : Nat := 4

/-- Slot zero, the call count and the last input. -/
def slotCount : Nat := 3

/-- The right-nested Wire product of `count + 1` Words. -/
def wordTuple : Nat → Ty
  | 0 => .word
  | count + 1 => .product .word (wordTuple count)

theorem wordTuple_toCore (count : Nat) :
    (wordTuple count).toCore = CoreContractEntryProfile.wordTupleType count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [wordTuple, Ty.toCore, CoreContractEntryProfile.wordTupleType, ih]

def resultType (arity : Nat) : Ty := .sum (wordTuple (arity - 1)) (.sum .word .word)

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

/-- In a frame of ten binders: `count` at 0, three Unit writes, then `r`,
`last`, `prior`, the input, the flags and the step at 4 to 9. Odd flags revert
with `r`; otherwise the first `arity` of `(r, count, prior, last)` return. -/
private def completion (arity : Nat) : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 8) (word 1)) (word 1))
    (.inRight (wordTuple (arity - 1)) (.inLeft .word (.var 4)))
    (.inLeft (.sum .word .word) (tupleOf ([.var 4, .var 0, .var 6, .var 5].take arity)))

private def contractExpression (stepBody : Expr) (arity : Nat) : Expr :=
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
                      (completion arity))))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) (arity : Nat) : Program := {
  resultType := resultType arity
  dataDefinitions := []
  body := contractExpression step.program.body arity
}

def canonicalNodes (step : Aggregates.CheckedDAG) (arity : Nat) : Nat :=
  programNodes (canonicalProgram step arity)

/-- Syntax-only measurement of the shell, the wrapper without the step, using a
one-node placeholder step that is never admitted or run. The shell lies inside
a case's node budget. -/
def shellNodes (arity : Nat) : Nat :=
  programNodes {resultType := resultType arity, dataDefinitions := [], body := contractExpression (word 0) arity} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  arity : Nat
  allowed : AllowedArity arity
  checked : (canonicalProgram step arity).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.arity

def ofParts? (step : Aggregates.CheckedDAG) (arity : Nat) : Option CheckedPlan :=
  if allowed : AllowedArity arity then
    if checked : (canonicalProgram step arity).check = true then some ⟨step, arity, allowed, checked⟩ else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

theorem hostChecked (plan : CheckedPlan) : plan.program.toCore.checkHost = true :=
  Program.check_promotes_current plan.checked

def code (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.program.toCore, plan.hostChecked⟩

theorem arity_le (plan : CheckedPlan) : plan.arity ≤ maxArity := by
  rcases plan.allowed with arity | arity | arity <;> simp [arity, maxArity]

/-- The tuple convention's `extraWords + 2` Words are the plan's arity. -/
theorem arity_eq (plan : CheckedPlan) : plan.arity - 2 + 2 = plan.arity := by
  rcases plan.allowed with arity | arity | arity <;> simp [arity]

theorem resultType_eq (plan : CheckedPlan) :
    plan.code.program.resultType =
      (CoreContractEntryProfile.wordTupleOutcomeV1 (plan.arity - 2)).resultType := by
  have predecessor : plan.arity - 1 = plan.arity - 2 + 1 := by
    rcases plan.allowed with arity | arity | arity <;> simp [arity]
  change (resultType plan.arity).toCore = _
  simp [resultType, Ty.toCore, wordTuple_toCore, CoreContractEntryProfile.resultType, predecessor]

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 plan.code (plan.arity - 2) plan.resultType_eq

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

theorem contract_entryProfile (plan : CheckedPlan) :
    plan.contract.entryProfile = .wordTupleOutcomeV1 (plan.arity - 2) := rfl

end CheckedPlan
end Solcore.Synthesis.Core.TupleReturn
end

section
-- leanmerge: from Solcore.Synthesis.Core.ArrayReturn
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
end

section
-- leanmerge: from Solcore.Synthesis.Core.BytesReturn
/-! A checked protocol that returns a `bytes` value of at most 64 bytes. The ABI
supplies `run(uint256 flags, uint256 input, uint256 length)`; the contract reads
`prior`, slot 0, and `last`, slot 2, applies a closed aggregate step to
`prior + input`, writes the result `r` to slot 0, slot 1 plus one to slot 1 and
the input to slot 2, then rereads slot 1 as `count`. Odd flags revert with `r`;
even flags return the first `length mod 65` bytes of the data Words `r · K` and
`(count · K) xor last` under the bounded `bytes` entry convention. The public
contract runtime commits or rolls back the resulting working world. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.BytesReturn

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-bytes-return-contract-v1"

/-- Slot zero, the call count and the last input. -/
def slotCount : Nat := 3

/-- The longest returned value; the contract reads its length Word modulo one
more. -/
def maxLength : Nat := CoreContractEntryProfile.boundedBytesLimit

def lengthModulus : Nat := maxLength + 1

/-- The odd constant whose products spread a data Word over its leading bytes. -/
def multiplier : Nat := 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95

/-- A non-empty value's length tag and two data Words. -/
def dataType : Ty := .product .word (.product .word .word)

/-- The returned side of the bounded convention: empty, or tagged data. -/
def bytesType : Ty := .sum .unit dataType

def resultType : Ty := .sum bytesType (.sum .word .word)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

/-- In a frame of eleven binders: `count` at 0, three Unit writes, then `r`,
`last`, `prior`, the length Word, the input, the flags and the step at 4 to 10.
Odd flags revert with `r`. Otherwise the length is the length Word modulo 65:
zero returns the empty value, and any other length its tag `length - 1` with
the data Words `r · K` and `(count · K) xor last`. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 9) (word 1)) (word 1))
    (.inRight bytesType (.inLeft .word (.var 4)))
    (.letE (.binary .wordMod (.var 7) (word lengthModulus))
      (.ifE (.binary .wordEq (.var 0) (word 0))
        (.inLeft (.sum .word .word) (.inLeft dataType .unit))
        (.inLeft (.sum .word .word) (.inRight .unit
          (.pair (.binary .wordSub (.var 0) (word 1))
            (.pair (.binary .wordMul (.var 5) (word multiplier))
              (.binary .wordXor (.binary .wordMul (.var 1) (word multiplier)) (.var 6))))))))

private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (readInput 3 68)
          (.letE (host 0 4 (word 0))
            (.letE (host 0 5 (word 2))
              (.letE (.apply (.var 5) (.binary .wordAdd (.var 1) (.var 3)))
                (.letE (host 1 7 (.pair (word 0) (.var 0)))
                  (.letE (host 1 8 (.pair (word 1) (.binary .wordAdd (host 0 8 (word 1)) (word 1))))
                    (.letE (host 1 9 (.pair (word 2) (.var 6)))
                      (.letE (host 0 10 (word 1))
                        completion))))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat :=
  programNodes (canonicalProgram step)

/-- Syntax-only measurement of the shell, the wrapper without the step, using a
one-node placeholder step that is never admitted or run. The shell lies inside
a case's node budget. -/
def shellNodes : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  checked : (canonicalProgram step).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step

def ofStep? (step : Aggregates.CheckedDAG) : Option CheckedPlan :=
  if checked : (canonicalProgram step).check = true then some ⟨step, checked⟩ else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

theorem hostChecked (plan : CheckedPlan) : plan.program.toCore.checkHost = true :=
  Program.check_promotes_current plan.checked

def code (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.program.toCore, plan.hostChecked⟩

theorem resultType_eq (plan : CheckedPlan) :
    plan.code.program.resultType = CoreContractEntryProfile.boundedBytesOutcomeV1.resultType :=
  rfl

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.boundedBytesOutcomeV1 plan.code plan.resultType_eq

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

theorem contract_entryProfile (plan : CheckedPlan) :
    plan.contract.entryProfile = .boundedBytesOutcomeV1 := rfl

end CheckedPlan
end Solcore.Synthesis.Core.BytesReturn
end

section
-- leanmerge: from Solcore.Synthesis.Source.ArrayReturnEmitter
/-! Emit the array-return protocol as a public method declared to return
`uint256`. After the protocol's writes it builds a `memory<DynArray<t>>` of
`length % 4` elements, encodes it with std's `abi_encode` and ends with the
`return_` opcode over the encoding, which is what std's dispatcher does after a
method returns (`do_exec`). The checked driver accepts this as written; it
refuses a declared array output (Q008).

The count and the inner lengths are read at run time, from `length` and from
the digits of `choice`, so that no optimizer can fold std's encoder loops; the
source depends only on the element type and the step. Element `i` is built
from `sc_rk + i` and `sc_mix + i`. A `bytes` element is a fresh 96-byte
allocation holding its length and both Words, so its memory past the length is
dirty; an inner array holds as many of the two Words as its length takes.
Memory at zero is touched only before the terminal revert. No emitter proof
covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ArrayReturn

open Solcore.Synthesis.Core.ArrayReturn (CheckedPlan Element)

def emitterVersion : String := "solcore-source-array-returns-v1"
def wrapperVersion : String := "solcore-array-returns-contract-v1"
def contractName : String := "SynthesizedArrayReturns"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256,uint256,uint256)"
def selector : String := "0x15509d2b"
def deployPath : List String := ["SynthesizedArrayReturnsDeploy"]
def runtimePath : List String := ["SynthesizedArrayReturnsDeploy", "SynthesizedArrayReturns"]

def multiplierLiteral : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 Solcore.Synthesis.Core.ArrayReturn.multiplier)

/-- The element's source type. -/
def elementType : Element → String
  | .words => "uint256"
  | .fourBytes => "bytes4"
  | .bytes => "memory<bytes>"
  | .nested => "memory<DynArray<uint256>>"

/-- Inner length `index` from `choice`: digit `index` of the element type's
base. -/
private def digit (element : Element) (index : Nat) : String :=
  let base := toString element.base
  if index = 0 then "(sc_choice % " ++ base ++ ")"
  else "((sc_choice / " ++ toString (element.base ^ index) ++ ") % " ++ base ++ ")"

/-- The statements that set element `index`, inside its count guard. -/
def elementLines (element : Element) (index : Nat) : List String :=
  let i := toString index
  let a := "(sc_rk + " ++ i ++ ")"
  let b := "(sc_mix + " ++ i ++ ")"
  let set := fun (value : String) => "            IndexAccess.set(sc_items, uint256(" ++ i ++ "), " ++ value ++ ");"
  match element with
  | .words => [set ("uint256(" ++ a ++ ")")]
  | .fourBytes => [
      "            let sc_tag" ++ i ++ ": bytes4 = Typedef.abs((" ++ a ++ " & 0xffffffff));",
      set ("sc_tag" ++ i)]
  | .bytes => [
      "            let sc_p" ++ i ++ ": word = allocate_memory(96);",
      "            mstore(sc_p" ++ i ++ ", " ++ digit element index ++ ");",
      "            mstore((sc_p" ++ i ++ " + 32), " ++ a ++ ");",
      "            mstore((sc_p" ++ i ++ " + 64), " ++ b ++ ");",
      "            let sc_b" ++ i ++ ": memory<bytes> = Typedef.abs(sc_p" ++ i ++ ");",
      set ("sc_b" ++ i)]
  | .nested => [
      "            let sc_size" ++ i ++ ": word = " ++ digit element index ++ ";",
      "            let sc_inner" ++ i ++ ": memory<DynArray<uint256>> = allocateDynamicArray(@uint256, sc_size" ++ i ++ ");",
      "            if (sc_size" ++ i ++ " > 0) {",
      "                IndexAccess.set(sc_inner" ++ i ++ ", uint256(0), uint256(" ++ a ++ "));",
      "            }",
      "            if (sc_size" ++ i ++ " > 1) {",
      "                IndexAccess.set(sc_inner" ++ i ++ ", uint256(1), uint256(" ++ b ++ "));",
      "            }",
      set ("sc_inner" ++ i)]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let element := plan.shape.element
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_", "return_"]
      (plan.step.helpers ++ [plan.step.entry]), ""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  let guarded := (List.range Solcore.Synthesis.Core.ArrayReturn.maxCount).map fun index =>
    ["        if (sc_count > " ++ toString index ++ ") {"] ++ elementLines element index ++ ["        }"]
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++
      "(flags: uint256, input: uint256, choice: uint256, length: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_choice: word = Typedef.rep(choice);",
    "        let sc_count: word = (Typedef.rep(length) % 4);",
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
    "        let sc_rk: word = (sc_result * " ++ multiplierLiteral ++ ");",
    "        let sc_mix: word = ((sload(1) * " ++ multiplierLiteral ++ ") ^ sc_last);",
    "        let sc_items: memory<DynArray<" ++ elementType element ++ ">> = allocateDynamicArray(@" ++
      elementType element ++ ", sc_count);"] ++ guarded.flatten ++
    ["        let sc_encoded: word = Typedef.rep(abi_encode(sc_items));",
    "        return_((sc_encoded + 32), mload(sc_encoded));",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.ArrayReturn
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.ArrayReturnExecution
/-! Execute the original checked array-return contract over a persistent account
world. Each invocation starts a fresh Core heap and only the public terminal
`finalWorld` becomes the next transaction's world. Calldata is the selector of
`run(uint256,uint256,uint256,uint256)` with the flags, input, choice and length
Words. Observations report the whole return data, the three declared slots and
the contract's whole committed storage.

`model` is an independent reading of the emitted source: a slot map, the step
evaluated alone in Core, the count and inner lengths read from the
transaction's `length` and `choice`, the elements' memory as the method writes
it, and std's `abi_encode` of the memory array run over a byte buffer: the
array encoder's offset, length and element loop, each element's codec, and for
`bytes` elements `encodeIntoFromBytesLike`, which copies the length Word and
the data from the element's memory and zeroes the rest of the last Word. A
reverted transaction keeps the prior slots. It shares nothing with the Core
contract but that step. Tests compare the two; neither is an oracle for the
differential paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.ArrayReturnExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ArrayReturn (CheckedPlan Element Shape)

def historySchema : String := "solcore-lean.array-return-history.v1"

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
def observedSlots : List Word := (List.range ArrayReturn.slotCount).map Word.ofNatModulo

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
array, or the one reverted Word) and the slots it leaves committed. -/
structure ModelRow where
  reverted : Bool
  output : ByteArray
  slots : List Word

private def slotAt (slots : List Word) (slot : Nat) : Word := slots.getD slot Word.zero

/-- An element's memory as the method writes it: a Word (`uint256`, or
`bytes4` right-aligned), a `bytes` value's 96 bytes (its length Word and two
data Words, dirty past the length), or an inner array's Words. -/
inductive Value where
  | word (value : Word)
  | block (length : Nat) (memory : ByteArray)
  | inner (values : List Word)

/-- A byte buffer standing for EVM memory: writes past the end extend it with
zeros, as memory expansion does. -/
private def write (buffer : ByteArray) (offset : Nat) (bytes : ByteArray) : ByteArray :=
  let padded := if buffer.size < offset + bytes.size then
      buffer ++ ⟨Array.replicate (offset + bytes.size - buffer.size) 0⟩
    else buffer
  bytes.copySlice 0 padded offset bytes.size

private def mstore (buffer : ByteArray) (offset : Nat) (value : Word) : ByteArray :=
  write buffer offset (encodeWordBytesBE value)

private def wordAt (value : Nat) : Word := Word.ofNatModulo value

/-- `encodeInto` of one element at `base + offset` with the tail at `tail`, as
std's codecs do; returns the buffer and the new tail. `uint256` stores its
Word, `bytes4` its Word shifted left by 224, `bytes` its offset from `base`,
then `length + 32` bytes copied from its memory and zeros to a whole Word, and
an inner array its offset, its length and its Words. -/
private def encodeElement (buffer : ByteArray) (base offset tail : Nat) : Value → ByteArray × Nat
  | .word value => (mstore buffer (base + offset) value, tail)
  | .block length memory =>
      let total := length + 32
      let rounded := (total + 31) / 32 * 32
      let buffer := mstore buffer (base + offset) (wordAt (tail - base))
      let buffer := write buffer tail (memory.extract 0 total)
      (write buffer (tail + total) ⟨Array.replicate (rounded - total) 0⟩, tail + rounded)
  | .inner values =>
      let buffer := mstore buffer (base + offset) (wordAt (tail - base))
      let buffer := mstore buffer tail (wordAt values.length)
      let buffer := values.zipIdx.foldl (fun buffer (value, index) => mstore buffer (tail + 32 + 32 * index) value)
        buffer
      (buffer, tail + 32 + 32 * values.length)

/-- std's `abi_encode` of a `memory<DynArray<t>>`: the head's offset Word, then
`ABIEncode<memory<DynArray<t>>>.encodeInto`, which writes the length at the
tail and runs each element's codec at stride 32 into the element region, the
dynamic tails following the heads. -/
def stdEncoding (element : Element) (values : List Value) : ByteArray := Id.run do
  let start := 32
  let tail := start + 32
  let mut buffer := mstore ByteArray.empty start (wordAt (tail - start))
  buffer := mstore buffer tail (wordAt values.length)
  let elements := tail + 32
  let mut next := elements + 32 * values.length
  for (value, index) in values.zipIdx do
    let shifted := match element, value with
      | .fourBytes, .word word => Value.word (word * wordAt (2 ^ 224))
      | _, value => value
    let (written, newTail) := encodeElement buffer elements (32 * index) next shifted
    buffer := written
    next := newTail
  return buffer.extract start next

/-- It follows the source: `sc_count = length % 4`, `sc_prior = sload(0)`,
`sc_last = sload(2)`, `sc_result = sc_step(sc_prior + sc_input)`, the three
writes, then `sc_calls = sload(1)` and `sc_mix = (sc_calls * K) ^ sc_last`;
element `i` below the count holds `a = sc_result * K + i` and `b = sc_mix + i`:
the Word `a`, `bytes4(a & 0xffffffff)`, 96 bytes of the inner length
`(choice / 65^i) % 65`, `a` and `b`, or an inner array of the first
`(choice / 3^i) % 3` of `a` and `b`. -/
def modelTransaction (step : Aggregates.CheckedDAG) (fuel : Nat) (element : Element) (prior : List Word)
    (transaction : Transaction) : Option ModelRow := do
  let before := slotAt prior 0
  let last := slotAt prior 2
  let result ← stepResult step fuel (before + transaction.input)
  let written := ((prior.set 0 result).set 1 (slotAt prior 1 + Word.ofNatModulo 1)).set 2 transaction.input
  if transaction.flags.val % 2 == 1 then
    return ⟨true, encodeWordBytesBE result, prior⟩
  let multiplier := Word.ofNatModulo ArrayReturn.multiplier
  let mix := (slotAt written 1 * multiplier) ^^^ last
  let count := transaction.length.val % 4
  let values := (List.range count).map fun index =>
    let a := result * multiplier + wordAt index
    let b := mix + wordAt index
    match element with
    | .words => Value.word a
    | .fourBytes => Value.word (a.bitAnd (wordAt 0xffffffff))
    | .bytes =>
        let length := transaction.choice.val / 65 ^ index % 65
        Value.block length (encodeWordBytesBE (wordAt length) ++ encodeWordBytesBE a ++ encodeWordBytesBE b)
    | .nested => Value.inner ([a, b].take (transaction.choice.val / 3 ^ index % 3))
  return ⟨false, stdEncoding element values, written⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (fuel : Nat) (element : Element) (transactions : List Transaction) :
    Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate ArrayReturn.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step fuel element slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

end Solcore.Synthesis.Stateful.ArrayReturnExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.ArrayReturnCases
/-! Array-return cases retain one original host-aware Core contract, its array's
shape and an ordered history of `(flags, input, choice, length)` transactions,
every one of which carries the shape's `choice` and `length`. Reductions remove
transactions, drop the last element, change the element type to `uint256`,
shorten inner lengths, reduce the step and simplify flags and inputs; a changed
shape changes every transaction's `choice` and `length` with it. Saved outputs
are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ArrayReturn
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ArrayReturn (CheckedPlan Element Shape)
open Solcore.Synthesis.Stateful.ArrayReturnExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-array-return-case.v1"
def planSchema : String := "solcore-lean.array-return-plan.v1"
def profileVersion : String := "stateful-array-returns-v1/array-sequence-seed-v1"
def templateVersion : String := "std-array-encode-result-count-last-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-array-return-corpus.v1"

/-- Flags values and inputs; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- `bytes` lengths drawn with probability one half: empty, the Word boundaries
and the bound. -/
def lengthBank : List Nat := [0, 1, 31, 32, 33, 63, 64]

/-- Complete contracts, shell included, stay within the largest step budget. -/
def maxProgramNodes : Nat := 512

/-- Whether a transaction carries the shape's run-time arguments. -/
def admits (shape : Shape) (transaction : Transaction) : Bool :=
  transaction.length.val == shape.lengthArgument && transaction.choice.val == shape.choiceArgument

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
  s!"array-return scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, each with the plan's count as its length and the plan's inner lengths as its choice"

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions plan.shape transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical array-return contract exceeds its case limit"
  else throw transactionRule

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("choice", toJson (toString tx.choice.val)), ("length", toJson (toString tx.length.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.ArrayReturnExecution.calldata tx.flags tx.input tx.choice
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

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("elements", toJson plan.shape.element.name),
  ("count", toJson plan.shape.count), ("lengths", toJson plan.shape.lengths),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported array-return plan schema"
  let some element := Element.ofName? (← json.getObjValAs? String "elements")
    | throw "unsupported array element type"
  let shape : Shape := ⟨element, ← json.getObjValAs? Nat "count", ← json.getObjValAs? (List Nat) "lengths"⟩
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step shape
    | throw "array-return plan needs at most three elements, one inner length per dynamic element within its bound, and full host-Core admission"
  unless json == planJson plan do throw "array-return plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "array-return contract exceeds its case limit"
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
    ("schema", toJson caseSchema), ("arrayReturnPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.ArrayReturnExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.ArrayReturn.version),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic array-return case schema"
  let plan ← checkedPlan (← json.getObjVal? "arrayReturnPlan")
  let transactions ← decodeTransactions plan.shape (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical array-return plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.ArrayReturnExecution.slotsJson do
    throw "observed slots must be zero through two"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.ArrayReturnExecution.observe scenario.plan scenario.transactions bindings fuel

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

/-- The element type, the count, then per element a `bytes` length selector, a
uniform `bytes` length and an inner array's length. -/
def shapeBounds : List Nat := [4, 4, 14, 14, 14, 65, 65, 65, 3, 3, 3]

def shapeChoices (seed : Seed) : List Nat := boundedDraws seed 0x6172722d73686170 shapeBounds

/-- The four element types in the order of the element-type draw. -/
def elementTypes : List Element := [.words, .fourBytes, .bytes, .nested]

/-- An element type and a count, uniformly; a `bytes` length from the bank
when its selector is below seven, else the uniform draw from 0 to 64; an inner
array's length uniformly from 0 to 2. -/
def generatedShape (seed : Seed) : Shape :=
  let choices := shapeChoices seed
  let element := elementTypes.getD (choices.getD 0 0) .words
  let count := choices.getD 1 0
  let length := fun (index : Nat) => match element with
    | .bytes =>
        let selector := choices.getD (2 + index) 0
        if selector < lengthBank.length then lengthBank.getD selector 0 else choices.getD (5 + index) 0
    | _ => choices.getD (8 + index) 0
  ⟨element, count, if element.dynamic then (List.range count).map length else []⟩

/-- Three flags, three inputs, then the completion pattern. -/
def sequenceBounds : List Nat := [6, 6, 6, 6, 6, 6, 4]

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x6172722d73657173 sequenceBounds

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 6 0) [false, false, false]

/-- A transaction of the shape's run-time arguments. -/
def shaped (shape : Shape) (id : String) (flags input : Word) : Transaction :=
  ⟨id, flags, input, Word.ofNatModulo shape.choiceArgument, Word.ofNatModulo shape.lengthArgument⟩

def blockTransactions (shape : Shape) (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    shaped shape ("tx-" ++ toString (first + index)) (parityInput odd (bank index)) (bank (3 + index))

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
  let shell := Solcore.Synthesis.Core.ArrayReturn.shellNodes shape
  unless nodes ≤ 512 && shell < nodes do
    throw "node budget is too small for the array-return wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - shell) revision
  let some plan := CheckedPlan.ofParts? step shape | throw "generated array-return plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions shape seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do
    throw "array-return contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "array-return-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("shapeChoices", toJson (shapeChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "array-return history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "array-return history did not follow its prescribed flags parities"

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
            error == "array-return history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "array-return-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- `uint256` 0, `bytes4` 1, inner arrays 2 and `bytes` 3. -/
def elementWeight : Element → Nat
  | .words => 0
  | .fourBytes => 1
  | .nested => 2
  | .bytes => 3

def totalLength (shape : Shape) : Nat := shape.lengths.foldl (· + ·) 0

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.flags.val + transaction.input.val) 0

/-- Transaction count, the element count, the element type's weight, the total
inner length, complete program size/literals, then flags and input values.
Every axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (candidate.plan.shape.count < source.plan.shape.count ∨
    (candidate.plan.shape.count = source.plan.shape.count ∧
      (elementWeight candidate.plan.shape.element < elementWeight source.plan.shape.element ∨
      (elementWeight candidate.plan.shape.element = elementWeight source.plan.shape.element ∧
        (totalLength candidate.plan.shape < totalLength source.plan.shape ∨
        (totalLength candidate.plan.shape = totalLength source.plan.shape ∧
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

/-- The transactions with a new shape's run-time arguments. -/
def reshaped (shape : Shape) (transactions : List Transaction) : List Transaction :=
  transactions.map fun tx => shaped shape tx.id tx.flags tx.input

/-- One-transaction removals, the last element dropped, `uint256` elements,
shorter inner lengths, step reductions, then per transaction the flags' parity
bit and the input's low byte. A changed shape changes every transaction's
arguments with it. Candidates still need execution to establish that they
preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let shape := source.plan.shape
  let mut raw : List (Aggregates.CheckedDAG × Shape × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, shape,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  let mut shapes : List Shape := []
  if shape.count > 0 then
    shapes := shapes ++ [{shape with count := shape.count - 1, lengths := shape.lengths.dropLast}]
  if shape.element != .words then
    shapes := shapes ++ [⟨.words, shape.count, []⟩]
  for (length, index) in shape.lengths.zipIdx do
    let shorter := match shape.element with
      | .bytes => [0, length / 2]
      | _ => [length - 1]
    for value in shorter.eraseDups do
      if value < length then
        shapes := shapes ++ [{shape with lengths := shape.lengths.set index value}]
  for smaller in shapes do
    raw := raw ++ [(source.plan.step, smaller, reshaped smaller source.transactions)]
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
      ("functionVersion", Solcore.Synthesis.Core.ArrayReturn.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from array-return plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from array-return wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "array-return-generated" then
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
      throw "saved origin differs from generated array-return provenance"
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
  else throw "unsupported array-return case origin"
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

end Solcore.Synthesis.Source.ArrayReturn
end

section
-- leanmerge: from Solcore.Synthesis.Source.BytesReturnEmitter
/-! Emit the bytes-return protocol as a public method returning `memory<bytes>`.
The method allocates three Words with std's `allocate_memory`, stores the
length and the two data Words and returns the pointer; std's dispatcher
ABI-encodes it with `abi_encode`, which copies the length and data and zeroes
the rest of the last Word. The second data Word rereads slot one after the
writes. Memory at zero is touched only before the terminal revert. No emitter
proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.BytesReturn

open Solcore.Synthesis.Core.BytesReturn (CheckedPlan)

def emitterVersion : String := "solcore-source-bytes-returns-v1"
def wrapperVersion : String := "solcore-bounded-bytes-returns-contract-v1"
def contractName : String := "SynthesizedBytesReturns"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256,uint256)"
def selector : String := "0x24b912e5"
def deployPath : List String := ["SynthesizedBytesReturnsDeploy"]
def runtimePath : List String := ["SynthesizedBytesReturnsDeploy", "SynthesizedBytesReturns"]

/-- The multiplier `K` as a hexadecimal literal. -/
def multiplierLiteral : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 Solcore.Synthesis.Core.BytesReturn.multiplier)

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), ""]
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
    "    function " ++ methodName ++
      "(flags: uint256, input: uint256, length: uint256) public returns (memory<bytes>) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
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
    "        let sc_pointer: word = allocate_memory(96);",
    "        mstore(sc_pointer, sc_length);",
    "        mstore((sc_pointer + 32), (sc_result * " ++ multiplierLiteral ++ "));",
    "        mstore((sc_pointer + 64), ((sload(1) * " ++ multiplierLiteral ++ ") ^ sc_last));",
    "        return Typedef.abs(sc_pointer);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.BytesReturn
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.BytesReturnExecution
/-! Execute the original checked bytes-return contract over a persistent account
world. Each invocation starts a fresh Core heap and only the public terminal
`finalWorld` becomes the next transaction's world. Calldata is the selector of
`run(uint256,uint256,uint256)` with the flags, input and length Words.
Observations report the whole return data, the three declared slots and the
contract's whole committed storage.

`model` is an independent reading of the emitted source: a slot map, the step
evaluated alone in Core, the method's three memory Words and std's
`encodeIntoFromBytesLike`, which writes the offset, copies the length Word and
`length` data bytes and zeroes the rest of the last Word. A reverted
transaction keeps the prior slots. It shares nothing with the Core contract but
that step. Tests compare the two; neither is an oracle for the differential
paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.BytesReturnExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.BytesReturn (CheckedPlan)

def historySchema : String := "solcore-lean.bytes-return-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  length : Word
  deriving BEq

/-- The selector of `run(uint256,uint256,uint256)`, then the flags, input and
length Words. -/
def inputData (flags input length : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x24, 0xb9, 0x12, 0xe5] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input ++
    encodeWordBytesBE length
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input length : Word) : String := encodeBytesText (inputData flags input length).bytes

/-- Slot zero holds the accumulator, slot one the committed call count and slot
two the last committed input. -/
def observedSlots : List Word := (List.range BytesReturn.slotCount).map Word.ofNatModulo

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
            inputData := inputData transaction.flags transaction.input transaction.length }
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

/-- std's `encodeIntoFromBytesLike` for the one returned value at `memory`: the
head offset 32, then `length + 32` bytes copied from the length Word on, then
zeros up to a multiple of 32. -/
def stdEncoding (memory : ByteArray) (length : Nat) : ByteArray :=
  let total := length + 32
  let rounded := (total + 31) / 32 * 32
  encodeWordBytesBE (Word.ofNatModulo 32) ++ memory.extract 0 total ++ ⟨Array.replicate (rounded - total) 0⟩

/-- It follows the source: `sc_length = length % 65`, `sc_prior = sload(0)`,
`sc_last = sload(2)`, `sc_result = sc_step(sc_prior + sc_input)`, the three
writes, then the 96 bytes at `sc_pointer`: `sc_length`, `sc_result * K` and
`(sload(1) * K) ^ sc_last`. -/
def modelTransaction (step : Aggregates.CheckedDAG) (fuel : Nat) (prior : List Word)
    (transaction : Transaction) : Option ModelRow := do
  let before := slotAt prior 0
  let last := slotAt prior 2
  let result ← stepResult step fuel (before + transaction.input)
  let written := ((prior.set 0 result).set 1 (slotAt prior 1 + Word.ofNatModulo 1)).set 2 transaction.input
  if transaction.flags.val % 2 == 1 then
    return ⟨true, encodeWordBytesBE result, prior⟩
  let length := transaction.length.val % 65
  let multiplier := Word.ofNatModulo BytesReturn.multiplier
  let memory := encodeWordBytesBE (Word.ofNatModulo length) ++ encodeWordBytesBE (result * multiplier) ++
    encodeWordBytesBE ((slotAt written 1 * multiplier) ^^^ last)
  return ⟨false, stdEncoding memory length, written⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (fuel : Nat) (transactions : List Transaction) :
    Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate BytesReturn.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step fuel slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

end Solcore.Synthesis.Stateful.BytesReturnExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.BytesReturnCases
/-! Bytes-return cases retain one original host-aware Core contract and an
ordered history of `(flags, input, length)` transactions. Reductions remove
transactions, shorten lengths, reduce the step and simplify flags and inputs.
Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.BytesReturn
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.BytesReturn (CheckedPlan)
open Solcore.Synthesis.Stateful.BytesReturnExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-bytes-return-case.v1"
def planSchema : String := "solcore-lean.bytes-return-plan.v1"
def profileVersion : String := "stateful-bytes-returns-v1/bytes-sequence-seed-v2"
def templateVersion : String := "bytes-result-count-last-length-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-bytes-return-corpus.v1"

/-- Flags values and inputs; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- Lengths drawn with probability one half: empty, the Word boundaries and the
bound. -/
def lengthBank : List Nat := [0, 1, 31, 32, 33, 63, 64]

/-- Complete contracts, shell included, stay within the largest step budget. -/
def maxProgramNodes : Nat := 512

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (fun tx => tx.length.val ≤ Solcore.Synthesis.Core.BytesReturn.maxLength) = true

instance (transactions : List Transaction) : Decidable (validTransactions transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical bytes-return contract exceeds its case limit"
  else throw s!"bytes-return scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs and lengths of at most {Solcore.Synthesis.Core.BytesReturn.maxLength}"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("length", toJson (toString tx.length.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.BytesReturnExecution.calldata tx.flags tx.input tx.length)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json :=
  toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← word (← row.getObjValAs? String "input"),
      ← word (← row.getObjValAs? String "length")⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, input, length, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw s!"bytes-return scenario requires distinct valid transaction IDs and lengths of at most {Solcore.Synthesis.Core.BytesReturn.maxLength}"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported bytes-return plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "bytes-return plan failed full host-Core admission"
  unless json == planJson plan do throw "bytes-return plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "bytes-return contract exceeds its case limit"
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
    ("schema", toJson caseSchema), ("bytesReturnPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.BytesReturnExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.BytesReturn.version),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic bytes-return case schema"
  let plan ← checkedPlan (← json.getObjVal? "bytesReturnPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical bytes-return plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.BytesReturnExecution.slotsJson do
    throw "observed slots must be zero through two"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.BytesReturnExecution.observe scenario.plan scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Three flags, three inputs, the completion pattern, then per transaction a
length selector and a uniform length. Each choice uses the high half of one
draw from a separate stream, which starts at SplitMix64's finalizer of the seed
xor its domain, so that consecutive seeds' choices do not step by a fixed
residue. -/
def sequenceBounds : List Nat := [6, 6, 6, 6, 6, 6, 4, 14, 14, 14, 65, 65, 65]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x62797465732d7371))
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 6 0) [false, false, false]

/-- A selector below seven picks that entry of the length bank; otherwise the
uniform draw from 0 to 64 is the length. -/
def generatedLength (choices : List Nat) (index : Nat) : Nat :=
  let selector := choices.getD (7 + index) 0
  if selector < lengthBank.length then lengthBank.getD selector 0 else choices.getD (10 + index) 0

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), parityInput odd (bank index), bank (3 + index),
      Word.ofNatModulo (generatedLength choices index)⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The shell lies inside the budget, and the complete contract is remeasured as
the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.BytesReturn.shellNodes < nodes do
    throw "node budget is too small for the bytes-return wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.BytesReturn.shellNodes) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated bytes-return plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do
    throw "bytes-return contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "bytes-return-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "bytes-return history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "bytes-return history did not follow its prescribed flags parities"

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
            error == "bytes-return history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "bytes-return-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def totalLength (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.length.val) 0

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.flags.val + transaction.input.val) 0

/-- Transaction count, the total length, complete program size/literals, then
flags and input values. Every axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (totalLength candidate < totalLength source ∨
    (totalLength candidate = totalLength source ∧
      ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
      (complexity candidate.program.body = complexity source.program.body ∧
        valueWeight candidate < valueWeight source)))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofStep? step
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

/-- One-transaction removals, shorter lengths, step reductions, then per
transaction the flags' parity bit and the input's low byte. Candidates still
need execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  -- A shorter length, empty or halved, keeps every effect of its transaction.
  for (transaction, index) in source.transactions.zipIdx do
    for shorter in [0, transaction.length.val / 2] do
      if shorter < transaction.length.val then
        raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx =>
          {tx with length := Word.ofNatModulo shorter})]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for index in List.range source.transactions.length do
    raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx =>
      {tx with input := tx.input.bitAnd (Word.ofNatModulo 255)})]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.candidate.program),
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
      ("functionVersion", Solcore.Synthesis.Core.BytesReturn.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from bytes-return plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from bytes-return wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "bytes-return-generated" then
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
      throw "saved origin differs from generated bytes-return provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported bytes-return case origin"
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

end Solcore.Synthesis.Source.BytesReturn
end

section
-- leanmerge: from Solcore.Synthesis.Source.TupleReturnEmitter
/-! Emit the tuple-return protocol as a public method whose return type is the
tuple of the plan's arity of uint256. The method returns a tuple expression,
which std's dispatcher ABI-encodes into one static head per Word; its second
Word rereads slot one after the writes. Memory at zero is touched only before
the terminal revert. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.TupleReturn

open Solcore.Synthesis.Core.TupleReturn (CheckedPlan)

def emitterVersion : String := "solcore-source-tuple-returns-v1"
def wrapperVersion : String := "solcore-word-tuple-returns-contract-v1"
def contractName : String := "SynthesizedTupleReturns"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedTupleReturnsDeploy"]
def runtimePath : List String := ["SynthesizedTupleReturnsDeploy", "SynthesizedTupleReturns"]

/-- The method's return type: the tuple of `arity` uint256. -/
def returnType (arity : Nat) : String :=
  "(" ++ String.intercalate ", " (List.replicate arity "uint256") ++ ")"

/-- The returned tuple's elements in protocol order, cut to the arity. -/
def returnedWords (arity : Nat) : List String :=
  ["uint256(sc_result)", "uint256(sload(1))", "uint256(sc_prior)", "uint256(sc_last)"].take arity

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), ""]
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
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns " ++
      returnType plan.arity ++ " {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
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
    "        return (" ++ String.intercalate ", " (returnedWords plan.arity) ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.TupleReturn
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.TupleReturnExecution
/-! Execute the original checked tuple-return contract over a persistent account
world. Each invocation starts a fresh Core heap and only the public terminal
`finalWorld` becomes the next transaction's world. Calldata is the selector of
`run(uint256,uint256)` with the flags and input Words. Observations report the
whole return data, the three declared slots and the contract's whole committed
storage.

`model` is an independent reading of the emitted source: a slot map, the step
evaluated alone in Core, and the returned Words listed in source order. A
reverted transaction keeps the prior slots. It shares nothing with the Core
contract but that step. Tests compare the two; neither is an oracle for the
differential paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.TupleReturnExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.TupleReturn (CheckedPlan)

def historySchema : String := "solcore-lean.tuple-return-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  deriving BEq

/-- The selector of `run(uint256,uint256)`, then the flags and input Words. -/
def inputData (flags input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input : Word) : String := encodeBytesText (inputData flags input).bytes

/-- Slot zero holds the accumulator, slot one the committed call count and slot
two the last committed input. -/
def observedSlots : List Word := (List.range TupleReturn.slotCount).map Word.ofNatModulo

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
            target := bindings.address, caller := bindings.caller,
            callValue := Word.zero, inputData := inputData transaction.flags transaction.input }
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

/-- One modelled transaction: whether it reverts, the Words of its output (the
returned tuple, or the one reverted Word) and the slots it leaves committed. It
follows the source: `sc_prior = sload(0)`, `sc_last = sload(2)`,
`sc_result = sc_step(sc_prior + sc_input)`, the three writes, then the returned
tuple `(sc_result, sload(1), sc_prior, sc_last)` cut to the arity. -/
structure ModelRow where
  reverted : Bool
  output : List Word
  slots : List Word
  deriving BEq

private def slotAt (slots : List Word) (slot : Nat) : Word := slots.getD slot Word.zero

def modelTransaction (step : Aggregates.CheckedDAG) (fuel arity : Nat) (prior : List Word)
    (transaction : Transaction) : Option ModelRow := do
  let before := slotAt prior 0
  let last := slotAt prior 2
  let result ← stepResult step fuel (before + transaction.input)
  let written := ((prior.set 0 result).set 1 (slotAt prior 1 + Word.ofNatModulo 1)).set 2 transaction.input
  let reverted := transaction.flags.val % 2 == 1
  let returned := [result, slotAt written 1, before, last].take arity
  return ⟨reverted, if reverted then [result] else returned, if reverted then prior else written⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (fuel arity : Nat) (transactions : List Transaction) :
    Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate TupleReturn.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step fuel arity slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

/-- The output bytes of a modelled row: its Words, big-endian and concatenated. -/
def outputBytes (row : ModelRow) : ByteArray :=
  row.output.foldl (fun bytes value => bytes ++ encodeWordBytesBE value) ByteArray.empty

end Solcore.Synthesis.Stateful.TupleReturnExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.TupleReturnCases
/-! Tuple-return cases retain one original host-aware Core contract, its arity
and an ordered history of `(flags, input)` transactions. Reductions remove
transactions, lower the arity, reduce the step and simplify flags and inputs.
Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.TupleReturn
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.TupleReturn (CheckedPlan)
open Solcore.Synthesis.Stateful.TupleReturnExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-tuple-return-case.v1"
def planSchema : String := "solcore-lean.tuple-return-plan.v1"
def profileVersion : String := "stateful-tuple-returns-v1/tuple-sequence-seed-v2"
def templateVersion : String := "tuple-result-count-prior-last-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-tuple-return-corpus.v1"

/-- Flags values and inputs; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- Complete contracts, shell included, stay within the largest step budget. -/
def maxProgramNodes : Nat := 512

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true

instance (transactions : List Transaction) : Decidable (validTransactions transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical tuple-return contract exceeds its case limit"
  else throw s!"tuple-return scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.TupleReturnExecution.calldata tx.flags tx.input)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json :=
  toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← word (← row.getObjValAs? String "input")⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, input, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "tuple-return scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("arity", toJson plan.arity)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported tuple-return plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let arity ← json.getObjValAs? Nat "arity"
  let some plan := CheckedPlan.ofParts? step arity |
    throw "tuple-return plan has an invalid arity or failed full host-Core admission"
  unless json == planJson plan do throw "tuple-return plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "tuple-return contract exceeds its case limit"
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
    ("schema", toJson caseSchema), ("tupleReturnPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.TupleReturnExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.TupleReturn.version),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic tuple-return case schema"
  let plan ← checkedPlan (← json.getObjVal? "tupleReturnPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical tuple-return plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.TupleReturnExecution.slotsJson do
    throw "observed slots must be zero through two"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.TupleReturnExecution.observe scenario.plan scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Three flags, three inputs, then the completion pattern. Each choice uses the
high half of one draw from a separate stream, which starts at SplitMix64's
finalizer of the seed xor its domain, so that consecutive seeds' choices do not
step by a fixed residue. -/
def sequenceBounds : List Nat := [6, 6, 6, 6, 6, 6, 4]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x7475706c652d7371))
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

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

/-- Separates the arity stream from other uses of a case seed. -/
private def arityDomain : UInt64 := 0x7475706c65617279

/-- A SplitMix64 hash of the seed, so that consecutive seeds vary in their arity
independently of the step's helper count and template. -/
def arityFor (seed : Seed) : Nat :=
  [2, 3, 4].getD ((GeneratorV2.mix (seed.toUInt64 ^^^ arityDomain)).toNat % 3) 4

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The shell lies inside the budget, and the complete contract is remeasured as
the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let arity := arityFor seed
  unless nodes ≤ 512 && Solcore.Synthesis.Core.TupleReturn.shellNodes arity < nodes do
    throw "node budget is too small for the tuple-return wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.TupleReturn.shellNodes arity) revision
  let some plan := CheckedPlan.ofParts? step arity | throw "generated tuple-return plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do
    throw "tuple-return contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "tuple-return-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("arity", toJson arity), ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "tuple-return history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "tuple-return history did not follow its prescribed flags parities"

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
            error == "tuple-return history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "tuple-return-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.flags.val + transaction.input.val) 0

/-- Transaction count, the arity, complete program size/literals, then flags
and input values. Every axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (candidate.plan.arity < source.plan.arity ∨
    (candidate.plan.arity = source.plan.arity ∧
      ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
      (complexity candidate.program.body = complexity source.program.body ∧
        valueWeight candidate < valueWeight source)))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (arity : Nat)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step arity
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

/-- One-transaction removals, lower arities, step reductions, then per
transaction the flags' parity bit and the input's low byte. Candidates still
need execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let arity := source.plan.arity
  let mut raw : List (Aggregates.CheckedDAG × Nat × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, arity,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  -- A lower arity drops trailing Words and keeps every effect.
  for lower in [3, 2] do
    if lower < arity then
      raw := raw ++ [(source.plan.step, lower, source.transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, arity, source.transactions)]
  for index in List.range source.transactions.length do
    raw := raw ++ [(source.plan.step, arity, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(source.plan.step, arity, replaceAt source.transactions index fun tx =>
      {tx with input := tx.input.bitAnd (Word.ofNatModulo 255)})]
  let mut seen : List String := []
  let mut result := []
  for (step, lower, transactions) in raw do
    if let some reduced := sealReduction source step lower transactions then
      let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.candidate.program),
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
      ("functionVersion", Solcore.Synthesis.Core.TupleReturn.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from tuple-return plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from tuple-return wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "tuple-return-generated" then
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
      throw "saved origin differs from generated tuple-return provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.arity admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported tuple-return case origin"
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

end Solcore.Synthesis.Source.TupleReturn
end
