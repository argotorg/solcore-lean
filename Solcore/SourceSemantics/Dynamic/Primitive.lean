import Solcore.SourceSemantics.Dynamic.Value
import Solcore.SourceSemantics.Expressions
import Solcore.SourceSemantics.Requirements
import Solcore.Frontend.WordLiteral

/-!
# Primitives and patterns

Primitive operations, coercions, mappings and pattern matching. Main declarations:
`Dynamic.BinaryPrimitiveApplies`, `Dynamic.UnaryPrimitiveApplies`, `Dynamic.BuiltinApplies`,
`Dynamic.CoercionPathApplies`, `Dynamic.PatternMatches`, `Dynamic.MatchCasesSelect`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.Dynamic.Primitive
/-!
Declarative primitive operations for source evaluation.

This module gives mathematical relations for literals, primitive operators,
compiler-provided functions, and mappings.  It does not call the executable
source runtime.  Equality is intentionally selective: closures and mappings are
not comparable, matching the source language's current equality behavior.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference

/-- Values for which source equality is structurally defined. -/
inductive ValueComparable : Value → Prop where
  | unit : ValueComparable .unit
  | bool (value : Bool) : ValueComparable (.bool value)
  | word (value : Core.Word) : ValueComparable (.word value)
  | integer (value : Int) : ValueComparable (.integer value)
  | product {left right : Value}
      (leftComparable : ValueComparable left)
      (rightComparable : ValueComparable right) :
      ValueComparable (.product left right)
  | proxy (inner : TypeSystem.Ty) : ValueComparable (.proxy inner)
  | constructed
      (instantiation : DataConstructorInstantiation)
      (arguments : List Value)
      (argumentsComparable :
        ∀ argument, argument ∈ arguments → ValueComparable argument) :
      ValueComparable (.constructed instantiation arguments)
  | global (function : GlobalFunction) : ValueComparable (.global function)
  | builtin (function : BuiltinFunction) : ValueComparable (.builtin function)

/-- Source equality succeeds exactly for identical comparable values. -/
def ValueEquivalent (left right : Value) : Prop :=
  left = right ∧ ValueComparable left

/-- Pointwise source equality of a value vector. -/
def ValuesEquivalent (left right : List Value) : Prop :=
  left = right ∧ ∀ value, value ∈ left → ValueComparable value

namespace ValueEquivalent

theorem refl {value : Value} (comparable : ValueComparable value) :
    ValueEquivalent value value :=
  ⟨rfl, comparable⟩

theorem eq {left right : Value}
    (equivalent : ValueEquivalent left right) : left = right :=
  equivalent.1

theorem comparable_left {left right : Value}
    (equivalent : ValueEquivalent left right) : ValueComparable left :=
  equivalent.2

theorem comparable_right {left right : Value}
    (equivalent : ValueEquivalent left right) : ValueComparable right := by
  rcases equivalent with ⟨rfl, comparable⟩
  exact comparable

theorem symmetric {left right : Value}
    (equivalent : ValueEquivalent left right) :
    ValueEquivalent right left := by
  rcases equivalent with ⟨rfl, comparable⟩
  exact ⟨rfl, comparable⟩

theorem transitive {first second third : Value}
    (left : ValueEquivalent first second)
    (right : ValueEquivalent second third) :
    ValueEquivalent first third := by
  rcases left with ⟨rfl, comparable⟩
  rcases right with ⟨rfl, _⟩
  exact ⟨rfl, comparable⟩

end ValueEquivalent

namespace ValuesEquivalent

theorem refl {values : List Value}
    (comparable : ∀ value, value ∈ values → ValueComparable value) :
    ValuesEquivalent values values :=
  ⟨rfl, comparable⟩

theorem eq {left right : List Value}
    (equivalent : ValuesEquivalent left right) : left = right :=
  equivalent.1

theorem nil : ValuesEquivalent [] [] :=
  ⟨rfl, by simp⟩

theorem cons {left right : Value} {lefts rights : List Value}
    (head : ValueEquivalent left right)
    (tail : ValuesEquivalent lefts rights) :
    ValuesEquivalent (left :: lefts) (right :: rights) := by
  rcases head with ⟨rfl, headComparable⟩
  rcases tail with ⟨rfl, tailComparable⟩
  refine ⟨rfl, ?_⟩
  intro value member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact headComparable
  · exact tailComparable value member

theorem symmetric {left right : List Value}
    (equivalent : ValuesEquivalent left right) :
    ValuesEquivalent right left := by
  rcases equivalent with ⟨rfl, comparable⟩
  exact ⟨rfl, comparable⟩

end ValuesEquivalent

/-- A compatibility literal constructs the modulo-Word value denoted by its
spelling. -/
inductive LiteralConstructs : Syntax.CoreLiteralValue → Value → Prop where
  | word {source : Syntax.CoreLiteralValue} {raw : Nat}
      (meaning : NumericLiteralDenotes source raw) :
      LiteralConstructs source (.word (Core.Word.ofNatModulo raw))

/-- A resolved integer literal constructs the value selected by its exact
target and retained evidence. -/
inductive ResolvedIntegerLiteralConstructs (context : Context) :
    Syntax.CoreLiteralValue → IntegerLiteralResolution → Value → Prop where
  | word
      {source : Syntax.CoreLiteralValue} {raw : Nat}
      {requirement : RequirementId}
      (meaning : NumericLiteralDenotes source raw)
      (evidence : RequirementProves context requirement
        (ProgramSignatures.builtinIntPredicate .word)) :
      ResolvedIntegerLiteralConstructs context source
        { rawValue := raw, targetType := .word, requirement := requirement }
        (.word (Core.Word.ofNatModulo raw))
  | integer
      {source : Syntax.CoreLiteralValue} {raw : Nat}
      {requirement : RequirementId}
      (meaning : NumericLiteralDenotes source raw)
      (evidence : RequirementProves context requirement
        (ProgramSignatures.builtinIntPredicate .integer)) :
      ResolvedIntegerLiteralConstructs context source
        { rawValue := raw, targetType := .integer, requirement := requirement }
        (.integer (Int.ofNat raw))
  /-- A literal at a fixed-width integer type is its word; it is at most the
  type's greatest value, so the word is canonical. -/
  | fixed
      {source : Syntax.CoreLiteralValue} {raw : Nat}
      {requirement : RequirementId} {type : TypeSystem.FixedInteger}
      (meaning : NumericLiteralDenotes source raw)
      (fits : raw ≤ type.maxNat)
      (evidence : RequirementProves context requirement
        (ProgramSignatures.builtinIntPredicate (.fixed type))) :
      ResolvedIntegerLiteralConstructs context source
        { rawValue := raw, targetType := .fixed type, requirement := requirement }
        (.word (Core.Word.ofNatModulo raw))

namespace LiteralConstructs

theorem functional {source : Syntax.CoreLiteralValue} {left right : Value}
    (leftConstruction : LiteralConstructs source left)
    (rightConstruction : LiteralConstructs source right) : left = right := by
  cases leftConstruction with
  | word leftMeaning =>
      cases rightConstruction with
      | word rightMeaning =>
          rw [NumericLiteralDenotes.value_unique leftMeaning rightMeaning]

end LiteralConstructs

namespace ResolvedIntegerLiteralConstructs

theorem valid
    {context : Context} {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution} {value : Value}
    (construction :
      ResolvedIntegerLiteralConstructs context source resolution value) :
    IntegerLiteralValid context source resolution := by
  cases construction with
  | word meaning evidence => exact .word meaning rfl evidence
  | integer meaning evidence => exact .integer meaning rfl evidence
  | fixed meaning _ evidence => exact .fixed meaning rfl evidence

theorem functional
    {context : Context} {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution} {left right : Value}
    (leftConstruction :
      ResolvedIntegerLiteralConstructs context source resolution left)
    (rightConstruction :
      ResolvedIntegerLiteralConstructs context source resolution right) :
    left = right := by
  cases leftConstruction <;> cases rightConstruction <;> rfl

end ResolvedIntegerLiteralConstructs

/-- Infinite two's-complement conjunction on mathematical integers. -/
def integerBitAnd : Int → Int → Int
  | .ofNat left, .ofNat right => .ofNat (left &&& right)
  | .ofNat left, .negSucc right =>
      .ofNat (left ^^^ (left &&& right))
  | .negSucc left, .ofNat right =>
      .ofNat (right ^^^ (right &&& left))
  | .negSucc left, .negSucc right => .negSucc (left ||| right)

/-- Infinite two's-complement disjunction on mathematical integers. -/
def integerBitOr : Int → Int → Int
  | .ofNat left, .ofNat right => .ofNat (left ||| right)
  | .ofNat left, .negSucc right =>
      .negSucc (right ^^^ (right &&& left))
  | .negSucc left, .ofNat right =>
      .negSucc (left ^^^ (left &&& right))
  | .negSucc left, .negSucc right => .negSucc (left &&& right)

/-- Infinite two's-complement exclusive disjunction on mathematical integers. -/
def integerBitXor : Int → Int → Int
  | .ofNat left, .ofNat right => .ofNat (left ^^^ right)
  | .ofNat left, .negSucc right => .negSucc (left ^^^ right)
  | .negSucc left, .ofNat right => .negSucc (left ^^^ right)
  | .negSucc left, .negSucc right => .ofNat (left ^^^ right)

/-- Primitive unary application.  Trait-selected unary methods are function
calls in the surrounding dynamic semantics, not extra primitive cases. -/
inductive UnaryPrimitiveApplies : Syntax.UnaryOp → Value → Value → Prop where
  | logicalNot (operand : Bool) :
      UnaryPrimitiveApplies .logicalNot (.bool operand) (.bool (!operand))
  | wordBitNot (operand : Core.Word) :
      UnaryPrimitiveApplies .bitNot (.word operand) (.word operand.bitNot)
  | integerBitNot (operand : Int) :
      UnaryPrimitiveApplies .bitNot (.integer operand) (.integer (~~~operand))

namespace UnaryPrimitiveApplies

theorem functional {operator : Syntax.UnaryOp} {operand left right : Value}
    (leftApplication : UnaryPrimitiveApplies operator operand left)
    (rightApplication : UnaryPrimitiveApplies operator operand right) :
    left = right := by
  cases leftApplication <;> cases rightApplication <;> rfl

end UnaryPrimitiveApplies

/-- Non-short-circuit binary operators evaluate their right operand
unconditionally. -/
inductive StrictBinaryOperator : Syntax.BinaryOp → Prop where
  | multiply : StrictBinaryOperator .multiply
  | divide : StrictBinaryOperator .divide
  | modulo : StrictBinaryOperator .modulo
  | add : StrictBinaryOperator .add
  | subtract : StrictBinaryOperator .subtract
  | shiftLeft : StrictBinaryOperator .shiftLeft
  | shiftRight : StrictBinaryOperator .shiftRight
  | bitAnd : StrictBinaryOperator .bitAnd
  | bitXor : StrictBinaryOperator .bitXor
  | bitOr : StrictBinaryOperator .bitOr
  | less : StrictBinaryOperator .less
  | greater : StrictBinaryOperator .greater
  | lessEqual : StrictBinaryOperator .lessEqual
  | greaterEqual : StrictBinaryOperator .greaterEqual
  | equal : StrictBinaryOperator .equal
  | notEqual : StrictBinaryOperator .notEqual
  | uncheckedAdd : StrictBinaryOperator .uncheckedAdd
  | uncheckedSubtract : StrictBinaryOperator .uncheckedSubtract
  | uncheckedMultiply : StrictBinaryOperator .uncheckedMultiply

/-- Strict operators with a primitive meaning on `integer`: every strict
operator but the shifts, which take Words only. -/
inductive IntegerStrictBinaryOperator : Syntax.BinaryOp → Prop where
  | multiply : IntegerStrictBinaryOperator .multiply
  | divide : IntegerStrictBinaryOperator .divide
  | modulo : IntegerStrictBinaryOperator .modulo
  | add : IntegerStrictBinaryOperator .add
  | subtract : IntegerStrictBinaryOperator .subtract
  | bitAnd : IntegerStrictBinaryOperator .bitAnd
  | bitXor : IntegerStrictBinaryOperator .bitXor
  | bitOr : IntegerStrictBinaryOperator .bitOr
  | less : IntegerStrictBinaryOperator .less
  | greater : IntegerStrictBinaryOperator .greater
  | lessEqual : IntegerStrictBinaryOperator .lessEqual
  | greaterEqual : IntegerStrictBinaryOperator .greaterEqual
  | equal : IntegerStrictBinaryOperator .equal
  | notEqual : IntegerStrictBinaryOperator .notEqual

theorem IntegerStrictBinaryOperator.toStrict {operator : Syntax.BinaryOp}
    (classification : IntegerStrictBinaryOperator operator) :
    StrictBinaryOperator operator := by
  cases classification <;> constructor

/-- Operators that evaluate both operands and then may panic instead of
giving a result: unchecked `/` and `%`, which panic with `0x12` on a zero
divisor. -/
inductive PanickingBinaryOperator : Syntax.BinaryOp → Prop where
  | uncheckedDivide : PanickingBinaryOperator .uncheckedDivide
  | uncheckedModulo : PanickingBinaryOperator .uncheckedModulo

/-- A left value which decides a lazy Boolean binary expression without
evaluating the right occurrence. -/
inductive ShortCircuits : Syntax.BinaryOp → Value → Value → Prop where
  | andFalse : ShortCircuits .logicalAnd (.bool false) (.bool false)
  | orTrue : ShortCircuits .logicalOr (.bool true) (.bool true)

/-- A binary expression must evaluate its right occurrence in these cases. -/
inductive EvaluatesRightOperand : Syntax.BinaryOp → Value → Prop where
  | strict {operator : Syntax.BinaryOp} {left : Value}
      (classification : StrictBinaryOperator operator) :
      EvaluatesRightOperand operator left
  | panicking {operator : Syntax.BinaryOp} {left : Value}
      (classification : PanickingBinaryOperator operator) :
      EvaluatesRightOperand operator left
  | andTrue : EvaluatesRightOperand .logicalAnd (.bool true)
  | orFalse : EvaluatesRightOperand .logicalOr (.bool false)

namespace ShortCircuits

theorem functional {operator : Syntax.BinaryOp} {left first second : Value}
    (firstCircuit : ShortCircuits operator left first)
    (secondCircuit : ShortCircuits operator left second) : first = second := by
  cases firstCircuit <;> cases secondCircuit <;> rfl

theorem excludes_right_operand
    {operator : Syntax.BinaryOp} {left result : Value}
    (circuit : ShortCircuits operator left result) :
    ¬ EvaluatesRightOperand operator left := by
  intro evaluates
  cases circuit with
  | andFalse =>
      cases evaluates with
      | strict classification => cases classification
      | panicking classification => cases classification
  | orTrue =>
      cases evaluates with
      | strict classification => cases classification
      | panicking classification => cases classification

end ShortCircuits

/-- Primitive binary application after both operands have been evaluated. -/
inductive BinaryPrimitiveApplies :
    Syntax.BinaryOp → Value → Value → Value → Prop where
  | wordMultiply (left right : Core.Word) :
      BinaryPrimitiveApplies .multiply (.word left) (.word right)
        (.word (left.mul right))
  | wordDivide (left right : Core.Word) :
      BinaryPrimitiveApplies .divide (.word left) (.word right)
        (.word (left.udiv right))
  | wordModulo (left right : Core.Word) :
      BinaryPrimitiveApplies .modulo (.word left) (.word right)
        (.word (left.umod right))
  | wordAdd (left right : Core.Word) :
      BinaryPrimitiveApplies .add (.word left) (.word right)
        (.word (left.add right))
  | wordSubtract (left right : Core.Word) :
      BinaryPrimitiveApplies .subtract (.word left) (.word right)
        (.word (left.sub right))
  | wordShiftLeft (value amount : Core.Word) :
      BinaryPrimitiveApplies .shiftLeft (.word value) (.word amount)
        (.word (value.shiftLeft amount))
  | wordShiftRight (value amount : Core.Word) :
      BinaryPrimitiveApplies .shiftRight (.word value) (.word amount)
        (.word (value.shiftRight amount))
  | wordUncheckedAdd (left right : Core.Word) :
      BinaryPrimitiveApplies .uncheckedAdd (.word left) (.word right)
        (.word (left.add right))
  | wordUncheckedSubtract (left right : Core.Word) :
      BinaryPrimitiveApplies .uncheckedSubtract (.word left) (.word right)
        (.word (left.sub right))
  | wordUncheckedMultiply (left right : Core.Word) :
      BinaryPrimitiveApplies .uncheckedMultiply (.word left) (.word right)
        (.word (left.mul right))
  | wordUncheckedDivide (left right : Core.Word) (nonzero : right ≠ Core.Word.zero) :
      BinaryPrimitiveApplies .uncheckedDivide (.word left) (.word right)
        (.word (left.udiv right))
  | wordUncheckedModulo (left right : Core.Word) (nonzero : right ≠ Core.Word.zero) :
      BinaryPrimitiveApplies .uncheckedModulo (.word left) (.word right)
        (.word (left.umod right))
  | wordBitAnd (left right : Core.Word) :
      BinaryPrimitiveApplies .bitAnd (.word left) (.word right)
        (.word (left.bitAnd right))
  | wordBitXor (left right : Core.Word) :
      BinaryPrimitiveApplies .bitXor (.word left) (.word right)
        (.word (left.bitXor right))
  | wordBitOr (left right : Core.Word) :
      BinaryPrimitiveApplies .bitOr (.word left) (.word right)
        (.word (left.bitOr right))
  | wordLess (left right : Core.Word) :
      BinaryPrimitiveApplies .less (.word left) (.word right)
        (.bool (decide (left < right)))
  | wordGreater (left right : Core.Word) :
      BinaryPrimitiveApplies .greater (.word left) (.word right)
        (.bool (decide (left > right)))
  | wordLessEqual (left right : Core.Word) :
      BinaryPrimitiveApplies .lessEqual (.word left) (.word right)
        (.bool (decide (left ≤ right)))
  | wordGreaterEqual (left right : Core.Word) :
      BinaryPrimitiveApplies .greaterEqual (.word left) (.word right)
        (.bool (decide (left ≥ right)))
  | integerMultiply (left right : Int) :
      BinaryPrimitiveApplies .multiply (.integer left) (.integer right)
        (.integer (left * right))
  | integerDivideZero (left : Int) :
      BinaryPrimitiveApplies .divide (.integer left) (.integer 0) (.integer 0)
  | integerDivide (left right : Int) (nonzero : right ≠ 0) :
      BinaryPrimitiveApplies .divide (.integer left) (.integer right)
        (.integer (left / right))
  | integerModuloZero (left : Int) :
      BinaryPrimitiveApplies .modulo (.integer left) (.integer 0) (.integer 0)
  | integerModulo (left right : Int) (nonzero : right ≠ 0) :
      BinaryPrimitiveApplies .modulo (.integer left) (.integer right)
        (.integer (left % right))
  | integerAdd (left right : Int) :
      BinaryPrimitiveApplies .add (.integer left) (.integer right)
        (.integer (left + right))
  | integerSubtract (left right : Int) :
      BinaryPrimitiveApplies .subtract (.integer left) (.integer right)
        (.integer (left - right))
  | integerBitAnd (left right : Int) :
      BinaryPrimitiveApplies .bitAnd (.integer left) (.integer right)
        (.integer (Dynamic.integerBitAnd left right))
  | integerBitXor (left right : Int) :
      BinaryPrimitiveApplies .bitXor (.integer left) (.integer right)
        (.integer (Dynamic.integerBitXor left right))
  | integerBitOr (left right : Int) :
      BinaryPrimitiveApplies .bitOr (.integer left) (.integer right)
        (.integer (Dynamic.integerBitOr left right))
  | integerLess (left right : Int) :
      BinaryPrimitiveApplies .less (.integer left) (.integer right)
        (.bool (decide (left < right)))
  | integerGreater (left right : Int) :
      BinaryPrimitiveApplies .greater (.integer left) (.integer right)
        (.bool (decide (left > right)))
  | integerLessEqual (left right : Int) :
      BinaryPrimitiveApplies .lessEqual (.integer left) (.integer right)
        (.bool (decide (left ≤ right)))
  | integerGreaterEqual (left right : Int) :
      BinaryPrimitiveApplies .greaterEqual (.integer left) (.integer right)
        (.bool (decide (left ≥ right)))
  | equalTrue {left right : Value}
      (equivalent : ValueEquivalent left right) :
      BinaryPrimitiveApplies .equal left right (.bool true)
  | equalFalse {left right : Value}
      (different : ¬ ValueEquivalent left right) :
      BinaryPrimitiveApplies .equal left right (.bool false)
  | notEqualTrue {left right : Value}
      (different : ¬ ValueEquivalent left right) :
      BinaryPrimitiveApplies .notEqual left right (.bool true)
  | notEqualFalse {left right : Value}
      (equivalent : ValueEquivalent left right) :
      BinaryPrimitiveApplies .notEqual left right (.bool false)
  | logicalAnd (left right : Bool) :
      BinaryPrimitiveApplies .logicalAnd (.bool left) (.bool right)
        (.bool (left && right))
  | logicalOr (left right : Bool) :
      BinaryPrimitiveApplies .logicalOr (.bool left) (.bool right)
        (.bool (left || right))

/-- A primitive application that panics instead of giving a result. -/
inductive BinaryPrimitivePanics : Syntax.BinaryOp → Value → Value → UInt8 → Prop where
  | wordUncheckedDivide (left : Core.Word) :
      BinaryPrimitivePanics .uncheckedDivide (.word left) (.word Core.Word.zero) 0x12
  | wordUncheckedModulo (left : Core.Word) :
      BinaryPrimitivePanics .uncheckedModulo (.word left) (.word Core.Word.zero) 0x12

theorem BinaryPrimitivePanics.excludes_application {operator : Syntax.BinaryOp}
    {left right result : Value} {code : UInt8}
    (panics : BinaryPrimitivePanics operator left right code)
    (applies : BinaryPrimitiveApplies operator left right result) : False := by
  cases panics <;> cases applies <;> rename_i nonzero <;> exact nonzero rfl

theorem BinaryPrimitivePanics.functional {operator : Syntax.BinaryOp}
    {left right : Value} {first second : UInt8}
    (firstPanic : BinaryPrimitivePanics operator left right first)
    (secondPanic : BinaryPrimitivePanics operator left right second) : first = second := by
  cases firstPanic <;> cases secondPanic <;> rfl

namespace BinaryPrimitiveApplies

theorem functional
    {operator : Syntax.BinaryOp} {left right first second : Value}
    (firstApplication : BinaryPrimitiveApplies operator left right first)
    (secondApplication : BinaryPrimitiveApplies operator left right second) :
    first = second := by
  cases firstApplication <;> cases secondApplication <;> simp_all

end BinaryPrimitiveApplies

/-- The integer a word stands for in two's complement: how the signed
fixed-width integer types read their canonical words. -/
def wordSigned (word : Core.Word) : Int :=
  if word.val < 2 ^ 255 then word.val else (word.val : Int) - 2 ^ 256

/-- The integer a canonical word of a fixed-width integer type stands for. -/
def fixedValue (type : TypeSystem.FixedInteger) (word : Core.Word) : Int :=
  if type.signed then wordSigned word else word.val

/-- The exact result of checked `+`, `-` or `*`. -/
def checkedResult : Syntax.BinaryOp → Int → Int → Int
  | .add, left, right => left + right
  | .subtract, left, right => left - right
  | _, left, right => left * right

/-- The exact result of checked `/` or `%`: the quotient rounded toward zero, or
the remainder with the dividend's sign. The `/` and `%` of Lean's `Int` are
Euclidean, so these are `Int.tdiv` and `Int.tmod`. -/
def divisionResult : Syntax.BinaryOp → Int → Int → Int
  | .modulo, left, right => left.tmod right
  | _, left, right => left.tdiv right

/-- Whether an integer lies in a fixed-width integer type's range. -/
def FixedInRange (type : TypeSystem.FixedInteger) (value : Int) : Prop :=
  type.min ≤ value ∧ value ≤ type.max

instance (type : TypeSystem.FixedInteger) (value : Int) : Decidable (FixedInRange type value) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The binary operators whose meaning on a fixed-width integer type differs
from Word's on its canonical words: the orderings on the signed types and
checked `+ - * / %` on every type. -/
inductive FixedBinaryOwn (type : TypeSystem.FixedInteger) : Syntax.BinaryOp → Prop where
  | less (signed : type.signed = true) : FixedBinaryOwn type .less
  | greater (signed : type.signed = true) : FixedBinaryOwn type .greater
  | lessEqual (signed : type.signed = true) : FixedBinaryOwn type .lessEqual
  | greaterEqual (signed : type.signed = true) : FixedBinaryOwn type .greaterEqual
  | add : FixedBinaryOwn type .add
  | subtract : FixedBinaryOwn type .subtract
  | multiply : FixedBinaryOwn type .multiply
  | divide : FixedBinaryOwn type .divide
  | modulo : FixedBinaryOwn type .modulo

theorem _root_.Solcore.SourceSemantics.FixedSignedComparison.own {type : TypeSystem.FixedInteger}
    {operator : Syntax.BinaryOp} (kind : FixedSignedComparison type operator) :
    FixedBinaryOwn type operator := by
  cases kind with
  | less signed => exact .less signed
  | greater signed => exact .greater signed
  | lessEqual signed => exact .lessEqual signed
  | greaterEqual signed => exact .greaterEqual signed

theorem _root_.Solcore.SourceSemantics.FixedCheckedArithmetic.own {type : TypeSystem.FixedInteger}
    {operator : Syntax.BinaryOp} (kind : FixedCheckedArithmetic operator) :
    FixedBinaryOwn type operator := by
  cases kind <;> constructor

theorem _root_.Solcore.SourceSemantics.FixedCheckedDivision.own {type : TypeSystem.FixedInteger}
    {operator : Syntax.BinaryOp} (kind : FixedCheckedDivision operator) :
    FixedBinaryOwn type operator := by
  cases kind <;> constructor

/-- Binary operators whose meaning on a fixed-width integer type differs from
Word's on its canonical words. The orderings on the signed types compare the
integers the words stand for, and checked `+ - *`, and `/ %` by a nonzero
divisor, give the exact result, as a canonical word, when it lies in the type's
range. -/
inductive FixedBinaryApplies (type : TypeSystem.FixedInteger) :
    Syntax.BinaryOp → Value → Value → Value → Prop where
  | signedLess (signed : type.signed = true) (left right : Core.Word) :
      FixedBinaryApplies type .less (.word left) (.word right)
        (.bool (decide (wordSigned left < wordSigned right)))
  | signedGreater (signed : type.signed = true) (left right : Core.Word) :
      FixedBinaryApplies type .greater (.word left) (.word right)
        (.bool (decide (wordSigned left > wordSigned right)))
  | signedLessEqual (signed : type.signed = true) (left right : Core.Word) :
      FixedBinaryApplies type .lessEqual (.word left) (.word right)
        (.bool (decide (wordSigned left ≤ wordSigned right)))
  | signedGreaterEqual (signed : type.signed = true) (left right : Core.Word) :
      FixedBinaryApplies type .greaterEqual (.word left) (.word right)
        (.bool (decide (wordSigned left ≥ wordSigned right)))
  | checked {operator : Syntax.BinaryOp} (kind : FixedCheckedArithmetic operator) (left right : Core.Word)
      (inRange : FixedInRange type (checkedResult operator (fixedValue type left) (fixedValue type right))) :
      FixedBinaryApplies type operator (.word left) (.word right)
        (.word (Core.Word.ofIntModulo (checkedResult operator (fixedValue type left) (fixedValue type right))))
  | division {operator : Syntax.BinaryOp} (kind : FixedCheckedDivision operator) (left right : Core.Word)
      (nonzero : right ≠ Core.Word.zero)
      (inRange : FixedInRange type (divisionResult operator (fixedValue type left) (fixedValue type right))) :
      FixedBinaryApplies type operator (.word left) (.word right)
        (.word (Core.Word.ofIntModulo (divisionResult operator (fixedValue type left) (fixedValue type right))))

namespace FixedBinaryApplies

theorem functional {type : TypeSystem.FixedInteger} {operator : Syntax.BinaryOp}
    {left right first second : Value}
    (firstApplication : FixedBinaryApplies type operator left right first)
    (secondApplication : FixedBinaryApplies type operator left right second) :
    first = second := by
  cases firstApplication with
  | checked kind =>
    cases secondApplication with
    | checked => rfl
    | division other => exact (kind.not_division other).elim
    | signedLess | signedGreater | signedLessEqual | signedGreaterEqual => cases kind
  | division kind =>
    cases secondApplication with
    | division => rfl
    | checked other => exact (other.not_division kind).elim
    | signedLess | signedGreater | signedLessEqual | signedGreaterEqual => cases kind
  | signedLess =>
    cases secondApplication with
    | signedLess => rfl
    | checked kind | division kind => cases kind
  | signedGreater =>
    cases secondApplication with
    | signedGreater => rfl
    | checked kind | division kind => cases kind
  | signedLessEqual =>
    cases secondApplication with
    | signedLessEqual => rfl
    | checked kind | division kind => cases kind
  | signedGreaterEqual =>
    cases secondApplication with
    | signedGreaterEqual => rfl
    | checked kind | division kind => cases kind

/-- The operators with a fixed-width meaning are those of `FixedBinaryOwn`. -/
theorem kind {type : TypeSystem.FixedInteger} {operator : Syntax.BinaryOp}
    {left right output : Value}
    (applies : FixedBinaryApplies type operator left right output) :
    FixedBinaryOwn type operator := by
  cases applies with
  | signedLess signed => exact .less signed
  | signedGreater signed => exact .greater signed
  | signedLessEqual signed => exact .lessEqual signed
  | signedGreaterEqual signed => exact .greaterEqual signed
  | checked kind => exact kind.own
  | division kind => exact kind.own

theorem strict {type : TypeSystem.FixedInteger} {operator : Syntax.BinaryOp}
    {left right output : Value}
    (applies : FixedBinaryApplies type operator left right output) :
    StrictBinaryOperator operator := by
  have own := applies.kind
  cases own <;> constructor

end FixedBinaryApplies

/-- The static type of an expression occurrence, as the evaluation rules read
it from the typed source: the operand type that chooses an operator's meaning. -/
def operandType? (source : TypedSource) (id : ExpressionId) : Option TypeSystem.Ty :=
  (source.lookupExpression? id).map (·.type)

theorem operandType?_of_found {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {type : TypeSystem.Ty}
    (found : source.lookupExpression? id = some node) (typeEq : node.type = type) :
    operandType? source id = some type := by
  simp [operandType?, found, typeEq]

/-- Core's signed comparison is the comparison of the integers the words stand
for in two's complement. -/
theorem signedGt_eq_wordSigned (left right : Core.Word) :
    left.signedGt right = decide (wordSigned left > wordSigned right) := by
  have leftBound := left.isLt
  have rightBound := right.isLt
  simp only [Core.wordModulus] at leftBound rightBound
  unfold Core.Word.signedGt wordSigned
  by_cases leftSmall : left.val < 2 ^ 255 <;> by_cases rightSmall : right.val < 2 ^ 255 <;>
    simp only [leftSmall, rightSmall, ↓reduceIte, gt_iff_lt, Fin.lt_def, decide_eq_decide] <;>
    first
      | omega
      | (simp only [decide_eq_true_eq]; omega)
      | (simp only [decide_eq_false_iff_not, not_lt]; omega)
      | (rw [eq_comm, decide_eq_true_eq]; omega)
      | (rw [eq_comm, decide_eq_false_iff_not]; omega)

/-- Word's, Integer's or Boolean's primitive meaning of a binary operator
applies unless the operands' static type is a fixed-width integer type on which
the operator's meaning differs (`FixedBinaryApplies`). -/
def BinaryWordMeaning (operandType : Option TypeSystem.Ty) (operator : Syntax.BinaryOp) : Prop :=
  ∀ type, operandType = some (.fixed type) → ¬ FixedBinaryOwn type operator

/-- A strict binary operator applied to evaluated operands whose static type is
`operandType`: its primitive meaning, or the fixed-width meaning where that
differs. The two cases exclude each other, so the result is unique. -/
inductive BinaryValueApplies (operandType : Option TypeSystem.Ty) (operator : Syntax.BinaryOp)
    (left right output : Value) : Prop where
  | primitive (plain : BinaryWordMeaning operandType operator)
      (applies : BinaryPrimitiveApplies operator left right output)
  | fixed {type : TypeSystem.FixedInteger} (operand : operandType = some (.fixed type))
      (applies : FixedBinaryApplies type operator left right output)

namespace BinaryValueApplies

theorem functional {operandType : Option TypeSystem.Ty} {operator : Syntax.BinaryOp}
    {left right first second : Value}
    (firstApplication : BinaryValueApplies operandType operator left right first)
    (secondApplication : BinaryValueApplies operandType operator left right second) :
    first = second := by
  cases firstApplication with
  | primitive plain applies =>
    cases secondApplication with
    | primitive _ other => exact applies.functional other
    | fixed operand other => exact absurd other.kind (plain _ operand)
  | fixed operand applies =>
    cases secondApplication with
    | primitive plain _ => exact absurd applies.kind (plain _ operand)
    | fixed other otherApplies =>
      rw [operand] at other
      cases Option.some.inj other
      exact applies.functional otherApplies

/-- Word's meaning applies at any static type that is not a fixed-width
integer type. -/
theorem word_meaning_of_not_fixed {operandType : Option TypeSystem.Ty} {operator : Syntax.BinaryOp}
    (notFixed : ∀ type, operandType ≠ some (.fixed type)) : BinaryWordMeaning operandType operator :=
  fun type operand => absurd operand (notFixed type)

/-- Word's meaning applies to every operator without a fixed-width meaning. -/
theorem word_meaning_of_not_own {operandType : Option TypeSystem.Ty} {operator : Syntax.BinaryOp}
    (notOwn : ∀ type, ¬ FixedBinaryOwn type operator) : BinaryWordMeaning operandType operator :=
  fun type _ => notOwn type

end BinaryValueApplies

theorem BinaryPrimitivePanics.excludes_value {operandType : Option TypeSystem.Ty}
    {operator : Syntax.BinaryOp} {left right result : Value} {code : UInt8}
    (panics : BinaryPrimitivePanics operator left right code)
    (applies : BinaryValueApplies operandType operator left right result) : False := by
  cases applies with
  | primitive _ applies => exact panics.excludes_application applies
  | fixed _ applies =>
    have own := applies.kind
    cases panics <;> cases own

/-- Checked `+ - *` on a fixed-width integer type panic with `Panic(0x11)` when
the exact result lies outside the type's range. Checked `/ %` panic with
`Panic(0x12)` on a zero divisor, and with `Panic(0x11)` when the quotient lies
outside the range, which only `MIN / -1` on a signed type does. -/
inductive FixedBinaryPanics (type : TypeSystem.FixedInteger) :
    Syntax.BinaryOp → Value → Value → UInt8 → Prop where
  | overflow {operator : Syntax.BinaryOp} (kind : FixedCheckedArithmetic operator) (left right : Core.Word)
      (outside : ¬ FixedInRange type (checkedResult operator (fixedValue type left) (fixedValue type right))) :
      FixedBinaryPanics type operator (.word left) (.word right) 0x11
  | divisionByZero {operator : Syntax.BinaryOp} (kind : FixedCheckedDivision operator) (left : Core.Word) :
      FixedBinaryPanics type operator (.word left) (.word Core.Word.zero) 0x12
  | divisionOverflow {operator : Syntax.BinaryOp} (kind : FixedCheckedDivision operator) (left right : Core.Word)
      (nonzero : right ≠ Core.Word.zero)
      (outside : ¬ FixedInRange type (divisionResult operator (fixedValue type left) (fixedValue type right))) :
      FixedBinaryPanics type operator (.word left) (.word right) 0x11

theorem FixedBinaryPanics.excludes_application {type : TypeSystem.FixedInteger}
    {operator : Syntax.BinaryOp} {left right result : Value} {code : UInt8}
    (panics : FixedBinaryPanics type operator left right code)
    (applies : FixedBinaryApplies type operator left right result) : False := by
  cases panics with
  | overflow kind left right outside =>
    cases applies
    all_goals first
      | exact outside (by assumption)
      | exact kind.not_division (by assumption)
      | cases kind
  | divisionByZero kind left =>
    cases applies
    all_goals first
      | exact absurd rfl (by assumption)
      | exact FixedCheckedArithmetic.not_division (by assumption) kind
      | cases kind
  | divisionOverflow kind left right nonzero outside =>
    cases applies
    all_goals first
      | exact outside (by assumption)
      | exact FixedCheckedArithmetic.not_division (by assumption) kind
      | cases kind

/-- A strict binary operator panicking on evaluated operands whose static type
is `operandType`: an unchecked `/` or `%` by zero, or at a fixed-width integer
type checked arithmetic out of its range, or a checked `/` or `%` by zero or out
of its range. -/
inductive BinaryValuePanics (operandType : Option TypeSystem.Ty) (operator : Syntax.BinaryOp)
    (left right : Value) (code : UInt8) : Prop where
  | primitive (panics : BinaryPrimitivePanics operator left right code)
  | fixed {type : TypeSystem.FixedInteger} (operand : operandType = some (.fixed type))
      (panics : FixedBinaryPanics type operator left right code)

namespace BinaryValuePanics

theorem excludes_value {operandType : Option TypeSystem.Ty}
    {operator : Syntax.BinaryOp} {left right result : Value} {code : UInt8}
    (panics : BinaryValuePanics operandType operator left right code)
    (applies : BinaryValueApplies operandType operator left right result) : False := by
  cases panics with
  | primitive panics => exact panics.excludes_value applies
  | fixed operand panics =>
    cases applies with
    | primitive plain _ =>
      cases panics with
      | overflow kind => exact plain _ operand kind.own
      | divisionByZero kind => exact plain _ operand kind.own
      | divisionOverflow kind => exact plain _ operand kind.own
    | fixed other applies =>
      rw [operand] at other
      cases Option.some.inj other
      exact panics.excludes_application applies

theorem functional {operandType : Option TypeSystem.Ty}
    {operator : Syntax.BinaryOp} {left right : Value} {first second : UInt8}
    (firstPanic : BinaryValuePanics operandType operator left right first)
    (secondPanic : BinaryValuePanics operandType operator left right second) : first = second := by
  cases firstPanic with
  | primitive firstPanic =>
    cases secondPanic with
    | primitive secondPanic => exact firstPanic.functional secondPanic
    | fixed _ secondPanic =>
      cases secondPanic with
      | overflow kind | divisionByZero kind | divisionOverflow kind => cases kind <;> cases firstPanic
  | fixed _ firstPanic =>
    cases secondPanic with
    | primitive secondPanic =>
      cases firstPanic with
      | overflow kind | divisionByZero kind | divisionOverflow kind => cases kind <;> cases secondPanic
    | fixed _ secondPanic =>
      cases firstPanic <;> cases secondPanic
      all_goals first
        | rfl
        | exact absurd rfl (by assumption)
        | exact (FixedCheckedArithmetic.not_division (by assumption) (by assumption)).elim

end BinaryValuePanics

/-- The word that keeps the low `N` bits of a word, for a fixed-width integer
type of `N` bits. -/
def fixedLowMask (type : TypeSystem.FixedInteger) : Core.Word :=
  Core.Word.ofNatModulo (2 ^ type.width.bits - 1)

/-- Unary operators whose meaning on a fixed-width integer type differs from
Word's on its canonical words. `~` on `uint8` … `uint128` keeps the low `N`
bits of Word's `~`. -/
inductive FixedUnaryApplies (type : TypeSystem.FixedInteger) :
    Syntax.UnaryOp → Value → Value → Prop where
  | narrowBitNot (unsigned : type.signed = false) (narrow : type.width ≠ .w256)
      (operand : Core.Word) :
      FixedUnaryApplies type .bitNot (.word operand)
        (.word (operand.bitNot.bitAnd (fixedLowMask type)))

namespace FixedUnaryApplies

theorem functional {type : TypeSystem.FixedInteger} {operator : Syntax.UnaryOp}
    {input first second : Value}
    (firstApplication : FixedUnaryApplies type operator input first)
    (secondApplication : FixedUnaryApplies type operator input second) :
    first = second := by
  cases firstApplication <;> cases secondApplication <;> rfl

/-- The operator with a fixed-width meaning is `~` on the narrower unsigned
types. -/
theorem kind {type : TypeSystem.FixedInteger} {operator : Syntax.UnaryOp}
    {input output : Value}
    (applies : FixedUnaryApplies type operator input output) :
    FixedNarrowBitNot type operator := by
  cases applies with
  | narrowBitNot unsigned narrow => exact .bitNot unsigned narrow

end FixedUnaryApplies

/-- Word's, Integer's or Boolean's primitive meaning of a unary operator applies
unless the operand's static type is a fixed-width integer type on which the
operator's meaning differs (`FixedUnaryApplies`). -/
def UnaryWordMeaning (operandType : Option TypeSystem.Ty) (operator : Syntax.UnaryOp) : Prop :=
  ∀ type, operandType = some (.fixed type) → ¬ FixedNarrowBitNot type operator

/-- A unary operator applied to an evaluated operand whose static type is
`operandType`: its primitive meaning, or the fixed-width meaning where that
differs. The two cases exclude each other, so the result is unique. -/
inductive UnaryValueApplies (operandType : Option TypeSystem.Ty) (operator : Syntax.UnaryOp)
    (input output : Value) : Prop where
  | primitive (plain : UnaryWordMeaning operandType operator)
      (applies : UnaryPrimitiveApplies operator input output)
  | fixed {type : TypeSystem.FixedInteger} (operand : operandType = some (.fixed type))
      (applies : FixedUnaryApplies type operator input output)

namespace UnaryValueApplies

theorem functional {operandType : Option TypeSystem.Ty} {operator : Syntax.UnaryOp}
    {input first second : Value}
    (firstApplication : UnaryValueApplies operandType operator input first)
    (secondApplication : UnaryValueApplies operandType operator input second) :
    first = second := by
  cases firstApplication with
  | primitive plain applies =>
    cases secondApplication with
    | primitive _ other => exact applies.functional other
    | fixed operand other => exact absurd other.kind (plain _ operand)
  | fixed operand applies =>
    cases secondApplication with
    | primitive plain _ => exact absurd applies.kind (plain _ operand)
    | fixed other otherApplies =>
      rw [operand] at other
      cases Option.some.inj other
      exact applies.functional otherApplies

/-- Word's meaning applies at any static type that is not a fixed-width
integer type. -/
theorem word_meaning_of_not_fixed {operandType : Option TypeSystem.Ty} {operator : Syntax.UnaryOp}
    (notFixed : ∀ type, operandType ≠ some (.fixed type)) : UnaryWordMeaning operandType operator :=
  fun type operand => absurd operand (notFixed type)

/-- Word's meaning applies to `!`. -/
theorem word_meaning_logicalNot (operandType : Option TypeSystem.Ty) :
    UnaryWordMeaning operandType .logicalNot :=
  fun _ _ kind => by cases kind

end UnaryValueApplies

/-- Application of one compiler-provided source function. -/
inductive BuiltinApplies : BuiltinFunctionId → List Value → Value → Prop where
  | integerSub (left right : Int) :
      BuiltinApplies .integerSub [.integer left, .integer right]
        (.integer (left - right))
  | wordFromInteger (value : Int) :
      BuiltinApplies .wordFromInteger [.integer value]
        (.word (Core.Word.ofIntModulo value))
  | integerAdd (left right : Int) :
      BuiltinApplies .integerAdd [.integer left, .integer right]
        (.integer (left + right))
  | integerEq (left right : Int) :
      BuiltinApplies .integerEq [.integer left, .integer right]
        (.bool (decide (left = right)))
  | integerLt (left right : Int) :
      BuiltinApplies .integerLt [.integer left, .integer right]
        (.bool (decide (left < right)))
  | integerMul (left right : Int) :
      BuiltinApplies .integerMul [.integer left, .integer right]
        (.integer (left * right))
  | wordToInteger (value : Core.Word) :
      BuiltinApplies .wordToInteger [.word value]
        (.integer (Int.ofNat value.val))

namespace BuiltinApplies

theorem functional
    {function : BuiltinFunctionId} {arguments : List Value}
    {left right : Value}
    (leftApplication : BuiltinApplies function arguments left)
    (rightApplication : BuiltinApplies function arguments right) :
    left = right := by
  cases leftApplication <;> cases rightApplication <;> rfl

theorem argument_count
    {function : BuiltinFunctionId} {arguments : List Value} {result : Value}
    (application : BuiltinApplies function arguments result) :
    arguments.length = function.parameterTypes.length := by
  cases application <;> rfl

end BuiltinApplies

/-- Runtime meaning of one supported coercion edge.  The edge's evidence is
checked separately by `CoercionApplies`, keeping primitive conversion and
trait justification visibly distinct. -/
inductive PrimitiveCoercionApplies : CoercionStep → Value → Value → Prop where
  | identity {step : CoercionStep} {value : Value}
      (sameType : step.source = step.target) :
      PrimitiveCoercionApplies step value value
  | integerToWord {step : CoercionStep} (value : Int)
      (source_eq : step.source = .integer)
      (target_eq : step.target = .word) :
      PrimitiveCoercionApplies step (.integer value)
        (.word (Core.Word.ofIntModulo value))
  | wordToInteger {step : CoercionStep} (value : Core.Word)
      (source_eq : step.source = .word)
      (target_eq : step.target = .integer) :
      PrimitiveCoercionApplies step (.word value)
        (.integer (Int.ofNat value.val))

/-- A coercion edge may execute only with its exact retained trait evidence. -/
inductive CoercionApplies (context : Context) :
    CoercionStep → Value → Value → Prop where
  | intro {step : CoercionStep} {input output : Value}
      (valid : CoercionStepValid context step)
      (primitive : PrimitiveCoercionApplies step input output) :
      CoercionApplies context step input output

/-- Left-to-right application of a retained coercion path. -/
inductive CoercionPathApplies (context : Context) :
    List CoercionStep → Value → Value → Prop where
  | nil (value : Value) : CoercionPathApplies context [] value value
  | cons {step : CoercionStep} {steps : List CoercionStep}
      {input middle output : Value}
      (head : CoercionApplies context step input middle)
      (tail : CoercionPathApplies context steps middle output) :
      CoercionPathApplies context (step :: steps) input output

namespace PrimitiveCoercionApplies

theorem functional {step : CoercionStep} {input left right : Value}
    (leftApplication : PrimitiveCoercionApplies step input left)
    (rightApplication : PrimitiveCoercionApplies step input right) :
    left = right := by
  cases leftApplication <;> cases rightApplication <;>
    simp_all [TypeSystem.Ty.integer, TypeSystem.Ty.word]

end PrimitiveCoercionApplies

namespace CoercionApplies

theorem functional {context : Context} {step : CoercionStep}
    {input left right : Value}
    (leftApplication : CoercionApplies context step input left)
    (rightApplication : CoercionApplies context step input right) :
    left = right := by
  cases leftApplication with
  | intro _ leftPrimitive =>
      cases rightApplication with
      | intro _ rightPrimitive => exact leftPrimitive.functional rightPrimitive

end CoercionApplies

namespace CoercionPathApplies

theorem functional {context : Context} {steps : List CoercionStep}
    {input left right : Value}
    (leftApplication : CoercionPathApplies context steps input left)
    (rightApplication : CoercionPathApplies context steps input right) :
    left = right := by
  induction leftApplication generalizing right with
  | nil =>
      cases rightApplication
      rfl
  | cons leftHead _ inductionHypothesis =>
      cases rightApplication with
      | cons rightHead rightTail =>
          have middle_eq := leftHead.functional rightHead
          cases middle_eq
          exact inductionHypothesis rightTail

end CoercionPathApplies

/-- Every entry has a key different from the queried key. -/
inductive MappingAbsent (key : Value) : List (Value × Value) → Prop where
  | nil : MappingAbsent key []
  | cons {storedKey storedValue entries}
      (different : ¬ ValueEquivalent key storedKey)
      (rest : MappingAbsent key entries) :
      MappingAbsent key ((storedKey, storedValue) :: entries)

/-- First-match lookup in an ordered mapping. -/
inductive MappingLookup (key : Value) :
    List (Value × Value) → Value → Prop where
  | head {storedKey value entries}
      (equivalent : ValueEquivalent key storedKey) :
      MappingLookup key ((storedKey, value) :: entries) value
  | tail {storedKey storedValue entries value}
      (different : ¬ ValueEquivalent key storedKey)
      (rest : MappingLookup key entries value) :
      MappingLookup key ((storedKey, storedValue) :: entries) value

/-- Replace the first equivalent key, retaining every other entry and its
relative position. -/
inductive MappingUpdate (key value : Value) :
    List (Value × Value) → List (Value × Value) → Prop where
  | head {storedKey storedValue entries}
      (equivalent : ValueEquivalent key storedKey) :
      MappingUpdate key value ((storedKey, storedValue) :: entries)
        ((key, value) :: entries)
  | tail {storedKey storedValue entries updated}
      (different : ¬ ValueEquivalent key storedKey)
      (rest : MappingUpdate key value entries updated) :
      MappingUpdate key value ((storedKey, storedValue) :: entries)
        ((storedKey, storedValue) :: updated)

/-- Ordered insertion updates the first equivalent entry when present and
otherwise appends one fresh entry. -/
inductive MappingInsert (key value : Value) :
    List (Value × Value) → List (Value × Value) → Prop where
  | update {entries updated}
      (replacement : MappingUpdate key value entries updated) :
      MappingInsert key value entries updated
  | append {entries}
      (absent : MappingAbsent key entries) :
      MappingInsert key value entries (entries ++ [(key, value)])

namespace MappingAbsent

theorem excludes_lookup {key value : Value} {entries : List (Value × Value)}
    (absent : MappingAbsent key entries) :
    ¬ MappingLookup key entries value := by
  intro lookup
  induction absent with
  | nil => cases lookup
  | cons different _ inductionHypothesis =>
      cases lookup with
      | head equivalent => exact different equivalent
      | tail _ rest => exact inductionHypothesis rest

end MappingAbsent

namespace MappingLookup

theorem functional {key left right : Value}
    {entries : List (Value × Value)}
    (leftLookup : MappingLookup key entries left)
    (rightLookup : MappingLookup key entries right) : left = right := by
  induction leftLookup with
  | head equivalent =>
      cases rightLookup with
      | head => rfl
      | tail different _ => exact (different equivalent).elim
  | tail different _ inductionHypothesis =>
      cases rightLookup with
      | head equivalent => exact (different equivalent).elim
      | tail _ rest => exact inductionHypothesis rest

theorem append {key value : Value} {entries suffix : List (Value × Value)}
    (lookup : MappingLookup key entries value) :
    MappingLookup key (entries ++ suffix) value := by
  induction lookup with
  | head equivalent => exact .head equivalent
  | tail different _ inductionHypothesis =>
      exact .tail different inductionHypothesis

end MappingLookup

namespace MappingUpdate

theorem functional {key value : Value} {entries left right : List (Value × Value)}
    (leftUpdate : MappingUpdate key value entries left)
    (rightUpdate : MappingUpdate key value entries right) : left = right := by
  induction leftUpdate generalizing right with
  | head equivalent =>
      cases rightUpdate with
      | head => rfl
      | tail different _ => exact (different equivalent).elim
  | tail different _ inductionHypothesis =>
      cases rightUpdate with
      | head equivalent => exact (different equivalent).elim
      | tail _ rest => rw [inductionHypothesis rest]

theorem length_eq {key value : Value} {entries updated : List (Value × Value)}
    (replacement : MappingUpdate key value entries updated) :
    updated.length = entries.length := by
  induction replacement with
  | head => rfl
  | tail _ _ inductionHypothesis => simp [inductionHypothesis]

theorem lookup_self {key value : Value}
    {entries updated : List (Value × Value)}
    (replacement : MappingUpdate key value entries updated) :
    MappingLookup key updated value := by
  induction replacement with
  | head equivalent => exact .head (ValueEquivalent.refl equivalent.comparable_left)
  | tail different _ inductionHypothesis => exact .tail different inductionHypothesis

theorem has_previous {key value : Value}
    {entries updated : List (Value × Value)}
    (replacement : MappingUpdate key value entries updated) :
    ∃ previous, MappingLookup key entries previous := by
  induction replacement with
  | head equivalent => exact ⟨_, .head equivalent⟩
  | tail different _ inductionHypothesis =>
      rcases inductionHypothesis with ⟨previous, lookup⟩
      exact ⟨previous, .tail different lookup⟩

theorem preserves_other {key value other previous : Value}
    {entries updated : List (Value × Value)}
    (replacement : MappingUpdate key value entries updated)
    (different : ¬ ValueEquivalent other key)
    (lookup : MappingLookup other entries previous) :
    MappingLookup other updated previous := by
  induction replacement generalizing previous with
  | head keyEquivalent =>
      cases lookup with
      | head otherEquivalent =>
          exact (different
            (otherEquivalent.transitive keyEquivalent.symmetric)).elim
      | tail _ rest => exact .tail different rest
  | tail _ _ inductionHypothesis =>
      cases lookup with
      | head equivalent => exact .head equivalent
      | tail otherDifferent rest =>
          exact .tail otherDifferent (inductionHypothesis rest)

end MappingUpdate

namespace MappingInsert

private theorem lookup_appended
    {key value : Value} {entries : List (Value × Value)}
    (comparable : ValueComparable key)
    (absent : MappingAbsent key entries) :
    MappingLookup key (entries ++ [(key, value)]) value := by
  induction absent with
  | nil => exact .head (ValueEquivalent.refl comparable)
  | cons different _ inductionHypothesis =>
      exact .tail different inductionHypothesis

theorem functional {key value : Value}
    {entries left right : List (Value × Value)}
    (leftInsert : MappingInsert key value entries left)
    (rightInsert : MappingInsert key value entries right) : left = right := by
  cases leftInsert with
  | update leftUpdate =>
      cases rightInsert with
      | update rightUpdate => exact leftUpdate.functional rightUpdate
      | append absent =>
          rcases leftUpdate.has_previous with ⟨previous, lookup⟩
          exact (absent.excludes_lookup lookup).elim
  | append absent =>
      cases rightInsert with
      | update rightUpdate =>
          rcases rightUpdate.has_previous with ⟨previous, lookup⟩
          exact (absent.excludes_lookup lookup).elim
      | append => rfl

theorem lookup_self {key value : Value}
    {entries updated : List (Value × Value)}
    (comparable : ValueComparable key)
    (insertion : MappingInsert key value entries updated) :
    MappingLookup key updated value := by
  cases insertion with
  | update replacement => exact replacement.lookup_self
  | append absent => exact lookup_appended comparable absent

theorem length_eq_or_succ {key value : Value}
    {entries updated : List (Value × Value)}
    (insertion : MappingInsert key value entries updated) :
    updated.length = entries.length ∨
      updated.length = entries.length + 1 := by
  cases insertion with
  | update replacement => exact .inl replacement.length_eq
  | append => simp

theorem member_origin_or_inserted {key value : Value}
    {entries updated : List (Value × Value)} {selected : Value × Value}
    (insertion : MappingInsert key value entries updated)
    (member : selected ∈ updated) :
    selected = (key, value) ∨ selected ∈ entries := by
  cases insertion with
  | update replacement =>
      induction replacement with
      | head =>
          simp only [List.mem_cons] at member ⊢
          rcases member with fresh | old
          · exact .inl fresh
          · exact .inr (.inr old)
      | tail _ _ inductionHypothesis =>
          simp only [List.mem_cons] at member ⊢
          rcases member with old | tail
          · exact .inr (.inl old)
          · rcases inductionHypothesis tail with fresh | old
            · exact .inl fresh
            · exact .inr (.inr old)
  | append =>
      rw [List.mem_append] at member
      rcases member with old | fresh
      · exact .inr old
      · simp only [List.mem_singleton] at fresh
        exact .inl fresh

theorem preserves_other {key value other previous : Value}
    {entries updated : List (Value × Value)}
    (insertion : MappingInsert key value entries updated)
    (different : ¬ ValueEquivalent other key)
    (lookup : MappingLookup other entries previous) :
    MappingLookup other updated previous := by
  cases insertion with
  | update replacement => exact replacement.preserves_other different lookup
  | append => exact lookup.append

end MappingInsert

end Solcore.SourceSemantics.Dynamic
end

section
-- leanmerge: from Solcore.SourceSemantics.Dynamic.Pattern
/-!
Declarative source-pattern dynamics.

The retained pattern representation is a self-delimiting prefix program.  The
relations in this module consume that program directly: constructor and tuple
roots consume all of their children, successful bindings are concatenated in
source order, and a failed pattern still has an exact unconsumed suffix.  No
executable pattern matcher is used as a premise.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference

/-- The source product encoding of a value sequence.  This is the dynamic
counterpart of `Ty.productMany`: zero values use Unit, one value is left
unwrapped, and two or more values form a right-associated product. -/
inductive ValuesPack : List Value → Value → Prop where
  | nil : ValuesPack [] .unit
  | singleton (value : Value) : ValuesPack [value] value
  | cons
      {first second : Value} {rest : List Value} {packed : Value}
      (tail : ValuesPack (second :: rest) packed) :
      ValuesPack (first :: second :: rest) (.product first packed)

namespace ValuesPack

/-- The product encoding determines its packed value. -/
theorem functional {values : List Value} {left right : Value}
    (leftPack : ValuesPack values left) (rightPack : ValuesPack values right) :
    left = right := by
  induction leftPack generalizing right with
  | nil => cases rightPack; rfl
  | singleton value => cases rightPack; rfl
  | cons tail inductionHypothesis =>
      cases rightPack with
      | cons otherTail => rw [inductionHypothesis otherTail]

/-- At a fixed arity, the packed value also determines the source-ordered
value sequence. -/
theorem injective_of_length_eq
    {left right : List Value} {packed : Value}
    (leftPack : ValuesPack left packed) (rightPack : ValuesPack right packed)
    (sameLength : left.length = right.length) : left = right := by
  induction leftPack generalizing right with
  | nil =>
      cases rightPack <;> simp_all
  | singleton value =>
      cases rightPack <;> simp_all
  | cons tail inductionHypothesis =>
      cases rightPack with
      | singleton => simp at sameLength
      | cons otherTail =>
          have tailLength := Nat.succ.inj sameLength
          rw [inductionHypothesis otherTail tailLength]

end ValuesPack

/-- Runtime-relevant equality of constructor instantiations.  Association-list
order in a rigid-parameter substitution is proof metadata; constructor
selection and all instantiated payload/result types are the observable
content used by matching. -/
structure ConstructorInstantiationsAgree
    (left right : DataConstructorInstantiation) : Prop where
  constructor_eq : left.constructor = right.constructor
  payload_types_eq : left.payloadTypes = right.payloadTypes
  result_type_eq : left.resultType = right.resultType

namespace ConstructorInstantiationsAgree

theorem refl (instantiation : DataConstructorInstantiation) :
    ConstructorInstantiationsAgree instantiation instantiation :=
  ⟨rfl, rfl, rfl⟩

theorem symm
    {left right : DataConstructorInstantiation}
    (agree : ConstructorInstantiationsAgree left right) :
    ConstructorInstantiationsAgree right left :=
  ⟨agree.constructor_eq.symm, agree.payload_types_eq.symm,
    agree.result_type_eq.symm⟩

end ConstructorInstantiationsAgree

mutual

  /-- Consume one self-delimiting instruction without inspecting a value. -/
  inductive PatternInstructionSkips :
      List MatchPatternInstruction → List MatchPatternInstruction → Prop where
    | wildcard {rest} :
        PatternInstructionSkips (.wildcard :: rest) rest
    | integerLiteral {rest source resolution} :
        PatternInstructionSkips (.integerLiteral source resolution :: rest) rest
    | binder {rest binder} :
        PatternInstructionSkips (.binder binder :: rest) rest
    | constructor {instructions rest instantiation argumentCount}
        (children : PatternInstructionsSkip instructions argumentCount rest) :
        PatternInstructionSkips
          (.constructor instantiation argumentCount :: instructions) rest
    | tuple {instructions rest elementCount}
        (children : PatternInstructionsSkip instructions elementCount rest) :
        PatternInstructionSkips (.tuple elementCount :: instructions) rest

  /-- Consume exactly `count` consecutive self-delimiting instructions. -/
  inductive PatternInstructionsSkip :
      List MatchPatternInstruction → Nat →
        List MatchPatternInstruction → Prop where
    | zero {instructions} : PatternInstructionsSkip instructions 0 instructions
    | succ {instructions afterHead rest count}
        (head : PatternInstructionSkips instructions afterHead)
        (tail : PatternInstructionsSkip afterHead count rest) :
        PatternInstructionsSkip instructions (count + 1) rest

end

mutual

  /-- Match one value against one prefix instruction and expose the exact
  source-ordered bindings and unconsumed suffix. -/
  inductive PatternInstructionMatches (context : Context) :
      Value → List MatchPatternInstruction →
        List (TypedBinder × Value) → List MatchPatternInstruction → Prop where
    | wildcard {value rest} :
        PatternInstructionMatches context value (.wildcard :: rest) [] rest
    | integerLiteral
        {source resolution value rest}
        (constructs :
          ResolvedIntegerLiteralConstructs context source resolution value) :
        PatternInstructionMatches context value
          (.integerLiteral source resolution :: rest) [] rest
    | binder {value binder rest} :
        PatternInstructionMatches context value (.binder binder :: rest)
          [(binder, value)] rest
    | constructor
        {actual expected : DataConstructorInstantiation}
        {arguments : List Value}
        {instructions rest : List MatchPatternInstruction}
        {argumentCount : Nat} {bindings : List (TypedBinder × Value)}
        (instantiations_agree : ConstructorInstantiationsAgree actual expected)
        (arity : arguments.length = argumentCount)
        (children : PatternInstructionsMatch context arguments instructions
          bindings rest) :
        PatternInstructionMatches context (.constructed actual arguments)
          (.constructor expected argumentCount :: instructions) bindings rest
    | tuple
        {value : Value} {elements : List Value}
        {instructions rest : List MatchPatternInstruction}
        {elementCount : Nat} {bindings : List (TypedBinder × Value)}
        (packed : ValuesPack elements value)
        (arity : elements.length = elementCount)
        (children : PatternInstructionsMatch context elements instructions
          bindings rest) :
        PatternInstructionMatches context value
          (.tuple elementCount :: instructions) bindings rest

  /-- Match a source-ordered value vector against the same number of prefix
  pattern trees.  Appending head bindings before tail bindings fixes binding
  order to source order. -/
  inductive PatternInstructionsMatch (context : Context) :
      List Value → List MatchPatternInstruction →
        List (TypedBinder × Value) → List MatchPatternInstruction → Prop where
    | nil {instructions} :
        PatternInstructionsMatch context [] instructions [] instructions
    | cons
        {value values instructions afterHead rest headBindings tailBindings}
        (head : PatternInstructionMatches context value instructions
          headBindings afterHead)
        (tail : PatternInstructionsMatch context values afterHead
          tailBindings rest) :
        PatternInstructionsMatch context (value :: values) instructions
          (headBindings ++ tailBindings) rest

end

/-- One instruction is a semantic non-match when it has a well-defined full
prefix extent and no binding sequence can match over that same extent. -/
structure PatternInstructionDoesNotMatch (context : Context) (value : Value)
    (instructions rest : List MatchPatternInstruction) : Prop where
  consumes : PatternInstructionSkips instructions rest
  mismatch : ∀ bindings,
    ¬ PatternInstructionMatches context value instructions bindings rest

/-- A value vector is a semantic non-match when its corresponding sequence of
pattern trees is well-delimited and admits no successful binding sequence. -/
structure PatternInstructionsDoNotMatch (context : Context)
    (values : List Value) (instructions rest : List MatchPatternInstruction) : Prop where
  consumes : PatternInstructionsSkip instructions values.length rest
  mismatch : ∀ bindings,
    ¬ PatternInstructionsMatch context values instructions bindings rest

/-- Match a complete root resolution, including exact exhaustion of its
flattened child stream. -/
def PatternResolutionMatches (context : Context)
    (resolution : MatchPatternResolution) (rootArity : Nat)
    (value : Value) (bindings : List (TypedBinder × Value)) : Prop :=
  PatternInstructionMatches context value
    (matchPatternResolutionInstructions resolution rootArity) bindings []

/-- A complete, well-delimited root resolution fails to match. -/
def PatternResolutionDoesNotMatch (context : Context)
    (resolution : MatchPatternResolution) (rootArity : Nat)
    (value : Value) : Prop :=
  PatternInstructionDoesNotMatch context value
    (matchPatternResolutionInstructions resolution rootArity) []

/-- Dynamic success for a retained typed source pattern.  The source carrier
fixes the root arity used to reconstitute the prefix program. -/
inductive PatternMatches (context : Context) :
    TypedMatchPattern → Value → List (TypedBinder × Value) → Prop where
  | intro
      {pattern value bindings rootArity}
      (source_represents : MatchPatternSourceRepresents context pattern.source
        pattern.resolution rootArity)
      (matched : PatternResolutionMatches context pattern.resolution rootArity
        value bindings) :
      PatternMatches context pattern value bindings

/-- Dynamic non-match for a retained typed source pattern. -/
inductive PatternDoesNotMatch (context : Context) :
    TypedMatchPattern → Value → Prop where
  | intro
      {pattern value rootArity}
      (source_represents : MatchPatternSourceRepresents context pattern.source
        pattern.resolution rootArity)
      (does_not_match : PatternResolutionDoesNotMatch context pattern.resolution
        rootArity value) :
      PatternDoesNotMatch context pattern value

namespace PatternInstructionDoesNotMatch

/-- A declared non-match excludes a successful match over the same prefix. -/
theorem excludes
    {context : Context} {value : Value}
    {instructions rest : List MatchPatternInstruction}
    (failure : PatternInstructionDoesNotMatch context value instructions rest)
    {bindings : List (TypedBinder × Value)} :
    ¬ PatternInstructionMatches context value instructions bindings rest :=
  failure.mismatch bindings

end PatternInstructionDoesNotMatch

namespace PatternInstructionsDoNotMatch

theorem excludes
    {context : Context} {values : List Value}
    {instructions rest : List MatchPatternInstruction}
    (failure : PatternInstructionsDoNotMatch context values instructions rest)
    {bindings : List (TypedBinder × Value)} :
    ¬ PatternInstructionsMatch context values instructions bindings rest :=
  failure.mismatch bindings

end PatternInstructionsDoNotMatch

/-- Result of first-match case selection before a branch body is executed. -/
inductive MatchCaseSelection where
  | arm (body : List StatementId) (bindings : List (TypedBinder × Value))
  | default (body : List StatementId)
  | noBranch
  deriving Repr

/-- Select the first matching arm.  A default is considered only after every
ordered arm has an explicit semantic non-match derivation. -/
inductive MatchCasesSelect (context : Context) (value : Value) :
    List TypedMatchCase → Option (List StatementId) → MatchCaseSelection → Prop where
  | head
      {arm rest fallback bindings}
      (matched : PatternMatches context arm.pattern value bindings) :
      MatchCasesSelect context value (arm :: rest) fallback
        (.arm arm.body bindings)
  | tail
      {arm rest fallback selection}
      (does_not_match : PatternDoesNotMatch context arm.pattern value)
      (selected : MatchCasesSelect context value rest fallback selection) :
      MatchCasesSelect context value (arm :: rest) fallback selection
  | default {body} :
      MatchCasesSelect context value [] (some body) (.default body)
  | noBranch :
      MatchCasesSelect context value [] none .noBranch

end Solcore.SourceSemantics.Dynamic
end
