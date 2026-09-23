import Solcore.SourceSemantics.Dynamic.Value
import Solcore.SourceSemantics.Literals
import Solcore.SourceSemantics.Operators
import Solcore.SourceSemantics.Coercions
import Solcore.Frontend.WordLiteralProperties

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
  | bitAnd : StrictBinaryOperator .bitAnd
  | bitXor : StrictBinaryOperator .bitXor
  | bitOr : StrictBinaryOperator .bitOr
  | less : StrictBinaryOperator .less
  | greater : StrictBinaryOperator .greater
  | lessEqual : StrictBinaryOperator .lessEqual
  | greaterEqual : StrictBinaryOperator .greaterEqual
  | equal : StrictBinaryOperator .equal
  | notEqual : StrictBinaryOperator .notEqual

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
  | orTrue =>
      cases evaluates with
      | strict classification => cases classification

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

namespace BinaryPrimitiveApplies

theorem functional
    {operator : Syntax.BinaryOp} {left right first second : Value}
    (firstApplication : BinaryPrimitiveApplies operator left right first)
    (secondApplication : BinaryPrimitiveApplies operator left right second) :
    first = second := by
  cases firstApplication <;> cases secondApplication <;> simp_all

end BinaryPrimitiveApplies

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
