import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Frontend.LocalExpressionCost
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.WordLiteralProperties
import Solcore.Resolved.LocalScopeProperties

/-! Successful direct execution constructs the independent raw cost relation.
Only selected children are used; opaque selected values remain unrestricted. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateLocalExpressionWithCost?_sound {table : LocalNameTable}
    {environment : Resolved.Environment} {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (accepted : evaluateLocalExpressionWithCost? table environment source = some (value, cost))
    (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table environment store source value store cost := by
  cases source with
  | mk span payload =>
      cases payload <;> try simp only [evaluateLocalExpressionWithCost?, reduceCtorEq] at accepted
      case identifier name =>
        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at accepted
        obtain ⟨id, named, actual, found, rfl, rfl⟩ := accepted
        exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)
      case literal literal =>
        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at accepted
        obtain ⟨word, meaning, rfl, rfl⟩ := accepted
        exact .wordLiteral (interpretWordLiteral?_sound meaning)
      case group inner => exact .group (evaluateLocalExpressionWithCost?_sound accepted store)
      case tuple elements =>
        cases elements with
        | mk tupleSpan children =>
          cases children with
          | nil =>
              simp only [evaluateLocalExpressionWithCost?, Option.some.injEq, Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              exact .unit
          | cons left remaining =>
            cases remaining with
            | nil => simp [evaluateLocalExpressionWithCost?] at accepted
            | cons right tail =>
              cases tail with
              | cons _ _ => simp [evaluateLocalExpressionWithCost?] at accepted
              | nil =>
                simp only [evaluateLocalExpressionWithCost?, bind, Option.bind_eq_some_iff,
                  pure, Option.some.injEq, Prod.mk.injEq] at accepted
                obtain ⟨⟨leftValue, leftCost⟩, leftResult, ⟨rightValue, rightCost⟩, rightResult, rfl, rfl⟩ := accepted
                exact .pair (evaluateLocalExpressionWithCost?_sound leftResult store)
                  (evaluateLocalExpressionWithCost?_sound rightResult store)
      case unary operator operand =>
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue <;>
          simp only [evaluateLocalExpressionWithCost?, bind, Option.bind_eq_some_iff] at accepted
        all_goals
          obtain ⟨⟨actual, childCost⟩, child, result⟩ := accepted
          cases actual <;> simp only [pure, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at result
          obtain ⟨rfl, rfl⟩ := result
          first
          | exact .logicalNot (evaluateLocalExpressionWithCost?_sound child store)
          | exact .bitNot (evaluateLocalExpressionWithCost?_sound child store)
      case binary left operator right =>
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue
        case logicalAnd =>
          simp only [evaluateLocalExpressionWithCost?, bind, Option.bind_eq_some_iff] at accepted
          obtain ⟨⟨actual, leftCost⟩, leftResult, result⟩ := accepted
          cases actual <;> simp only [reduceCtorEq] at result
          rename_i choice
          cases choice
          · simp only [Bool.false_eq_true, ↓reduceIte, pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨rfl, rfl⟩ := result
            exact .andFalse (evaluateLocalExpressionWithCost?_sound leftResult store)
          · simp only [↓reduceIte, Option.bind_eq_some_iff] at result
            obtain ⟨⟨actual, rightCost⟩, rightResult, result⟩ := result
            simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨rfl, rfl⟩ := result
            exact .andTrue (evaluateLocalExpressionWithCost?_sound leftResult store)
              (evaluateLocalExpressionWithCost?_sound rightResult store)
        case logicalOr =>
          simp only [evaluateLocalExpressionWithCost?, bind, Option.bind_eq_some_iff] at accepted
          obtain ⟨⟨actual, leftCost⟩, leftResult, result⟩ := accepted
          cases actual <;> simp only [reduceCtorEq] at result
          rename_i choice
          cases choice
          · simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at result
            obtain ⟨⟨actual, rightCost⟩, rightResult, result⟩ := result
            simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨rfl, rfl⟩ := result
            exact .orFalse (evaluateLocalExpressionWithCost?_sound leftResult store)
              (evaluateLocalExpressionWithCost?_sound rightResult store)
          · simp only [↓reduceIte, pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨rfl, rfl⟩ := result
            exact .orTrue (evaluateLocalExpressionWithCost?_sound leftResult store)
        all_goals
          simp only [evaluateLocalExpressionWithCost?, bind, Option.bind_eq_some_iff] at accepted
          obtain ⟨⟨actualLeft, leftCost⟩, leftResult, result⟩ := accepted
          cases actualLeft <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
          obtain ⟨⟨actualRight, rightCost⟩, rightResult, result⟩ := result
          cases actualRight <;> simp only [reduceCtorEq, evaluateLocalWordBinaryWithCost?,
            Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at result
          obtain ⟨rfl, rfl⟩ := result
          first
          | exact .add (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .subtract (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .multiply (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .divide (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .modulo (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .bitAnd (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .bitOr (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .bitXor (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .greater (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .less (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .equal (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .notEqual (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .lessEqual (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
          | exact .greaterEqual (evaluateLocalExpressionWithCost?_sound leftResult store) (evaluateLocalExpressionWithCost?_sound rightResult store)
      case conditional condition question thenBranch colon elseBranch =>
        simp only [bind, Option.bind_eq_some_iff] at accepted
        obtain ⟨⟨actual, conditionCost⟩, conditionResult, result⟩ := accepted
        cases actual <;> simp only [reduceCtorEq] at result
        rename_i choice
        cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at result
        all_goals
          obtain ⟨⟨actual, branchCost⟩, branchResult, result⟩ := result
          simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
          obtain ⟨rfl, rfl⟩ := result
          first
          | exact .ifTrue (evaluateLocalExpressionWithCost?_sound conditionResult store) (evaluateLocalExpressionWithCost?_sound branchResult store)
          | exact .ifFalse (evaluateLocalExpressionWithCost?_sound conditionResult store) (evaluateLocalExpressionWithCost?_sound branchResult store)
termination_by sizeOf source

end Solcore.Frontend
