import Solcore.Frontend.LocalExpressionShapeProperties
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.WordLiteralProperties

/-! Exact structural resolution for the supported canonical expression fragment.
All written children must resolve, including short-circuit operands; branch
selection belongs to evaluation. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ResolvesLocalExpression.complete {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved) :
    resolveLocalExpression? table source = some resolved := by
  induction resolution with
  | identifier found =>
      simp only [resolveLocalExpression?, LocalNameTable.lookup?_iff.mpr found, Option.map_some]
  | wordLiteral meaning =>
      simp only [resolveLocalExpression?, interpretWordLiteral?_complete meaning, Option.map_some]
  | group _ ih => simpa only [resolveLocalExpression?] using ih
  | logicalNot _ ih | bitNot _ ih => simp only [resolveLocalExpression?, ih, Option.map_some]
  | add _ _ leftIH rightIH | subtract _ _ leftIH rightIH | multiply _ _ leftIH rightIH
  | greater _ _ leftIH rightIH | equal _ _ leftIH rightIH | notEqual _ _ leftIH rightIH
  | lessEqual _ _ leftIH rightIH | less _ _ leftIH rightIH
  | greaterEqual _ _ leftIH rightIH
  | bitAnd _ _ leftIH rightIH
  | bitOr _ _ leftIH rightIH | bitXor _ _ leftIH rightIH
  | logicalAnd _ _ leftIH rightIH | logicalOr _ _ leftIH rightIH =>
      simp [resolveLocalExpression?, leftIH, rightIH]
  | conditional _ _ _ conditionIH thenIH elseIH =>
      simp [resolveLocalExpression?, conditionIH, thenIH, elseIH]

theorem resolveLocalExpression?_sound {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (result : resolveLocalExpression? table source = some resolved) :
    ResolvesLocalExpression table source resolved := by
  cases source with
  | mk span payload =>
      cases payload <;> try simp only [resolveLocalExpression?, reduceCtorEq] at result
      case identifier name =>
        cases found : table.lookup? name.value with
        | none => simp only [found, Option.map_none, reduceCtorEq] at result
        | some id =>
            simp only [found, Option.map_some, Option.some.injEq] at result
            cases result
            exact .identifier (LocalNameTable.lookup?_iff.mp found)
      case literal literal =>
        simp only [Option.map_eq_some_iff] at result
        obtain ⟨word, interpreted, same⟩ := result
        cases same
        exact .wordLiteral (interpretWordLiteral?_sound interpreted)
      case group inner => exact .group (resolveLocalExpression?_sound result)
      case unary operator operand =>
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue with
        | logicalNot =>
            simp only [resolveLocalExpression?, Option.map_eq_some_iff] at result
            obtain ⟨resolvedOperand, operandResult, same⟩ := result
            cases same
            exact .logicalNot (resolveLocalExpression?_sound operandResult)
        | bitNot =>
            simp only [resolveLocalExpression?, Option.map_eq_some_iff] at result
            obtain ⟨resolvedOperand, operandResult, same⟩ := result
            cases same
            exact .bitNot (resolveLocalExpression?_sound operandResult)
      case binary left operator right =>
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue <;> try simp only [resolveLocalExpression?, reduceCtorEq] at result
        case add =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .add (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case subtract =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .subtract (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case multiply =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .multiply (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case greater =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .greater (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case equal =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .equal (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case notEqual =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .notEqual (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case lessEqual =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .lessEqual (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case less =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .less (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case greaterEqual =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .greaterEqual (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case bitAnd =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .bitAnd (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case bitOr =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .bitOr (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case bitXor =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .bitXor (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case logicalAnd =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .logicalAnd (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case logicalOr =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .logicalOr (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
      case conditional condition question thenBranch colon elseBranch =>
        simp only [bind, Option.bind_eq_some_iff, pure] at result
        obtain ⟨resolvedCondition, conditionResult, resolvedThen, thenResult,
          resolvedElse, elseResult, same⟩ := result
        cases same
        exact .conditional (resolveLocalExpression?_sound conditionResult)
          (resolveLocalExpression?_sound thenResult) (resolveLocalExpression?_sound elseResult)
termination_by sizeOf source

theorem resolveLocalExpression?_iff {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr} :
    resolveLocalExpression? table source = some resolved ↔
      ResolvesLocalExpression table source resolved :=
  ⟨resolveLocalExpression?_sound, ResolvesLocalExpression.complete⟩

theorem resolveLocalExpression?_eq_none_iff {table : LocalNameTable} {source : Syntax.Expr} :
    resolveLocalExpression? table source = none ↔
      ¬ ∃ resolved, ResolvesLocalExpression table source resolved := by
  constructor
  · intro result ⟨resolved, resolution⟩
    have accepted := resolution.complete
    rw [result] at accepted
    cases accepted
  · intro absent
    cases result : resolveLocalExpression? table source with
    | none => rfl
    | some resolved => exact False.elim (absent ⟨resolved, resolveLocalExpression?_sound result⟩)

theorem ResolvesLocalExpression.deterministic {table : LocalNameTable}
    {source : Syntax.Expr} {left right : Resolved.Expr}
    (leftResolution : ResolvesLocalExpression table source left)
    (rightResolution : ResolvesLocalExpression table source right) : left = right :=
  Option.some.inj (leftResolution.complete.symm.trans rightResolution.complete)

/-- The established reference fragment embeds without changing its selected identity. -/
theorem ResolvesLocalReference.toLocalExpression {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (reference : ResolvesLocalReference table source id) :
    ResolvesLocalExpression table source (.var id) := by
  induction reference with
  | identifier found => exact .identifier found
  | group _ ih => exact .group ih

end Solcore.Frontend
