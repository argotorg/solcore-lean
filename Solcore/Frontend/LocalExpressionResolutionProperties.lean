import Solcore.Frontend.LocalExpression
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

/-- Changing the outer source range does not change structural resolution. -/
theorem resolveLocalExpression?_span (table : LocalNameTable) (source : Syntax.Expr)
    (span : Syntax.SourceSpan) :
    resolveLocalExpression? table { source with span } = resolveLocalExpression? table source := by
  cases source with
  | mk sourceSpan payload =>
      cases payload <;> try simp only [resolveLocalExpression?]
      case unary operator operand =>
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue <;> simp only [resolveLocalExpression?]
      case binary left operator right =>
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue <;> simp only [resolveLocalExpression?]

/-- Literal spelling is retained, while both literal and outer ranges are ignored. -/
theorem resolveLocalExpression?_literal_spans (table : LocalNameTable)
    (payload : Syntax.CoreLiteralValue)
    (span literalSpan otherSpan otherLiteralSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table ⟨span, .literal ⟨literalSpan, payload⟩⟩ =
      resolveLocalExpression? table ⟨otherSpan, .literal ⟨otherLiteralSpan, payload⟩⟩ := by
  simp only [resolveLocalExpression?, interpretWordLiteral?]

/-- Conditional punctuation and the outer range carry no resolution meaning. -/
theorem resolveLocalExpression?_conditional_spans (table : LocalNameTable)
    (condition thenBranch elseBranch : Syntax.Expr)
    (span question colon otherSpan otherQuestion otherColon : Syntax.SourceSpan) :
    resolveLocalExpression? table
        { span, value := .conditional condition question thenBranch colon elseBranch } =
      resolveLocalExpression? table
        { span := otherSpan,
          value := .conditional condition otherQuestion thenBranch otherColon elseBranch } := by
  simp only [resolveLocalExpression?]

/-- Boolean negation ignores its operator range and the enclosing expression range. -/
theorem resolveLocalExpression?_logicalNot_spans (table : LocalNameTable) (operand : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .unary ⟨operatorSpan, .logicalNot⟩ operand } =
      resolveLocalExpression? table
        { span := otherSpan, value := .unary ⟨otherOperatorSpan, .logicalNot⟩ operand } := by
  simp only [resolveLocalExpression?]

/-- Word complement ignores its operator range and the enclosing expression range. -/
theorem resolveLocalExpression?_bitNot_spans (table : LocalNameTable) (operand : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .unary ⟨operatorSpan, .bitNot⟩ operand } =
      resolveLocalExpression? table
        { span := otherSpan, value := .unary ⟨otherOperatorSpan, .bitNot⟩ operand } := by
  simp only [resolveLocalExpression?]

/-- Conjunction's generated false constant is independent of its source ranges. -/
theorem resolveLocalExpression?_logicalAnd_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .logicalAnd⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Disjunction's generated true constant is independent of its source ranges. -/
theorem resolveLocalExpression?_logicalOr_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .logicalOr⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Identifier spelling, not either occurrence range, selects the local ID. -/
theorem resolveLocalExpression?_identifier_value_eq (table : LocalNameTable)
    {left right : Syntax.Identifier} (same : left.value = right.value)
    (leftSpan rightSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span := leftSpan, value := .identifier left } =
      resolveLocalExpression? table { span := rightSpan, value := .identifier right } := by
  simp only [resolveLocalExpression?, same]

theorem resolveLocalExpression?_group (table : LocalNameTable) (span : Syntax.SourceSpan)
    (inner : Syntax.Expr) :
    resolveLocalExpression? table { span, value := .group inner } = resolveLocalExpression? table inner := by
  simp only [resolveLocalExpression?]

/-- The established reference fragment embeds without changing its selected identity. -/
theorem ResolvesLocalReference.toLocalExpression {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (reference : ResolvesLocalReference table source id) :
    ResolvesLocalExpression table source (.var id) := by
  induction reference with
  | identifier found => exact .identifier found
  | group _ ih => exact .group ih

end Solcore.Frontend
