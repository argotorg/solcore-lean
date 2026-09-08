import Solcore.Frontend.LocalExpression

/-! Source ranges, identifier spelling, and grouping laws for the canonical
local-expression adapter. These laws do not depend on resolution correctness. -/

set_option autoImplicit false

namespace Solcore.Frontend

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

/-- Word addition keeps both operand trees and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_add_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .add⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .add⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word subtraction retains operand order and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_subtract_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .subtract⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .subtract⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word multiplication keeps both operand trees and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_multiply_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .multiply⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .multiply⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Unsigned comparison retains operand order and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_greater_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .greater⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .greater⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word conjunction keeps both operand trees and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_bitAnd_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .bitAnd⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .bitAnd⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word disjunction keeps both operand trees and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_bitOr_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .bitOr⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .bitOr⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word exclusive-or keeps both operand trees and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_bitXor_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .bitXor⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .bitXor⟩ right } := by
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

end Solcore.Frontend
