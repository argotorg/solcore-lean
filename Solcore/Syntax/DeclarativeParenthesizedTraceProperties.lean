import Solcore.Syntax.DeclarativeParenthesizedTraceGrammar

/-! Parenthesized trace erasure and structural laws. Unlike generic delimited
whole-list erasure, these older grammars impose no child carrier condition.
Carrier/end-index preservation remains a separate conditional structural law. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {elementParses : Remainder → Syntax.Expr → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem ParenthesizedTupleTailTraceParses.comma_present
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .comma } := by
  cases parsed with
  | trailing span _ comma _ | final span _ comma _ _ _ _ _ | next span _ comma _ _ _ _ => exact ⟨span, comma.1⟩

theorem ParenthesizedTupleTailTraceParses.comma_conflicts_absent
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .comma)) : False :=
  absent parsed.comma_present

theorem ParenthesizedTupleTailTraceParses.ordinary
    (erases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      elementParses input value output)
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace) :
    ParenthesizedTupleTailParses elementParses input values closingSpan output := by
  induction parsed with
  | trailing span closing comma finish => exact .trailing span closing comma finish
  | final span closing comma absent child progress noComma finish =>
      exact .final span closing comma absent (erases child) progress noComma finish
  | next span closing comma absent child progress tail ih =>
      exact .next span closing comma absent (erases child) progress ih

theorem ParenthesizedExpressionTraceParses.ordinary
    (erases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      elementParses input value output)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedExpressionTraceParses elementTrace source endByte input value output trace) :
    ParenthesizedExpressionParses elementParses input value output := by
  cases parsed with
  | empty span closing opening finish => exact .empty span closing opening finish
  | group span closing opening absent child progress noComma finish =>
      exact .group span closing opening absent (erases child) progress noComma finish
  | tuple span closing opening absent child progress tail =>
      exact .tuple span closing opening absent (erases child) progress (tail.ordinary erases)

theorem ParenthesizedTupleTailTraceParses.output_window
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  induction parsed with
  | trailing span closing comma finish => rw [finish.2, comma.2]; exact ⟨rfl, rfl⟩
  | final span closing comma absent child progress noComma finish =>
      rw [finish.2]
      simpa only [comma.2] using elementWindow child
  | next span closing comma absent child progress tail ih =>
      have frame := elementWindow child
      simpa only [comma.2] using And.intro (ih.1.trans frame.1) (ih.2.trans frame.2)

theorem ParenthesizedExpressionTraceParses.output_window
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedExpressionTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | empty span closing opening finish => rw [finish.2, opening.2]; exact ⟨rfl, rfl⟩
  | group span closing opening absent child progress noComma finish =>
      rw [finish.2]
      simpa only [opening.2] using elementWindow child
  | tuple span closing opening absent child progress tail =>
      have headFrame := elementWindow child
      have tailFrame := tail.output_window elementWindow
      simpa only [opening.2] using And.intro (tailFrame.1.trans headFrame.1) (tailFrame.2.trans headFrame.2)

theorem ParenthesizedTupleTailTraceParses.cursor_lt
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace) :
    input.cursor < output.cursor := by
  induction parsed with
  | trailing span closing comma finish => rw [finish.2, comma.2]; exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  | final span closing comma absent child progress noComma finish =>
      rw [comma.2] at progress
      rw [finish.2]
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) (Nat.lt_succ_self _)
  | next span closing comma absent child progress tail ih =>
      rw [comma.2] at progress
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) ih

theorem ParenthesizedTupleTailTraceParses.output_cursor_le_endIndex
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace) :
    output.cursor ≤ output.endIndex := by
  induction parsed with
  | trailing _ _ _ finish | final _ _ _ _ _ _ _ finish => rw [finish.2]; exact finish.1.1
  | next _ _ _ _ _ _ _ ih => exact ih

theorem ParenthesizedExpressionTraceParses.cursor_lt
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedExpressionTraceParses elementTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | empty span closing opening finish => rw [finish.2, opening.2]; exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  | group span closing opening absent child progress noComma finish =>
      rw [opening.2] at progress
      rw [finish.2]
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) (Nat.lt_succ_self _)
  | tuple span closing opening absent child progress tail =>
      rw [opening.2] at progress
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) tail.cursor_lt

end Solcore.Syntax.DeclarativeGrammar
