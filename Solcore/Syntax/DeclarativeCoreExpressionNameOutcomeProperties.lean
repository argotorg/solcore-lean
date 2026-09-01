import Solcore.Syntax.DeclarativeCoreExpressionNameOutcomeGrammar

/-! Deterministic ordinary outcomes for one Boolean-first Core name. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Every ordinary expression name consumes exactly its current token. -/
theorem ExpressionNameOrdinaryParses.output_eq
    {input output : Remainder} {name : Syntax.Identifier}
    (parsed : ExpressionNameOrdinaryParses input name output) :
    output = { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | boolean parsed => cases parsed <;> rfl
  | identifier trueAbsent falseAbsent parsed =>
      rcases parsed with ⟨token, tokensEq, endIndexEq, cursorEq⟩
      cases input
      cases output
      simp_all

/-- Ordinary expression-name output is functional. -/
theorem ExpressionNameOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionNameOrdinaryParses input left afterLeft)
    (rightParsed : ExpressionNameOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  rw [leftParsed.output_eq, rightParsed.output_eq]

/-- Exact name rejection excludes every ordinary expression-name success. -/
theorem ExpressionNameRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ExpressionNameRejects input rejected) :
    ¬ ∃ name output,
      ExpressionNameOrdinaryParses input name output := by
  rintro ⟨name, output, successful⟩
  cases rejection with
  | absent absent =>
      cases successful with
      | boolean parsed =>
          cases parsed with
          | trueKeyword token =>
              exact absent_conflicts_token absent.1 token
          | falseKeyword token =>
              exact absent_conflicts_token absent.2.1 token
      | identifier trueAbsent falseAbsent parsed =>
          exact absent.2.2 ⟨name.span, name.value, parsed.1⟩

/-- Boolean-first expression names form a deterministic ordinary outcome. -/
theorem expressionNameDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ExpressionNameOrdinaryParses
      ExpressionNameRejects where
  successOutputUnique := ExpressionNameOrdinaryParses.output_unique
  successRejectDisjoint := ExpressionNameRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
