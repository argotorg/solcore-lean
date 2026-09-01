import Solcore.Syntax.DeclarativeCoreLiteralOutcomeGrammar

/-! Deterministic ordinary outcomes for Core literal leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every ordinary Core literal consumes exactly its current token. -/
theorem CoreLiteralOrdinaryParses.output_eq
    {input output : Remainder} {literal : Syntax.CoreLiteral}
    (parsed : CoreLiteralOrdinaryParses input literal output) :
    output = { input with cursor := input.cursor + 1 } := by
  cases parsed <;> rfl

/-- Ordinary Core-literal output is functional. -/
theorem CoreLiteralOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.CoreLiteral}
    {afterLeft afterRight : Remainder}
    (leftParsed : CoreLiteralOrdinaryParses input left afterLeft)
    (rightParsed : CoreLiteralOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  rw [leftParsed.output_eq, rightParsed.output_eq]

/-- Exact literal rejection excludes every ordinary literal success. -/
theorem CoreLiteralRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : CoreLiteralRejects input rejected) :
    ¬ ∃ literal output, CoreLiteralOrdinaryParses input literal output := by
  rintro ⟨literal, output, successful⟩
  cases rejection with
  | absent absent =>
      cases successful with
      | decimal token => exact absent.1 ⟨_, _, token⟩
      | hexadecimal token => exact absent.2.1 ⟨_, _, token⟩
      | string token => exact absent.2.2 ⟨_, _, token⟩

/-- Core literal primitives form deterministic ordinary outcomes. -/
theorem coreLiteralDeterministicOutcomeSpec :
    DeterministicOutcomeSpec CoreLiteralOrdinaryParses
      CoreLiteralRejects where
  successOutputUnique := CoreLiteralOrdinaryParses.output_unique
  successRejectDisjoint := CoreLiteralRejects.disjointOrdinary

/-- Every ordinary literal expression consumes exactly its literal token. -/
theorem LiteralExpressionOrdinaryParses.output_eq
    {input output : Remainder} {expression : Syntax.Expr}
  (parsed : LiteralExpressionOrdinaryParses input expression output) :
    output = { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | parsed literalParsed => cases literalParsed <;> rfl

/-- Ordinary literal-expression output is functional. -/
theorem LiteralExpressionOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : LiteralExpressionOrdinaryParses input left afterLeft)
    (rightParsed : LiteralExpressionOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  rw [leftParsed.output_eq, rightParsed.output_eq]

/-- Exact literal-expression rejection excludes every ordinary success. -/
theorem LiteralExpressionRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : LiteralExpressionRejects input rejected) :
    ¬ ∃ expression output,
      LiteralExpressionOrdinaryParses input expression output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | absent absent =>
      cases successful with
      | parsed literalParsed =>
          cases literalParsed with
          | decimal token => exact absent.1 ⟨_, _, token⟩
          | hexadecimal token => exact absent.2.1 ⟨_, _, token⟩
          | string token => exact absent.2.2 ⟨_, _, token⟩

/-- Literal-expression leaves form deterministic ordinary outcomes. -/
theorem literalExpressionDeterministicOutcomeSpec :
    DeterministicOutcomeSpec LiteralExpressionOrdinaryParses
      LiteralExpressionRejects where
  successOutputUnique := LiteralExpressionOrdinaryParses.output_unique
  successRejectDisjoint := LiteralExpressionRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
