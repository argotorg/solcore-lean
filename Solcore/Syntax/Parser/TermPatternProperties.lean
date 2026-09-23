import Solcore.Syntax.Parser.Term
import Solcore.Syntax.Parser.Pattern

/-! Fuel-inductive contracts for the public canonical pattern parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace TermInternals

/-- Every fuel-bounded pattern parser preserves ordinary token windows. -/
theorem corePatternWithFuel_preservesTokenWindow
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow (coreExpressionWithFuel fuel)) :
    ∀ fuel, Parser.PreservesTokenWindow (corePatternWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero => intro input; trivial
  | succ fuel inductionHypothesis =>
      exact PatternInternals.patternLayer_preservesTokenWindow
        (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
        inductionHypothesis (expressionPreserves fuel)

/-- Every successful fuel-bounded pattern parse retains its token carrier. -/
theorem corePatternWithFuel_preservesTokensOnSuccess
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow (coreExpressionWithFuel fuel))
    (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (corePatternWithFuel fuel) :=
  (corePatternWithFuel_preservesTokenWindow expressionPreserves fuel).preservesTokensOnSuccess

/-- Fuel-bounded pattern successes never rewind their caller. -/
theorem corePatternWithFuel_cursorMonotoneOnSuccess
    (expressionMonotone : ∀ fuel,
      Parser.CursorMonotoneOnSuccess (coreExpressionWithFuel fuel)) :
    ∀ fuel, Parser.CursorMonotoneOnSuccess (corePatternWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input pattern next result
      simp [corePatternWithFuel] at result
  | succ fuel inductionHypothesis =>
      exact PatternInternals.patternLayer_cursorMonotoneOnSuccess
        (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
        inductionHypothesis (expressionMonotone fuel)

/-- Fuel-bounded pattern successes start at their current input token. -/
theorem corePatternWithFuel_startsAtCurrentTokenOnSuccess
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow (coreExpressionWithFuel fuel)) :
    ∀ fuel, Parser.StartsAtCurrentTokenOnSuccess
      (corePatternWithFuel fuel) (·.span) := by
  intro fuel
  cases fuel with
  | zero =>
      intro input pattern next result
      simp [corePatternWithFuel] at result
  | succ fuel =>
      exact PatternInternals.patternLayer_startsAtCurrentTokenOnSuccess
        (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
        (corePatternWithFuel_preservesTokenWindow expressionPreserves fuel)
        (expressionPreserves fuel)

/-- Every fuel-bounded pattern parser retains recursive source provenance. -/
theorem corePatternWithFuel_validFor
    (expressionValid : SourceFile → Expr → Prop)
    (expressionParserValid : ∀ fuel,
      (coreExpressionWithFuel fuel).ValidFor expressionValid)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (expressionStarts : ∀ fuel,
      Parser.StartsAtCurrentTokenOnSuccess
        (coreExpressionWithFuel fuel) (·.span))
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow (coreExpressionWithFuel fuel)) :
    ∀ fuel, (corePatternWithFuel fuel).ValidFor
      (Pattern.ValidFor expressionValid) := by
  intro fuel
  induction fuel with
  | zero => intro input inputValid; trivial
  | succ fuel inductionHypothesis =>
      exact PatternInternals.patternLayer_validFor
        (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
        expressionValid inductionHypothesis
        (corePatternWithFuel_preservesTokenWindow expressionPreserves fuel)
        (expressionParserValid fuel) expressionSpanValid
        (expressionStarts fuel) (expressionPreserves fuel)

end TermInternals

/-- Public pattern parsing preserves ordinary token windows when Core
expression parsing does so at every fuel. -/
theorem pattern_preservesTokenWindow_of_coreExpression
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow
        (TermInternals.coreExpressionWithFuel fuel)) :
    Parser.PreservesTokenWindow pattern := by
  intro input
  unfold pattern
  exact TermInternals.corePatternWithFuel_preservesTokenWindow
    expressionPreserves (input.remainingCount + 1) input

/-- Public pattern success retains the token carrier under the same
compositional expression contract. -/
theorem pattern_preservesTokensOnSuccess_of_coreExpression
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow
        (TermInternals.coreExpressionWithFuel fuel)) :
    Parser.PreservesTokensOnSuccess pattern :=
  (pattern_preservesTokenWindow_of_coreExpression expressionPreserves).preservesTokensOnSuccess

/-- Public pattern success is cursor-monotone whenever fuel-bounded Core
expression success is cursor-monotone. -/
theorem pattern_cursorMonotoneOnSuccess_of_coreExpression
    (expressionMonotone : ∀ fuel,
      Parser.CursorMonotoneOnSuccess
        (TermInternals.coreExpressionWithFuel fuel)) :
    Parser.CursorMonotoneOnSuccess pattern := by
  intro input value next result
  unfold pattern at result
  exact TermInternals.corePatternWithFuel_cursorMonotoneOnSuccess
    expressionMonotone (input.remainingCount + 1) input value next result

/-- Public pattern success starts at the current token whenever fuel-bounded
Core expression parsing preserves token windows. -/
theorem pattern_startsAtCurrentTokenOnSuccess_of_coreExpression
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow
        (TermInternals.coreExpressionWithFuel fuel)) :
    Parser.StartsAtCurrentTokenOnSuccess pattern (·.span) := by
  intro input value next result
  unfold pattern at result
  exact TermInternals.corePatternWithFuel_startsAtCurrentTokenOnSuccess
    expressionPreserves (input.remainingCount + 1) input value next result

/-- Public pattern parsing retains recursive source provenance under the
fuel-indexed Core expression contracts required by comptime patterns. -/
theorem pattern_validFor_of_coreExpression
    (expressionValid : SourceFile → Expr → Prop)
    (expressionParserValid : ∀ fuel,
      (TermInternals.coreExpressionWithFuel fuel).ValidFor expressionValid)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (expressionStarts : ∀ fuel,
      Parser.StartsAtCurrentTokenOnSuccess
        (TermInternals.coreExpressionWithFuel fuel) (·.span))
    (expressionPreserves : ∀ fuel,
      Parser.PreservesTokenWindow
        (TermInternals.coreExpressionWithFuel fuel)) :
    pattern.ValidFor (Pattern.ValidFor expressionValid) := by
  intro input inputValid
  unfold pattern
  exact TermInternals.corePatternWithFuel_validFor expressionValid
    expressionParserValid expressionSpanValid expressionStarts
    expressionPreserves (input.remainingCount + 1) input inputValid

end Solcore.Syntax.Parser
