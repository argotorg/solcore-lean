import Solcore.Syntax.Parser.Pattern
import Solcore.Syntax.Parser.ExpressionProperties
import Solcore.Syntax.Parser.TermPatternProperties

/-! Fuel-inductive totality for the recursive canonical pattern family. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

theorem corePatternWithFuel_fuelElementTotalityContract
    (statementValid : SourceFile → Statement → Prop)
    (expressionSyntax : ∀ fuel,
      ExpressionInternals.ExpressionContract statementValid
        (coreExpressionWithFuel fuel))
    (expressionTotality : ∀ fuel,
      FuelElementTotalityContract (coreExpressionWithFuel fuel) fuel)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      Expr.ValidFor statementValid file value → value.span.ValidFor file) :
    ∀ fuel,
      FuelElementTotalityContract (corePatternWithFuel fuel) fuel := by
  intro fuel
  induction fuel with
  | zero =>
      exact {
        validFor := by
          intro input inputValid
          simp only [corePatternWithFuel]
          trivial
        preservesTokenWindow := by
          intro input
          trivial
        cursorLtOnSuccess := by
          intro input next value result
          simp [corePatternWithFuel] at result
        ordinary := by
          intro input inputValid adequate
          omega
      }
  | succ fuel inductionHypothesis =>
      have expressionValidFamily : ∀ level,
          (coreExpressionWithFuel level).ValidFor
            (Expr.ValidFor statementValid) :=
        fun level => (expressionSyntax level).validFor
      have expressionStartsFamily : ∀ level,
          Parser.StartsAtCurrentTokenOnSuccess
            (coreExpressionWithFuel level) (·.span) :=
        fun level => (expressionSyntax level).startsAtCurrentTokenOnSuccess
      have expressionWindowFamily : ∀ level,
          Parser.PreservesTokenWindow (coreExpressionWithFuel level) :=
        fun level => (expressionSyntax level).preservesTokenWindow
      have nestedValid := corePatternWithFuel_validFor
        (Expr.ValidFor statementValid) expressionValidFamily
        expressionSpanValid expressionStartsFamily expressionWindowFamily fuel
      have layer := PatternInternals.patternLayer_fuelElementTotalityContract
        (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
        fuel fuel inductionHypothesis (expressionTotality fuel)
        (Expr.ValidFor statementValid) nestedValid
        (expressionSyntax fuel).validFor expressionSpanValid
        (expressionSyntax fuel).startsAtCurrentTokenOnSuccess
      simpa only [corePatternWithFuel, Nat.min_self] using layer

end Solcore.Syntax.Parser.TermInternals
