import Solcore.Syntax.Parser.TermPatternFuelTotalityProperties

/-! Public totality for the canonical pattern parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem pattern_invariantFreeOnValid_of_coreExpressionTotality
    (statementValid : SourceFile → Statement → Prop)
    (expressionSyntax : ∀ fuel,
      ExpressionInternals.ExpressionContract statementValid
        (TermInternals.coreExpressionWithFuel fuel))
    (expressionTotality : ∀ fuel,
      FuelElementTotalityContract
        (TermInternals.coreExpressionWithFuel fuel) fuel)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      Expr.ValidFor statementValid file value → value.span.ValidFor file) :
    Parser.InvariantFreeOnValid pattern := by
  intro input inputValid
  have patternTotality :=
    TermInternals.corePatternWithFuel_fuelElementTotalityContract
      statementValid expressionSyntax expressionTotality expressionSpanValid
        (input.remainingCount + 1)
  unfold pattern
  exact patternTotality.ordinary input inputValid (by omega)

theorem pattern_ne_invariant_of_coreExpressionTotality
    (statementValid : SourceFile → Statement → Prop)
    (expressionSyntax : ∀ fuel,
      ExpressionInternals.ExpressionContract statementValid
        (TermInternals.coreExpressionWithFuel fuel))
    (expressionTotality : ∀ fuel,
      FuelElementTotalityContract
        (TermInternals.coreExpressionWithFuel fuel) fuel)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      Expr.ValidFor statementValid file value → value.span.ValidFor file)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    pattern input ≠ .invariant error :=
  (pattern_invariantFreeOnValid_of_coreExpressionTotality statementValid
    expressionSyntax expressionTotality expressionSpanValid).ne_invariant
      input inputValid error

theorem pattern_elementTotalityContract_of_coreExpression
    (statementValid : SourceFile → Statement → Prop)
    (expressionSyntax : ∀ fuel,
      ExpressionInternals.ExpressionContract statementValid
        (TermInternals.coreExpressionWithFuel fuel))
    (expressionTotality : ∀ fuel,
      FuelElementTotalityContract
        (TermInternals.coreExpressionWithFuel fuel) fuel)
    (expressionSpanValid : ∀ {file : SourceFile} {value : Expr},
      Expr.ValidFor statementValid file value → value.span.ValidFor file) :
    ElementTotalityContract pattern := by
  have expressionValid : ∀ fuel,
      (TermInternals.coreExpressionWithFuel fuel).ValidFor
        (Expr.ValidFor statementValid) :=
    fun fuel => (expressionSyntax fuel).validFor
  have expressionStarts : ∀ fuel,
      Parser.StartsAtCurrentTokenOnSuccess
        (TermInternals.coreExpressionWithFuel fuel) (·.span) :=
    fun fuel => (expressionSyntax fuel).startsAtCurrentTokenOnSuccess
  have expressionWindow : ∀ fuel,
      Parser.PreservesTokenWindow
        (TermInternals.coreExpressionWithFuel fuel) :=
    fun fuel => (expressionSyntax fuel).preservesTokenWindow
  exact {
    validFor := (pattern_validFor_of_coreExpression
      (Expr.ValidFor statementValid) expressionValid expressionSpanValid
        expressionStarts expressionWindow).mono (fun _ _ _ => trivial)
    preservesTokenWindow :=
      pattern_preservesTokenWindow_of_coreExpression expressionWindow
    cursorLtOnSuccess := by
      intro input next value parsed
      unfold pattern at parsed
      exact (TermInternals.corePatternWithFuel_fuelElementTotalityContract
        statementValid expressionSyntax expressionTotality expressionSpanValid
          (input.remainingCount + 1)).cursorLtOnSuccess parsed
    invariantFree :=
      (pattern_invariantFreeOnValid_of_coreExpressionTotality statementValid
        expressionSyntax expressionTotality expressionSpanValid).ne_invariant
  }

end Solcore.Syntax.Parser
