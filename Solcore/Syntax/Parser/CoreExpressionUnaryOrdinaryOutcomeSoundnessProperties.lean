import Solcore.Syntax.DeclarativeCoreExpressionUnaryLeftOutcomeProperties
import Solcore.Syntax.Parser.CoreExpressionUnarySoundnessProperties
import Solcore.Syntax.Parser.ExpressionUnaryTotalityProperties

/-!
Executable ordinary-success and exact-rejection bridges for the Core prefix
unary expression layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

private theorem applyUnaryOperators_eq_declarative
    (operators : List (Located UnaryOp)) (base : Expr) :
    applyUnaryOperators operators base =
      DeclarativeGrammar.applyUnaryOperators operators base := by
  rfl

/-- Every executable unary success follows the maximal prefix grammar and the
supplied ordinary postfix grammar, independently of diagnostics. -/
theorem expressionUnary_success_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
    (postfixOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (postfixSuccessSound :
      ∀ {postfixInput postfixOutput : State} {base : Expr},
        expressionPostfix nested block postfixInput = .ok base postfixOutput →
          postfixOrdinary postfixInput.declarativeRemainder base
            postfixOutput.declarativeRemainder)
    {input output : State} {expression : Expr}
    (result : expressionUnary nested block input = .ok expression output) :
    DeclarativeGrammar.ExpressionUnaryOrdinaryParses postfixOrdinary
      input.declarativeRemainder expression output.declarativeRemainder := by
  rcases unaryOperators_production_exists_ok [] input with
    ⟨operators, afterOperators, operatorsResult⟩
  unfold expressionUnary at result
  simp only [operatorsResult] at result
  cases postfixResult : expressionPostfix nested block afterOperators with
  | invariant error => simp [postfixResult] at result
  | reject failure rejected => simp [postfixResult] at result
  | ok base afterPostfix =>
      simp only [postfixResult] at result
      cases result
      exact ⟨operators, afterOperators.declarativeRemainder, base,
        unaryOperators_success_sound operatorsResult,
        postfixSuccessSound postfixResult,
        applyUnaryOperators_eq_declarative operators base⟩

/-- Every executable unary rejection is exactly a postfix rejection after the
same maximal prefix scan. -/
theorem expressionUnary_reject_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
    (postfixRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (postfixRejectSound :
      ∀ {postfixInput rejected : State} {failure : Failure},
        expressionPostfix nested block postfixInput =
            .reject failure rejected →
          postfixRejects postfixInput.declarativeRemainder
            rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : expressionUnary nested block input =
      .reject failure rejected) :
    DeclarativeGrammar.ExpressionUnaryRejects postfixRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases unaryOperators_production_exists_ok [] input with
    ⟨operators, afterOperators, operatorsResult⟩
  unfold expressionUnary at result
  simp only [operatorsResult] at result
  cases postfixResult : expressionPostfix nested block afterOperators with
  | invariant error => simp [postfixResult] at result
  | ok base afterPostfix => simp [postfixResult] at result
  | reject postfixFailure postfixRejected =>
      simp only [postfixResult] at result
      cases result
      exact .postfixRejected
        (unaryOperators_success_sound operatorsResult)
        (postfixRejectSound postfixResult)

/-- Package both executable ordinary outcomes for a supplied postfix bridge. -/
theorem expressionUnary_ordinaryOutcome_sound
    (nested : Parser Expr) (block : Parser Block)
    (postfixOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (postfixRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (postfixSuccessSound :
      ∀ {postfixInput postfixOutput : State} {base : Expr},
        expressionPostfix nested block postfixInput = .ok base postfixOutput →
          postfixOrdinary postfixInput.declarativeRemainder base
            postfixOutput.declarativeRemainder)
    (postfixRejectSound :
      ∀ {postfixInput rejected : State} {failure : Failure},
        expressionPostfix nested block postfixInput =
            .reject failure rejected →
          postfixRejects postfixInput.declarativeRemainder
            rejected.declarativeRemainder) :
    (∀ {input output : State} {expression : Expr},
      expressionUnary nested block input = .ok expression output →
        DeclarativeGrammar.ExpressionUnaryOrdinaryParses postfixOrdinary
          input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expressionUnary nested block input = .reject failure rejected →
        DeclarativeGrammar.ExpressionUnaryRejects postfixRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨expressionUnary_success_ordinary_sound nested block postfixOrdinary
      postfixSuccessSound,
    expressionUnary_reject_ordinary_sound nested block postfixRejects
      postfixRejectSound⟩

/-- Lift a deterministic postfix outcome contract to the unary layer. -/
theorem expressionUnary_ordinaryOutcomeSpec
    {postfixOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {postfixRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (outcomes : DeclarativeGrammar.DeterministicOutcomeSpec postfixOrdinary
      postfixRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ExpressionUnaryOrdinaryParses postfixOrdinary)
      (DeclarativeGrammar.ExpressionUnaryRejects postfixRejects) :=
  DeclarativeGrammar.expressionUnaryDeterministicOutcomeSpec outcomes

end Solcore.Syntax.Parser.ExpressionInternals
