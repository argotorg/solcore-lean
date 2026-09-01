import Solcore.Syntax.DeclarativeCoreProxyExpressionOutcomeProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Expression.Atom

/-!
Executable ordinary outcomes for the guarded Core proxy-expression branch.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable proxy success retains its exact marker, nested type,
outer span, AST, and remainder through a supplied ordinary type bridge. -/
theorem proxyExpression_success_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output →
        typeOrdinary input.declarativeRemainder type
          output.declarativeRemainder)
    {input output : State} {expression : Expr}
    (result : proxyExpression input = .ok expression output) :
    DeclarativeGrammar.ProxyExpressionOrdinaryParses typeOrdinary
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold proxyExpression at result
  cases markerResult : symbol .at .expression input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases typeResult : typeExpr afterMarker with
      | invariant error => simp [typeResult] at result
      | reject failure rejected => simp [typeResult] at result
      | ok type afterType =>
          simp only [typeResult, pure] at result
          cases result
          exact .parsed marker.span
            (symbol_success_exactTokenParses .at .expression markerResult)
            (typeSuccessSound typeResult)

/-- Under the dispatcher's positive `@` guard, executable proxy rejection can
only be the exact rejection reported by the nested type parser. -/
theorem proxyExpression_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected →
        typeRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (markerPresent : isSymbol input .at = true)
    (result : proxyExpression input = .reject failure rejected) :
    DeclarativeGrammar.ProxyExpressionRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .at .expression markerPresent with
    ⟨marker, markerResult⟩
  unfold proxyExpression at result
  simp only [bind, markerResult] at result
  cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
  | invariant error => simp [typeResult] at result
  | ok type afterType => simp [typeResult, pure] at result
  | reject typeFailure typeRejected =>
      simp only [typeResult] at result
      cases result
      exact .typeRejected marker.span
        (symbol_success_exactTokenParses .at .expression markerResult)
        (typeRejectSound typeResult)

/-- Package unconditional success and guarded rejection over supplied
executable type callbacks. -/
theorem proxyExpression_guardedOrdinaryOutcome_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output →
        typeOrdinary input.declarativeRemainder type
          output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected →
        typeRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {expression : Expr},
      proxyExpression input = .ok expression output →
        DeclarativeGrammar.ProxyExpressionOrdinaryParses typeOrdinary
          input.declarativeRemainder expression output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isSymbol input .at = true →
        proxyExpression input = .reject failure rejected →
          DeclarativeGrammar.ProxyExpressionRejects typeRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨proxyExpression_success_ordinary_sound typeOrdinary typeSuccessSound,
    proxyExpression_reject_ordinary_sound typeRejects typeRejectSound⟩

/-- Lift a deterministic nested type outcome to the guarded proxy branch. -/
theorem proxyExpression_ordinaryOutcomeSpec
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ProxyExpressionOrdinaryParses typeOrdinary)
      (DeclarativeGrammar.ProxyExpressionRejects typeRejects) :=
  DeclarativeGrammar.proxyExpressionDeterministicOutcomeSpec typeOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
