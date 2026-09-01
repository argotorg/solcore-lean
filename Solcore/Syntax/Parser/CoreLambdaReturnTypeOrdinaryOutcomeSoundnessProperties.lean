import Solcore.Syntax.DeclarativeCoreExpressionLambdaOutcomeProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Executable ordinary outcomes for an optional Core lambda return type. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every optional-return success takes exactly the absent-arrow branch or a
present arrow followed by the supplied ordinary type success. -/
theorem optionalLambdaReturnType_success_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    {input output : State} {returnType : Option TypeExpr}
    (result : optionalLambdaReturnType input = .ok returnType output) :
    DeclarativeGrammar.OptionalLambdaReturnTypeOrdinaryParses typeOrdinary
      input.declarativeRemainder returnType output.declarativeRemainder := by
  unfold optionalLambdaReturnType getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .arrow
  · simp only [present, if_true] at result
    cases arrowResult : symbol .arrow .typeExpr input with
    | invariant error => simp [arrowResult] at result
    | reject failure rejected => simp [arrowResult] at result
    | ok arrow afterArrow =>
        simp only [arrowResult] at result
        cases typeResult : typeExpr afterArrow with
        | invariant error => simp [typeResult] at result
        | reject failure rejected => simp [typeResult] at result
        | ok type afterType =>
            simp only [typeResult, pure] at result
            cases result
            exact .present arrow.span
              (symbol_success_exactTokenParses .arrow .typeExpr arrowResult)
              (typeSuccessSound typeResult)
  · have absent : isSymbol input .arrow = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .arrow absent)

/-- Every optional-return rejection occurs only after a present arrow and is
the exact supplied type rejection. -/
theorem optionalLambdaReturnType_reject_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalLambdaReturnType input = .reject failure rejected) :
    DeclarativeGrammar.OptionalLambdaReturnTypeRejects typeOrdinary
      typeRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalLambdaReturnType getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .arrow
  · rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .typeExpr present with
      ⟨arrow, arrowResult⟩
    simp only [present, if_true, arrowResult] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | ok type afterType => simp [typeResult, pure] at result
    | reject typeFailure typeRejected =>
        simp only [typeResult] at result
        cases result
        exact .typeRejected arrow.span
          (symbol_success_exactTokenParses .arrow .typeExpr arrowResult)
          (typeRejectSound typeResult)
  · have absent : isSymbol input .arrow = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package both executable optional-return outcomes. -/
theorem optionalLambdaReturnType_ordinaryOutcome_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {returnType : Option TypeExpr},
      optionalLambdaReturnType input = .ok returnType output →
        DeclarativeGrammar.OptionalLambdaReturnTypeOrdinaryParses
          typeOrdinary input.declarativeRemainder returnType
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      optionalLambdaReturnType input = .reject failure rejected →
        DeclarativeGrammar.OptionalLambdaReturnTypeRejects typeOrdinary
          typeRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨optionalLambdaReturnType_success_ordinary_sound typeOrdinary
      typeSuccessSound,
    optionalLambdaReturnType_reject_ordinary_sound typeOrdinary typeRejects
      typeRejectSound⟩

/-- Lift a deterministic supplied type outcome to optional returns. -/
theorem optionalLambdaReturnType_ordinaryOutcomeSpec
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.OptionalLambdaReturnTypeOrdinaryParses
        typeOrdinary)
      (DeclarativeGrammar.OptionalLambdaReturnTypeRejects typeOrdinary
        typeRejects) :=
  DeclarativeGrammar.optionalLambdaReturnTypeDeterministicOutcomeSpec
    typeOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
