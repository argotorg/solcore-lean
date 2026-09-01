import Solcore.Syntax.Parser.CoreLambdaParameterCoreOrdinaryRejectionSoundnessProperties

/-! Complete executable ordinary outcome of `lambdaParameterCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

/-- Package exact ordinary success and rejection of the Core parser. -/
theorem lambdaParameterCore_ordinaryOutcome_sound
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
    (∀ {input output : State} {parameter : LambdaParameter},
      lambdaParameterCore input = .ok parameter output →
        DeclarativeGrammar.LambdaParameterCoreOrdinaryParses typeOrdinary
          input.declarativeRemainder parameter output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      lambdaParameterCore input = .reject failure rejected →
        DeclarativeGrammar.LambdaParameterCoreRejects typeRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨lambdaParameterCore_success_ordinary_sound typeOrdinary
      typeSuccessSound,
    lambdaParameterCore_reject_ordinary_sound typeRejects typeRejectSound⟩

/-- Re-export the deterministic Core relation contract. -/
theorem lambdaParameterCore_ordinaryOutcomeSpec
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LambdaParameterCoreOrdinaryParses typeOrdinary)
      (DeclarativeGrammar.LambdaParameterCoreRejects typeRejects) :=
  DeclarativeGrammar.lambdaParameterCoreDeterministicOutcomeSpec typeOutcomes

end Solcore.Syntax.Parser.LambdaParameterInternals
