import Solcore.Syntax.DeclarativeFunctionParameterCoreOutcomeProperties
import Solcore.Syntax.Parser.FunctionParameterCoreOrdinaryRejectionSoundnessProperties

/-! Complete executable ordinary outcome of `namedParameterCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

/-- Package exact ordinary success and rejection of the Core parser. -/
theorem namedParameterCore_ordinaryOutcome_sound
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
    (∀ {input output : State} {parameter : FunctionParameter},
      namedParameterCore input = .ok parameter output →
        DeclarativeGrammar.FunctionParameterCoreOrdinaryParses typeOrdinary
          input.declarativeRemainder parameter output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      namedParameterCore input = .reject failure rejected →
        DeclarativeGrammar.FunctionParameterCoreRejects typeRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨namedParameterCore_success_ordinary_sound typeOrdinary typeSuccessSound,
    namedParameterCore_reject_ordinary_sound typeRejects typeRejectSound⟩

/-- Re-export the deterministic Core relation contract. -/
theorem namedParameterCore_ordinaryOutcomeSpec
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.FunctionParameterCoreOrdinaryParses typeOrdinary)
      (DeclarativeGrammar.FunctionParameterCoreRejects typeRejects) :=
  DeclarativeGrammar.functionParameterCoreDeterministicOutcomeSpec
    typeOutcomes

end Solcore.Syntax.Parser.FunctionParameterInternals
