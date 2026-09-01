import Solcore.Syntax.DeclarativeCoreExpressionAtomCoreOutcomeProperties
import Solcore.Syntax.Parser.CoreExpressionAtomCoreOrdinaryRejectionSoundnessProperties

/-! Packaged executable ordinary outcomes for `expressionAtomCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Package unconditional Core-atom success and exact selected rejection over
supplied subordinate executable outcome bridges. -/
theorem expressionAtomCore_ordinaryOutcome_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (parameterOrdinary : DeclarativeGrammar.Remainder → LambdaParameter →
      DeclarativeGrammar.Remainder → Prop)
    (parameterRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (parameterSuccessSound :
      ∀ {input output : State} {parameter : LambdaParameter},
        lambdaParameter input = .ok parameter output →
          parameterOrdinary input.declarativeRemainder parameter
            output.declarativeRemainder)
    (parameterRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        lambdaParameter input = .reject failure rejected →
          parameterRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (parameterShape : Parser.PreservesTokenWindow lambdaParameter)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (blockSuccessSound : ∀ {input output : State} {body : Block},
      block input = .ok body output → blockOrdinary
        input.declarativeRemainder body output.declarativeRemainder)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      block input = .reject failure rejected → blockRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {expression : Expr},
      expressionAtomCore nested block input = .ok expression output →
        DeclarativeGrammar.ExpressionAtomCoreOrdinaryParses nestedOrdinary
          parameterOrdinary typeOrdinary blockOrdinary
            input.declarativeRemainder expression
              output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expressionAtomCore nested block input = .reject failure rejected →
        DeclarativeGrammar.ExpressionAtomCoreRejects nestedOrdinary
          nestedRejects parameterOrdinary parameterRejects typeOrdinary
            typeRejects blockRejects input.declarativeRemainder
              rejected.declarativeRemainder) :=
  ⟨expressionAtomCore_success_ordinary_sound nested block nestedOrdinary
      parameterOrdinary typeOrdinary blockOrdinary nestedSuccessSound
        nestedShape parameterSuccessSound parameterShape typeSuccessSound
          blockSuccessSound,
    expressionAtomCore_reject_ordinary_sound nested block nestedOrdinary
      nestedRejects parameterOrdinary parameterRejects typeOrdinary
        typeRejects blockRejects nestedSuccessSound nestedRejectSound
          parameterSuccessSound parameterRejectSound parameterShape
            typeSuccessSound typeRejectSound blockRejectSound⟩

/-- Lift deterministic subordinate outcomes through the executable Core-atom
dispatcher relations. -/
theorem expressionAtomCore_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {parameterOrdinary : DeclarativeGrammar.Remainder → LambdaParameter →
      DeclarativeGrammar.Remainder → Prop}
    {parameterRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop}
    {blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects)
    (parameterOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      parameterOrdinary parameterRejects)
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects)
    (blockOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec blockOrdinary
      blockRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ExpressionAtomCoreOrdinaryParses nestedOrdinary
        parameterOrdinary typeOrdinary blockOrdinary)
      (DeclarativeGrammar.ExpressionAtomCoreRejects nestedOrdinary
        nestedRejects parameterOrdinary parameterRejects typeOrdinary
          typeRejects blockRejects) :=
  DeclarativeGrammar.expressionAtomCoreDeterministicOutcomeSpec
    nestedOutcomes parameterOutcomes typeOutcomes blockOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
