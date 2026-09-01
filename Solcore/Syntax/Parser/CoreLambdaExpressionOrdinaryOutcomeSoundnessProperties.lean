import Solcore.Syntax.Parser.CoreLambdaExpressionOrdinaryRejectionSoundnessProperties

/-! Composed executable ordinary outcomes for guarded Core lambdas. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Package unconditional lambda success with rejection under the atom
dispatcher's positive lambda-keyword guard. -/
theorem lambdaExpression_guardedOrdinaryOutcome_sound
    (block : Parser Block)
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
      lambdaExpression block input = .ok expression output →
        DeclarativeGrammar.LambdaExpressionOrdinaryParses
          parameterOrdinary typeOrdinary blockOrdinary
            input.declarativeRemainder expression
              output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isKeyword input .lamKw = true →
        lambdaExpression block input = .reject failure rejected →
          DeclarativeGrammar.LambdaExpressionRejects parameterOrdinary
            parameterRejects typeOrdinary typeRejects blockRejects
              input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨lambdaExpression_success_ordinary_sound block parameterOrdinary
      typeOrdinary blockOrdinary parameterSuccessSound parameterShape
        typeSuccessSound blockSuccessSound,
    lambdaExpression_reject_ordinary_sound block parameterOrdinary
      parameterRejects typeOrdinary typeRejects blockRejects
        parameterSuccessSound parameterRejectSound parameterShape
          typeSuccessSound typeRejectSound blockRejectSound⟩

/-- Lift deterministic subordinate outcomes to the guarded lambda branch. -/
theorem lambdaExpression_ordinaryOutcomeSpec
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
    (parameterOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      parameterOrdinary parameterRejects)
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects)
    (blockOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec blockOrdinary
      blockRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LambdaExpressionOrdinaryParses parameterOrdinary
        typeOrdinary blockOrdinary)
      (DeclarativeGrammar.LambdaExpressionRejects parameterOrdinary
        parameterRejects typeOrdinary typeRejects blockRejects) :=
  DeclarativeGrammar.lambdaExpressionDeterministicOutcomeSpec
    parameterOutcomes typeOutcomes blockOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
