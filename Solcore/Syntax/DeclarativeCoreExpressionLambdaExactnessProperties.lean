import Solcore.Syntax.DeclarativeCoreExpressionLambdaOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties

/-! Exact optional return types and complete Core lambda expression ASTs. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Arrow priority fixes the optional lambda return type and its exact AST. -/
theorem OptionalLambdaReturnTypeOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Option Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input left afterLeft)
    (rightParsed : OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present _ rightArrow _ => exact False.elim (leftAbsent ⟨_, rightArrow.1⟩)
  | present _ leftArrow leftType =>
      cases rightParsed with
      | absent rightAbsent => exact False.elim (rightAbsent ⟨_, leftArrow.1⟩)
      | present _ rightArrow rightType =>
          have outputEq := leftArrow.output_unique rightArrow
          subst outputEq
          exact congrArg some (outcomes.successValueUnique leftType rightType)

/-- Exact parameters, types, and bodies fix a lambda's complete AST and spans. -/
theorem LambdaExpressionOrdinaryParses.value_unique
    {parameterOrdinary : Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (parameterOutcomes : ExactDeterministicOutcomeSpec parameterOrdinary parameterRejects)
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : ExactDeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
      blockOrdinary input left afterLeft)
    (rightParsed : LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
      blockOrdinary input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftParameters leftReturn leftBody =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightParameters rightReturn rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases (trailingDelimitedListExactOutcomeSpec .leftParen .rightParen
            parameterOutcomes).successResultUnique leftParameters rightParameters with
            ⟨parametersEq, parametersOutputEq⟩
          subst parametersEq
          subst parametersOutputEq
          have returnEq := leftReturn.value_unique typeOutcomes rightReturn
          have returnOutputEq := leftReturn.output_unique typeOutcomes.toDeterministicOutcomeSpec rightReturn
          subst returnEq
          subst returnOutputEq
          cases blockOutcomes.successValueUnique leftBody rightBody
          rfl

/-- Exact lambda successes fix both the complete AST and final remainder. -/
theorem LambdaExpressionOrdinaryParses.result_unique
    {parameterOrdinary : Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (parameterOutcomes : ExactDeterministicOutcomeSpec parameterOrdinary parameterRejects)
    (typeOutcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : ExactDeterministicOutcomeSpec blockOrdinary blockRejects)
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
      blockOrdinary input left afterLeft)
    (rightParsed : LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
      blockOrdinary input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique parameterOutcomes typeOutcomes blockOutcomes rightParsed,
    leftParsed.output_unique parameterOutcomes.toDeterministicOutcomeSpec
      typeOutcomes.toDeterministicOutcomeSpec blockOutcomes.toDeterministicOutcomeSpec rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
