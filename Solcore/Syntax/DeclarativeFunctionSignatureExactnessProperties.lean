import Solcore.Syntax.DeclarativeFunctionParametersExactnessProperties
import Solcore.Syntax.DeclarativeFunctionModifierExactnessProperties
import Solcore.Syntax.DeclarativeGenericParametersExactnessProperties
import Solcore.Syntax.DeclarativeReturnClauseExactnessProperties
import Solcore.Syntax.DeclarativeWhereClauseExactnessProperties

/-! Exact values and rejection endpoints for complete function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem signature_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- The fixed `public`-then-`payable` sequence fixes its modifier AST. -/
theorem FunctionModifiersParses.value_unique
    {input : Remainder} {left right : Syntax.FunctionModifiers}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionModifiersParses input left afterLeft)
    (rightParsed : FunctionModifiersParses input right afterRight) :
    left = right := by
  cases left
  cases right
  simp_all only [FunctionModifiersParses]
  rcases leftParsed with ⟨leftAfterPublic, leftPublic, leftPayable⟩
  rcases rightParsed with ⟨rightAfterPublic, rightPublic, rightPayable⟩
  rcases leftPublic.result_unique rightPublic with
    ⟨publicEq, afterPublicEq⟩
  subst publicEq
  subst afterPublicEq
  have payableEq := leftPayable.value_unique rightPayable
  subst payableEq
  rfl

/-- The fixed modifier sequence fixes its AST and final remainder. -/
theorem FunctionModifiersParses.result_unique
    {input : Remainder} {left right : Syntax.FunctionModifiers}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionModifiersParses input left afterLeft)
    (rightParsed : FunctionModifiersParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A complete function-signature success fixes its AST. -/
theorem FunctionSignatureOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.FunctionSignature}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionSignatureOrdinaryParses input left afterLeft)
    (rightParsed : FunctionSignatureOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftKeywordSpan leftKeyword leftName leftGenerics leftParameters
      leftModifiers leftReturns leftWhere =>
      cases rightParsed with
      | parsed rightKeywordSpan rightKeyword rightName rightGenerics
          rightParameters rightModifiers rightReturns rightWhere =>
          rcases leftKeyword.result_unique rightKeyword with
            ⟨keywordSpanEq, afterKeywordEq⟩
          subst keywordSpanEq
          subst afterKeywordEq
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases optionalGenericParametersExactOutcomeSpec.successResultUnique
              leftGenerics rightGenerics with
            ⟨genericsEq, afterGenericsEq⟩
          subst genericsEq
          subst afterGenericsEq
          rcases functionParametersExactOutcomeSpec.successResultUnique
              leftParameters rightParameters with
            ⟨parametersEq, afterParametersEq⟩
          subst parametersEq
          subst afterParametersEq
          rcases leftModifiers.result_unique rightModifiers with
            ⟨modifiersEq, afterModifiersEq⟩
          subst modifiersEq
          subst afterModifiersEq
          rcases optionalReturnClauseExactOutcomeSpec.successResultUnique
              leftReturns rightReturns with
            ⟨returnsEq, afterReturnsEq⟩
          subst returnsEq
          subst afterReturnsEq
          have whereEq := optionalWhereClauseExactOutcomeSpec
            |>.successValueUnique leftWhere rightWhere
          subst whereEq
          rfl

/-- A complete function-signature success fixes its AST and final remainder. -/
theorem FunctionSignatureOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.FunctionSignature}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionSignatureOrdinaryParses input left afterLeft)
    (rightParsed : FunctionSignatureOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The six-stage function-signature rejection sequence has one endpoint. -/
theorem FunctionSignatureRejects.output_unique
    {input left right : Remainder}
    (leftRejected : FunctionSignatureRejects input left)
    (rightRejected : FunctionSignatureRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 10) [signature_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successRejectDisjoint,
      optionalGenericParametersExactOutcomeSpec.rejectOutputUnique,
      functionParametersExactOutcomeSpec.successOutputUnique,
      functionParametersExactOutcomeSpec.successRejectDisjoint,
      functionParametersExactOutcomeSpec.rejectOutputUnique,
      FunctionModifiersParses.output_unique,
      optionalReturnClauseExactOutcomeSpec.successOutputUnique,
      optionalReturnClauseExactOutcomeSpec.successRejectDisjoint,
      optionalReturnClauseExactOutcomeSpec.rejectOutputUnique,
      optionalWhereClauseExactOutcomeSpec.rejectOutputUnique]

/-- Complete recovery-aware function signatures have exact outcomes. -/
theorem functionSignatureExactOutcomeSpec :
    ExactDeterministicOutcomeSpec FunctionSignatureOrdinaryParses
      FunctionSignatureRejects where
  toDeterministicOutcomeSpec := functionSignatureDeterministicOutcomeSpec
  successValueUnique := FunctionSignatureOrdinaryParses.value_unique
  rejectOutputUnique := FunctionSignatureRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
