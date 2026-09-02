import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeFunctionParametersOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionSignatureOutcomeGrammar
import Solcore.Syntax.DeclarativeGenericParametersOutcomeProperties
import Solcore.Syntax.DeclarativeReturnClauseOutcomeProperties
import Solcore.Syntax.DeclarativeWhereClauseOutcomeProperties

/-!
Functionality and rejection exclusivity for ordinary named-function signature
outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- One prioritized optional modifier has one final remainder. -/
theorem OptionalFunctionModifierParses.output_unique
    {keyword : HardKeyword} {input : Remainder}
    {left right : Option SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : OptionalFunctionModifierParses keyword input left afterLeft)
    (rightParsed : OptionalFunctionModifierParses keyword input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightToken =>
          exact False.elim (absent_conflicts_exact leftAbsent rightToken)
  | present leftSpan leftToken =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
      | present rightSpan rightToken =>
          exact exactToken_output_unique leftToken rightToken

/-- Fixed-order optional function modifiers have one final remainder. -/
theorem FunctionModifiersParses.output_unique
    {input : Remainder} {left right : Syntax.FunctionModifiers}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionModifiersParses input left afterLeft)
    (rightParsed : FunctionModifiersParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftAfterPublic, leftPublic, leftPayable⟩
  rcases rightParsed with
    ⟨rightAfterPublic, rightPublic, rightPayable⟩
  have afterPublicEq := leftPublic.output_unique rightPublic
  subst afterPublicEq
  exact leftPayable.output_unique rightPayable

/-- Ordinary function-signature success has one final remainder. -/
theorem FunctionSignatureOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.FunctionSignature}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionSignatureOrdinaryParses input left afterLeft)
    (rightParsed : FunctionSignatureOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftKeywordSpan leftKeyword leftName leftGenerics leftParameters
        leftModifiers leftReturns leftWhere =>
      cases rightParsed with
      | parsed rightKeywordSpan rightKeyword rightName rightGenerics
            rightParameters rightModifiers rightReturns rightWhere =>
          have afterKeywordEq := exactToken_output_unique leftKeyword
            rightKeyword
          subst afterKeywordEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          have afterGenericsEq := leftGenerics.output_unique rightGenerics
          subst afterGenericsEq
          have afterParametersEq := leftParameters.output_unique
            rightParameters
          subst afterParametersEq
          have afterModifiersEq := leftModifiers.output_unique rightModifiers
          subst afterModifiersEq
          have afterReturnsEq := leftReturns.output_unique rightReturns
          subst afterReturnsEq
          exact leftWhere.output_unique rightWhere

/-- Exact first-stage signature rejection excludes every ordinary success. -/
theorem FunctionSignatureRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : FunctionSignatureRejects input rejected) :
    ¬ ∃ signature output,
      FunctionSignatureOrdinaryParses input signature output := by
  rintro ⟨signature, output, successful⟩
  cases successful with
  | parsed successfulKeywordSpan successfulKeyword successfulName
        successfulGenerics successfulParameters successfulModifiers
        successfulReturns successfulWhere =>
      cases rejection with
      | keywordMissing keywordAbsent =>
          exact absent_conflicts_exact keywordAbsent successfulKeyword
      | nameRejected rejectedKeywordSpan rejectedKeyword nameRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | genericsRejected rejectedKeywordSpan rejectedKeyword rejectedName
            genericsRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          exact optionalGenericParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint genericsRejected
              ⟨_, _, successfulGenerics⟩
      | parametersRejected rejectedKeywordSpan rejectedKeyword rejectedName
            rejectedGenerics parametersRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          exact functionParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint parametersRejected
              ⟨_, _, successfulParameters⟩
      | returnsRejected rejectedKeywordSpan rejectedKeyword rejectedName
            rejectedGenerics rejectedParameters rejectedModifiers
            returnsRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterModifiersEq := rejectedModifiers.output_unique
            successfulModifiers
          subst afterModifiersEq
          exact optionalReturnClauseDeterministicOutcomeSpec
            |>.successRejectDisjoint returnsRejected
              ⟨_, _, successfulReturns⟩
      | whereRejected rejectedKeywordSpan rejectedKeyword rejectedName
            rejectedGenerics rejectedParameters rejectedModifiers
            rejectedReturns whereRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterModifiersEq := rejectedModifiers.output_unique
            successfulModifiers
          subst afterModifiersEq
          have afterReturnsEq := rejectedReturns.output_unique
            successfulReturns
          subst afterReturnsEq
          exact optionalWhereClauseDeterministicOutcomeSpec
            |>.successRejectDisjoint whereRejected ⟨_, _, successfulWhere⟩

/-- Complete named-function signatures have deterministic and exclusive
ordinary outcomes. -/
theorem functionSignatureDeterministicOutcomeSpec :
    DeterministicOutcomeSpec FunctionSignatureOrdinaryParses
      FunctionSignatureRejects where
  successOutputUnique := FunctionSignatureOrdinaryParses.output_unique
  successRejectDisjoint := FunctionSignatureRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
