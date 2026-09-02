import Solcore.Syntax.DeclarativeTypeAliasParametersOutcomeProperties
import Solcore.Syntax.DeclarativeTypeAliasValueOutcomeProperties

/-! Deterministic exact ordinary outcomes for complete type-alias declarations. -/

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

/-- Ordinary complete type-alias success has one final remainder. -/
theorem TypeAliasDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.TypeAliasDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasDeclOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftKeywordSpan leftEqualSpan leftSemicolonSpan leftKeyword leftName
        leftParameters leftEqual leftValue leftSemicolon =>
      cases rightParsed with
      | parsed rightKeywordSpan rightEqualSpan rightSemicolonSpan rightKeyword
            rightName rightParameters rightEqual rightValue rightSemicolon =>
          have afterKeywordEq := exactToken_output_unique leftKeyword
            rightKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          have afterParametersEq := leftParameters.output_unique rightParameters
          subst afterParametersEq
          have afterEqualEq := exactToken_output_unique leftEqual rightEqual
          subst afterEqualEq
          have afterValueEq := leftValue.output_unique rightValue
          subst afterValueEq
          exact exactToken_output_unique leftSemicolon rightSemicolon

/-- Exact complete type-alias rejection excludes every ordinary success. -/
theorem TypeAliasDeclRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : TypeAliasDeclRejects input rejected) :
    ¬ ∃ declaration output,
      TypeAliasDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulKeywordSpan successfulEqualSpan successfulSemicolonSpan
        successfulKeyword successfulName successfulParameters successfulEqual
        successfulValue successfulSemicolon =>
      cases rejection with
      | keywordMissing keywordAbsent =>
          exact absent_conflicts_exact keywordAbsent successfulKeyword
      | nameRejected rejectedKeywordSpan rejectedKeyword nameRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | parametersRejected rejectedKeywordSpan rejectedKeyword rejectedName
            parametersRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact optionalTypeAliasParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint parametersRejected
              ⟨_, _, successfulParameters⟩
      | equalMissing rejectedKeywordSpan rejectedKeyword rejectedName
            rejectedParameters equalAbsent =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          exact absent_conflicts_exact equalAbsent successfulEqual
      | valueRejected rejectedKeywordSpan rejectedEqualSpan rejectedKeyword
            rejectedName rejectedParameters rejectedEqual valueRejected =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterEqualEq := exactToken_output_unique rejectedEqual
            successfulEqual
          subst afterEqualEq
          exact typeAliasValueDeterministicOutcomeSpec
            |>.successRejectDisjoint valueRejected ⟨_, _, successfulValue⟩
      | semicolonMissing rejectedKeywordSpan rejectedEqualSpan rejectedKeyword
            rejectedName rejectedParameters rejectedEqual rejectedValue
            semicolonAbsent =>
          have afterKeywordEq := exactToken_output_unique rejectedKeyword
            successfulKeyword
          subst afterKeywordEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterEqualEq := exactToken_output_unique rejectedEqual
            successfulEqual
          subst afterEqualEq
          have afterValueEq := rejectedValue.output_unique successfulValue
          subst afterValueEq
          exact absent_conflicts_exact semicolonAbsent successfulSemicolon

/-- Complete broad type aliases have deterministic and exclusive ordinary
outcomes. -/
theorem typeAliasDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TypeAliasDeclOrdinaryParses
      TypeAliasDeclRejects where
  successOutputUnique := TypeAliasDeclOrdinaryParses.output_unique
  successRejectDisjoint := TypeAliasDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
