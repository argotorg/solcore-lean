import Solcore.Syntax.DeclarativeTypeAliasOutcomeProperties
import Solcore.Syntax.DeclarativeTypeAliasParametersExactnessProperties
import Solcore.Syntax.DeclarativeTypeAliasValueExactnessProperties

/-! Full exact outcomes for recovery-aware transparent type aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem typeAlias_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A complete type-alias success constructs one exact declaration AST. -/
theorem TypeAliasDeclOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.TypeAliasDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasDeclOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftKeywordSpan leftEqualSpan leftSemicolonSpan leftKeyword leftName
      leftParameters leftEqual leftValue leftSemicolon =>
      cases rightParsed with
      | parsed rightKeywordSpan rightEqualSpan rightSemicolonSpan rightKeyword
          rightName rightParameters rightEqual rightValue rightSemicolon =>
          rcases leftKeyword.result_unique rightKeyword with
            ⟨keywordSpanEq, afterKeywordEq⟩
          subst keywordSpanEq
          subst afterKeywordEq
          rcases leftName.result_unique rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases leftParameters.result_unique rightParameters with
            ⟨parametersEq, afterParametersEq⟩
          subst parametersEq
          subst afterParametersEq
          rcases leftEqual.result_unique rightEqual with
            ⟨equalSpanEq, afterEqualEq⟩
          subst equalSpanEq
          subst afterEqualEq
          rcases leftValue.result_unique rightValue with
            ⟨valueEq, afterValueEq⟩
          subst valueEq
          subst afterValueEq
          rcases leftSemicolon.result_unique rightSemicolon with
            ⟨semicolonSpanEq, afterSemicolonEq⟩
          subst semicolonSpanEq
          rfl

/-- A complete type-alias success fixes its AST and final remainder. -/
theorem TypeAliasDeclOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.TypeAliasDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasDeclOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The six-stage type-alias rejection sequence has one first failing
endpoint. -/
theorem TypeAliasDeclRejects.output_unique
    {input left right : Remainder}
    (leftRejects : TypeAliasDeclRejects input left)
    (rightRejects : TypeAliasDeclRejects input right) : left = right := by
  cases leftRejects <;> cases rightRejects <;>
    grind [typeAlias_absent_conflicts_exact, ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      optionalTypeAliasParametersExactOutcomeSpec.successOutputUnique,
      optionalTypeAliasParametersExactOutcomeSpec.successRejectDisjoint,
      optionalTypeAliasParametersExactOutcomeSpec.rejectOutputUnique,
      typeAliasValueExactOutcomeSpec.successOutputUnique,
      typeAliasValueExactOutcomeSpec.successRejectDisjoint,
      typeAliasValueExactOutcomeSpec.rejectOutputUnique]

/-- Transparent type aliases have fully exact broad ordinary outcomes. -/
theorem typeAliasDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TypeAliasDeclOrdinaryParses
      TypeAliasDeclRejects where
  toDeterministicOutcomeSpec := typeAliasDeclDeterministicOutcomeSpec
  successValueUnique := TypeAliasDeclOrdinaryParses.value_unique
  rejectOutputUnique := TypeAliasDeclRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
