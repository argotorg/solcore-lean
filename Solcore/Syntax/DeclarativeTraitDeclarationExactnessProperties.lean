import Solcore.Syntax.DeclarativeGenericParametersExactnessProperties
import Solcore.Syntax.DeclarativeTraitBodyExactnessProperties
import Solcore.Syntax.DeclarativeTraitDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeWhereClauseExactnessProperties

/-! Exact values and rejection endpoints for complete trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem traitDecl_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A successful complete trait declaration fixes its AST. -/
theorem TraitDeclOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.TraitDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitDeclOrdinaryParses input left afterLeft)
    (rightParsed : TraitDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftGenerics leftWhere
      leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightGenerics rightWhere
          rightBody =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases genericParametersExactOutcomeSpec.successResultUnique
              leftGenerics rightGenerics with
            ⟨genericsEq, afterGenericsEq⟩
          subst genericsEq
          subst afterGenericsEq
          rcases optionalWhereClauseExactOutcomeSpec.successResultUnique
              leftWhere rightWhere with ⟨whereEq, afterWhereEq⟩
          subst whereEq
          subst afterWhereEq
          rcases leftBody.result_unique rightBody with
            ⟨bodySpanEq, methodsEq, afterBodyEq⟩
          subst bodySpanEq
          subst methodsEq
          rfl

/-- A successful complete trait declaration fixes its AST and remainder. -/
theorem TraitDeclOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.TraitDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitDeclOrdinaryParses input left afterLeft)
    (rightParsed : TraitDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The five-stage trait-declaration rejection sequence has one endpoint. -/
theorem TraitDeclRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TraitDeclRejects input left)
    (rightRejected : TraitDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 10) [traitDecl_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      genericParametersExactOutcomeSpec.successOutputUnique,
      genericParametersExactOutcomeSpec.successRejectDisjoint,
      genericParametersExactOutcomeSpec.rejectOutputUnique,
      optionalWhereClauseExactOutcomeSpec.successOutputUnique,
      optionalWhereClauseExactOutcomeSpec.successRejectDisjoint,
      optionalWhereClauseExactOutcomeSpec.rejectOutputUnique,
      traitBodyExactOutcomeSpec.successOutputUnique,
      traitBodyExactOutcomeSpec.successRejectDisjoint,
      traitBodyExactOutcomeSpec.rejectOutputUnique]

/-- Complete broad trait declarations have fully exact ordinary outcomes. -/
theorem traitDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TraitDeclOrdinaryParses TraitDeclRejects where
  toDeterministicOutcomeSpec := traitDeclDeterministicOutcomeSpec
  successValueUnique := TraitDeclOrdinaryParses.value_unique
  rejectOutputUnique := TraitDeclRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
