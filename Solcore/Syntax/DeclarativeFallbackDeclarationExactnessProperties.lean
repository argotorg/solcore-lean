import Solcore.Syntax.DeclarativeContractEntryModifierExactnessProperties
import Solcore.Syntax.DeclarativeCoreBlockIsolationExactnessProperties
import Solcore.Syntax.DeclarativeFallbackDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionParametersExactnessProperties

/-!
Exactness transport through broad fallback declarations.

The sole remaining premise is an exact isolated `.require` Core body.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem fallback_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Fallback success has one exact AST whenever its isolated body has exact
outcomes. -/
theorem FallbackDeclOrdinaryParses.value_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input : Remainder} {left right : Syntax.FallbackDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FallbackDeclOrdinaryParses input left afterLeft)
    (rightParsed : FallbackDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftParameters leftValidation
        leftModifiers leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightParameters rightValidation
            rightModifiers rightBody =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          cases markerSpanEq
          cases afterMarkerEq
          rcases functionParametersExactOutcomeSpec.successResultUnique
              leftParameters rightParameters with
            ⟨parametersEq, afterParametersEq⟩
          cases parametersEq
          cases afterParametersEq
          have afterValidationEq : _ := leftValidation.output_eq_input.trans
            rightValidation.output_eq_input.symm
          cases afterValidationEq
          rcases leftModifiers.result_unique rightModifiers with
            ⟨payableEq, afterModifiersEq⟩
          cases payableEq
          cases afterModifiersEq
          rcases bodyOutcomes.successResultUnique leftBody rightBody with
            ⟨bodyEq, afterBodyEq⟩
          cases bodyEq
          rfl

/-- Under an exact body contract, fallback success fixes its AST and final
remainder. -/
theorem FallbackDeclOrdinaryParses.result_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input : Remainder} {left right : Syntax.FallbackDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FallbackDeclOrdinaryParses input left afterLeft)
    (rightParsed : FallbackDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_exact_body bodyOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Fallback rejection has one endpoint whenever its isolated body has exact
outcomes. -/
theorem FallbackDeclRejects.output_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    {input left right : Remainder}
    (leftRejected : FallbackDeclRejects input left)
    (rightRejected : FallbackDeclRejects input right) : left = right := by
  cases leftRejected with
  | markerMissing leftMarkerAbsent =>
      cases rightRejected with
      | markerMissing => rfl
      | parametersRejected rightMarkerSpan rightMarker rightParameters =>
          exact False.elim
            (fallback_absent_conflicts_exact leftMarkerAbsent rightMarker)
      | bodyRejected rightMarkerSpan rightMarker rightParameters
          rightValidation rightModifiers rightBody =>
          exact False.elim
            (fallback_absent_conflicts_exact leftMarkerAbsent rightMarker)
  | parametersRejected leftMarkerSpan leftMarker leftParameters =>
      cases rightRejected with
      | markerMissing rightMarkerAbsent =>
          exact False.elim
            (fallback_absent_conflicts_exact rightMarkerAbsent leftMarker)
      | parametersRejected rightMarkerSpan rightMarker rightParameters =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          exact functionParametersExactOutcomeSpec.rejectOutputUnique
            leftParameters rightParameters
      | bodyRejected rightMarkerSpan rightMarker rightParameters
          rightValidation rightModifiers rightBody =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          exact False.elim
            (functionParametersExactOutcomeSpec.successRejectDisjoint
              leftParameters ⟨_, _, rightParameters⟩)
  | bodyRejected leftMarkerSpan leftMarker leftParameters leftValidation
      leftModifiers leftBody =>
      cases rightRejected with
      | markerMissing rightMarkerAbsent =>
          exact False.elim
            (fallback_absent_conflicts_exact rightMarkerAbsent leftMarker)
      | parametersRejected rightMarkerSpan rightMarker rightParameters =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          exact False.elim
            (functionParametersExactOutcomeSpec.successRejectDisjoint
              rightParameters ⟨_, _, leftParameters⟩)
      | bodyRejected rightMarkerSpan rightMarker rightParameters
          rightValidation rightModifiers rightBody =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          cases afterMarkerEq
          have afterParametersEq :=
            functionParametersExactOutcomeSpec.successOutputUnique
              leftParameters rightParameters
          cases afterParametersEq
          have afterValidationEq : _ := leftValidation.output_eq_input.trans
            rightValidation.output_eq_input.symm
          cases afterValidationEq
          have afterModifiersEq := leftModifiers.output_unique rightModifiers
          cases afterModifiersEq
          exact bodyOutcomes.rejectOutputUnique leftBody rightBody

/-- An exact isolated required body lifts to fully exact fallback declaration
outcomes. -/
theorem fallbackDeclExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require)) :
    ExactDeterministicOutcomeSpec FallbackDeclOrdinaryParses
      FallbackDeclRejects where
  toDeterministicOutcomeSpec := fallbackDeclDeterministicOutcomeSpec
  successValueUnique :=
    FallbackDeclOrdinaryParses.value_unique_of_exact_body bodyOutcomes
  rejectOutputUnique :=
    FallbackDeclRejects.output_unique_of_exact_body bodyOutcomes

/-- Fixed-fuel Core-statement exactness supplies the isolated body contract
needed for fully exact fallback declarations. -/
theorem fallbackDeclExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec FallbackDeclOrdinaryParses
      FallbackDeclRejects :=
  fallbackDeclExactOutcomeSpecOfBody
    (isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes
      .require)

end Solcore.Syntax.DeclarativeGrammar
