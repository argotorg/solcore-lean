import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeFallbackDeclarationOutcomeGrammar

/-! Deterministic exact ordinary outcomes for canonical fallback declarations. -/

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

/-- Pure fallback-parameter validation has one final remainder. -/
theorem FallbackParameterValidationOrdinaryParses.output_unique
    {parameters : DelimitedList Syntax.FunctionParameter}
    {input afterLeft afterRight : Remainder}
    (leftParsed : FallbackParameterValidationOrdinaryParses parameters input
      afterLeft)
    (rightParsed : FallbackParameterValidationOrdinaryParses parameters input
      afterRight) : afterLeft = afterRight := by
  cases leftParsed <;> cases rightParsed <;> rfl

/-- Pure fallback-parameter validation leaves its input remainder unchanged. -/
theorem FallbackParameterValidationOrdinaryParses.output_eq_input
    {parameters : DelimitedList Syntax.FunctionParameter}
    {input output : Remainder}
    (parsed : FallbackParameterValidationOrdinaryParses parameters input
      output) : output = input := by
  cases parsed <;> rfl

/-- Ordinary fallback success has one final remainder. -/
theorem FallbackDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.FallbackDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FallbackDeclOrdinaryParses input left afterLeft)
    (rightParsed : FallbackDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftParameters leftValidation
        leftModifiers leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightParameters rightValidation
            rightModifiers rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterParametersEq := leftParameters.output_unique
            rightParameters
          subst afterParametersEq
          have afterValidationEq : _ := leftValidation.output_eq_input.trans
            rightValidation.output_eq_input.symm
          subst afterValidationEq
          have afterModifiersEq := leftModifiers.output_unique rightModifiers
          subst afterModifiersEq
          exact (isolatedCoreBlockPublicOutcomeSpec .require)
            |>.successOutputUnique leftBody rightBody

/-- Exact fallback rejection excludes every ordinary fallback success. -/
theorem FallbackDeclRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : FallbackDeclRejects input rejected) :
    ¬ ∃ declaration output,
      FallbackDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulParameters
        successfulValidation successfulModifiers successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | parametersRejected rejectedMarkerSpan rejectedMarker
            parametersRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact functionParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint parametersRejected
              ⟨_, _, successfulParameters⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedParameters
            rejectedValidation rejectedModifiers bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterValidationEq : _ := rejectedValidation.output_eq_input.trans
            successfulValidation.output_eq_input.symm
          subst afterValidationEq
          have afterModifiersEq := rejectedModifiers.output_unique
            successfulModifiers
          subst afterModifiersEq
          exact (isolatedCoreBlockPublicOutcomeSpec .require)
            |>.successRejectDisjoint bodyRejected ⟨_, _, successfulBody⟩

/-- Canonical fallback declarations have deterministic and exclusive ordinary
outcomes. -/
theorem fallbackDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec FallbackDeclOrdinaryParses
      FallbackDeclRejects where
  successOutputUnique := FallbackDeclOrdinaryParses.output_unique
  successRejectDisjoint := FallbackDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
