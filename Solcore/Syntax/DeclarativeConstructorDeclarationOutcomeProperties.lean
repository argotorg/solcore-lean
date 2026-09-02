import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeFunctionParametersOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionSignatureOutcomeProperties

/-! Deterministic exact ordinary outcomes for canonical constructors. -/

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

/-- Fixed-order ordinary entry modifiers have one final remainder. -/
theorem ContractEntryModifiersOrdinaryParses.output_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractEntryModifiersOrdinaryParses input left afterLeft)
    (rightParsed : ContractEntryModifiersOrdinaryParses input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftPublic leftPayable =>
      cases rightParsed with
      | parsed rightPublic rightPayable =>
          have afterPublicEq := leftPublic.output_unique rightPublic
          subst afterPublicEq
          exact leftPayable.output_unique rightPayable

/-- Ordinary constructor success has one final remainder. -/
theorem ConstructorDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ConstructorDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorDeclOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftParameters leftModifiers leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightParameters rightModifiers
            rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterParametersEq := leftParameters.output_unique
            rightParameters
          subst afterParametersEq
          have afterModifiersEq := leftModifiers.output_unique rightModifiers
          subst afterModifiersEq
          exact (isolatedCoreBlockPublicOutcomeSpec .require)
            |>.successOutputUnique leftBody rightBody

/-- Exact constructor rejection excludes every ordinary constructor success. -/
theorem ConstructorDeclRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ConstructorDeclRejects input rejected) :
    ¬ ∃ declaration output,
      ConstructorDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulParameters
        successfulModifiers successfulBody =>
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
            rejectedModifiers bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterModifiersEq := rejectedModifiers.output_unique
            successfulModifiers
          subst afterModifiersEq
          exact (isolatedCoreBlockPublicOutcomeSpec .require)
            |>.successRejectDisjoint bodyRejected ⟨_, _, successfulBody⟩

/-- Canonical constructors have deterministic and exclusive ordinary
outcomes. -/
theorem constructorDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ConstructorDeclOrdinaryParses
      ConstructorDeclRejects where
  successOutputUnique := ConstructorDeclOrdinaryParses.output_unique
  successRejectDisjoint := ConstructorDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
