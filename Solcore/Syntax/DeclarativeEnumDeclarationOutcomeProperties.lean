import Solcore.Syntax.DeclarativeEnumBodyOutcomeProperties
import Solcore.Syntax.DeclarativeEnumDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeGenericParametersOutcomeProperties

/-! Deterministic exact ordinary outcomes for complete enum declarations. -/

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

private theorem enumBody_output_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftConstructors rightConstructors : List Syntax.EnumConstructor}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumBodyOrdinaryParses input leftSpan leftConstructors
      afterLeft)
    (rightParsed : EnumBodyOrdinaryParses input rightSpan rightConstructors
      afterRight) : afterLeft = afterRight :=
  enumBodyDeterministicOutcomeSpec.successOutputUnique
    (left := (leftSpan, leftConstructors))
    (right := (rightSpan, rightConstructors)) leftParsed rightParsed

private theorem enumBody_reject_disjoint
    {input rejected : Remainder} (rejection : EnumBodyRejects input rejected) :
    ¬ ∃ span constructors output,
      EnumBodyOrdinaryParses input span constructors output := by
  rintro ⟨span, constructors, output, parsed⟩
  exact enumBodyDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨(span, constructors), output, parsed⟩

/-- Ordinary enum-declaration success has one final remainder. -/
theorem EnumDeclOrdinaryParses.output_unique
    (deriveAttribute : Option Syntax.DeriveAttribute)
    {input : Remainder} {left right : Syntax.EnumDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumDeclOrdinaryParses deriveAttribute input left afterLeft)
    (rightParsed : EnumDeclOrdinaryParses deriveAttribute input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftParameters leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightParameters
            rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          have afterParametersEq := leftParameters.output_unique
            rightParameters
          subst afterParametersEq
          exact enumBody_output_unique leftBody rightBody

/-- Exact enum-declaration rejection excludes every ordinary success. -/
theorem EnumDeclRejects.disjointOrdinary
    (deriveAttribute : Option Syntax.DeriveAttribute)
    {input rejected : Remainder}
    (rejection : EnumDeclRejects input rejected) :
    ¬ ∃ declaration output,
      EnumDeclOrdinaryParses deriveAttribute input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulName
        successfulParameters successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | nameRejected rejectedMarkerSpan rejectedMarker nameRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | parametersRejected rejectedMarkerSpan rejectedMarker rejectedName
            parametersRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact optionalGenericParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint parametersRejected
              ⟨_, _, successfulParameters⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedParameters bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          exact enumBody_reject_disjoint bodyRejected
            ⟨_, _, _, successfulBody⟩

/-- Enum declarations have deterministic and exclusive ordinary outcomes. -/
theorem enumDeclDeterministicOutcomeSpec
    (deriveAttribute : Option Syntax.DeriveAttribute) :
    DeterministicOutcomeSpec (EnumDeclOrdinaryParses deriveAttribute)
      EnumDeclRejects where
  successOutputUnique := EnumDeclOrdinaryParses.output_unique deriveAttribute
  successRejectDisjoint := EnumDeclRejects.disjointOrdinary deriveAttribute

end Solcore.Syntax.DeclarativeGrammar
