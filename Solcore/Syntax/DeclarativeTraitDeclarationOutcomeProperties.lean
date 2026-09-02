import Solcore.Syntax.DeclarativeGenericParametersOutcomeProperties
import Solcore.Syntax.DeclarativeTraitBodyOutcomeProperties
import Solcore.Syntax.DeclarativeTraitDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeWhereClauseOutcomeProperties

/-! Deterministic exact ordinary outcomes for complete trait declarations. -/

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

private theorem traitBody_output_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMethods rightMethods : List Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitBodyOrdinaryParses input leftSpan leftMethods afterLeft)
    (rightParsed : TraitBodyOrdinaryParses input rightSpan rightMethods
      afterRight) : afterLeft = afterRight :=
  traitBodyDeterministicOutcomeSpec.successOutputUnique
    (left := (leftSpan, leftMethods))
    (right := (rightSpan, rightMethods)) leftParsed rightParsed

private theorem traitBody_reject_disjoint
    {input rejected : Remainder} (rejection : TraitBodyRejects input rejected) :
    ¬ ∃ span methods output,
      TraitBodyOrdinaryParses input span methods output := by
  rintro ⟨span, methods, output, parsed⟩
  exact traitBodyDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨(span, methods), output, parsed⟩

/-- Ordinary trait-declaration success has one final remainder. -/
theorem TraitDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.TraitDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitDeclOrdinaryParses input left afterLeft)
    (rightParsed : TraitDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftGenerics leftWhere
        leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightGenerics rightWhere
            rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          have afterGenericsEq := leftGenerics.output_unique rightGenerics
          subst afterGenericsEq
          have afterWhereEq := leftWhere.output_unique rightWhere
          subst afterWhereEq
          exact traitBody_output_unique leftBody rightBody

/-- Exact trait-declaration rejection excludes every ordinary success. -/
theorem TraitDeclRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : TraitDeclRejects input rejected) :
    ¬ ∃ declaration output,
      TraitDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulName
        successfulGenerics successfulWhere successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | nameRejected rejectedMarkerSpan rejectedMarker nameRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | genericsRejected rejectedMarkerSpan rejectedMarker rejectedName
            genericsRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact genericParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint genericsRejected
              ⟨_, _, successfulGenerics⟩
      | whereRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedGenerics whereRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          exact optionalWhereClauseDeterministicOutcomeSpec
            |>.successRejectDisjoint whereRejected ⟨_, _, successfulWhere⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedGenerics rejectedWhere bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          have afterWhereEq := rejectedWhere.output_unique successfulWhere
          subst afterWhereEq
          exact traitBody_reject_disjoint bodyRejected
            ⟨_, _, _, successfulBody⟩

/-- Trait declarations have deterministic and exclusive ordinary outcomes. -/
theorem traitDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TraitDeclOrdinaryParses TraitDeclRejects where
  successOutputUnique := TraitDeclOrdinaryParses.output_unique
  successRejectDisjoint := TraitDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
