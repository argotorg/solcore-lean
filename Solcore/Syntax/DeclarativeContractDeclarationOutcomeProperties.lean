import Solcore.Syntax.DeclarativeContractBodyOutcomeProperties
import Solcore.Syntax.DeclarativeContractDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeGenericParametersOutcomeProperties

/-! Deterministic exact ordinary outcomes for contract declarations. -/

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

private theorem contractBody_output_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMembers rightMembers : List Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractBodyOrdinaryParses input leftSpan leftMembers
      afterLeft)
    (rightParsed : ContractBodyOrdinaryParses input rightSpan rightMembers
      afterRight) : afterLeft = afterRight :=
  contractBodyDeterministicOutcomeSpec.successOutputUnique
    (left := (leftSpan, leftMembers))
    (right := (rightSpan, rightMembers)) leftParsed rightParsed

private theorem contractBody_reject_disjoint
    {input rejected : Remainder} (rejection : ContractBodyRejects input rejected) :
    ¬ ∃ span members output,
      ContractBodyOrdinaryParses input span members output := by
  rintro ⟨span, members, output, parsed⟩
  exact contractBodyDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨(span, members), output, parsed⟩

/-- Broad contract-declaration success has one final remainder. -/
theorem ContractDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ContractDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractDeclOrdinaryParses input left afterLeft)
    (rightParsed : ContractDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftGenerics leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightGenerics rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          cases afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          cases afterNameEq
          have afterGenericsEq := leftGenerics.output_unique rightGenerics
          cases afterGenericsEq
          exact contractBody_output_unique leftBody rightBody

/-- Exact contract-declaration rejection excludes every broad success. -/
theorem ContractDeclRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : ContractDeclRejects input rejected) :
    ¬ ∃ declaration output,
      ContractDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulName
        successfulGenerics successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | nameRejected rejectedMarkerSpan rejectedMarker nameRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | genericsRejected rejectedMarkerSpan rejectedMarker rejectedName
            genericsRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          cases afterNameEq
          exact optionalGenericParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint genericsRejected
              ⟨_, _, successfulGenerics⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedGenerics bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          cases afterNameEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          cases afterGenericsEq
          exact contractBody_reject_disjoint bodyRejected
            ⟨_, _, _, successfulBody⟩

/-- Contract declarations have deterministic and exclusive broad outcomes. -/
theorem contractDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ContractDeclOrdinaryParses ContractDeclRejects where
  successOutputUnique := ContractDeclOrdinaryParses.output_unique
  successRejectDisjoint := ContractDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
