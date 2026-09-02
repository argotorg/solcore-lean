import Solcore.Syntax.DeclarativeGenericParametersOutcomeProperties
import Solcore.Syntax.DeclarativeImplBodyOutcomeProperties
import Solcore.Syntax.DeclarativeImplDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeImplDefaultMarkerOutcomeProperties
import Solcore.Syntax.DeclarativeImplHeadArgumentsOutcomeProperties
import Solcore.Syntax.DeclarativeWhereClauseOutcomeProperties

/-! Deterministic exact ordinary outcomes for implementation declarations. -/

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

private theorem implBody_output_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMethods rightMethods : List Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplBodyOrdinaryParses input leftSpan leftMethods afterLeft)
    (rightParsed : ImplBodyOrdinaryParses input rightSpan rightMethods
      afterRight) : afterLeft = afterRight :=
  implBodyDeterministicOutcomeSpec.successOutputUnique
    (left := (leftSpan, leftMethods))
    (right := (rightSpan, rightMethods)) leftParsed rightParsed

private theorem implBody_reject_disjoint
    {input rejected : Remainder} (rejection : ImplBodyRejects input rejected) :
    ¬ ∃ span methods output,
      ImplBodyOrdinaryParses input span methods output := by
  rintro ⟨span, methods, output, parsed⟩
  exact implBodyDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨(span, methods), output, parsed⟩

/-- Ordinary implementation-declaration success has one final remainder. -/
theorem ImplDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ImplDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplDeclOrdinaryParses input left afterLeft)
    (rightParsed : ImplDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftDefault leftMarkerSpan leftMarker leftGenerics leftName
        leftArguments leftWhere leftBody =>
      cases rightParsed with
      | parsed rightDefault rightMarkerSpan rightMarker rightGenerics
            rightName rightArguments rightWhere rightBody =>
          have afterDefaultEq := leftDefault.output_unique rightDefault
          subst afterDefaultEq
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterGenericsEq := leftGenerics.output_unique rightGenerics
          subst afterGenericsEq
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          have afterArgumentsEq := leftArguments.output_unique rightArguments
          subst afterArgumentsEq
          have afterWhereEq := leftWhere.output_unique rightWhere
          subst afterWhereEq
          exact implBody_output_unique leftBody rightBody

/-- Exact implementation-declaration rejection excludes every ordinary
success. -/
theorem ImplDeclRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : ImplDeclRejects input rejected) :
    ¬ ∃ declaration output,
      ImplDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulDefault successfulMarkerSpan successfulMarker
        successfulGenerics successfulName successfulArguments successfulWhere
        successfulBody =>
      cases rejection with
      | markerMissing rejectedDefault markerAbsent =>
          have afterDefaultEq := rejectedDefault.output_unique
            successfulDefault
          subst afterDefaultEq
          exact absent_conflicts_exact markerAbsent successfulMarker
      | genericsRejected rejectedDefault rejectedMarkerSpan rejectedMarker
            genericsRejected =>
          have afterDefaultEq := rejectedDefault.output_unique
            successfulDefault
          subst afterDefaultEq
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact optionalGenericParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint genericsRejected
              ⟨_, _, successfulGenerics⟩
      | nameRejected rejectedDefault rejectedMarkerSpan rejectedMarker
            rejectedGenerics nameRejected =>
          have afterDefaultEq := rejectedDefault.output_unique
            successfulDefault
          subst afterDefaultEq
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | argumentsRejected rejectedDefault rejectedMarkerSpan rejectedMarker
            rejectedGenerics rejectedName argumentsRejected =>
          have afterDefaultEq := rejectedDefault.output_unique
            successfulDefault
          subst afterDefaultEq
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact implHeadArgumentsDeterministicOutcomeSpec
            |>.successRejectDisjoint argumentsRejected
              ⟨_, _, successfulArguments⟩
      | whereRejected rejectedDefault rejectedMarkerSpan rejectedMarker
            rejectedGenerics rejectedName rejectedArguments whereRejected =>
          have afterDefaultEq := rejectedDefault.output_unique
            successfulDefault
          subst afterDefaultEq
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterArgumentsEq := rejectedArguments.output_unique
            successfulArguments
          subst afterArgumentsEq
          exact optionalWhereClauseDeterministicOutcomeSpec
            |>.successRejectDisjoint whereRejected ⟨_, _, successfulWhere⟩
      | bodyRejected rejectedDefault rejectedMarkerSpan rejectedMarker
            rejectedGenerics rejectedName rejectedArguments rejectedWhere
            bodyRejected =>
          have afterDefaultEq := rejectedDefault.output_unique
            successfulDefault
          subst afterDefaultEq
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterGenericsEq := rejectedGenerics.output_unique
            successfulGenerics
          subst afterGenericsEq
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterArgumentsEq := rejectedArguments.output_unique
            successfulArguments
          subst afterArgumentsEq
          have afterWhereEq := rejectedWhere.output_unique successfulWhere
          subst afterWhereEq
          exact implBody_reject_disjoint bodyRejected
            ⟨_, _, _, successfulBody⟩

/-- Implementation declarations have deterministic and exclusive broad
ordinary outcomes. -/
theorem implDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ImplDeclOrdinaryParses ImplDeclRejects where
  successOutputUnique := ImplDeclOrdinaryParses.output_unique
  successRejectDisjoint := ImplDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
