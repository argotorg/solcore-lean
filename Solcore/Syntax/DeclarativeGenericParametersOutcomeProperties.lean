import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeDelimitedNonemptyTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeGenericParametersOutcomeGrammar

/-! Deterministic exact outcomes for canonical generic parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem GenericParametersParses.opening_present
    {input output : Remainder} {parameters : Syntax.GenericParameters}
    (parsed : GenericParametersParses input parameters output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .symbol .less
    } := by
  unfold GenericParametersParses at parsed
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact ⟨openingSpan, openingToken⟩

/-- A successful generic-parameter list has one final remainder. -/
theorem GenericParametersParses.output_unique
    {input : Remainder} {left right : Syntax.GenericParameters}
    {afterLeft afterRight : Remainder}
    (leftParsed : GenericParametersParses input left afterLeft)
    (rightParsed : GenericParametersParses input right afterRight) :
    afterLeft = afterRight := by
  unfold GenericParametersParses at leftParsed rightParsed
  exact NonemptyTrailingDelimitedListParses.output_unique
    (opening := .less) (closing := .greater)
    (elementParses := IdentifierParses) IdentifierParses.output_unique
    leftParsed rightParsed

/-- Exact generic-parameter rejection excludes every successful list. -/
theorem GenericParametersRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : GenericParametersRejects input rejected) :
    ¬ ∃ parameters output, GenericParametersParses input parameters output := by
  rintro ⟨parameters, output, parsed⟩
  exact rejection.disjointNonemptyTrailing identifierDeterministicOutcomeSpec
    (fun successful => successful) ⟨_, output, parsed⟩

/-- Required canonical generic parameters have deterministic and exclusive
ordinary outcomes. -/
theorem genericParametersDeterministicOutcomeSpec :
    DeterministicOutcomeSpec GenericParametersParses
      GenericParametersRejects where
  successOutputUnique := GenericParametersParses.output_unique
  successRejectDisjoint := GenericParametersRejects.disjointOrdinary

/-- Optional generic-parameter success has one final remainder. -/
theorem OptionalGenericParametersParses.output_unique
    {input : Remainder} {left right : Option Syntax.GenericParameters}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalGenericParametersParses input left afterLeft)
    (rightParsed : OptionalGenericParametersParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightParsed =>
          rcases rightParsed.opening_present with ⟨span, openingPresent⟩
          exact False.elim
            (absent_conflicts_token leftAbsent openingPresent)
  | present leftParsed =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases leftParsed.opening_present with ⟨span, openingPresent⟩
          exact False.elim
            (absent_conflicts_token rightAbsent openingPresent)
      | present rightParsed =>
          exact leftParsed.output_unique rightParsed

/-- Exact optional-generic rejection excludes absent and present success. -/
theorem OptionalGenericParametersRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalGenericParametersRejects input rejected) :
    ¬ ∃ parameters output,
      OptionalGenericParametersParses input parameters output := by
  rintro ⟨parameters, output, successful⟩
  cases rejection with
  | present openingPresent parametersRejected =>
      cases successful with
      | absent openingAbsent =>
          rcases openingPresent with ⟨span, openingToken⟩
          exact absent_conflicts_token openingAbsent openingToken
      | present parametersParsed =>
          exact genericParametersDeterministicOutcomeSpec.successRejectDisjoint
            parametersRejected ⟨_, _, parametersParsed⟩

/-- Optional canonical generic parameters have deterministic and exclusive
ordinary outcomes. -/
theorem optionalGenericParametersDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalGenericParametersParses
      OptionalGenericParametersRejects where
  successOutputUnique := OptionalGenericParametersParses.output_unique
  successRejectDisjoint := OptionalGenericParametersRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
