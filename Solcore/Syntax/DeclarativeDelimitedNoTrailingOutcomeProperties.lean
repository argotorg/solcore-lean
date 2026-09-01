import Solcore.Syntax.DeclarativeDelimitedNoTrailingSuccessProperties
import Solcore.Syntax.DeclarativeDelimitedTailRejectionProperties

/-!
Deterministic ordinary outcomes for possibly empty comma-separated lists that
forbid a trailing comma.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Exact rejection of an allow-empty, no-trailing list excludes every
ordinary success for the same deterministic element outcomes. -/
theorem DelimitedListRejects.disjointAllowEmptyNoTrailing {alpha : Type}
    {opening closing : Symbol}
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input rejected : Remainder}
    (rejection : DelimitedListRejects opening closing true false
      ordinaryParses nestedRejects input rejected) :
    ¬ ∃ values output,
      NoTrailingDelimitedListParses opening closing ordinaryParses input values
        output := by
  rintro ⟨values, output, successful⟩
  cases rejection with
  | openingMissing openingAbsent =>
      cases successful with
      | empty openingSpan closingSpan openingToken closingToken =>
          exact absent_conflicts_token openingAbsent openingToken
      | nonempty closingAbsent parsed =>
          rcases parsed with ⟨openingSpan, first, afterFirst, rest,
            closingSpan, tokensEq, endIndexEq, openingToken, firstParsed,
            progress, tail, elementsEq, spanEq⟩
          exact absent_conflicts_token openingAbsent openingToken
  | firstRejected openingSpan openingToken continues firstRejected =>
      cases continues with
      | absent closingAbsent =>
          cases successful with
          | empty successfulOpeningSpan closingSpan successfulOpening
                closingToken =>
              exact absent_conflicts_token closingAbsent closingToken
          | nonempty successfulClosingAbsent parsed =>
              rcases parsed with ⟨successfulOpeningSpan, first, afterFirst,
                rest, closingSpan, tokensEq, endIndexEq, successfulOpening,
                firstParsed, progress, tail, elementsEq, spanEq⟩
              exact outcomes.successRejectDisjoint firstRejected
                ⟨first, afterFirst, firstParsed⟩
  | tailRejected openingSpan openingToken continues firstParsed progress
        tailRejected =>
      cases continues with
      | absent closingAbsent =>
          cases successful with
          | empty successfulOpeningSpan closingSpan successfulOpening
                closingToken =>
              exact absent_conflicts_token closingAbsent closingToken
          | nonempty successfulClosingAbsent parsed =>
              rcases parsed with ⟨successfulOpeningSpan, successfulFirst,
                successfulAfterFirst, rest, closingSpan, tokensEq, endIndexEq,
                successfulOpening, successfulFirstParsed, successfulProgress,
                successfulTail, elementsEq, spanEq⟩
              have afterFirstEq := outcomes.successOutputUnique firstParsed
                successfulFirstParsed
              subst afterFirstEq
              exact tailRejected.disjointNoTrailing outcomes
                (fun parsed => parsed)
                ⟨rest, closingSpan, output, successfulTail⟩

/-- Construct the deterministic outcome contract for an allow-empty,
no-trailing delimited list. -/
theorem noTrailingDelimitedListDeterministicOutcomeSpec {alpha : Type}
    (opening closing : Symbol)
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects) :
    DeterministicOutcomeSpec
      (NoTrailingDelimitedListParses opening closing ordinaryParses)
      (DelimitedListRejects opening closing true false ordinaryParses
        nestedRejects) where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact NoTrailingDelimitedListParses.output_unique
      (opening := opening) (closing := closing)
      (elementParses := ordinaryParses) outcomes.successOutputUnique leftParsed
      rightParsed
  successRejectDisjoint :=
    DelimitedListRejects.disjointAllowEmptyNoTrailing outcomes

end Solcore.Syntax.DeclarativeGrammar
