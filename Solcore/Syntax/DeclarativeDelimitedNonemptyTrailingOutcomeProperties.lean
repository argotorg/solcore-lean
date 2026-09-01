import Solcore.Syntax.DeclarativeDelimitedTailRejectionProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingSuccessProperties

/-!
Diagnostic-inclusive deterministic outcomes for nonempty comma-separated lists
that allow a trailing comma.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- A required allow-trailing list rejection excludes every nonempty
allow-trailing success. -/
theorem DelimitedListRejects.disjointNonemptyTrailing {alpha : Type}
    {opening closing : Symbol}
    {ordinaryParses cleanParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input rejectedOutput : Remainder}
    (rejected : DelimitedListRejects opening closing false true
      ordinaryParses nestedRejects input rejectedOutput) :
    ¬ ∃ values output,
      NonemptyTrailingDelimitedListParses opening closing cleanParses input
        values output := by
  intro successful
  rcases successful with ⟨values, output, openingSpan, first, afterFirst,
    rest, closingSpan, tokensEq, endIndexEq, openingToken, firstParsed,
    progress, tail, elementsEq, spanEq⟩
  cases rejected with
  | openingMissing openingAbsent =>
      exact absent_conflicts_token openingAbsent openingToken
  | firstRejected rejectedOpeningSpan rejectedOpening continues
        nestedRejected =>
      cases continues
      exact outcomes.successRejectDisjoint nestedRejected
        ⟨_, _, cleanToOrdinary firstParsed⟩
  | tailRejected rejectedOpeningSpan rejectedOpening continues ordinaryFirst
        rejectedProgress tailRejected =>
      cases continues
      have cleanFirst := cleanToOrdinary firstParsed
      have afterFirstEq := outcomes.successOutputUnique ordinaryFirst cleanFirst
      subst afterFirstEq
      exact tailRejected.disjointTrailing outcomes cleanToOrdinary
        ⟨_, _, _, tail⟩

end Solcore.Syntax.DeclarativeGrammar
