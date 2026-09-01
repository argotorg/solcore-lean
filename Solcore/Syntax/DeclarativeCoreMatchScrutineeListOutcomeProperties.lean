import Solcore.Syntax.DeclarativeDelimitedTailRejectionProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingSuccessProperties

/-!
Diagnostic-inclusive deterministic outcomes for the parenthesized,
nonempty, trailing-comma Core match scrutinee list.
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

/-- Ordinary success of the exact Core match scrutinee list parser. -/
abbrev MatchScrutineeListOrdinaryParses
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop) :=
  NonemptyTrailingDelimitedListParses .leftParen .rightParen
    expressionOrdinary

/-- Exact rejection of the required, allow-trailing scrutinee list. -/
abbrev MatchScrutineeListRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :=
  DelimitedListRejects .leftParen .rightParen false true
    expressionOrdinary expressionRejects

/-- Ordinary Core match scrutinee-list success has one final remainder. -/
theorem MatchScrutineeListOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : DelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      left afterLeft)
    (rightParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      right afterRight) : afterLeft = afterRight :=
  NonemptyTrailingDelimitedListParses.output_unique
    (opening := .leftParen) (closing := .rightParen)
    (elementParses := expressionOrdinary)
    expressionOutcomes.successOutputUnique leftParsed rightParsed

/-- Exact scrutinee-list rejection excludes ordinary success. -/
theorem MatchScrutineeListRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : MatchScrutineeListRejects expressionOrdinary
      expressionRejects input rejected) :
    ¬ ∃ values output,
      MatchScrutineeListOrdinaryParses expressionOrdinary input values
        output :=
  rejection.disjointNonemptyTrailing expressionOutcomes
    (fun parsed => parsed)

/-- Lift expression outcomes through the Core match scrutinee list. -/
theorem matchScrutineeListDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (MatchScrutineeListOrdinaryParses expressionOrdinary)
      (MatchScrutineeListRejects expressionOrdinary expressionRejects) where
  successOutputUnique := MatchScrutineeListOrdinaryParses.output_unique
    expressionOutcomes
  successRejectDisjoint := MatchScrutineeListRejects.disjointOrdinary
    expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
