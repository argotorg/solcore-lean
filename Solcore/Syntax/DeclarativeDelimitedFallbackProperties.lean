import Solcore.Syntax.DeclarativeDelimitedTailRejectionProperties
import Solcore.Syntax.DeclarativeCorePatternConstructorGrammar
import Solcore.Syntax.DeclarativeYulExpressionGrammar

/-!
Whole-list rejection disjointness and concrete transactional fallback specs.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- A required no-trailing list rejection excludes every clean success. -/
theorem DelimitedListRejects.disjointNonemptyNoTrailing {α : Type}
    {opening closing : Symbol}
    {ordinaryParses cleanParses : Remainder → α → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input rejectedOutput : Remainder}
    (rejected : DelimitedListRejects opening closing false false
      ordinaryParses nestedRejects input rejectedOutput) :
    ¬ ∃ values output,
      NonemptyNoTrailingDelimitedListParses opening closing cleanParses
        input values output := by
  intro successful
  rcases successful with ⟨values, output, openingSpan, first, afterFirst,
    rest, closingSpan, tokensEq, endIndexEq, openingToken, firstParsed,
    progress, tail, elementsEq, spanEq⟩
  cases rejected with
  | openingMissing openingAbsent =>
      exact absent_conflicts_token openingAbsent openingToken
  | firstRejected _ _ continues nestedRejected =>
      cases continues
      exact outcomes.successRejectDisjoint nestedRejected
        ⟨_, _, cleanToOrdinary firstParsed⟩
  | tailRejected _ _ continues ordinaryFirst _ tailRejected =>
      cases continues
      have cleanFirst := cleanToOrdinary firstParsed
      have outputEq := outcomes.successOutputUnique ordinaryFirst cleanFirst
      subst outputEq
      exact tailRejected.disjointNoTrailing outcomes cleanToOrdinary
        ⟨_, _, _, tail⟩

/-- An allow-empty/trailing list rejection excludes every clean success. -/
theorem DelimitedListRejects.disjointAllowEmptyTrailing {α : Type}
    {opening closing : Symbol}
    {ordinaryParses cleanParses : Remainder → α → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input rejectedOutput : Remainder}
    (rejected : DelimitedListRejects opening closing true true
      ordinaryParses nestedRejects input rejectedOutput) :
    ¬ ∃ values output,
      TrailingDelimitedListParses opening closing cleanParses input values
        output := by
  rintro ⟨values, output, successful⟩
  cases rejected with
  | openingMissing openingAbsent =>
      cases successful with
      | empty _ _ openingToken _ =>
          exact absent_conflicts_token openingAbsent openingToken
      | nonempty _ parsed =>
          rcases parsed with ⟨openingSpan, first, afterFirst, rest,
            closingSpan, tokensEq, endIndexEq, openingToken, firstParsed,
            progress, tail, elementsEq, spanEq⟩
          exact absent_conflicts_token openingAbsent openingToken
  | firstRejected _ openingToken continues nestedRejected =>
      cases continues with
      | absent closingAbsent =>
          cases successful with
          | empty _ _ _ closingToken =>
              exact absent_conflicts_token closingAbsent closingToken
          | nonempty _ parsed =>
              rcases parsed with ⟨openingSpan, first, afterFirst, rest,
                closingSpan, tokensEq, endIndexEq, parsedOpening, firstParsed,
                progress, tail, elementsEq, spanEq⟩
              exact outcomes.successRejectDisjoint nestedRejected
                ⟨_, _, cleanToOrdinary firstParsed⟩
  | tailRejected _ openingToken continues ordinaryFirst _ tailRejected =>
      cases continues with
      | absent closingAbsent =>
          cases successful with
          | empty _ _ _ closingToken =>
              exact absent_conflicts_token closingAbsent closingToken
          | nonempty _ parsed =>
              rcases parsed with ⟨openingSpan, first, afterFirst, rest,
                closingSpan, tokensEq, endIndexEq, parsedOpening, firstParsed,
                progress, tail, elementsEq, spanEq⟩
              have cleanFirst := cleanToOrdinary firstParsed
              have outputEq := outcomes.successOutputUnique ordinaryFirst
                cleanFirst
              subst outputEq
              exact tailRejected.disjointTrailing outcomes cleanToOrdinary
                ⟨_, _, _, tail⟩

/-- Exact rejection predicate for required pattern constructor arguments. -/
def ConstructorArgumentsRejects
    (ordinaryParses : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ rejected, DelimitedListRejects .leftParen .rightParen false false
    ordinaryParses nestedRejects input rejected

/-- Build the committed pattern fallback from deterministic nested outcomes. -/
def ConstructorArgumentsFallbackSpec.ofOutcomes
    (ordinaryParses cleanParses :
      Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop)
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output) :
    ConstructorArgumentsFallbackSpec cleanParses where
  rejects := ConstructorArgumentsRejects ordinaryParses nestedRejects
  disjoint := by
    intro input rejected
    rcases rejected with ⟨rejectedOutput, rejected⟩
    rintro ⟨arguments, output, parsed⟩
    exact rejected.disjointNonemptyNoTrailing outcomes cleanToOrdinary
      ⟨{
        span := arguments.span
        elements := arguments.elements.toList
      }, output, parsed⟩

/-- Exact rejection predicate for allow-empty/trailing Yul call arguments. -/
def YulCallArgumentsRejects
    (ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ rejected, DelimitedListRejects .leftParen .rightParen true true
    ordinaryParses nestedRejects input rejected

/-- Build the committed Yul fallback from deterministic nested outcomes. -/
def YulCallArgumentsFallbackSpec.ofOutcomes
    (ordinaryParses cleanParses :
      Remainder → Syntax.YulExpr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop)
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output) :
    YulCallArgumentsFallbackSpec cleanParses where
  rejects := YulCallArgumentsRejects ordinaryParses nestedRejects
  disjoint := by
    intro input rejected
    rcases rejected with ⟨rejectedOutput, rejected⟩
    exact rejected.disjointAllowEmptyTrailing outcomes cleanToOrdinary

end Solcore.Syntax.DeclarativeGrammar
