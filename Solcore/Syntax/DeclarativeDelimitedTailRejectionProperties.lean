import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-! Disjointness of exact delimited-tail rejection traces from success. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- A no-trailing tail rejection cannot overlap a clean successful tail. -/
theorem DelimitedTailRejects.disjointNoTrailing {α : Type}
    {closing : Symbol}
    {ordinaryParses cleanParses : Remainder → α → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input rejectedOutput : Remainder}
    (rejected : DelimitedTailRejects closing false ordinaryParses
      nestedRejects input rejectedOutput) :
    ¬ ∃ elements closingSpan output,
      NoTrailingDelimitedTailParses closing cleanParses input elements
        closingSpan output := by
  induction rejected with
  | delimiterMissing commaAbsent closingAbsent =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | close _ closingToken =>
          exact absent_conflicts_token closingAbsent closingToken
      | next commaToken _ _ _ =>
          exact absent_conflicts_token commaAbsent commaToken
  | elementRejected commaSpan commaToken continues nestedRejected =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | close commaAbsent _ =>
          exact absent_conflicts_token commaAbsent commaToken
      | next _ elementParsed _ _ =>
          exact outcomes.successRejectDisjoint nestedRejected
            ⟨_, _, cleanToOrdinary elementParsed⟩
  | laterRejected commaSpan commaToken continues elementParsed progress
        tailRejected inductionHypothesis =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | close commaAbsent _ =>
          exact absent_conflicts_token commaAbsent commaToken
      | next _ cleanElementParsed _ cleanTail =>
          have ordinaryClean := cleanToOrdinary cleanElementParsed
          have outputEq := outcomes.successOutputUnique elementParsed
            ordinaryClean
          subst outputEq
          exact inductionHypothesis ⟨_, _, _, cleanTail⟩

/-- An allow-trailing tail rejection cannot overlap a clean successful tail. -/
theorem DelimitedTailRejects.disjointTrailing {α : Type}
    {closing : Symbol}
    {ordinaryParses cleanParses : Remainder → α → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanParses input value output → ordinaryParses input value output)
    {input rejectedOutput : Remainder}
    (rejected : DelimitedTailRejects closing true ordinaryParses
      nestedRejects input rejectedOutput) :
    ¬ ∃ elements closingSpan output,
      TrailingDelimitedTailParses closing cleanParses input elements
        closingSpan output := by
  induction rejected with
  | delimiterMissing commaAbsent closingAbsent =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | close _ closingToken =>
          exact absent_conflicts_token closingAbsent closingToken
      | trailing commaToken _ =>
          exact absent_conflicts_token commaAbsent commaToken
      | next commaToken _ _ _ _ =>
          exact absent_conflicts_token commaAbsent commaToken
  | elementRejected commaSpan commaToken continues nestedRejected =>
      cases continues with
      | absent closingAbsent =>
          rintro ⟨elements, closingSpan, output, parsed⟩
          cases parsed with
          | close commaAbsent _ =>
              exact absent_conflicts_token commaAbsent commaToken
          | trailing _ closingToken =>
              exact absent_conflicts_token closingAbsent closingToken
          | next _ _ elementParsed _ _ =>
              exact outcomes.successRejectDisjoint nestedRejected
                ⟨_, _, cleanToOrdinary elementParsed⟩
  | laterRejected commaSpan commaToken continues elementParsed progress
        tailRejected inductionHypothesis =>
      cases continues with
      | absent closingAbsent =>
          rintro ⟨elements, closingSpan, output, parsed⟩
          cases parsed with
          | close commaAbsent _ =>
              exact absent_conflicts_token commaAbsent commaToken
          | trailing _ closingToken =>
              exact absent_conflicts_token closingAbsent closingToken
          | next _ _ cleanElementParsed _ cleanTail =>
              have ordinaryClean := cleanToOrdinary cleanElementParsed
              have outputEq := outcomes.successOutputUnique elementParsed
                ordinaryClean
              subst outputEq
              exact inductionHypothesis ⟨_, _, _, cleanTail⟩

end Solcore.Syntax.DeclarativeGrammar
