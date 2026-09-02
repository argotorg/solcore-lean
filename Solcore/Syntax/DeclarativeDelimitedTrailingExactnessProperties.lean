import Solcore.Syntax.DeclarativeDelimitedNonemptyTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedRejectionExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingOutcomeProperties

/-! Full functionality of generic allow-trailing delimited-list outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- An allow-trailing tail fixes its elements, closing span, and output when
the nested production has exact outcomes. -/
theorem TrailingDelimitedTailParses.result_unique {alpha : Type}
    {closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects) :
    ∀ {input : Remainder} {left right : List alpha}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      TrailingDelimitedTailParses closing elementParses input left leftClosing
          afterLeft →
      TrailingDelimitedTailParses closing elementParses input right rightClosing
          afterRight →
      left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight
    leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | close leftCommaAbsent leftClosingToken =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent rightClosingToken =>
          have tokenEq := leftClosingToken.token_unique rightClosingToken
          cases tokenEq
          exact ⟨rfl, rfl, rfl⟩
      | trailing rightCommaToken rightClosingToken =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightCommaToken)
      | next rightCommaToken rightClosingAbsent rightElement rightProgress
            rightTail =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightCommaToken)
  | trailing leftCommaToken leftClosingToken =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent rightClosingToken =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftCommaToken)
      | trailing rightCommaToken rightClosingToken =>
          have tokenEq := leftClosingToken.token_unique rightClosingToken
          cases tokenEq
          exact ⟨rfl, rfl, rfl⟩
      | next rightCommaToken rightClosingAbsent rightElement rightProgress
            rightTail =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosingToken)
  | next leftCommaToken leftClosingAbsent leftElement leftProgress leftTail
        inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent rightClosingToken =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftCommaToken)
      | trailing rightCommaToken rightClosingToken =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosingToken)
      | next rightCommaToken rightClosingAbsent rightElement rightProgress
            rightTail =>
          rcases outcomes.successResultUnique leftElement rightElement with
            ⟨elementEq, afterElementEq⟩
          subst elementEq
          subst afterElementEq
          rcases inductionHypothesis rightTail with
            ⟨elementsEq, closingEq, outputEq⟩
          subst elementsEq
          exact ⟨rfl, closingEq, outputEq⟩

/-- A required allow-trailing list fixes its complete delimited-list value. -/
theorem NonemptyTrailingDelimitedListParses.value_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : NonemptyTrailingDelimitedListParses opening closing
      elementParses input left afterLeft)
    (rightParsed : NonemptyTrailingDelimitedListParses opening closing
      elementParses input right afterRight) :
    left = right := by
  rcases leftParsed with ⟨leftOpening, leftFirst, leftAfterFirst,
    leftRest, leftClosing, leftTokensEq, leftEndIndexEq, leftOpeningToken,
    leftFirstParsed, leftProgress, leftTail, leftElementsEq, leftSpanEq⟩
  rcases rightParsed with ⟨rightOpening, rightFirst, rightAfterFirst,
    rightRest, rightClosing, rightTokensEq, rightEndIndexEq,
    rightOpeningToken, rightFirstParsed, rightProgress, rightTail,
    rightElementsEq, rightSpanEq⟩
  have openingTokenEq := leftOpeningToken.token_unique rightOpeningToken
  have openingEq : leftOpening = rightOpening :=
    congrArg (fun token : Token => token.span) openingTokenEq
  rcases outcomes.successResultUnique leftFirstParsed rightFirstParsed with
    ⟨firstEq, afterFirstEq⟩
  subst firstEq
  subst afterFirstEq
  rcases leftTail.result_unique outcomes rightTail with
    ⟨restEq, closingEq, outputEq⟩
  cases left
  cases right
  simp_all

/-- An allow-empty, allow-trailing list fixes its complete value. -/
theorem TrailingDelimitedListParses.value_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : TrailingDelimitedListParses opening closing elementParses
      input left afterLeft)
    (rightParsed : TrailingDelimitedListParses opening closing elementParses
      input right afterRight) :
    left = right := by
  cases leftParsed with
  | empty leftOpening leftClosing leftOpeningToken leftClosingToken =>
      cases rightParsed with
      | empty rightOpening rightClosing rightOpeningToken rightClosingToken =>
          have openingTokenEq :=
            leftOpeningToken.token_unique rightOpeningToken
          have openingEq : leftOpening = rightOpening :=
            congrArg (fun token : Token => token.span) openingTokenEq
          have closingTokenEq :=
            leftClosingToken.token_unique rightClosingToken
          have closingEq : leftClosing = rightClosing :=
            congrArg (fun token : Token => token.span) closingTokenEq
          subst openingEq
          subst closingEq
          rfl
      | nonempty rightClosingAbsent rightNonempty =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosingToken)
  | nonempty leftClosingAbsent leftNonempty =>
      cases rightParsed with
      | empty rightOpening rightClosing rightOpeningToken rightClosingToken =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosingToken)
      | nonempty rightClosingAbsent rightNonempty =>
          exact leftNonempty.value_unique outcomes rightNonempty

/-- Required allow-trailing lists have exact success values and rejection
endpoints. -/
theorem nonemptyTrailingDelimitedListExactOutcomeSpec {alpha : Type}
    (opening closing : Symbol)
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects) :
    ExactDeterministicOutcomeSpec
      (NonemptyTrailingDelimitedListParses opening closing elementParses)
      (DelimitedListRejects opening closing false true elementParses
        nestedRejects) where
  toDeterministicOutcomeSpec := {
    successOutputUnique := by
      intro input left right afterLeft afterRight leftParsed rightParsed
      exact NonemptyTrailingDelimitedListParses.output_unique
        (opening := opening) (closing := closing)
        (elementParses := elementParses) outcomes.successOutputUnique
        leftParsed rightParsed
    successRejectDisjoint := by
      intro input rejected rejection
      exact rejection.disjointNonemptyTrailing
        outcomes.toDeterministicOutcomeSpec (fun parsed => parsed)
  }
  successValueUnique :=
    NonemptyTrailingDelimitedListParses.value_unique outcomes
  rejectOutputUnique := DelimitedListRejects.output_unique outcomes

/-- Allow-empty, allow-trailing lists have exact success values and rejection
endpoints. -/
theorem trailingDelimitedListExactOutcomeSpec {alpha : Type}
    (opening closing : Symbol)
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects) :
    ExactDeterministicOutcomeSpec
      (TrailingDelimitedListParses opening closing elementParses)
      (DelimitedListRejects opening closing true true elementParses
        nestedRejects) where
  toDeterministicOutcomeSpec :=
    trailingDelimitedListDeterministicOutcomeSpec opening closing
      outcomes.toDeterministicOutcomeSpec
  successValueUnique := TrailingDelimitedListParses.value_unique outcomes
  rejectOutputUnique := DelimitedListRejects.output_unique outcomes

end Solcore.Syntax.DeclarativeGrammar
