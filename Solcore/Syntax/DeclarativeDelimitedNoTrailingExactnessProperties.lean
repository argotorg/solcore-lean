import Solcore.Syntax.DeclarativeDelimitedNoTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedRejectionExactnessProperties

/-! Full functionality of no-trailing generic delimited-list outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- A no-trailing tail fixes its element sequence, closing span, and final
remainder whenever one nested element has exact ordinary outcomes. -/
theorem NoTrailingDelimitedTailParses.result_unique {alpha : Type}
    {closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects) :
    ∀ {input : Remainder} {left right : List alpha}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      NoTrailingDelimitedTailParses closing elementParses input left
          leftClosing afterLeft →
      NoTrailingDelimitedTailParses closing elementParses input right
          rightClosing afterRight →
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
      | next rightCommaToken rightElement rightProgress rightTail =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightCommaToken)
  | next leftCommaToken leftElement leftProgress leftTail
        inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent rightClosingToken =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftCommaToken)
      | next rightCommaToken rightElement rightProgress rightTail =>
          rcases outcomes.successResultUnique leftElement rightElement with
            ⟨elementEq, afterElementEq⟩
          subst elementEq
          subst afterElementEq
          rcases inductionHypothesis rightTail with
            ⟨elementsEq, closingEq, outputEq⟩
          subst elementsEq
          exact ⟨rfl, closingEq, outputEq⟩

/-- A nonempty no-trailing list fixes its complete delimited-list value. -/
theorem NonemptyNoTrailingDelimitedListParses.value_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : NonemptyNoTrailingDelimitedListParses opening closing
      elementParses input left afterLeft)
    (rightParsed : NonemptyNoTrailingDelimitedListParses opening closing
      elementParses input right afterRight) : left = right := by
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

/-- An allow-empty no-trailing list fixes its complete delimited-list value. -/
theorem NoTrailingDelimitedListParses.value_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec elementParses nestedRejects)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : NoTrailingDelimitedListParses opening closing elementParses
      input left afterLeft)
    (rightParsed : NoTrailingDelimitedListParses opening closing elementParses
      input right afterRight) : left = right := by
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

/-- Allow-empty no-trailing delimited lists have fully functional success and
rejection outcomes. -/
theorem noTrailingDelimitedListExactOutcomeSpec {alpha : Type}
    (opening closing : Symbol)
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects) :
    ExactDeterministicOutcomeSpec
      (NoTrailingDelimitedListParses opening closing ordinaryParses)
      (DelimitedListRejects opening closing true false ordinaryParses
        nestedRejects) where
  toDeterministicOutcomeSpec :=
    noTrailingDelimitedListDeterministicOutcomeSpec opening closing
      outcomes.toDeterministicOutcomeSpec
  successValueUnique := NoTrailingDelimitedListParses.value_unique outcomes
  rejectOutputUnique := DelimitedListRejects.output_unique outcomes

end Solcore.Syntax.DeclarativeGrammar
