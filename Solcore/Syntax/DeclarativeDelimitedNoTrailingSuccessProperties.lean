import Solcore.Syntax.DeclarativeGrammar

/-!
Functionality and relation embeddings for successful generic delimited lists
that reject a trailing comma.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- A no-trailing tail has a unique output whenever one nested element does.
Element values and closing spans need not agree. -/
theorem NoTrailingDelimitedTailParses.output_unique {alpha : Type}
    {closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    (elementOutputUnique : ∀ {input : Remainder} {left right : alpha}
      {afterLeft afterRight : Remainder},
      elementParses input left afterLeft →
      elementParses input right afterRight →
      afterLeft = afterRight) :
    ∀ {input : Remainder} {left right : List alpha}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      NoTrailingDelimitedTailParses closing elementParses input left
          leftClosing afterLeft →
      NoTrailingDelimitedTailParses closing elementParses input right
          rightClosing afterRight →
      afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight
    leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | close leftCommaAbsent leftClosingToken =>
      intro rightParsed
      cases rightParsed with
      | close => rfl
      | next rightCommaToken _ _ _ =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightCommaToken)
  | next leftCommaToken leftElementParsed leftProgress leftTail
        inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | close rightCommaAbsent _ =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftCommaToken)
      | next _ rightElementParsed _ rightTail =>
          have afterElementEq :=
            elementOutputUnique leftElementParsed rightElementParsed
          subst afterElementEq
          exact inductionHypothesis rightTail

/-- Pointwise inclusion of element relations lifts to no-trailing tails. -/
theorem NoTrailingDelimitedTailParses.mapElementRelation {alpha : Type}
    {closing : Symbol}
    {source target : Remainder → alpha → Remainder → Prop}
    (includeElement : ∀ {input value output},
      source input value output → target input value output)
    {input output : Remainder} {elements : List alpha}
    {closingSpan : SourceSpan}
    (parsed : NoTrailingDelimitedTailParses closing source input elements
      closingSpan output) :
    NoTrailingDelimitedTailParses closing target input elements closingSpan
      output := by
  induction parsed with
  | close commaAbsent closingToken =>
      exact .close commaAbsent closingToken
  | next commaToken elementParsed progress tail inductionHypothesis =>
      exact .next commaToken (includeElement elementParsed) progress
        inductionHypothesis

/-- A nonempty no-trailing list has functional output whenever its nested
element relation does. -/
theorem NonemptyNoTrailingDelimitedListParses.output_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    (elementOutputUnique : ∀ {input : Remainder} {left right : alpha}
      {afterLeft afterRight : Remainder},
      elementParses input left afterLeft →
      elementParses input right afterRight →
      afterLeft = afterRight)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : NonemptyNoTrailingDelimitedListParses opening closing
      elementParses input left afterLeft)
    (rightParsed : NonemptyNoTrailingDelimitedListParses opening closing
      elementParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftOpening, leftFirst, leftAfterFirst,
    leftRest, leftClosing, leftTokensEq, leftEndIndexEq, leftOpeningToken,
    leftFirstParsed, leftProgress, leftTail, leftElementsEq, leftSpanEq⟩
  rcases rightParsed with ⟨rightOpening, rightFirst, rightAfterFirst,
    rightRest, rightClosing, rightTokensEq, rightEndIndexEq,
    rightOpeningToken, rightFirstParsed, rightProgress, rightTail,
    rightElementsEq, rightSpanEq⟩
  have afterFirstEq := elementOutputUnique leftFirstParsed rightFirstParsed
  subst afterFirstEq
  exact NoTrailingDelimitedTailParses.output_unique
    (closing := closing) (elementParses := elementParses)
    elementOutputUnique leftTail rightTail

/-- Pointwise inclusion of element relations lifts to nonempty no-trailing
lists without changing their value or remainder. -/
theorem NonemptyNoTrailingDelimitedListParses.mapElementRelation
    {alpha : Type} {opening closing : Symbol}
    {source target : Remainder → alpha → Remainder → Prop}
    (includeElement : ∀ {input value output},
      source input value output → target input value output)
    {input output : Remainder} {values : DelimitedList alpha}
    (parsed : NonemptyNoTrailingDelimitedListParses opening closing source
      input values output) :
    NonemptyNoTrailingDelimitedListParses opening closing target input values
      output := by
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact ⟨openingSpan, first, afterFirst, rest, closingSpan, tokensEq,
    endIndexEq, openingToken, includeElement firstParsed, progress,
    tail.mapElementRelation includeElement, elementsEq, spanEq⟩

/-- An allow-empty no-trailing list has functional output whenever its nested
element relation does. -/
theorem NoTrailingDelimitedListParses.output_unique {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    (elementOutputUnique : ∀ {input : Remainder} {left right : alpha}
      {afterLeft afterRight : Remainder},
      elementParses input left afterLeft →
      elementParses input right afterRight →
      afterLeft = afterRight)
    {input : Remainder} {left right : DelimitedList alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : NoTrailingDelimitedListParses opening closing elementParses
      input left afterLeft)
    (rightParsed : NoTrailingDelimitedListParses opening closing elementParses
      input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | empty leftOpening leftClosing leftOpeningToken leftClosingToken =>
      cases rightParsed with
      | empty => rfl
      | nonempty rightClosingAbsent rightParsed =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosingToken)
  | nonempty leftClosingAbsent leftParsed =>
      cases rightParsed with
      | empty _ _ _ rightClosingToken =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosingToken)
      | nonempty rightClosingAbsent rightParsed =>
          exact NonemptyNoTrailingDelimitedListParses.output_unique
            (opening := opening) (closing := closing)
            (elementParses := elementParses) elementOutputUnique leftParsed
            rightParsed

/-- Pointwise inclusion of element relations lifts to allow-empty no-trailing
lists. -/
theorem NoTrailingDelimitedListParses.mapElementRelation {alpha : Type}
    {opening closing : Symbol}
    {source target : Remainder → alpha → Remainder → Prop}
    (includeElement : ∀ {input value output},
      source input value output → target input value output)
    {input output : Remainder} {values : DelimitedList alpha}
    (parsed : NoTrailingDelimitedListParses opening closing source input values
      output) :
    NoTrailingDelimitedListParses opening closing target input values output :=
  by
    cases parsed with
    | empty openingSpan closingSpan openingToken closingToken =>
        exact .empty openingSpan closingSpan openingToken closingToken
    | nonempty closingAbsent parsed =>
        exact .nonempty closingAbsent
          (parsed.mapElementRelation includeElement)

end Solcore.Syntax.DeclarativeGrammar
