import Solcore.Syntax.DeclarativeCoreExpressionPostfixOutcomeGrammar

/-!
Functionality and relation embeddings for ordinary Core postfix successes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- Checked identifiers have a unique output remainder. -/
theorem IdentifierParses.output_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierParses input left afterLeft)
    (rightParsed : IdentifierParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftToken, leftTokens, leftEndIndex, leftCursor⟩
  rcases rightParsed with ⟨rightToken, rightTokens, rightEndIndex,
    rightCursor⟩
  cases input
  cases afterLeft
  cases afterRight
  simp_all

/-- Checked-identifier rejection excludes checked-identifier success. -/
theorem IdentifierRejects.disjoint {input rejected : Remainder}
    (rejection : IdentifierRejects input rejected) :
    ¬ ∃ name output, IdentifierParses input name output := by
  cases rejection with
  | absent identifierAbsent =>
      rintro ⟨name, output, parsed⟩
      exact identifierAbsent ⟨name.span, name.value, parsed.1⟩

/-- Checked identifiers form a deterministic ordinary outcome. -/
theorem identifierDeterministicOutcomeSpec :
    DeterministicOutcomeSpec IdentifierParses IdentifierRejects where
  successOutputUnique := IdentifierParses.output_unique
  successRejectDisjoint := IdentifierRejects.disjoint

/-- Every allow-empty no-trailing list success exposes its opening token. -/
theorem NoTrailingDelimitedListParses.opening_present {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {input output : Remainder} {values : DelimitedList alpha}
    (parsed : NoTrailingDelimitedListParses opening closing elementParses input
      values output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .symbol opening
    } := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

/-- A maximal ordinary postfix tail has a unique output remainder. -/
theorem PostfixTailParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {leftBase rightBase left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : PostfixTailParses nestedOrdinary input leftBase left
      afterLeft)
    (rightParsed : PostfixTailParses nestedOrdinary input rightBase right
      afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightBase right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => rfl
      | index openingSpan closingSpan openingToken indexParsed closingToken
            tail =>
          exact False.elim
            (absent_conflicts_token leftAbsent.1 openingToken.1)
      | call indexAbsent argumentsParsed tail =>
          rcases argumentsParsed.opening_present with ⟨span, openingToken⟩
          exact False.elim
            (absent_conflicts_token leftAbsent.2.1 openingToken)
      | field dotSpan indexAbsent callAbsent dotToken nameParsed tail =>
          exact False.elim
            (absent_conflicts_token leftAbsent.2.2 dotToken.1)
  | index leftOpeningSpan leftClosingSpan leftOpening leftIndex leftClosing
        leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim
            (absent_conflicts_token rightAbsent.1 leftOpening.1)
      | index rightOpeningSpan rightClosingSpan rightOpening rightIndex
            rightClosing rightTail =>
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterIndexEq := nestedOutcomes.successOutputUnique leftIndex
            rightIndex
          subst afterIndexEq
          have afterClosingEq := exactToken_output_unique leftClosing
            rightClosing
          subst afterClosingEq
          exact inductionHypothesis rightTail
      | call rightIndexAbsent argumentsParsed tail =>
          exact False.elim
            (absent_conflicts_token rightIndexAbsent leftOpening.1)
      | field dotSpan rightIndexAbsent callAbsent dotToken nameParsed tail =>
          exact False.elim
            (absent_conflicts_token rightIndexAbsent leftOpening.1)
  | call leftIndexAbsent leftArguments leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          rcases leftArguments.opening_present with ⟨span, openingToken⟩
          exact False.elim
            (absent_conflicts_token rightAbsent.2.1 openingToken)
      | index openingSpan closingSpan rightOpening indexParsed closingToken
            tail =>
          exact False.elim
            (absent_conflicts_token leftIndexAbsent rightOpening.1)
      | call rightIndexAbsent rightArguments rightTail =>
          have afterArgumentsEq :=
            NoTrailingDelimitedListParses.output_unique
              (opening := .leftParen) (closing := .rightParen)
              (elementParses := nestedOrdinary)
              nestedOutcomes.successOutputUnique leftArguments rightArguments
          subst afterArgumentsEq
          exact inductionHypothesis rightTail
      | field dotSpan rightIndexAbsent rightCallAbsent dotToken nameParsed
            tail =>
          rcases leftArguments.opening_present with ⟨span, openingToken⟩
          exact False.elim
            (absent_conflicts_token rightCallAbsent openingToken)
  | field leftDotSpan leftIndexAbsent leftCallAbsent leftDot leftName leftTail
        inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim
            (absent_conflicts_token rightAbsent.2.2 leftDot.1)
      | index openingSpan closingSpan rightOpening indexParsed closingToken
            tail =>
          exact False.elim
            (absent_conflicts_token leftIndexAbsent rightOpening.1)
      | call rightIndexAbsent rightArguments tail =>
          rcases rightArguments.opening_present with ⟨span, openingToken⟩
          exact False.elim
            (absent_conflicts_token leftCallAbsent openingToken)
      | field rightDotSpan rightIndexAbsent rightCallAbsent rightDot rightName
            rightTail =>
          have afterDotEq := exactToken_output_unique leftDot rightDot
          subst afterDotEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact inductionHypothesis rightTail

/-- Complete ordinary postfix success has a unique output remainder. -/
theorem ExpressionPostfixOrdinaryParses.output_unique
    {atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {atomRejects nestedRejects : Remainder → Remainder → Prop}
    (atomOutcomes : DeterministicOutcomeSpec atomOrdinary atomRejects)
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary
      input left afterLeft)
    (rightParsed : ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary
      input right afterRight) : afterLeft = afterRight := by
  rcases leftParsed with ⟨leftBase, leftAfterAtom, leftAtom, leftTail⟩
  rcases rightParsed with ⟨rightBase, rightAfterAtom, rightAtom, rightTail⟩
  have afterAtomEq := atomOutcomes.successOutputUnique leftAtom rightAtom
  subst afterAtomEq
  exact leftTail.output_unique nestedOutcomes rightTail

/-- Pointwise nested inclusion lifts through every postfix suffix. -/
theorem PostfixTailParses.mapNestedRelation
    {source target : Remainder → Syntax.Expr → Remainder → Prop}
    (includeNested : ∀ {input expression output},
      source input expression output → target input expression output)
    {input output : Remainder} {base expression : Syntax.Expr}
    (parsed : PostfixTailParses source input base expression output) :
    PostfixTailParses target input base expression output := by
  induction parsed with
  | done absent => exact .done absent
  | index openingSpan closingSpan openingToken indexParsed closingToken tail
        inductionHypothesis =>
      exact .index openingSpan closingSpan openingToken
        (includeNested indexParsed) closingToken inductionHypothesis
  | call indexAbsent argumentsParsed tail inductionHypothesis =>
      exact .call indexAbsent
        (argumentsParsed.mapElementRelation includeNested) inductionHypothesis
  | field dotSpan indexAbsent callAbsent dotToken nameParsed tail
        inductionHypothesis =>
      exact .field dotSpan indexAbsent callAbsent dotToken nameParsed
        inductionHypothesis

end Solcore.Syntax.DeclarativeGrammar
