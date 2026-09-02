import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeSelectorNameOutcomeGrammar

/-! Deterministic and exclusive broad outcomes for selector names. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_kind_eq {tokens : Array Token} {endIndex index : Nat}
    {leftSpan rightSpan : SourceSpan} {leftKind rightKind : TokenKind}
    (left : TokenAt tokens endIndex index {
      span := leftSpan
      value := leftKind
    })
    (right : TokenAt tokens endIndex index {
      span := rightSpan
      value := rightKind
    }) :
    leftKind = rightKind := by
  have tokenEq : ({ span := leftSpan, value := leftKind } : Token) = {
      span := rightSpan
      value := rightKind
    } := Option.some.inj (left.2.symm.trans right.2)
  exact congrArg (fun token : Token => token.value) tokenEq

private theorem identifier_conflicts_leftParen {tokens : Array Token}
    {endIndex index : Nat} {nameSpan openingSpan : SourceSpan}
    {name : String}
    (nameToken : TokenAt tokens endIndex index {
      span := nameSpan
      value := .identifier name
    })
    (openingToken : TokenAt tokens endIndex index {
      span := openingSpan
      value := .symbol .leftParen
    }) : False := by
  cases tokenAt_kind_eq nameToken openingToken

private theorem rightParen_part_absent {tokens : Array Token}
    {endIndex cursor : Nat} {span : SourceSpan}
    (closingToken : TokenAt tokens endIndex cursor {
      span
      value := .symbol .rightParen
    }) :
    SelectorOperatorPartAbsentAt {
      tokens
      endIndex
      cursor
    } := by
  rintro ⟨symbol, partSpan, allowed, partToken⟩
  have kindEq := tokenAt_kind_eq partToken closingToken
  injection kindEq with symbolEq
  subst symbol
  exact allowed

/-- A maximal operator scan preserves its immutable token carrier and window. -/
theorem MaximalSelectorOperatorPartsParses.preservesCarrier
    {input output : Remainder} {parts : List String}
    (parsed : MaximalSelectorOperatorPartsParses input parts output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  induction parsed with
  | done => exact ⟨rfl, rfl⟩
  | next allowed span token tail inductionHypothesis =>
      simpa using inductionHypothesis

/-- Maximal operator scans from one remainder have one final remainder. -/
theorem MaximalSelectorOperatorPartsParses.output_unique
    {input afterLeft afterRight : Remainder}
    {leftParts rightParts : List String}
    (leftParsed : MaximalSelectorOperatorPartsParses input leftParts
      afterLeft)
    (rightParsed : MaximalSelectorOperatorPartsParses input rightParts
      afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightParts afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => rfl
      | next allowed span token tail =>
          exact False.elim (leftAbsent ⟨_, _, allowed, token⟩)
  | next allowed span token tail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent ⟨_, _, allowed, token⟩)
      | next rightAllowed rightSpan rightToken rightTail =>
          exact inductionHypothesis rightTail

private theorem SelectorOperatorPartsParses.finish_unique_of_stops
    {tokens : Array Token} {endIndex cursor : Nat}
    {leftParts : List String} {leftFinish : Nat}
    (leftParsed : SelectorOperatorPartsParses tokens endIndex cursor
      leftParts leftFinish) :
    ∀ {rightParts : List String} {rightFinish : Nat},
      SelectorOperatorPartsParses tokens endIndex cursor rightParts
          rightFinish →
      SelectorOperatorPartAbsentAt { tokens, endIndex, cursor := leftFinish } →
      SelectorOperatorPartAbsentAt { tokens, endIndex, cursor := rightFinish } →
      leftFinish = rightFinish := by
  induction leftParsed with
  | done cursor =>
      intro rightParts rightFinish rightParsed leftAbsent rightAbsent
      cases rightParsed with
      | done => rfl
      | next allowed span token tail =>
          exact False.elim (leftAbsent ⟨_, _, allowed, token⟩)
  | next allowed span token tail inductionHypothesis =>
      intro rightParts rightFinish rightParsed leftAbsent rightAbsent
      cases rightParsed with
      | done =>
          exact False.elim (rightAbsent ⟨_, _, allowed, token⟩)
      | next rightAllowed rightSpan rightToken rightTail =>
          exact inductionHypothesis rightTail leftAbsent rightAbsent

private theorem MaximalSelectorOperatorPartsParses.finish_eq_of_parts_stop
    {input output : Remainder} {parts : List String}
    (parsed : MaximalSelectorOperatorPartsParses input parts output) :
    ∀ {otherParts : List String} {otherFinish : Nat},
      SelectorOperatorPartsParses input.tokens input.endIndex input.cursor
          otherParts otherFinish →
      SelectorOperatorPartAbsentAt {
        tokens := input.tokens
        endIndex := input.endIndex
        cursor := otherFinish
      } →
      output.cursor = otherFinish := by
  induction parsed with
  | done partAbsent =>
      intro otherParts otherFinish otherParsed otherAbsent
      cases otherParsed with
      | done => rfl
      | next allowed span token tail =>
          exact False.elim (partAbsent ⟨_, _, allowed, token⟩)
  | next allowed span token tail inductionHypothesis =>
      intro otherParts otherFinish otherParsed otherAbsent
      cases otherParsed with
      | done =>
          exact False.elim (otherAbsent ⟨_, _, allowed, token⟩)
      | next rightAllowed rightSpan rightToken rightTail =>
          exact inductionHypothesis rightTail (by simpa using otherAbsent)

private theorem OperatorSelectorParses.opening_present
    {input output : Remainder} {selector : Syntax.SelectorName}
    (parsed : OperatorSelectorParses input selector output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .symbol .leftParen
    } := by
  unfold OperatorSelectorParses at parsed
  rcases parsed with ⟨openingSpan, closingSpan, parts, closingIndex,
    tokensEq, endIndexEq, openingToken, partsParsed, partsNonempty,
    closingToken, cursorEq, selectorEq⟩
  exact ⟨openingSpan, openingToken⟩

private theorem SelectorOperatorPartsParses.first_present
    {tokens : Array Token} {endIndex cursor finish : Nat}
    {parts : List String}
    (parsed : SelectorOperatorPartsParses tokens endIndex cursor parts finish)
    (nonempty : parts ≠ []) :
    ∃ symbol span,
      SelectorOperatorSymbol symbol ∧
        TokenAt tokens endIndex cursor { span, value := .symbol symbol } := by
  cases parsed with
  | done => exact False.elim (nonempty rfl)
  | next allowed span token tail => exact ⟨_, _, allowed, token⟩

/-- Exact operator-selector success has one final remainder. -/
theorem OperatorSelectorParses.output_unique
    {input afterLeft afterRight : Remainder}
    {left right : Syntax.SelectorName}
    (leftParsed : OperatorSelectorParses input left afterLeft)
    (rightParsed : OperatorSelectorParses input right afterRight) :
    afterLeft = afterRight := by
  unfold OperatorSelectorParses at leftParsed rightParsed
  rcases leftParsed with ⟨leftOpeningSpan, leftClosingSpan, leftParts,
    leftClosingIndex, leftTokensEq, leftEndIndexEq, leftOpening,
    leftPartsParsed, leftNonempty, leftClosing, leftCursorEq, leftSelectorEq⟩
  rcases rightParsed with ⟨rightOpeningSpan, rightClosingSpan, rightParts,
    rightClosingIndex, rightTokensEq, rightEndIndexEq, rightOpening,
    rightPartsParsed, rightNonempty, rightClosing, rightCursorEq,
    rightSelectorEq⟩
  have closingIndexEq := leftPartsParsed.finish_unique_of_stops
    rightPartsParsed (rightParen_part_absent leftClosing)
      (rightParen_part_absent rightClosing)
  cases input
  cases afterLeft
  cases afterRight
  simp_all

/-- Ordinary selector-name success has one final remainder. -/
theorem SelectorNameOrdinaryParses.output_unique
    {input afterLeft afterRight : Remainder}
    {left right : Syntax.SelectorName}
    (leftParsed : SelectorNameOrdinaryParses input left afterLeft)
    (rightParsed : SelectorNameOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | identifier leftName leftTokens leftEndIndex leftCursor =>
      cases rightParsed with
      | identifier rightName rightTokens rightEndIndex rightCursor =>
          cases input
          cases afterLeft
          cases afterRight
          simp_all
      | operator rightOperator =>
          rcases rightOperator.opening_present with ⟨_, openingToken⟩
          exact False.elim
            (identifier_conflicts_leftParen leftName openingToken)
  | operator leftOperator =>
      cases rightParsed with
      | identifier rightName rightTokens rightEndIndex rightCursor =>
          rcases leftOperator.opening_present with ⟨_, openingToken⟩
          exact False.elim
            (identifier_conflicts_leftParen rightName openingToken)
      | operator rightOperator =>
          exact leftOperator.output_unique rightOperator

/-- Exact selector-name rejection excludes every ordinary success. -/
theorem SelectorNameRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : SelectorNameRejects input rejected) :
    ¬ ∃ selector output,
      SelectorNameOrdinaryParses input selector output := by
  rintro ⟨selector, output, successful⟩
  cases rejection with
  | identifierRejected openingAbsent nameRejected =>
      cases successful with
      | identifier nameToken tokensEq endIndexEq cursorEq =>
          cases nameRejected with
          | absent identifierAbsent =>
              exact identifierAbsent ⟨_, _, nameToken⟩
      | operator operatorParsed =>
          rcases operatorParsed.opening_present with ⟨span, openingToken⟩
          exact openingAbsent ⟨span, openingToken⟩
  | emptyOperator openingSpan openingParsed partAbsent =>
      cases successful with
      | identifier nameToken tokensEq endIndexEq cursorEq =>
          exact identifier_conflicts_leftParen nameToken openingParsed.1
      | operator operatorParsed =>
          unfold OperatorSelectorParses at operatorParsed
          rcases operatorParsed with ⟨successfulOpeningSpan,
            successfulClosingSpan, parts, closingIndex, tokensEq, endIndexEq,
            successfulOpening, partsParsed, partsNonempty, closingToken,
            cursorEq, selectorEq⟩
          rw [openingParsed.2] at partAbsent
          rcases partsParsed.first_present partsNonempty with
            ⟨symbol, span, allowed, firstToken⟩
          exact partAbsent ⟨symbol, span, allowed, by simpa using firstToken⟩
  | closingMissing openingSpan openingParsed partsParsed partsNonempty
      closingAbsent =>
      cases successful with
      | identifier nameToken tokensEq endIndexEq cursorEq =>
          exact identifier_conflicts_leftParen nameToken openingParsed.1
      | operator operatorParsed =>
          unfold OperatorSelectorParses at operatorParsed
          rcases operatorParsed with ⟨successfulOpeningSpan,
            successfulClosingSpan, successfulParts, closingIndex, tokensEq,
            endIndexEq, successfulOpening, successfulPartsParsed,
            successfulPartsNonempty, successfulClosing, cursorEq,
            selectorEq⟩
          rw [openingParsed.2] at partsParsed
          have closingIndexEq :=
            partsParsed.finish_eq_of_parts_stop successfulPartsParsed
              (rightParen_part_absent successfulClosing)
          have carrier := partsParsed.preservesCarrier
          apply closingAbsent
          refine ⟨successfulClosingSpan, ?_⟩
          rw [carrier.1, carrier.2, closingIndexEq]
          exact successfulClosing

/-- Selector names have deterministic and exclusive broad ordinary outcomes. -/
theorem selectorNameDeterministicOutcomeSpec :
    DeterministicOutcomeSpec SelectorNameOrdinaryParses
      SelectorNameRejects where
  successOutputUnique := SelectorNameOrdinaryParses.output_unique
  successRejectDisjoint := SelectorNameRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
