import Solcore.Syntax.DeclarativeSelectorNameOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact maximal operator strings and prioritized selector-name outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem SelectorOperatorPartsParses.cursor_le
    {tokens : Array Token} {endIndex cursor finish : Nat} {parts : List String}
    (parsed : SelectorOperatorPartsParses tokens endIndex cursor parts finish) :
    cursor ≤ finish := by
  induction parsed with
  | done => exact Nat.le_refl _
  | next _ _ _ _ ih => omega

/-- A possibly nonmaximal operator scan fixes its parts only at a shared end. -/
theorem SelectorOperatorPartsParses.value_unique_of_same_finish
    {tokens : Array Token} {endIndex cursor finish : Nat} {left right : List String}
    (leftParsed : SelectorOperatorPartsParses tokens endIndex cursor left finish)
    (rightParsed : SelectorOperatorPartsParses tokens endIndex cursor right finish) :
    left = right := by
  induction leftParsed generalizing right with
  | done cursor =>
      cases rightParsed with
      | done => rfl
      | next _ _ _ tail => have := tail.cursor_le; omega
  | next allowed span token tail ih =>
      cases rightParsed with
      | done => have := tail.cursor_le; omega
      | next rightAllowed rightSpan rightToken rightTail =>
          have tokenEq := token.token_unique rightToken
          have partsEq := ih rightTail
          simp_all

/-- A maximal scan fixes both its forward operator pieces and its remainder. -/
theorem MaximalSelectorOperatorPartsParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : List String}
    (leftParsed : MaximalSelectorOperatorPartsParses input left afterLeft)
    (rightParsed : MaximalSelectorOperatorPartsParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done absent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next allowed span token _ => exact False.elim (absent ⟨_, _, allowed, token⟩)
  | next allowed span token tail ih =>
      cases rightParsed with
      | done absent => exact False.elim (absent ⟨_, _, allowed, token⟩)
      | next rightAllowed rightSpan rightToken rightTail =>
          have tokenEq := token.token_unique rightToken
          have tailEq := ih rightTail
          simp_all

/-- The closing delimiter forces one complete operator selector AST. -/
theorem OperatorSelectorParses.value_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.SelectorName}
    (leftParsed : OperatorSelectorParses input left afterLeft)
    (rightParsed : OperatorSelectorParses input right afterRight) : left = right := by
  have outputEq := leftParsed.output_unique rightParsed
  rcases leftParsed with ⟨leftOpeningSpan, leftClosingSpan, leftParts, leftFinish,
    leftTokens, leftEnd, leftOpening, leftScan, leftNonempty, leftClosing,
    leftCursor, leftValue⟩
  rcases rightParsed with ⟨rightOpeningSpan, rightClosingSpan, rightParts, rightFinish,
    rightTokens, rightEnd, rightOpening, rightScan, rightNonempty, rightClosing,
    rightCursor, rightValue⟩
  have finishEq : leftFinish = rightFinish := by
    have := congrArg Remainder.cursor outputEq
    omega
  subst finishEq
  have openingEq := leftOpening.token_unique rightOpening
  have closingEq := leftClosing.token_unique rightClosing
  have partsEq := leftScan.value_unique_of_same_finish rightScan
  simp_all

/-- The identifier/operator branch fixes the complete located selector value. -/
theorem SelectorNameOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.SelectorName}
    (leftParsed : SelectorNameOrdinaryParses input left afterLeft)
    (rightParsed : SelectorNameOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | identifier leftToken leftTokens leftEnd leftCursor =>
      cases rightParsed with
      | identifier rightToken rightTokens rightEnd rightCursor =>
          have nameEq := IdentifierParses.value_unique
            ⟨leftToken, leftTokens, leftEnd, leftCursor⟩
            ⟨rightToken, rightTokens, rightEnd, rightCursor⟩
          cases nameEq
          rfl
      | operator parsed =>
          rcases parsed with ⟨_, _, _, _, _, _, opening, _⟩
          have := leftToken.token_unique opening
          cases congrArg (fun token : Token => token.value) this
  | operator leftOperator =>
      cases rightParsed with
      | identifier token _ _ _ =>
          rcases leftOperator with ⟨_, _, _, _, _, _, opening, _⟩
          have := token.token_unique opening
          cases congrArg (fun token : Token => token.value) this
      | operator rightOperator => exact leftOperator.value_unique rightOperator

/-- Ordinary selector names fix their complete AST and remainder. -/
theorem SelectorNameOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.SelectorName}
    (leftParsed : SelectorNameOrdinaryParses input left afterLeft)
    (rightParsed : SelectorNameOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Prioritized selector rejection fixes its first failing remainder. -/
theorem SelectorNameRejects.output_unique {input left right : Remainder}
    (leftRejected : SelectorNameRejects input left)
    (rightRejected : SelectorNameRejects input right) : left = right := by
  cases leftRejected with
  | identifierRejected absent leftName =>
      cases rightRejected with
      | identifierRejected _ rightName => exact leftName.output_unique rightName
      | emptyOperator _ opening _ => exact False.elim (absent ⟨_, opening.1⟩)
      | closingMissing _ opening _ _ _ => exact False.elim (absent ⟨_, opening.1⟩)
  | emptyOperator _ leftOpening absent =>
      cases rightRejected with
      | identifierRejected openingAbsent _ =>
          exact False.elim (openingAbsent ⟨_, leftOpening.1⟩)
      | emptyOperator _ rightOpening _ => exact leftOpening.output_unique rightOpening
      | closingMissing _ rightOpening scan nonempty _ =>
          have inputEq := leftOpening.output_unique rightOpening
          subst inputEq
          have partsEq := (scan.result_unique (.done absent)).1
          exact False.elim (nonempty partsEq)
  | closingMissing _ leftOpening leftScan nonempty _ =>
      cases rightRejected with
      | identifierRejected openingAbsent _ =>
          exact False.elim (openingAbsent ⟨_, leftOpening.1⟩)
      | emptyOperator _ rightOpening absent =>
          have inputEq := leftOpening.output_unique rightOpening
          subst inputEq
          have partsEq := (leftScan.result_unique (.done absent)).1
          exact False.elim (nonempty partsEq)
      | closingMissing _ rightOpening rightScan _ _ =>
          have inputEq := leftOpening.output_unique rightOpening
          subst inputEq
          exact (leftScan.result_unique rightScan).2

/-- Checked identifiers and maximal operator selectors have exact outcomes. -/
theorem selectorNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec SelectorNameOrdinaryParses SelectorNameRejects where
  toDeterministicOutcomeSpec := selectorNameDeterministicOutcomeSpec
  successValueUnique := SelectorNameOrdinaryParses.value_unique
  rejectOutputUnique := SelectorNameRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
