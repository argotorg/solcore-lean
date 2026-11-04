import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Grammar.Modules
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Internal.DelimitedExactness

/-!
Properties of the declarative grammar of exports: outcomes are deterministic, and
successful values and rejection points are unique. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectorNameOutcomeProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSelectorNameExactnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExportPathOutcomeProperties
/-! Deterministic and exclusive broad outcomes for maximal export paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A maximal dotted export-path tail has one final cursor. -/
theorem ExportPathTailParses.output_unique :
    ∀ {tokens : Array Token} {endIndex cursor : Nat}
      {leftComponents rightComponents : List Syntax.Identifier}
      {leftFinish rightFinish : Nat},
      ExportPathTailParses tokens endIndex cursor leftComponents leftFinish →
      ExportPathTailParses tokens endIndex cursor rightComponents rightFinish →
      leftFinish = rightFinish := by
  intro tokens endIndex cursor leftComponents rightComponents leftFinish
    rightFinish leftParsed
  induction leftParsed generalizing rightComponents rightFinish with
  | done cursor stopped =>
      intro rightParsed
      cases rightParsed with
      | done => rfl
      | next dotSpan dotToken componentToken tail =>
          exact False.elim (stopped ⟨dotSpan, _, _, dotToken,
            componentToken⟩)
  | next dotSpan dotToken componentToken tail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | done cursor stopped =>
          exact False.elim (stopped ⟨dotSpan, _, _, dotToken,
            componentToken⟩)
      | next rightDotSpan rightDotToken rightComponentToken rightTail =>
          exact inductionHypothesis rightTail

/-- Maximal export paths have one final remainder. -/
theorem ExportPathParses.output_unique
    {input : Remainder} {left right : Syntax.QualifiedName}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportPathParses input left afterLeft)
    (rightParsed : ExportPathParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftTokens, leftEndIndex, leftFirst, leftTail, leftSpan⟩
  rcases rightParsed with
    ⟨rightTokens, rightEndIndex, rightFirst, rightTail, rightSpan⟩
  have cursorEq := ExportPathTailParses.output_unique leftTail rightTail
  cases input
  cases afterLeft
  cases afterRight
  simp_all

/-- First-identifier rejection excludes every maximal export-path success. -/
theorem ExportPathRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : ExportPathRejects input rejected) :
    ¬ ∃ path output, ExportPathOrdinaryParses input path output := by
  rintro ⟨path, output, parsed⟩
  cases rejection with
  | firstRejected identifierRejected =>
      unfold ExportPathOrdinaryParses ExportPathParses at parsed
      have firstParsed : IdentifierParses input path.value.components.head
          { input with cursor := input.cursor + 1 } :=
        ⟨parsed.2.2.1, rfl, rfl, rfl⟩
      exact identifierDeterministicOutcomeSpec.successRejectDisjoint
        identifierRejected ⟨_, _, firstParsed⟩

/-- Maximal export paths have deterministic and exclusive broad outcomes. -/
theorem exportPathDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ExportPathOrdinaryParses ExportPathRejects where
  successOutputUnique := ExportPathParses.output_unique
  successRejectDisjoint := ExportPathRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExportPathExactnessProperties
/-! Exact maximal export-path components, covering spans, and rejection endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A maximal dotted export tail fixes every source-order identifier component. -/
theorem ExportPathTailParses.value_unique :
    ∀ {tokens : Array Token} {endIndex cursor : Nat}
      {left right : List Syntax.Identifier} {leftFinish rightFinish : Nat},
      ExportPathTailParses tokens endIndex cursor left leftFinish →
      ExportPathTailParses tokens endIndex cursor right rightFinish → left = right := by
  intro tokens endIndex cursor left right leftFinish rightFinish leftParsed
  induction leftParsed generalizing right rightFinish with
  | done cursor leftStopped =>
      intro rightParsed
      cases rightParsed with
      | done => rfl
      | next rightDotSpan rightDot rightComponent rightTail =>
          exact False.elim (leftStopped ⟨_, _, _, rightDot, rightComponent⟩)
  | @next cursor finish component components leftDotSpan leftDot leftComponent leftTail ih =>
      intro rightParsed
      cases rightParsed with
      | done cursor rightStopped =>
          exact False.elim (rightStopped ⟨_, _, _, leftDot, leftComponent⟩)
      | @next _ rightFinish rightComponent rightComponents _ _ rightToken rightTail =>
          have tokenEq := leftComponent.token_unique rightToken
          have componentEq : component = rightComponent := by
            cases component
            cases rightComponent
            simp_all
          cases componentEq
          cases ih rightTail
          rfl

/-- The first token and maximal tail fix the complete located export path. -/
theorem ExportPathParses.value_unique
    {input : Remainder} {left right : Syntax.QualifiedName}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportPathParses input left afterLeft)
    (rightParsed : ExportPathParses input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftTokens, leftEndIndex, leftFirst, leftTail, leftSpan⟩
  rcases rightParsed with ⟨rightTokens, rightEndIndex, rightFirst, rightTail, rightSpan⟩
  have firstEq := leftFirst.token_unique rightFirst
  have tailEq := leftTail.value_unique rightTail
  rcases left with ⟨leftSpan, ⟨⟨leftHead, leftRest⟩⟩⟩
  rcases right with ⟨rightSpan, ⟨⟨rightHead, rightRest⟩⟩⟩
  cases leftHead
  cases rightHead
  simp_all

/-- An export path fixes its complete AST and final declarative remainder. -/
theorem ExportPathParses.result_unique
    {input : Remainder} {left right : Syntax.QualifiedName}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportPathParses input left afterLeft)
    (rightParsed : ExportPathParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- First-identifier rejection fixes the complete export-path failure endpoint. -/
theorem ExportPathRejects.output_unique {input left right : Remainder}
    (leftRejected : ExportPathRejects input left)
    (rightRejected : ExportPathRejects input right) : left = right := by
  cases leftRejected with
  | firstRejected leftIdentifier =>
      cases rightRejected with
      | firstRejected rightIdentifier => exact leftIdentifier.output_unique rightIdentifier

/-- Export paths have exact located components and rejecting endpoints. -/
theorem exportPathExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ExportPathOrdinaryParses ExportPathRejects where
  toDeterministicOutcomeSpec := exportPathDeterministicOutcomeSpec
  successValueUnique := ExportPathParses.value_unique
  rejectOutputUnique := ExportPathRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeConstructorSelectionOutcomeProperties
/-! Deterministic and exclusive broad outcomes for constructor selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem star_conflicts_identifier {tokens : Array Token}
    {endIndex index : Nat} {starSpan nameSpan : SourceSpan} {name : String}
    (starToken : TokenAt tokens endIndex index {
      span := starSpan
      value := .symbol .star
    })
    (nameToken : TokenAt tokens endIndex index {
      span := nameSpan
      value := .identifier name
    }) : False := by
  cases tokenAt_kind_eq starToken nameToken

private theorem identifier_output_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierParses input left afterLeft)
    (rightParsed : IdentifierParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftToken, leftTokens, leftEndIndex, leftCursor⟩
  rcases rightParsed with
    ⟨rightToken, rightTokens, rightEndIndex, rightCursor⟩
  rcases afterLeft with ⟨afterLeftTokens, afterLeftEndIndex,
    afterLeftCursor⟩
  rcases afterRight with ⟨afterRightTokens, afterRightEndIndex,
    afterRightCursor⟩
  have tokensEq : afterLeftTokens = afterRightTokens :=
    leftTokens.trans rightTokens.symm
  have endIndexEq : afterLeftEndIndex = afterRightEndIndex :=
    leftEndIndex.trans rightEndIndex.symm
  have cursorEq : afterLeftCursor = afterRightCursor :=
    leftCursor.trans rightCursor.symm
  cases tokensEq
  cases endIndexEq
  cases cursorEq
  rfl

private theorem identifier_outcome_spec :
    DeterministicOutcomeSpec IdentifierParses IdentifierRejects where
  successOutputUnique := identifier_output_unique
  successRejectDisjoint := IdentifierRejects.disjoint

private theorem ConstructorNamesParses.opening_token
    {input output : Remainder} {constructors : NonemptyList Syntax.Identifier}
    {span : SourceSpan}
    (parsed : ConstructorNamesParses input constructors span output) :
    ∃ openingSpan, TokenAt input.tokens input.endIndex input.cursor {
      span := openingSpan
      value := .symbol .leftParen
    } := by
  unfold ConstructorNamesParses at parsed
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact ⟨openingSpan, openingToken⟩

private theorem ConstructorNamesParses.first_identifier_token
    {input output : Remainder} {constructors : NonemptyList Syntax.Identifier}
    {span : SourceSpan}
    (parsed : ConstructorNamesParses input constructors span output) :
    ∃ nameSpan name, TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := nameSpan
      value := .identifier name
    } := by
  unfold ConstructorNamesParses at parsed
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact ⟨first.span, first.value, by simpa using firstParsed.1⟩

/-- Constructor-selection success has one final remainder. -/
theorem ConstructorSelectionOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ConstructorSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorSelectionOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorSelectionOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | all leftOpeningSpan leftMarkerSpan leftClosingSpan leftOpening
      leftMarker leftClosing =>
      cases rightParsed with
      | all => rfl
      | named rightNames =>
          rcases rightNames.first_identifier_token with
            ⟨nameSpan, name, nameToken⟩
          exact False.elim (star_conflicts_identifier leftMarker nameToken)
  | named leftNames =>
      cases rightParsed with
      | all rightOpeningSpan rightMarkerSpan rightClosingSpan rightOpening
          rightMarker rightClosing =>
          rcases leftNames.first_identifier_token with
            ⟨nameSpan, name, nameToken⟩
          exact False.elim (star_conflicts_identifier rightMarker nameToken)
      | named rightNames =>
          unfold ConstructorNamesParses at leftNames rightNames
          exact NonemptyNoTrailingDelimitedListParses.output_unique
            (opening := .leftParen) (closing := .rightParen)
            (elementParses := IdentifierParses)
            identifier_output_unique leftNames rightNames

/-- Exact constructor-selection rejection excludes every ordinary success. -/
theorem ConstructorSelectionRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ConstructorSelectionRejects input rejected) :
    ¬ ∃ selection output,
      ConstructorSelectionOrdinaryParses input selection output := by
  rintro ⟨selection, output, successful⟩
  cases rejection with
  | openingMissing markerSpan markerToken openingAbsent =>
      cases successful with
      | all openingSpan successfulMarkerSpan closingSpan openingToken
          successfulMarker closingToken =>
          exact absent_conflicts_token openingAbsent openingToken
      | named namesParsed =>
          rcases namesParsed.opening_token with ⟨openingSpan, openingToken⟩
          exact absent_conflicts_token openingAbsent openingToken
  | closingMissing openingSpan markerSpan openingParsed markerParsed
      closingAbsent =>
      cases successful with
      | all successfulOpeningSpan successfulMarkerSpan successfulClosingSpan
          successfulOpening successfulMarker successfulClosing =>
          apply closingAbsent
          refine ⟨successfulClosingSpan, ?_⟩
          simpa [markerParsed.2, openingParsed.2, Nat.add_assoc] using
            successfulClosing
      | named namesParsed =>
          rcases namesParsed.first_identifier_token with
            ⟨nameSpan, name, nameToken⟩
          have markerAtInput : TokenAt input.tokens input.endIndex
              (input.cursor + 1) {
                span := markerSpan
                value := .symbol .star
              } := by
            simpa [openingParsed.2] using markerParsed.1
          exact star_conflicts_identifier markerAtInput nameToken
  | namedRejected markerAbsent namesRejected =>
      cases successful with
      | all openingSpan markerSpan closingSpan openingToken markerToken
          closingToken =>
          exact absent_conflicts_token markerAbsent markerToken
      | named namesParsed =>
          unfold ConstructorNamesParses at namesParsed
          exact namesRejected.disjointNonemptyNoTrailing
            identifier_outcome_spec (fun parsed => parsed)
            ⟨_, _, namesParsed⟩

/-- Constructor selections have deterministic and exclusive broad outcomes. -/
theorem constructorSelectionDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ConstructorSelectionOrdinaryParses
      ConstructorSelectionRejects where
  successOutputUnique := ConstructorSelectionOrdinaryParses.output_unique
  successRejectDisjoint := ConstructorSelectionRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExportNameOutcomeProperties
/-! Deterministic and exclusive broad ordinary outcomes for export names. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem present_conflicts_absent {input : Remainder}
    {kind : TokenKind}
    (present : ExportNameTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      kind) : False := by
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩

private theorem token_conflicts_absent {input : Remainder}
    {kind : TokenKind} {span : SourceSpan}
    (token : TokenAt input.tokens input.endIndex input.cursor {
      span
      value := kind
    })
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      kind) : False :=
  absent ⟨span, token⟩

private theorem operatorSelector_opening_present
    {input output : Remainder} {selector : Syntax.SelectorName}
    (parsed : OperatorSelectorParses input selector output) :
    ExportNameTokenPresentAt input (.symbol .leftParen) := by
  unfold OperatorSelectorParses at parsed
  rcases parsed with ⟨openingSpan, closingSpan, parts, closingIndex,
    tokensEq, endIndexEq, openingToken, partsParsed, partsNonempty,
    closingToken, cursorEq, selectorEq⟩
  exact ⟨openingSpan, openingToken⟩

private theorem constructorSelection_opening_present
    {input output : Remainder} {selection : Syntax.ConstructorSelection}
    (parsed : ConstructorSelectionOrdinaryParses input selection output) :
    ExportNameTokenPresentAt input (.symbol .leftParen) := by
  cases parsed with
  | all openingSpan markerSpan closingSpan openingToken markerToken
      closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | named namesParsed =>
      unfold ConstructorNamesParses NonemptyNoTrailingDelimitedListParses at namesParsed
      rcases namesParsed with ⟨openingSpan, first, afterFirst, rest,
        closingSpan, tokensEq, endIndexEq, openingToken, firstParsed,
        progress, tail, elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

private theorem optionalConstructorSelection_output_unique
    {input : Remainder}
    {left right : Option Syntax.ConstructorSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalConstructorSelectionParses input left afterLeft)
    (rightParsed : OptionalConstructorSelectionParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSelection =>
          exact False.elim (present_conflicts_absent
            (constructorSelection_opening_present rightSelection) leftAbsent)
  | present leftSelection =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (present_conflicts_absent
            (constructorSelection_opening_present leftSelection) rightAbsent)
      | present rightSelection =>
          exact constructorSelectionDeterministicOutcomeSpec
            |>.successOutputUnique leftSelection rightSelection

/-- Prioritized export-name success has one final remainder. -/
theorem ExportNameOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ExportName}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportNameOrdinaryParses input left afterLeft)
    (rightParsed : ExportNameOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | wildcard leftSpan leftMarker =>
      cases rightParsed with
      | wildcard => rfl
      | operator rightStar rightOperator =>
          exact False.elim (token_conflicts_absent leftMarker rightStar)
      | identifier rightStar rightOpening rightName rightConstructors =>
          exact False.elim (token_conflicts_absent leftMarker rightStar)
  | operator leftStar leftOperator =>
      cases rightParsed with
      | wildcard rightSpan rightMarker =>
          exact False.elim (token_conflicts_absent rightMarker leftStar)
      | operator rightStar rightOperator =>
          exact OperatorSelectorParses.output_unique leftOperator
            rightOperator
      | identifier rightStar rightOpening rightName rightConstructors =>
          exact False.elim (present_conflicts_absent
            (operatorSelector_opening_present leftOperator) rightOpening)
  | identifier leftStar leftOpening leftName leftConstructors =>
      cases rightParsed with
      | wildcard rightSpan rightMarker =>
          exact False.elim (token_conflicts_absent rightMarker leftStar)
      | operator rightStar rightOperator =>
          exact False.elim (present_conflicts_absent
            (operatorSelector_opening_present rightOperator) leftOpening)
      | identifier rightStar rightOpening rightName rightConstructors =>
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          exact optionalConstructorSelection_output_unique leftConstructors
            rightConstructors

/-- Exact first-stage export-name rejection excludes ordinary success. -/
theorem ExportNameRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : ExportNameRejects input rejected) :
    ¬ ∃ name output, ExportNameOrdinaryParses input name output := by
  rintro ⟨name, output, successful⟩
  cases rejection with
  | operatorRejected starAbsent openingPresent selectorRejected =>
      cases successful with
      | wildcard markerSpan markerToken =>
          exact token_conflicts_absent markerToken starAbsent
      | operator successfulStar operatorParsed =>
          exact selectorNameDeterministicOutcomeSpec.successRejectDisjoint
            selectorRejected ⟨_, _, .operator operatorParsed⟩
      | identifier successfulStar openingAbsent nameParsed constructorsParsed =>
          exact present_conflicts_absent openingPresent openingAbsent
  | identifierRejected starAbsent openingAbsent nameRejected =>
      cases successful with
      | wildcard markerSpan markerToken =>
          exact token_conflicts_absent markerToken starAbsent
      | operator successfulStar operatorParsed =>
          exact present_conflicts_absent
            (operatorSelector_opening_present operatorParsed) openingAbsent
      | identifier successfulStar successfulOpening nameParsed
          constructorsParsed =>
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, nameParsed⟩
  | constructorsRejected starAbsent openingAbsent rejectedName
      openingPresent selectionRejected =>
      cases successful with
      | wildcard markerSpan markerToken =>
          exact token_conflicts_absent markerToken starAbsent
      | operator successfulStar operatorParsed =>
          exact present_conflicts_absent
            (operatorSelector_opening_present operatorParsed) openingAbsent
      | identifier successfulStar successfulOpening successfulName
          successfulConstructors =>
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          cases successfulConstructors with
          | absent selectionAbsent =>
              exact present_conflicts_absent openingPresent selectionAbsent
          | present selectionParsed =>
              exact constructorSelectionDeterministicOutcomeSpec
                |>.successRejectDisjoint selectionRejected
                  ⟨_, _, selectionParsed⟩

/-- Export names have deterministic and exclusive broad ordinary outcomes. -/
theorem exportNameDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ExportNameOrdinaryParses ExportNameRejects where
  successOutputUnique := ExportNameOrdinaryParses.output_unique
  successRejectDisjoint := ExportNameRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLocalExportItemOutcomeProperties
/-! Deterministic and exclusive broad outcomes for local export items. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem qualifiedStart_conflicts_absent {input : Remainder}
    (present : LocalExportItemQualifiedStartAt input)
    (absent : IdentifierDotAbsentAt input.tokens input.endIndex input.cursor) :
    False := by
  rcases present with ⟨identifierSpan, dotSpan, text, identifierToken,
    dotToken⟩
  exact absent ⟨identifierSpan, dotSpan, text, identifierToken, dotToken⟩

private theorem initial_dot_of_path_tail
    {tokens : Array Token} {endIndex cursor finish : Nat}
    {components : List Syntax.Identifier} {dotSpan : SourceSpan}
    (tail : ExportPathTailParses tokens endIndex cursor components finish)
    (finishDot : TokenAt tokens endIndex finish {
      span := dotSpan
      value := .symbol .dot
    }) :
    ∃ firstDotSpan, TokenAt tokens endIndex cursor {
      span := firstDotSpan
      value := .symbol .dot
    } := by
  cases tail with
  | done cursor stopped =>
      exact ⟨dotSpan, finishDot⟩
  | next firstDotSpan firstDot componentToken rest =>
      exact ⟨firstDotSpan, firstDot⟩

private theorem qualifiedStart_of_path_dot
    {input afterPath : Remainder} {path : Syntax.QualifiedName}
    {dotSpan : SourceSpan}
    (pathParsed : ExportPathOrdinaryParses input path afterPath)
    (dotToken : TokenAt afterPath.tokens afterPath.endIndex afterPath.cursor {
      span := dotSpan
      value := .symbol .dot
    }) : LocalExportItemQualifiedStartAt input := by
  unfold ExportPathOrdinaryParses ExportPathParses at pathParsed
  rcases pathParsed with ⟨tokensEq, endIndexEq, firstToken, tail, spanEq⟩
  have finishDot : TokenAt input.tokens input.endIndex afterPath.cursor {
      span := dotSpan
      value := .symbol .dot
    } := by
    simpa only [tokensEq, endIndexEq] using dotToken
  rcases initial_dot_of_path_tail tail finishDot with
    ⟨firstDotSpan, firstDot⟩
  exact ⟨_, firstDotSpan, _, firstToken, firstDot⟩

/-- Prioritized local-export-item success has one final remainder. -/
theorem LocalExportItemOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.LocalExportItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : LocalExportItemOrdinaryParses input left afterLeft)
    (rightParsed : LocalExportItemOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | moduleWildcard leftDotSpan leftMarkerSpan leftPath leftDot leftMarker =>
      cases rightParsed with
      | moduleWildcard rightDotSpan rightMarkerSpan rightPath rightDot
          rightMarker =>
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique leftPath rightPath
          subst afterPathEq
          rfl
      | name rightQualifiedAbsent rightName =>
          exact False.elim (qualifiedStart_conflicts_absent
            (qualifiedStart_of_path_dot leftPath leftDot)
            rightQualifiedAbsent)
  | name leftQualifiedAbsent leftName =>
      cases rightParsed with
      | moduleWildcard rightDotSpan rightMarkerSpan rightPath rightDot
          rightMarker =>
          exact False.elim (qualifiedStart_conflicts_absent
            (qualifiedStart_of_path_dot rightPath rightDot)
            leftQualifiedAbsent)
      | name rightQualifiedAbsent rightName =>
          exact exportNameDeterministicOutcomeSpec.successOutputUnique
            leftName rightName

/-- Exact first-stage local-export-item rejection excludes ordinary success. -/
theorem LocalExportItemRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : LocalExportItemRejects input rejected) :
    ¬ ∃ item output, LocalExportItemOrdinaryParses input item output := by
  rintro ⟨item, output, successful⟩
  cases rejection with
  | moduleDotMissing qualifiedStart rejectedPath dotAbsent =>
      cases successful with
      | moduleWildcard dotSpan markerSpan successfulPath dotToken
          markerToken =>
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath successfulPath
          subst afterPathEq
          exact dotAbsent ⟨dotSpan, dotToken⟩
      | name qualifiedAbsent nameParsed =>
          exact qualifiedStart_conflicts_absent qualifiedStart
            qualifiedAbsent
  | moduleStarMissing qualifiedStart rejectedPath dotSpan dotParsed
      starAbsent =>
      cases successful with
      | moduleWildcard successfulDotSpan markerSpan successfulPath dotToken
          markerToken =>
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath successfulPath
          subst afterPathEq
          rw [dotParsed.2] at starAbsent
          exact starAbsent ⟨markerSpan, by simpa using markerToken⟩
      | name qualifiedAbsent nameParsed =>
          exact qualifiedStart_conflicts_absent qualifiedStart
            qualifiedAbsent
  | nameRejected qualifiedAbsent nameRejected =>
      cases successful with
      | moduleWildcard dotSpan markerSpan pathParsed dotToken markerToken =>
          exact qualifiedStart_conflicts_absent
            (qualifiedStart_of_path_dot pathParsed dotToken)
            qualifiedAbsent
      | name successfulQualifiedAbsent nameParsed =>
          exact exportNameDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, nameParsed⟩

/-- Local export items have deterministic and exclusive broad outcomes. -/
theorem localExportItemDeterministicOutcomeSpec :
    DeterministicOutcomeSpec LocalExportItemOrdinaryParses
      LocalExportItemRejects where
  successOutputUnique := LocalExportItemOrdinaryParses.output_unique
  successRejectDisjoint := LocalExportItemRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExportSelectionOutcomeProperties
/-! Deterministic and exclusive broad outcomes for export selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exportSelectionItemsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec
      (TrailingDelimitedListParses .leftBrace .rightBrace
        ExportNameOrdinaryParses)
      (DelimitedListRejects .leftBrace .rightBrace true true
        ExportNameOrdinaryParses ExportNameRejects) :=
  trailingDelimitedListDeterministicOutcomeSpec .leftBrace .rightBrace
    exportNameDeterministicOutcomeSpec

/-- Prioritized export-selection success has one final remainder. -/
theorem ExportSelectionOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ExportSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportSelectionOrdinaryParses input left afterLeft)
    (rightParsed : ExportSelectionOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | wildcard leftSpan leftMarker =>
      cases rightParsed with
      | wildcard => rfl
      | selected rightStar rightItems =>
          exact False.elim (token_conflicts_absent leftMarker rightStar)
  | selected leftStar leftItems =>
      cases rightParsed with
      | wildcard rightSpan rightMarker =>
          exact False.elim (token_conflicts_absent rightMarker leftStar)
      | selected rightStar rightItems =>
          exact exportSelectionItemsDeterministicOutcomeSpec
            |>.successOutputUnique leftItems rightItems

/-- Exact selected-branch rejection excludes ordinary export-selection
success. -/
theorem ExportSelectionRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ExportSelectionRejects input rejected) :
    ¬ ∃ selection output,
      ExportSelectionOrdinaryParses input selection output := by
  rintro ⟨selection, output, successful⟩
  cases rejection with
  | selectedRejected starAbsent itemsRejected =>
      cases successful with
      | wildcard markerSpan markerToken =>
          exact token_conflicts_absent markerToken starAbsent
      | selected successfulStar itemsParsed =>
          exact exportSelectionItemsDeterministicOutcomeSpec
            |>.successRejectDisjoint itemsRejected ⟨_, _, itemsParsed⟩

/-- Export selections have deterministic and exclusive broad outcomes. -/
theorem exportSelectionDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ExportSelectionOrdinaryParses
      ExportSelectionRejects where
  successOutputUnique := ExportSelectionOrdinaryParses.output_unique
  successRejectDisjoint := ExportSelectionRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeConstructorSelectionExactnessProperties
/-! Exact all-or-named export constructor selections and optional presence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem constructorNames_first_token
    {input output : Remainder} {names : NonemptyList Syntax.Identifier}
    {span : SourceSpan} (parsed : ConstructorNamesParses input names span output) :
    ∃ name : Syntax.Identifier,
      TokenAt input.tokens input.endIndex (input.cursor + 1)
        { span := name.span, value := .identifier name.value } := by
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, opening, firstParsed, progress, tail, valuesEq, spanEq⟩
  exact ⟨first, firstParsed.1⟩

/-- Named constructor selections fix their nonempty source-order names,
covering span, and final remainder. -/
theorem ConstructorNamesParses.result_unique
    {input : Remainder} {left right : NonemptyList Syntax.Identifier}
    {leftSpan rightSpan : SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorNamesParses input left leftSpan afterLeft)
    (rightParsed : ConstructorNamesParses input right rightSpan afterRight) :
    left = right ∧ leftSpan = rightSpan ∧ afterLeft = afterRight := by
  rcases (nonemptyNoTrailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    identifierExactOutcomeSpec).successResultUnique leftParsed rightParsed with
    ⟨valuesEq, outputsEq⟩
  cases left
  cases right
  simp_all [NonemptyList.toList]

/-- Every successful constructor selection begins with a left parenthesis. -/
theorem ConstructorSelectionOrdinaryParses.opening_token
    {input output : Remainder} {selection : Syntax.ConstructorSelection}
    (parsed : ConstructorSelectionOrdinaryParses input selection output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .symbol .leftParen } := by
  cases parsed with
  | all openingSpan markerSpan closingSpan opening marker closing =>
      exact ⟨openingSpan, opening⟩
  | named names =>
      rcases names with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, opening, firstParsed, progress, tail, valuesEq,
        spanEq⟩
      exact ⟨openingSpan, opening⟩

/-- All and named selections fix their complete located constructor AST. -/
theorem ConstructorSelectionOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.ConstructorSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorSelectionOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorSelectionOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | all leftOpeningSpan leftMarkerSpan leftClosingSpan leftOpening leftMarker
      leftClosing =>
      cases rightParsed with
      | all rightOpeningSpan rightMarkerSpan rightClosingSpan rightOpening
          rightMarker rightClosing =>
          grind [TokenAt.token_unique]
      | named rightNames =>
          obtain ⟨name, nameToken⟩ := constructorNames_first_token rightNames
          cases leftMarker.token_unique nameToken
  | named leftNames =>
      cases rightParsed with
      | all rightOpeningSpan rightMarkerSpan rightClosingSpan rightOpening
          rightMarker rightClosing =>
          obtain ⟨name, nameToken⟩ := constructorNames_first_token leftNames
          cases rightMarker.token_unique nameToken
      | named rightNames =>
          rcases leftNames.result_unique rightNames with ⟨namesEq, spanEq, _⟩
          cases namesEq
          cases spanEq
          rfl

/-- Constructor-selection success fixes its complete AST and remainder. -/
theorem ConstructorSelectionOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.ConstructorSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorSelectionOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorSelectionOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

private theorem constructorSelection_marker_at_input
    {input afterOpening afterMarker : Remainder}
    {openingSpan markerSpan : SourceSpan}
    (opening : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
    (marker : ExactTokenParses (.symbol .star) afterOpening markerSpan afterMarker) :
    TokenAt input.tokens input.endIndex (input.cursor + 1)
      { span := markerSpan, value := .symbol .star } := by
  simpa [opening.2] using marker.1

private theorem constructorSelection_absent_conflicts_token
    {tokens : Array Token} {endIndex cursor : Nat} {kind : TokenKind}
    {span : SourceSpan} (absent : TokenKindAbsentAt tokens endIndex cursor kind)
    (present : TokenAt tokens endIndex cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Constructor-selection rejection fixes its priority-selected endpoint. -/
theorem ConstructorSelectionRejects.output_unique
    {input left right : Remainder}
    (leftRejected : ConstructorSelectionRejects input left)
    (rightRejected : ConstructorSelectionRejects input right) : left = right := by
  have namesOutcomes := nonemptyNoTrailingDelimitedListExactOutcomeSpec
    .leftParen .rightParen identifierExactOutcomeSpec
  cases leftRejected <;> cases rightRejected <;>
    grind [constructorSelection_absent_conflicts_token,
      constructorSelection_marker_at_input, ExactTokenParses,
      namesOutcomes.rejectOutputUnique]

/-- Constructor selections have unconditional exact ordinary outcomes. -/
theorem constructorSelectionExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ConstructorSelectionOrdinaryParses
      ConstructorSelectionRejects where
  toDeterministicOutcomeSpec := constructorSelectionDeterministicOutcomeSpec
  successValueUnique := ConstructorSelectionOrdinaryParses.value_unique
  rejectOutputUnique := ConstructorSelectionRejects.output_unique

/-- Optional selection presence fixes its value and final remainder. -/
theorem OptionalConstructorSelectionParses.result_unique
    {input : Remainder} {left right : Option Syntax.ConstructorSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalConstructorSelectionParses input left afterLeft)
    (rightParsed : OptionalConstructorSelectionParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present rightSelection =>
          exact False.elim (leftAbsent
            (ConstructorSelectionOrdinaryParses.opening_token rightSelection))
  | present leftSelection =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (rightAbsent
            (ConstructorSelectionOrdinaryParses.opening_token leftSelection))
      | present rightSelection =>
          rcases ConstructorSelectionOrdinaryParses.result_unique leftSelection
            rightSelection with ⟨valueEq, afterEq⟩
          exact ⟨congrArg some valueEq, afterEq⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExportNameExactnessProperties
/-! Exact wildcard, operator, and constructor-qualified export names. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exportName_token_conflicts_absent {input : Remainder}
    {kind : TokenKind} {span : SourceSpan}
    (present : TokenAt input.tokens input.endIndex input.cursor
      { span, value := kind })
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent ⟨span, present⟩

private theorem exportName_operator_opening
    {input output : Remainder} {selector : Syntax.SelectorName}
    (parsed : OperatorSelectorParses input selector output) :
    ExportNameTokenPresentAt input (.symbol .leftParen) := by
  rcases parsed with ⟨openingSpan, closingSpan, parts, closingIndex, tokensEq,
    endIndexEq, opening, partsParsed, nonempty, closing, cursorEq, selectorEq⟩
  exact ⟨openingSpan, opening⟩

private theorem exportName_present_conflicts_absent {input : Remainder}
    {kind : TokenKind} (present : ExportNameTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent present

/-- Prioritized export names fix every located name and constructor selection. -/
theorem ExportNameOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.ExportName}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportNameOrdinaryParses input left afterLeft)
    (rightParsed : ExportNameOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [TokenAt.token_unique, exportName_token_conflicts_absent,
      exportName_present_conflicts_absent, → exportName_operator_opening,
      OperatorSelectorParses.value_unique, IdentifierParses.result_unique,
      OptionalConstructorSelectionParses.result_unique]

/-- Export-name success fixes its complete AST and final remainder. -/
theorem ExportNameOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.ExportName}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportNameOrdinaryParses input left afterLeft)
    (rightParsed : ExportNameOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Export-name rejection fixes the priority-selected failing endpoint. -/
theorem ExportNameRejects.output_unique {input left right : Remainder}
    (leftRejected : ExportNameRejects input left)
    (rightRejected : ExportNameRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [exportName_present_conflicts_absent,
      selectorNameExactOutcomeSpec.rejectOutputUnique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      constructorSelectionExactOutcomeSpec.rejectOutputUnique]

/-- Export names have unconditional exact ordinary outcomes. -/
theorem exportNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ExportNameOrdinaryParses ExportNameRejects where
  toDeterministicOutcomeSpec := exportNameDeterministicOutcomeSpec
  successValueUnique := ExportNameOrdinaryParses.value_unique
  rejectOutputUnique := ExportNameRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLocalExportItemExactnessProperties
/-! Exact local export names and qualified module wildcards. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem localExport_initial_dot
    {tokens : Array Token} {endIndex cursor finish : Nat}
    {components : List Syntax.Identifier} {dotSpan : SourceSpan}
    (tail : ExportPathTailParses tokens endIndex cursor components finish)
    (dot : TokenAt tokens endIndex finish
      { span := dotSpan, value := .symbol .dot }) :
    ∃ span, TokenAt tokens endIndex cursor
      { span, value := .symbol .dot } := by
  cases tail with
  | done cursor stopped => exact ⟨dotSpan, dot⟩
  | next initialSpan initialDot component rest => exact ⟨initialSpan, initialDot⟩

private theorem localExport_qualified_of_path_dot
    {input afterPath : Remainder} {path : Syntax.QualifiedName}
    {dotSpan : SourceSpan}
    (parsed : ExportPathParses input path afterPath)
    (dot : TokenAt afterPath.tokens afterPath.endIndex afterPath.cursor
      { span := dotSpan, value := .symbol .dot }) :
    LocalExportItemQualifiedStartAt input := by
  rcases parsed with ⟨tokensEq, endIndexEq, first, tail, spanEq⟩
  have finishDot : TokenAt input.tokens input.endIndex afterPath.cursor
      { span := dotSpan, value := .symbol .dot } := by
    simpa only [tokensEq, endIndexEq] using dot
  obtain ⟨initialSpan, initialDot⟩ := localExport_initial_dot tail finishDot
  exact ⟨_, initialSpan, _, first, initialDot⟩

private theorem localExport_qualified_conflicts_absent {input : Remainder}
    (present : LocalExportItemQualifiedStartAt input)
    (absent : IdentifierDotAbsentAt input.tokens input.endIndex input.cursor) :
    False :=
  absent present

private theorem localExport_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Local export items fix the complete path, wildcard marker, or name AST. -/
theorem LocalExportItemOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.LocalExportItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : LocalExportItemOrdinaryParses input left afterLeft)
    (rightParsed : LocalExportItemOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [→ localExport_qualified_of_path_dot,
      localExport_qualified_conflicts_absent,
      exportPathExactOutcomeSpec.successResultUnique,
      exportNameExactOutcomeSpec.successValueUnique, TokenAt.token_unique]

/-- Local export-item success fixes its complete AST and final remainder. -/
theorem LocalExportItemOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.LocalExportItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : LocalExportItemOrdinaryParses input left afterLeft)
    (rightParsed : LocalExportItemOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Local export-item rejection fixes its selected path or name endpoint. -/
theorem LocalExportItemRejects.output_unique {input left right : Remainder}
    (leftRejected : LocalExportItemRejects input left)
    (rightRejected : LocalExportItemRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [localExport_qualified_conflicts_absent,
      localExport_absent_conflicts_exact,
      exportPathExactOutcomeSpec.successOutputUnique,
      exportNameExactOutcomeSpec.rejectOutputUnique,
      ExactTokenParses.output_unique]

/-- Local export items have unconditional exact ordinary outcomes. -/
theorem localExportItemExactOutcomeSpec :
    ExactDeterministicOutcomeSpec LocalExportItemOrdinaryParses
      LocalExportItemRejects where
  toDeterministicOutcomeSpec := localExportItemDeterministicOutcomeSpec
  successValueUnique := LocalExportItemOrdinaryParses.value_unique
  rejectOutputUnique := LocalExportItemRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExportSelectionExactnessProperties
/-! Exact wildcard or source-order braced remote export selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exportSelection_token_conflicts_absent {input : Remainder}
    {kind : TokenKind} {span : SourceSpan}
    (present : TokenAt input.tokens input.endIndex input.cursor
      { span, value := kind })
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent ⟨span, present⟩

/-- Remote export selections fix their wildcard span or full braced list. -/
theorem ExportSelectionOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.ExportSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportSelectionOrdinaryParses input left afterLeft)
    (rightParsed : ExportSelectionOrdinaryParses input right afterRight) :
    left = right := by
  have itemsOutcomes := trailingDelimitedListExactOutcomeSpec .leftBrace
    .rightBrace exportNameExactOutcomeSpec
  cases leftParsed <;> cases rightParsed <;>
    grind [exportSelection_token_conflicts_absent, TokenAt.token_unique,
      itemsOutcomes.successValueUnique]

/-- Remote export-selection success fixes its complete AST and remainder. -/
theorem ExportSelectionOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.ExportSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportSelectionOrdinaryParses input left afterLeft)
    (rightParsed : ExportSelectionOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Remote export-selection rejection fixes its braced-list endpoint. -/
theorem ExportSelectionRejects.output_unique {input left right : Remainder}
    (leftRejected : ExportSelectionRejects input left)
    (rightRejected : ExportSelectionRejects input right) : left = right := by
  cases leftRejected with
  | selectedRejected leftAbsent leftItems =>
      cases rightRejected with
      | selectedRejected rightAbsent rightItems =>
          exact (trailingDelimitedListExactOutcomeSpec .leftBrace .rightBrace
            exportNameExactOutcomeSpec).rejectOutputUnique leftItems rightItems

/-- Remote export selections have unconditional exact ordinary outcomes. -/
theorem exportSelectionExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ExportSelectionOrdinaryParses
      ExportSelectionRejects where
  toDeterministicOutcomeSpec := exportSelectionDeterministicOutcomeSpec
  successValueUnique := ExportSelectionOrdinaryParses.value_unique
  rejectOutputUnique := ExportSelectionRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFinishExportOutcomeProperties
/-! Deterministic and exclusive broad outcomes for finishing an export. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact export finishing has one final remainder. -/
theorem FinishExportParses.output_unique
    {start : SourceSpan} {value : Syntax.ExportDeclValue}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FinishExportParses start value input left afterLeft)
    (rightParsed : FinishExportParses start value input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftSemicolonSpan, leftSemicolon, leftOutputEq, leftDeclarationEq⟩
  rcases rightParsed with
    ⟨rightSemicolonSpan, rightSemicolon, rightOutputEq,
      rightDeclarationEq⟩
  rw [leftOutputEq, rightOutputEq]

/-- Missing-semicolon rejection excludes every ordinary export finish. -/
theorem FinishExportRejects.disjointOrdinary
    (start : SourceSpan) (value : Syntax.ExportDeclValue)
    {input rejected : Remainder}
    (rejection : FinishExportRejects input rejected) :
    ¬ ∃ declaration output,
      FinishExportOrdinaryParses start value input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases rejection with
  | semicolonMissing semicolonAbsent =>
      rcases successful with
        ⟨semicolonSpan, semicolon, outputEq, declarationEq⟩
      exact semicolonAbsent ⟨semicolonSpan, semicolon⟩

/-- Export finishing has a deterministic and exclusive broad outcome. -/
theorem finishExportDeterministicOutcomeSpec (start : SourceSpan)
    (value : Syntax.ExportDeclValue) :
    DeterministicOutcomeSpec (FinishExportOrdinaryParses start value)
      FinishExportRejects where
  successOutputUnique := FinishExportParses.output_unique
  successRejectDisjoint := FinishExportRejects.disjointOrdinary start value

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLocalExportOutcomeProperties
/-! Deterministic and exclusive broad outcomes for local export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem localExportItemsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec
      (TrailingDelimitedListParses .leftBrace .rightBrace
        LocalExportItemOrdinaryParses)
      (DelimitedListRejects .leftBrace .rightBrace true true
        LocalExportItemOrdinaryParses LocalExportItemRejects) :=
  trailingDelimitedListDeterministicOutcomeSpec .leftBrace .rightBrace
    localExportItemDeterministicOutcomeSpec

private theorem finishExport_output_unique_anyValue
    {start : SourceSpan} {leftValue rightValue : Syntax.ExportDeclValue}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FinishExportOrdinaryParses start leftValue input left
      afterLeft)
    (rightParsed : FinishExportOrdinaryParses start rightValue input right
      afterRight) : afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftSemicolonSpan, leftSemicolon, leftOutputEq, leftDeclarationEq⟩
  rcases rightParsed with
    ⟨rightSemicolonSpan, rightSemicolon, rightOutputEq,
      rightDeclarationEq⟩
  rw [leftOutputEq, rightOutputEq]

/-- Ordinary local-export payload success has one final remainder. -/
theorem LocalExportOrdinaryParses.output_unique (start : SourceSpan)
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : LocalExportOrdinaryParses start input left afterLeft)
    (rightParsed : LocalExportOrdinaryParses start input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftItems, leftAfterItems, leftItemsParsed,
    leftFinish⟩
  rcases rightParsed with ⟨rightItems, rightAfterItems, rightItemsParsed,
    rightFinish⟩
  have afterItemsEq := localExportItemsDeterministicOutcomeSpec
    |>.successOutputUnique leftItemsParsed rightItemsParsed
  subst afterItemsEq
  exact finishExport_output_unique_anyValue leftFinish rightFinish

/-- Exact local-export rejection excludes every ordinary success. -/
theorem LocalExportRejects.disjointOrdinary (start : SourceSpan)
    {input rejected : Remainder}
    (rejection : LocalExportRejects input rejected) :
    ¬ ∃ declaration output,
      LocalExportOrdinaryParses start input declaration output := by
  rintro ⟨declaration, output, successful⟩
  rcases successful with ⟨successfulItems, successfulAfterItems,
    successfulItemsParsed, successfulFinish⟩
  cases rejection with
  | itemsRejected itemsRejected =>
      exact localExportItemsDeterministicOutcomeSpec.successRejectDisjoint
        itemsRejected ⟨_, _, successfulItemsParsed⟩
  | finishRejected rejectedItems finishRejected =>
      have afterItemsEq := localExportItemsDeterministicOutcomeSpec
        |>.successOutputUnique rejectedItems successfulItemsParsed
      subst afterItemsEq
      exact (finishExportDeterministicOutcomeSpec start
        (.local successfulItems)).successRejectDisjoint finishRejected
          ⟨_, _, successfulFinish⟩

/-- Local export payloads have deterministic and exclusive broad outcomes for
each fixed outer start span. -/
theorem localExportDeterministicOutcomeSpec (start : SourceSpan) :
    DeterministicOutcomeSpec (LocalExportOrdinaryParses start)
      LocalExportRejects where
  successOutputUnique := LocalExportOrdinaryParses.output_unique start
  successRejectDisjoint := LocalExportRejects.disjointOrdinary start

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePathExportOutcomeProperties
/-! Deterministic and exclusive broad outcomes for path export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem token_conflict_after_path {kind : TokenKind}
    {input leftAfter rightAfter : Remainder}
    {leftPath rightPath : Syntax.QualifiedName} {span : SourceSpan}
    (leftParsed : ExportPathOrdinaryParses input leftPath leftAfter)
    (rightParsed : ExportPathOrdinaryParses input rightPath rightAfter)
    (present : TokenAt leftAfter.tokens leftAfter.endIndex leftAfter.cursor {
      span
      value := kind
    })
    (absent : TokenKindAbsentAt rightAfter.tokens rightAfter.endIndex
      rightAfter.cursor kind) : False := by
  have afterPathEq :=
    exportPathDeterministicOutcomeSpec.successOutputUnique leftParsed rightParsed
  subst afterPathEq
  exact absent ⟨span, present⟩
private theorem guard_conflict_after_path {kind : TokenKind}
    {input leftAfter rightAfter : Remainder}
    {leftPath rightPath : Syntax.QualifiedName}
    (leftParsed : ExportPathOrdinaryParses input leftPath leftAfter)
    (rightParsed : ExportPathOrdinaryParses input rightPath rightAfter)
    (present : PathExportTokenPresentAt leftAfter kind)
    (absent : TokenKindAbsentAt rightAfter.tokens rightAfter.endIndex
      rightAfter.cursor kind) : False := by
  have afterPathEq :=
    exportPathDeterministicOutcomeSpec.successOutputUnique leftParsed rightParsed
  subst afterPathEq
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩
private theorem finishExport_output_unique_anyValue_variant
    {start : SourceSpan} {leftValue rightValue : Syntax.ExportDeclValue}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FinishExportOrdinaryParses start leftValue input left
      afterLeft)
    (rightParsed : FinishExportOrdinaryParses start rightValue input right
      afterRight) : afterLeft = afterRight := by
  rcases leftParsed with ⟨leftSpan, leftToken, leftOutput, leftDecl⟩
  rcases rightParsed with ⟨rightSpan, rightToken, rightOutput, rightDecl⟩
  rw [leftOutput, rightOutput]
/-- Ordinary path-export success has one final remainder. -/
theorem PathExportOrdinaryParses.output_unique (start : SourceSpan)
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : PathExportOrdinaryParses start input left afterLeft)
    (rightParsed : PathExportOrdinaryParses start input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | itemsFrom leftItems =>
      unfold ItemsFromExportTailParses at leftItems
      rcases leftItems with
        ⟨_, _, _, _, _, leftPathParsed, leftDot, leftSelectionParsed, leftFinish⟩
      cases rightParsed with
      | itemsFrom rightItems =>
          unfold ItemsFromExportTailParses at rightItems
          rcases rightItems with
            ⟨_, _, _, _, _, rightPathParsed, _, rightSelectionParsed, rightFinish⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique leftPathParsed rightPathParsed
          subst afterPathEq
          have afterSelectionEq := exportSelectionDeterministicOutcomeSpec
            |>.successOutputUnique leftSelectionParsed rightSelectionParsed
          subst afterSelectionEq
          exact finishExport_output_unique_anyValue_variant leftFinish rightFinish
      | moduleAs rightAlias =>
          unfold ModuleAsExportTailParses at rightAlias
          rcases rightAlias with
            ⟨_, _, _, _, _, rightPathParsed, rightDotAbsent, _, _, _⟩
          exact False.elim (token_conflict_after_path leftPathParsed
            rightPathParsed leftDot rightDotAbsent)
      | module rightModule =>
          unfold ModuleExportTailParses at rightModule
          rcases rightModule with
            ⟨_, _, rightPathParsed, rightDotAbsent, _, _⟩
          exact False.elim (token_conflict_after_path leftPathParsed
            rightPathParsed leftDot rightDotAbsent)
  | moduleAs leftAlias =>
      unfold ModuleAsExportTailParses at leftAlias
      rcases leftAlias with
        ⟨_, _, _, _, _, leftPathParsed, leftDotAbsent, leftAs,
          leftNameParsed, leftFinish⟩
      cases rightParsed with
      | itemsFrom rightItems =>
          unfold ItemsFromExportTailParses at rightItems
          rcases rightItems with
            ⟨_, _, _, _, _, rightPathParsed, rightDot, _, _⟩
          exact False.elim (token_conflict_after_path rightPathParsed
            leftPathParsed rightDot leftDotAbsent)
      | moduleAs rightAlias =>
          unfold ModuleAsExportTailParses at rightAlias
          rcases rightAlias with
            ⟨_, _, _, _, _, rightPathParsed, _, _, rightNameParsed,
              rightFinish⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique leftPathParsed rightPathParsed
          subst afterPathEq
          have afterAliasEq := IdentifierParses.output_unique leftNameParsed
            rightNameParsed
          subst afterAliasEq
          exact finishExport_output_unique_anyValue_variant leftFinish rightFinish
      | module rightModule =>
          unfold ModuleExportTailParses at rightModule
          rcases rightModule with
            ⟨_, _, rightPathParsed, _, rightAsAbsent, _⟩
          exact False.elim (token_conflict_after_path leftPathParsed
            rightPathParsed leftAs rightAsAbsent)
  | module leftModule =>
      unfold ModuleExportTailParses at leftModule
      rcases leftModule with
        ⟨_, _, leftPathParsed, leftDotAbsent, leftAsAbsent, leftFinish⟩
      cases rightParsed with
      | itemsFrom rightItems =>
          unfold ItemsFromExportTailParses at rightItems
          rcases rightItems with
            ⟨_, _, _, _, _, rightPathParsed, rightDot, _, _⟩
          exact False.elim (token_conflict_after_path rightPathParsed
            leftPathParsed rightDot leftDotAbsent)
      | moduleAs rightAlias =>
          unfold ModuleAsExportTailParses at rightAlias
          rcases rightAlias with
            ⟨_, _, _, _, _, rightPathParsed, _, rightAs, _, _⟩
          exact False.elim (token_conflict_after_path rightPathParsed
            leftPathParsed rightAs leftAsAbsent)
      | module rightModule =>
          unfold ModuleExportTailParses at rightModule
          rcases rightModule with
            ⟨_, _, rightPathParsed, _, _, rightFinish⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique leftPathParsed rightPathParsed
          subst afterPathEq
          exact finishExport_output_unique_anyValue_variant leftFinish rightFinish

/-- Exact path-export rejection excludes every ordinary success. -/
theorem PathExportRejects.disjointOrdinary (start : SourceSpan) {input
    rejected : Remainder} (rejection : PathExportRejects input rejected) :
    ¬ ∃ declaration output,
      PathExportOrdinaryParses start input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases rejection with
  | pathRejected pathRejected =>
      cases successful with
      | itemsFrom parsed =>
          unfold ItemsFromExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, _, _, _⟩
          exact exportPathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, pathParsed⟩
      | moduleAs parsed =>
          unfold ModuleAsExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, _, _, _, _⟩
          exact exportPathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, pathParsed⟩
      | module parsed =>
          unfold ModuleExportTailParses at parsed
          rcases parsed with ⟨_, _, pathParsed, _, _, _⟩
          exact exportPathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, pathParsed⟩
  | selectionRejected dotSpan rejectedPath dotPresent dotParsed
      selectionRejected =>
      cases successful with
      | itemsFrom parsed =>
          unfold ItemsFromExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, _,
            selectionParsed, _⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath pathParsed
          subst afterPathEq
          rw [dotParsed.2] at selectionRejected
          exact exportSelectionDeterministicOutcomeSpec.successRejectDisjoint
            selectionRejected ⟨_, _, selectionParsed⟩
      | moduleAs parsed =>
          unfold ModuleAsExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed,
            successfulDotAbsent, _, _, _⟩
          exact guard_conflict_after_path rejectedPath pathParsed dotPresent
            successfulDotAbsent
      | module parsed =>
          unfold ModuleExportTailParses at parsed
          rcases parsed with ⟨_, _, pathParsed, successfulDotAbsent, _, _⟩
          exact guard_conflict_after_path rejectedPath pathParsed dotPresent
            successfulDotAbsent
  | selectionFinishRejected dotSpan rejectedPath dotPresent dotParsed
      rejectedSelection finishRejected =>
      cases successful with
      | itemsFrom parsed =>
          unfold ItemsFromExportTailParses at parsed
          rcases parsed with ⟨path, _, _, selection, _, pathParsed, _,
            selectionParsed, finish⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath pathParsed
          subst afterPathEq
          rw [dotParsed.2] at rejectedSelection
          have afterSelectionEq := exportSelectionDeterministicOutcomeSpec
            |>.successOutputUnique rejectedSelection selectionParsed
          subst afterSelectionEq
          exact (finishExportDeterministicOutcomeSpec start
            (.itemsFrom path selection)).successRejectDisjoint finishRejected
              ⟨_, _, finish⟩
      | moduleAs parsed =>
          unfold ModuleAsExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed,
            successfulDotAbsent, _, _, _⟩
          exact guard_conflict_after_path rejectedPath pathParsed dotPresent
            successfulDotAbsent
      | module parsed =>
          unfold ModuleExportTailParses at parsed
          rcases parsed with ⟨_, _, pathParsed, successfulDotAbsent, _, _⟩
          exact guard_conflict_after_path rejectedPath pathParsed dotPresent
            successfulDotAbsent
  | aliasRejected asSpan rejectedPath dotAbsent asPresent asParsed
      aliasRejected =>
      cases successful with
      | itemsFrom parsed =>
          unfold ItemsFromExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, dotToken, _, _⟩
          exact token_conflict_after_path pathParsed rejectedPath dotToken
            dotAbsent
      | moduleAs parsed =>
          unfold ModuleAsExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, _, _,
            aliasParsed, _⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath pathParsed
          subst afterPathEq
          rw [asParsed.2] at aliasRejected
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            aliasRejected ⟨_, _, aliasParsed⟩
      | module parsed =>
          unfold ModuleExportTailParses at parsed
          rcases parsed with ⟨_, _, pathParsed, _, successfulAsAbsent, _⟩
          exact guard_conflict_after_path rejectedPath pathParsed asPresent
            successfulAsAbsent
  | aliasFinishRejected asSpan rejectedPath dotAbsent asPresent asParsed
      rejectedAlias finishRejected =>
      cases successful with
      | itemsFrom parsed =>
          unfold ItemsFromExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, dotToken, _, _⟩
          exact token_conflict_after_path pathParsed rejectedPath dotToken
            dotAbsent
      | moduleAs parsed =>
          unfold ModuleAsExportTailParses at parsed
          rcases parsed with ⟨path, _, _, alias, _, pathParsed, _, _,
            aliasParsed, finish⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath pathParsed
          subst afterPathEq
          rw [asParsed.2] at rejectedAlias
          have afterAliasEq := IdentifierParses.output_unique rejectedAlias
            aliasParsed
          subst afterAliasEq
          exact (finishExportDeterministicOutcomeSpec start
            (.moduleAs path alias)).successRejectDisjoint finishRejected
              ⟨_, _, finish⟩
      | module parsed =>
          unfold ModuleExportTailParses at parsed
          rcases parsed with ⟨_, _, pathParsed, _, successfulAsAbsent, _⟩
          exact guard_conflict_after_path rejectedPath pathParsed asPresent
            successfulAsAbsent
  | moduleFinishRejected rejectedPath dotAbsent asAbsent finishRejected =>
      cases successful with
      | itemsFrom parsed =>
          unfold ItemsFromExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, dotToken, _, _⟩
          exact token_conflict_after_path pathParsed rejectedPath dotToken
            dotAbsent
      | moduleAs parsed =>
          unfold ModuleAsExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, _, asToken, _, _⟩
          exact token_conflict_after_path pathParsed rejectedPath asToken
            asAbsent
      | module parsed =>
          unfold ModuleExportTailParses at parsed
          rcases parsed with ⟨path, _, pathParsed, _, _, finish⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath pathParsed
          subst afterPathEq
          exact (finishExportDeterministicOutcomeSpec start
            (.module path)).successRejectDisjoint finishRejected
              ⟨_, _, finish⟩

/-- Deterministic broad path-export outcomes for each fixed outer start. -/
theorem pathExportDeterministicOutcomeSpec (start : SourceSpan) :
    DeterministicOutcomeSpec (PathExportOrdinaryParses start)
      PathExportRejects where
  successOutputUnique := PathExportOrdinaryParses.output_unique start
  successRejectDisjoint := PathExportRejects.disjointOrdinary start

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExportDeclOutcomeProperties
/-! Deterministic and exclusive broad outcomes for complete exports. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem exactToken_span_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftSpan = rightSpan := by
  have tokenEq :
      ({ span := leftSpan, value := kind } : Token) =
        { span := rightSpan, value := kind } :=
    Option.some.inj (leftParsed.1.2.symm.trans rightParsed.1.2)
  exact congrArg (fun token : Token => token.span) tokenEq

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem localExport_leftBrace_present {start : SourceSpan}
    {input : Remainder} {declaration : Syntax.ExportDecl}
    {output : Remainder}
    (parsed : LocalExportOrdinaryParses start input declaration output) :
    ExportDeclLeftBracePresentAt input := by
  rcases parsed with ⟨items, afterItems, itemsParsed, finishParsed⟩
  cases itemsParsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

private theorem ExportDeclOrdinaryParses.to_dispatch
    {input : Remainder} {declaration : Syntax.ExportDecl}
    {output : Remainder}
    (parsed : ExportDeclOrdinaryParses input declaration output) :
    ∃ keywordSpan afterKeyword,
      ExactTokenParses (.keyword .exportKw) input keywordSpan afterKeyword ∧
      ((ExportDeclLeftBracePresentAt afterKeyword ∧
          LocalExportOrdinaryParses keywordSpan afterKeyword declaration
            output) ∨
        (TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
            afterKeyword.cursor (.symbol .leftBrace) ∧
          PathExportOrdinaryParses keywordSpan afterKeyword declaration
            output)) := by
  cases parsed with
  | ofLocal parsed =>
      unfold LocalExportDeclParses at parsed
      rcases parsed with ⟨keywordSpan, keywordToken, payloadParsed⟩
      refine ⟨keywordSpan, { input with cursor := input.cursor + 1 },
        ⟨keywordToken, rfl⟩, Or.inl ⟨?_, payloadParsed⟩⟩
      exact localExport_leftBrace_present payloadParsed
  | ofModule parsed =>
      unfold ModuleExportDeclParses at parsed
      rcases parsed with
        ⟨keywordSpan, keywordToken, leftBraceAbsent, payloadParsed⟩
      exact ⟨keywordSpan, { input with cursor := input.cursor + 1 },
        ⟨keywordToken, rfl⟩,
        Or.inr ⟨leftBraceAbsent, .module payloadParsed⟩⟩
  | ofModuleAs parsed =>
      unfold ModuleAsExportDeclParses at parsed
      rcases parsed with
        ⟨keywordSpan, keywordToken, leftBraceAbsent, payloadParsed⟩
      exact ⟨keywordSpan, { input with cursor := input.cursor + 1 },
        ⟨keywordToken, rfl⟩,
        Or.inr ⟨leftBraceAbsent, .moduleAs payloadParsed⟩⟩
  | ofItemsFrom parsed =>
      unfold ItemsFromExportDeclParses at parsed
      rcases parsed with
        ⟨keywordSpan, keywordToken, leftBraceAbsent, payloadParsed⟩
      exact ⟨keywordSpan, { input with cursor := input.cursor + 1 },
        ⟨keywordToken, rfl⟩,
        Or.inr ⟨leftBraceAbsent, .itemsFrom payloadParsed⟩⟩

private theorem leftBrace_conflict_after_keyword
    {input leftAfter rightAfter : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftKeyword : ExactTokenParses (.keyword .exportKw) input leftSpan
      leftAfter)
    (rightKeyword : ExactTokenParses (.keyword .exportKw) input rightSpan
      rightAfter)
    (present : ExportDeclLeftBracePresentAt leftAfter)
    (absent : TokenKindAbsentAt rightAfter.tokens rightAfter.endIndex
      rightAfter.cursor (.symbol .leftBrace)) : False := by
  have afterKeywordEq := exactToken_output_unique leftKeyword rightKeyword
  subst afterKeywordEq
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩

private theorem payload_output_unique_after_keyword
    {payload : SourceSpan → Remainder → Syntax.ExportDecl →
      Remainder → Prop}
    {payloadRejects : Remainder → Remainder → Prop}
    (outcomes : ∀ start,
      DeterministicOutcomeSpec (payload start) payloadRejects)
    {input leftAfter rightAfter leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan} {left right : Syntax.ExportDecl}
    (leftKeyword : ExactTokenParses (.keyword .exportKw) input leftSpan
      leftAfter)
    (rightKeyword : ExactTokenParses (.keyword .exportKw) input rightSpan
      rightAfter)
    (leftPayload : payload leftSpan leftAfter left leftOutput)
    (rightPayload : payload rightSpan rightAfter right rightOutput) :
    leftOutput = rightOutput := by
  have afterKeywordEq := exactToken_output_unique leftKeyword rightKeyword
  subst afterKeywordEq
  have keywordSpanEq := exactToken_span_unique leftKeyword rightKeyword
  subst keywordSpanEq
  exact (outcomes leftSpan).successOutputUnique leftPayload rightPayload

private theorem payload_reject_disjoint_after_keyword
    {payload : SourceSpan → Remainder → Syntax.ExportDecl →
      Remainder → Prop}
    {payloadRejects : Remainder → Remainder → Prop}
    (outcomes : ∀ start,
      DeterministicOutcomeSpec (payload start) payloadRejects)
    {input rejectedAfter successfulAfter rejected output : Remainder}
    {rejectedSpan successfulSpan : SourceSpan}
    {declaration : Syntax.ExportDecl}
    (rejectedKeyword : ExactTokenParses (.keyword .exportKw) input
      rejectedSpan rejectedAfter)
    (successfulKeyword : ExactTokenParses (.keyword .exportKw) input
      successfulSpan successfulAfter)
    (payloadRejected : payloadRejects rejectedAfter rejected)
    (payloadParsed : payload successfulSpan successfulAfter declaration
      output) : False := by
  have afterKeywordEq := exactToken_output_unique rejectedKeyword
    successfulKeyword
  subst afterKeywordEq
  have keywordSpanEq := exactToken_span_unique rejectedKeyword
    successfulKeyword
  subst keywordSpanEq
  exact (outcomes rejectedSpan).successRejectDisjoint payloadRejected
    ⟨_, _, payloadParsed⟩

/-- Complete broad export success has one final remainder. -/
theorem ExportDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportDeclOrdinaryParses input left afterLeft)
    (rightParsed : ExportDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed.to_dispatch with
    ⟨leftSpan, leftAfterKeyword, leftKeyword, leftBranch⟩
  rcases rightParsed.to_dispatch with
    ⟨rightSpan, rightAfterKeyword, rightKeyword, rightBranch⟩
  cases leftBranch with
  | inl leftLocal =>
      cases rightBranch with
      | inl rightLocal =>
          exact payload_output_unique_after_keyword
            localExportDeterministicOutcomeSpec leftKeyword rightKeyword
              leftLocal.2 rightLocal.2
      | inr rightPath =>
          exact False.elim (leftBrace_conflict_after_keyword leftKeyword
            rightKeyword leftLocal.1 rightPath.1)
  | inr leftPath =>
      cases rightBranch with
      | inl rightLocal =>
          exact False.elim (leftBrace_conflict_after_keyword rightKeyword
            leftKeyword rightLocal.1 leftPath.1)
      | inr rightPath =>
          exact payload_output_unique_after_keyword
            pathExportDeterministicOutcomeSpec leftKeyword rightKeyword
              leftPath.2 rightPath.2

/-- Exact complete-export rejection excludes every broad ordinary success. -/
theorem ExportDeclRejects.disjointOrdinary {input rejected : Remainder}
    (rejection : ExportDeclRejects input rejected) :
    ¬ ∃ declaration output,
      ExportDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  rcases successful.to_dispatch with
    ⟨successfulSpan, successfulAfterKeyword, successfulKeyword,
      successfulBranch⟩
  cases rejection with
  | keywordMissing keywordAbsent =>
      exact absent_conflicts_exact keywordAbsent successfulKeyword
  | localRejected rejectedSpan rejectedKeyword leftBracePresent
        payloadRejected =>
      cases successfulBranch with
      | inl successfulLocal =>
          exact payload_reject_disjoint_after_keyword
            localExportDeterministicOutcomeSpec rejectedKeyword
              successfulKeyword payloadRejected successfulLocal.2
      | inr successfulPath =>
          exact leftBrace_conflict_after_keyword rejectedKeyword
            successfulKeyword leftBracePresent successfulPath.1
  | pathRejected rejectedSpan rejectedKeyword leftBraceAbsent
        payloadRejected =>
      cases successfulBranch with
      | inl successfulLocal =>
          exact leftBrace_conflict_after_keyword successfulKeyword
            rejectedKeyword successfulLocal.1 leftBraceAbsent
      | inr successfulPath =>
          exact payload_reject_disjoint_after_keyword
            pathExportDeterministicOutcomeSpec rejectedKeyword
              successfulKeyword payloadRejected successfulPath.2

/-- Complete exports have deterministic and exclusive broad outcomes. -/
theorem exportDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ExportDeclOrdinaryParses ExportDeclRejects where
  successOutputUnique := ExportDeclOrdinaryParses.output_unique
  successRejectDisjoint := ExportDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFinishExportExactnessProperties
/-! Exact export finishing for a fixed start span and declaration payload. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The exact semicolon fixes the full export AST at a shared start and payload. -/
theorem FinishExportParses.result_unique
    {start : SourceSpan} {value : Syntax.ExportDeclValue}
    {input afterLeft afterRight : Remainder} {left right : Syntax.ExportDecl}
    (leftParsed : FinishExportParses start value input left afterLeft)
    (rightParsed : FinishExportParses start value input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  have outputEq := leftParsed.output_unique rightParsed
  rcases leftParsed with ⟨leftSpan, leftToken, _, leftValue⟩
  rcases rightParsed with ⟨rightSpan, rightToken, _, rightValue⟩
  have spanEq := congrArg (fun token : Token => token.span)
    (leftToken.token_unique rightToken)
  simp_all

/-- Missing export semicolons reject at the unchanged complete remainder. -/
theorem FinishExportRejects.output_unique {input left right : Remainder}
    (leftRejected : FinishExportRejects input left)
    (rightRejected : FinishExportRejects input right) : left = right := by
  cases leftRejected
  cases rightRejected
  rfl

/-- Export finishing has exact values and endpoints at fixed supplied data. -/
theorem finishExportExactOutcomeSpec (start : SourceSpan)
    (value : Syntax.ExportDeclValue) :
    ExactDeterministicOutcomeSpec (FinishExportOrdinaryParses start value)
      FinishExportRejects where
  toDeterministicOutcomeSpec := finishExportDeterministicOutcomeSpec start value
  successValueUnique := fun left right => (left.result_unique right).1
  rejectOutputUnique := FinishExportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeLocalExportExactnessProperties
/-! Exact source-order local export payloads at a fixed declaration start. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A local export fixes its entire item list and semicolon-covered AST. -/
theorem LocalExportOrdinaryParses.value_unique {start : SourceSpan}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : LocalExportOrdinaryParses start input left afterLeft)
    (rightParsed : LocalExportOrdinaryParses start input right afterRight) :
    left = right := by
  rcases leftParsed with ⟨leftItems, leftAfterItems, leftList, leftFinish⟩
  rcases rightParsed with ⟨rightItems, rightAfterItems, rightList, rightFinish⟩
  rcases (trailingDelimitedListExactOutcomeSpec .leftBrace .rightBrace
    localExportItemExactOutcomeSpec).successResultUnique leftList rightList with
    ⟨itemsEq, afterEq⟩
  cases itemsEq
  cases afterEq
  exact (leftFinish.result_unique rightFinish).1

/-- Local export success fixes its entire declaration AST and remainder. -/
theorem LocalExportOrdinaryParses.result_unique {start : SourceSpan}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : LocalExportOrdinaryParses start input left afterLeft)
    (rightParsed : LocalExportOrdinaryParses start input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    LocalExportOrdinaryParses.output_unique start leftParsed rightParsed⟩

/-- Local export rejection fixes the list or finishing endpoint. -/
theorem LocalExportRejects.output_unique {input left right : Remainder}
    (leftRejected : LocalExportRejects input left)
    (rightRejected : LocalExportRejects input right) : left = right := by
  have itemsOutcomes := trailingDelimitedListExactOutcomeSpec .leftBrace
    .rightBrace localExportItemExactOutcomeSpec
  cases leftRejected <;> cases rightRejected <;>
    grind [itemsOutcomes.successOutputUnique, itemsOutcomes.successRejectDisjoint,
      itemsOutcomes.rejectOutputUnique, FinishExportRejects.output_unique]

/-- Local export payloads have unconditional exact outcomes at a shared start. -/
theorem localExportExactOutcomeSpec (start : SourceSpan) :
    ExactDeterministicOutcomeSpec (LocalExportOrdinaryParses start)
      LocalExportRejects where
  toDeterministicOutcomeSpec := localExportDeterministicOutcomeSpec start
  successValueUnique := LocalExportOrdinaryParses.value_unique
  rejectOutputUnique := LocalExportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativePathExportExactnessProperties
/-! Exact module, alias, and selected path export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem pathExport_token_conflicts_absent {input : Remainder}
    {kind : TokenKind} {span : SourceSpan}
    (present : TokenAt input.tokens input.endIndex input.cursor
      { span, value := kind })
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent ⟨span, present⟩

private theorem pathExport_present_conflicts_absent {input : Remainder}
    {kind : TokenKind} (present : PathExportTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent present

/-- Path export payloads fix their paths, suffixes, and semicolon-covered AST
at a shared outer declaration start. -/
theorem PathExportOrdinaryParses.value_unique {start : SourceSpan}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : PathExportOrdinaryParses start input left afterLeft)
    (rightParsed : PathExportOrdinaryParses start input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [ItemsFromExportTailParses, ModuleAsExportTailParses,
      ModuleExportTailParses, pathExport_token_conflicts_absent,
      exportPathExactOutcomeSpec.successResultUnique,
      exportSelectionExactOutcomeSpec.successResultUnique,
      identifierExactOutcomeSpec.successResultUnique,
      FinishExportParses.result_unique]

/-- Path export success fixes its complete declaration AST and remainder. -/
theorem PathExportOrdinaryParses.result_unique {start : SourceSpan}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : PathExportOrdinaryParses start input left afterLeft)
    (rightParsed : PathExportOrdinaryParses start input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    PathExportOrdinaryParses.output_unique start leftParsed rightParsed⟩

/-- Path export rejection fixes its first priority-selected failing endpoint. -/
theorem PathExportRejects.output_unique {input left right : Remainder}
    (leftRejected : PathExportRejects input left)
    (rightRejected : PathExportRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [pathExport_present_conflicts_absent, ExactTokenParses.output_unique,
      exportPathExactOutcomeSpec.successOutputUnique,
      exportPathExactOutcomeSpec.successRejectDisjoint,
      exportPathExactOutcomeSpec.rejectOutputUnique,
      exportSelectionExactOutcomeSpec.successOutputUnique,
      exportSelectionExactOutcomeSpec.successRejectDisjoint,
      exportSelectionExactOutcomeSpec.rejectOutputUnique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      FinishExportRejects.output_unique]

/-- Path export payloads have unconditional exact outcomes at a shared start. -/
theorem pathExportExactOutcomeSpec (start : SourceSpan) :
    ExactDeterministicOutcomeSpec (PathExportOrdinaryParses start)
      PathExportRejects where
  toDeterministicOutcomeSpec := pathExportDeterministicOutcomeSpec start
  successValueUnique := PathExportOrdinaryParses.value_unique
  rejectOutputUnique := PathExportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExportDeclExactnessProperties
/-! Exact complete export declarations across all four canonical forms. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exportDecl_local_opening {start : SourceSpan}
    {input output : Remainder} {declaration : Syntax.ExportDecl}
    (parsed : LocalExportOrdinaryParses start input declaration output) :
    ExportDeclLeftBracePresentAt input := by
  rcases parsed with ⟨items, afterItems, itemsParsed, finishParsed⟩
  cases itemsParsed with
  | empty openingSpan closingSpan opening closing => exact ⟨openingSpan, opening⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, opening, firstParsed, progress, tail, elementsEq,
        spanEq⟩
      exact ⟨openingSpan, opening⟩

private theorem exportDecl_exact_dispatch
    {input output : Remainder} {declaration : Syntax.ExportDecl}
    (parsed : ExportDeclOrdinaryParses input declaration output) :
    ∃ start afterKeyword,
      ExactTokenParses (.keyword .exportKw) input start afterKeyword ∧
      ((ExportDeclLeftBracePresentAt afterKeyword ∧
          LocalExportOrdinaryParses start afterKeyword declaration output) ∨
        (TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
            afterKeyword.cursor (.symbol .leftBrace) ∧
          PathExportOrdinaryParses start afterKeyword declaration output)) := by
  cases parsed with
  | ofLocal localParsed =>
      rcases localParsed with ⟨start, keyword, payload⟩
      exact ⟨start, _, ⟨keyword, rfl⟩,
        Or.inl ⟨exportDecl_local_opening payload, payload⟩⟩
  | ofModule moduleParsed =>
      rcases moduleParsed with ⟨start, keyword, absent, payload⟩
      exact ⟨start, _, ⟨keyword, rfl⟩,
        Or.inr ⟨absent, .module payload⟩⟩
  | ofModuleAs aliasParsed =>
      rcases aliasParsed with ⟨start, keyword, absent, payload⟩
      exact ⟨start, _, ⟨keyword, rfl⟩,
        Or.inr ⟨absent, .moduleAs payload⟩⟩
  | ofItemsFrom selectedParsed =>
      rcases selectedParsed with ⟨start, keyword, absent, payload⟩
      exact ⟨start, _, ⟨keyword, rfl⟩,
        Or.inr ⟨absent, .itemsFrom payload⟩⟩

/-- Complete exports fix their keyword span, entire payload, and closing span. -/
theorem ExportDeclOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportDeclOrdinaryParses input left afterLeft)
    (rightParsed : ExportDeclOrdinaryParses input right afterRight) :
    left = right := by
  rcases exportDecl_exact_dispatch leftParsed with
    ⟨leftSpan, leftAfterKeyword, leftKeyword, leftBranch⟩
  rcases exportDecl_exact_dispatch rightParsed with
    ⟨rightSpan, rightAfterKeyword, rightKeyword, rightBranch⟩
  rcases leftKeyword.result_unique rightKeyword with ⟨spanEq, afterEq⟩
  cases spanEq
  cases afterEq
  rcases leftBranch with ⟨leftPresent, leftLocal⟩ | ⟨leftAbsent, leftPath⟩
  · rcases rightBranch with ⟨rightPresent, rightLocal⟩ | ⟨rightAbsent, rightPath⟩
    · exact (localExportExactOutcomeSpec leftSpan).successValueUnique
        leftLocal rightLocal
    · exact False.elim (rightAbsent leftPresent)
  · rcases rightBranch with ⟨rightPresent, rightLocal⟩ | ⟨rightAbsent, rightPath⟩
    · exact False.elim (leftAbsent rightPresent)
    · exact (pathExportExactOutcomeSpec leftSpan).successValueUnique
        leftPath rightPath

/-- Complete export success fixes its entire AST and final remainder. -/
theorem ExportDeclOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportDeclOrdinaryParses input left afterLeft)
    (rightParsed : ExportDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

private theorem exportDecl_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem exportDecl_present_conflicts_absent {input : Remainder}
    (present : ExportDeclLeftBracePresentAt input)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftBrace)) : False :=
  absent present

/-- Complete export rejection fixes the selected local or path endpoint. -/
theorem ExportDeclRejects.output_unique {input left right : Remainder}
    (leftRejected : ExportDeclRejects input left)
    (rightRejected : ExportDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [exportDecl_absent_conflicts_exact, exportDecl_present_conflicts_absent,
      ExactTokenParses.output_unique, LocalExportRejects.output_unique,
      PathExportRejects.output_unique]

/-- Complete export declarations have unconditional exact AST, remainder,
and rejecting-endpoint outcomes, without diagnostic payload equality. -/
theorem exportDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ExportDeclOrdinaryParses ExportDeclRejects where
  toDeterministicOutcomeSpec := exportDeclDeterministicOutcomeSpec
  successValueUnique := ExportDeclOrdinaryParses.value_unique
  rejectOutputUnique := ExportDeclRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end
