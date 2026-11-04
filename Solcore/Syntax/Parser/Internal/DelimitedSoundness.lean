import Solcore.Syntax.Parser.Tokens
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.State
import Solcore.Syntax.Module
import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Parser.Primitive
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Internal.DelimitedOutcomes

/-!
Soundness of the parsers of delimited lists and identifiers: each success and each
rejection has its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Operator
set_option autoImplicit false

namespace Solcore.Syntax.Parser

open OperatorInternals

private theorem operatorParts_validFor (context : ParseContext) :
    ∀ fuel partsRev state,
      (state.ValidFor →
        (operatorParts context fuel partsRev state).ValidFor state
          (fun _ _ => True)) ∧
      ∀ parts next, operatorParts context fuel partsRev state = .ok parts next →
        next.tokens = state.tokens ∧ state.cursor ≤ next.cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro partsRev state
      refine ⟨fun _ => trivial, ?_⟩
      intro parts next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro partsRev state
      unfold operatorParts
      cases found : state.peek? with
      | some token =>
          simp only
          cases part : operatorPart? token.value with
          | some spelling =>
              simp only
              have recursive := inductionHypothesis (spelling :: partsRev)
                { state with cursor := state.cursor + 1 }
              refine ⟨?_, ?_⟩
              · intro stateValid
                have advancedValid :
                    ({ state with cursor := state.cursor + 1 } : State).ValidFor := by
                  apply stateValid.advance?_validFor (token := token)
                  unfold State.advance?
                  rw [found]
                  rfl
                exact (recursive.1 advancedValid).of_file_eq rfl
              intro parts next result
              have shape := recursive.2 parts next result
              exact ⟨shape.1, Nat.le_trans
                (Nat.le_add_right state.cursor 1) shape.2⟩
          | none =>
              simp only
              split
              · refine ⟨?_, ?_⟩
                · intro stateValid
                  unfold rejectAt Reply.ValidFor
                  exact ⟨stateValid.currentSpan_validFor, stateValid, rfl⟩
                · intro parts next result
                  contradiction
              · refine ⟨?_, ?_⟩
                · intro stateValid
                  exact ⟨trivial, stateValid, rfl⟩
                intro parts next result
                cases result
                exact ⟨rfl, Nat.le_refl _⟩

      | none =>
          simp only
          split
          · refine ⟨?_, ?_⟩
            · intro stateValid
              unfold rejectAt Reply.ValidFor
              exact ⟨stateValid.currentSpan_validFor, stateValid, rfl⟩
            · intro parts next result
              contradiction
          · refine ⟨?_, ?_⟩
            · intro stateValid
              exact ⟨trivial, stateValid, rfl⟩
            intro parts next result
            cases result
            exact ⟨rfl, Nat.le_refl _⟩

private theorem operatorParts_preservesTokenWindow
    (context : ParseContext) :
    ∀ fuel partsRev,
      Parser.PreservesTokenWindow (operatorParts context fuel partsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro partsRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro partsRev input
      unfold operatorParts
      cases found : input.peek? with
      | some token =>
          simp only
          cases part : operatorPart? token.value with
          | some spelling =>
              simp only
              exact (inductionHypothesis (spelling :: partsRev)
                { input with cursor := input.cursor + 1 }).trans ⟨rfl, rfl⟩
          | none =>
              simp only
              split
              · exact rejectAt_preservesTokenWindow input _ _
              · exact ⟨rfl, rfl⟩
      | none =>
          simp only
          split
          · exact rejectAt_preservesTokenWindow input _ _
          · exact ⟨rfl, rfl⟩

/-- Parenthesized operator selectors preserve their complete source range. -/
theorem operatorSelector_validFor (context : ParseContext) :
    (operatorSelector context).ValidFor SelectorName.ValidFor := by
  intro input inputValid
  unfold operatorSelector
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have openingValid := symbol_validFor .leftParen context input inputValid
      rw [openingResult] at openingValid
      simpa only [Reply.ValidFor] using openingValid
  | ok opening afterOpening =>
      have openingValid := symbol_validFor .leftParen context input inputValid
      rw [openingResult] at openingValid
      have openingShape :=
        symbol_ok_state_shape .leftParen context openingResult
      have partsProperties := operatorParts_validFor context
        (afterOpening.remainingCount + 1) [] afterOpening
      simp only
      cases partsResult : operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          have partsValid := partsProperties.1 openingValid.2.1
          rw [partsResult] at partsValid
          simpa only [Reply.ValidFor] using
            partsValid.of_file_eq openingValid.2.2
      | ok parts afterParts =>
          have partsValid := partsProperties.1 openingValid.2.1
          rw [partsResult] at partsValid
          have partsShape := partsProperties.2 parts afterParts partsResult
          have openingFoundInput :=
            State.getElem?_eq_some_of_peek?_eq_some openingShape.1
          have openingFoundAfterParts :
              afterParts.tokens[input.cursor]? = some opening := by
            simpa [partsShape.1, openingShape.2] using openingFoundInput
          have openingBeforeAfterOpening :
              input.cursor < afterOpening.cursor := by
            rw [openingShape.2]
            simp
          have openingBeforeAfterParts : input.cursor < afterParts.cursor :=
            Nat.lt_of_lt_of_le openingBeforeAfterOpening partsShape.2
          have openingSpanValidAfterParts :
              opening.span.ValidFor afterParts.file := by
            have spanValid : opening.span.ValidFor input.file := by
              simpa only [Located.ValidFor] using openingValid.1
            simpa [partsValid.2.2, openingValid.2.2] using spanValid
          simp only
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp only [Reply.ValidFor]
          | reject failure rejected =>
              have closingValid :=
                symbol_validFor .rightParen context afterParts partsValid.2.1
              rw [closingResult] at closingValid
              simpa only [Reply.ValidFor] using closingValid.of_file_eq
                (partsValid.2.2.trans openingValid.2.2)
          | ok closing next =>
              have closingValid :=
                symbol_validFor .rightParen context afterParts partsValid.2.1
              rw [closingResult] at closingValid
              have closingShape :=
                symbol_ok_state_shape .rightParen context closingResult
              have closingFound :=
                State.getElem?_eq_some_of_peek?_eq_some closingShape.1
              have openingBeforeClosing :=
                partsValid.2.1.token_end_le_token_start_of_getElem?_lt
                  openingFoundAfterParts closingFound openingBeforeAfterParts
              have closingSpanValid :
                  closing.span.ValidFor afterParts.file := by
                simpa only [Located.ValidFor] using closingValid.1
              have coverValidAfterParts :
                  (SourceSpan.cover opening.span closing.span).ValidFor
                    afterParts.file := by
                apply SourceSpan.cover_validFor openingSpanValidAfterParts
                  closingSpanValid
                exact Nat.le_trans openingSpanValidAfterParts.2.1
                  (Nat.le_trans openingBeforeClosing closingSpanValid.2.1)
              have coverValidInput :
                  (SourceSpan.cover opening.span closing.span).ValidFor
                    input.file := by
                simpa [partsValid.2.2, openingValid.2.2] using
                  coverValidAfterParts
              simp only
              unfold Reply.ValidFor SelectorName.ValidFor
              exact ⟨⟨coverValidInput, trivial⟩, closingValid.2.1,
                closingValid.2.2.trans
                  (partsValid.2.2.trans openingValid.2.2)⟩

/-- Operator selectors preserve the token window on every ordinary reply. -/
theorem operatorSelector_preservesTokenWindow (context : ParseContext) :
    Parser.PreservesTokenWindow (operatorSelector context) := by
  intro input
  unfold operatorSelector
  have openingShape := symbol_preservesTokenWindow .leftParen context input
  cases openingResult : symbol .leftParen context input with
  | invariant error =>
      simp only [Reply.PreservesTokenWindow]
  | reject failure rejected =>
      rw [openingResult] at openingShape
      simpa only [openingResult, Reply.PreservesTokenWindow] using openingShape
  | ok opening afterOpening =>
      rw [openingResult] at openingShape
      simp only
      have partsShape := operatorParts_preservesTokenWindow context
        (afterOpening.remainingCount + 1) [] afterOpening
      cases partsResult : operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error =>
          simp only [Reply.PreservesTokenWindow]
      | reject failure rejected =>
          rw [partsResult] at partsShape
          simpa only [Reply.PreservesTokenWindow] using
            partsShape.trans openingShape
      | ok parts afterParts =>
          rw [partsResult] at partsShape
          simp only
          have closingShape := symbol_preservesTokenWindow .rightParen
            context afterParts
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error =>
              simp only [Reply.PreservesTokenWindow]
          | reject failure rejected =>
              rw [closingResult] at closingShape
              simpa only [Reply.PreservesTokenWindow] using
                closingShape.trans (partsShape.trans openingShape)
          | ok closing next =>
              rw [closingResult] at closingShape
              simpa only [Reply.PreservesTokenWindow] using
                closingShape.trans (partsShape.trans openingShape)

/-- Operator-selector success preserves the immutable token carrier. -/
theorem operatorSelector_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (operatorSelector context) := by
  intro input selector next result
  unfold operatorSelector at result
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      cases partsResult : operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp [partsResult] at result
      | reject failure rejected => simp [partsResult] at result
      | ok parts afterParts =>
          simp only [partsResult] at result
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | ok closing final =>
              simp only [closingResult] at result
              cases result
              have openingShape :=
                symbol_ok_state_shape .leftParen context openingResult
              have partsShape := (operatorParts_validFor context
                (afterOpening.remainingCount + 1) [] afterOpening).2
                  parts afterParts partsResult
              have closingShape :=
                symbol_ok_state_shape .rightParen context closingResult
              calc
                next.tokens = afterParts.tokens := by rw [closingShape.2]
                _ = afterOpening.tokens := partsShape.1
                _ = input.tokens := by rw [openingShape.2]

/-- An operator selector starts at its retained opening parenthesis. -/
theorem operatorSelector_startsAtCurrentTokenOnSuccess
    (context : ParseContext) :
    Parser.StartsAtCurrentTokenOnSuccess
      (operatorSelector context) (·.span) := by
  intro input selector next result
  unfold operatorSelector at result
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      cases partsResult : operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp [partsResult] at result
      | reject failure rejected => simp [partsResult] at result
      | ok parts afterParts =>
          simp only [partsResult] at result
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | ok closing final =>
              simp only [closingResult] at result
              cases result
              exact ⟨opening,
                (symbol_ok_state_shape .leftParen context openingResult).1,
                rfl⟩

/-- Identifier and operator selector branches preserve every stored source span. -/
theorem selectorName_validFor (context : ParseContext) :
    (selectorName context).ValidFor SelectorName.ValidFor := by
  intro input inputValid
  unfold selectorName
  split
  · exact operatorSelector_validFor context input inputValid
  · cases identifierResult : identifier context input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have nameValid := identifier_validFor context input inputValid
        rw [identifierResult] at nameValid
        simpa only [Reply.ValidFor] using nameValid
    | ok name next =>
        have nameValid := identifier_validFor context input inputValid
        rw [identifierResult] at nameValid
        have spanValid : name.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using nameValid.1
        simp only
        unfold Reply.ValidFor SelectorName.ValidFor
        exact ⟨⟨spanValid, spanValid⟩, nameValid.2.1, nameValid.2.2⟩

/-- Selector names preserve the token window on every ordinary reply. -/
theorem selectorName_preservesTokenWindow (context : ParseContext) :
    Parser.PreservesTokenWindow (selectorName context) := by
  intro input
  unfold selectorName
  split
  · exact operatorSelector_preservesTokenWindow context input
  · have nameShape := identifier_preservesTokenWindow context input
    cases nameResult : identifier context input with
    | invariant error =>
        simp only [Reply.PreservesTokenWindow]
    | reject failure rejected =>
        rw [nameResult] at nameShape
        simpa only [nameResult, Reply.PreservesTokenWindow] using nameShape
    | ok name next =>
        rw [nameResult] at nameShape
        simpa only [nameResult, Reply.PreservesTokenWindow] using nameShape

/-- Selector-name success preserves the token carrier in both branches. -/
theorem selectorName_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (selectorName context) := by
  intro input selector next result
  unfold selectorName at result
  split at result
  · exact operatorSelector_preservesTokensOnSuccess context
      input selector next result
  · cases identifierResult : identifier context input with
    | invariant error => simp [identifierResult] at result
    | reject failure rejected => simp [identifierResult] at result
    | ok name afterName =>
        simp only [identifierResult] at result
        cases result
        rcases identifier_ok_state_shape context identifierResult with
          ⟨_token, _found, _span, tokensEq, _cursor⟩
        exact tokensEq

/-- A selector name starts at its identifier or opening parenthesis. -/
theorem selectorName_startsAtCurrentTokenOnSuccess (context : ParseContext) :
    Parser.StartsAtCurrentTokenOnSuccess (selectorName context) (·.span) := by
  intro input selector next result
  unfold selectorName at result
  split at result
  · exact operatorSelector_startsAtCurrentTokenOnSuccess context
      input selector next result
  · cases identifierResult : identifier context input with
    | invariant error => simp [identifierResult] at result
    | reject failure rejected => simp [identifierResult] at result
    | ok name afterName =>
        simp only [identifierResult] at result
        cases result
        rcases identifier_ok_state_shape context identifierResult with
          ⟨token, found, span, _tokens, _cursor⟩
        exact ⟨token, found, congrArg SourceSpan.startByte span⟩

/-- Parenthesized operator selectors consume both delimiters. -/
theorem operatorSelector_cursor_lt_onSuccess (context : ParseContext)
    {input next : State} {selector : SelectorName}
    (result : operatorSelector context input = .ok selector next) :
    input.cursor < next.cursor := by
  unfold operatorSelector at result
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      cases partsResult : operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp [partsResult] at result
      | reject failure rejected => simp [partsResult] at result
      | ok parts afterParts =>
          simp only [partsResult] at result
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | ok closing final =>
              simp only [closingResult] at result
              cases result
              have openingProgress : input.cursor < afterOpening.cursor := by
                rw [(symbol_ok_state_shape .leftParen context
                  openingResult).2]
                simp
              have partsMonotone := (operatorParts_validFor context
                (afterOpening.remainingCount + 1) [] afterOpening).2
                  parts afterParts partsResult |>.2
              have closingProgress : afterParts.cursor < next.cursor := by
                rw [(symbol_ok_state_shape .rightParen context
                  closingResult).2]
                simp
              exact Nat.lt_trans openingProgress
                (Nat.lt_of_le_of_lt partsMonotone closingProgress)

/-- Operator-selector success never moves the parser cursor backwards. -/
theorem operatorSelector_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (operatorSelector context) := by
  intro input selector next result
  exact Nat.le_of_lt (operatorSelector_cursor_lt_onSuccess context result)

/-- Every successful selector consumes an identifier or operator group. -/
theorem selectorName_cursor_lt_onSuccess (context : ParseContext)
    {input next : State} {selector : SelectorName}
    (result : selectorName context input = .ok selector next) :
    input.cursor < next.cursor := by
  unfold selectorName at result
  split at result
  · exact operatorSelector_cursor_lt_onSuccess context result
  · cases identifierResult : identifier context input with
    | invariant error => simp [identifierResult] at result
    | reject failure rejected => simp [identifierResult] at result
    | ok name afterName =>
        simp only [identifierResult] at result
        cases result
        rw [(identifier_ok_state_shape context identifierResult).choose_spec.2.2.2]
        simp

/-- Selector-name success never moves the parser cursor backwards. -/
theorem selectorName_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (selectorName context) := by
  intro input selector next result
  exact Nat.le_of_lt (selectorName_cursor_lt_onSuccess context result)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.OperatorTotalityProperties`
-/

/-! Fuel adequacy and totality for operator selector parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace OperatorInternals

/-- More fuel than remaining tokens excludes collector fuel exhaustion. -/
theorem operatorParts_ordinary_of_remainingCount_lt
    (context : ParseContext) :
    ∀ fuel partsRev state, state.remainingCount < fuel →
      (∃ parts next,
        operatorParts context fuel partsRev state = .ok parts next) ∨
      (∃ failure next,
        operatorParts context fuel partsRev state = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro partsRev state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro partsRev state adequate
      unfold operatorParts
      cases found : state.peek? with
      | some token =>
          simp only
          cases part : operatorPart? token.value with
          | some spelling =>
              simp only
              apply inductionHypothesis (spelling :: partsRev)
                { state with cursor := state.cursor + 1 }
              have cursorBeforeEnd :=
                State.cursor_lt_endIndex_of_peek?_eq_some found
              simp only [State.remainingCount] at adequate ⊢
              omega
          | none =>
              simp only
              split
              · exact Or.inr (by simp [rejectAt])
              · exact Or.inl ⟨_, state, rfl⟩
      | none =>
          simp only
          split
          · exact Or.inr (by simp [rejectAt])
          · exact Or.inl ⟨_, state, rfl⟩

/-- Adequately fueled collection cannot expose an invariant reply. -/
theorem operatorParts_ne_invariant_of_remainingCount_lt
    (context : ParseContext) (fuel : Nat) (partsRev : List String)
    (state : State) (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    operatorParts context fuel partsRev state ≠ .invariant error := by
  intro failed
  rcases operatorParts_ordinary_of_remainingCount_lt context fuel partsRev
      state adequate with
    ⟨parts, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- The production collector fuel is always adequate. -/
theorem operatorParts_production_ordinary
    (context : ParseContext) (partsRev : List String) (state : State) :
    (∃ parts next,
      operatorParts context (state.remainingCount + 1) partsRev state =
        .ok parts next) ∨
      (∃ failure next,
        operatorParts context (state.remainingCount + 1) partsRev state =
          .reject failure next) :=
  operatorParts_ordinary_of_remainingCount_lt context
    (state.remainingCount + 1) partsRev state (by omega)

/-- Production collector fuel cannot expose an invariant reply. -/
theorem operatorParts_production_ne_invariant
    (context : ParseContext) (partsRev : List String) (state : State)
    (error : ParserInvariantError) :
    operatorParts context (state.remainingCount + 1) partsRev state ≠
      .invariant error :=
  operatorParts_ne_invariant_of_remainingCount_lt context
    (state.remainingCount + 1) partsRev state (by omega) error

end OperatorInternals

open OperatorInternals

/-- Parenthesized operator-selector parsing is ordinary on every input. -/
theorem operatorSelector_ordinary (context : ParseContext) :
    Parser.Ordinary (operatorSelector context) := by
  intro input
  rcases (symbol_ordinary .leftParen context) input with
    ⟨opening, afterOpening, openingResult⟩ |
    ⟨failure, rejected, openingResult⟩
  · rcases operatorParts_production_ordinary context [] afterOpening with
      ⟨parts, afterParts, partsResult⟩ |
      ⟨failure, rejected, partsResult⟩
    · rcases (symbol_ordinary .rightParen context) afterParts with
        ⟨closing, next, closingResult⟩ |
        ⟨failure, rejected, closingResult⟩
      · refine Or.inl ⟨{
            span := SourceSpan.cover opening.span closing.span
            value := .operator (String.join parts)
          }, next, ?_⟩
        unfold operatorSelector
        simp only [openingResult, partsResult, closingResult]
      · exact Or.inr ⟨failure, rejected, by
          unfold operatorSelector
          simp only [openingResult, partsResult, closingResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        unfold operatorSelector
        simp only [openingResult, partsResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      unfold operatorSelector
      simp only [openingResult]⟩

/-- Operator-selector parsing cannot expose an invariant reply. -/
theorem operatorSelector_ne_invariant (context : ParseContext)
    (input : State) (error : ParserInvariantError) :
    operatorSelector context input ≠ .invariant error :=
  (operatorSelector_ordinary context).ne_invariant input error

/-- Selector-name dispatch is ordinary on every input. -/
theorem selectorName_ordinary (context : ParseContext) :
    Parser.Ordinary (selectorName context) := by
  intro input
  unfold selectorName
  split
  · exact operatorSelector_ordinary context input
  · rcases (identifier_ordinary context) input with
      ⟨name, next, result⟩ | ⟨failure, rejected, result⟩
    · exact Or.inl ⟨{
          span := name.span
          value := .identifier name
        }, next, by simp only [result]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [result]⟩

/-- Selector-name parsing cannot expose an invariant reply. -/
theorem selectorName_ne_invariant (context : ParseContext)
    (input : State) (error : ParserInvariantError) :
    selectorName context input ≠ .invariant error :=
  (selectorName_ordinary context).ne_invariant input error

/-- Operator selectors satisfy the strict generic-element totality boundary. -/
theorem operatorSelector_elementTotalityContract (context : ParseContext) :
    ElementTotalityContract (operatorSelector context) := {
  validFor := (operatorSelector_validFor context).mono
    (fun _ _ _ => trivial)
  preservesTokenWindow := operatorSelector_preservesTokenWindow context
  cursorLtOnSuccess := operatorSelector_cursor_lt_onSuccess context
  invariantFree := fun input _inputValid error =>
    operatorSelector_ne_invariant context input error
}

/-- Selector names satisfy the strict generic-element totality boundary. -/
theorem selectorName_elementTotalityContract (context : ParseContext) :
    ElementTotalityContract (selectorName context) := {
  validFor := (selectorName_validFor context).mono
    (fun _ _ _ => trivial)
  preservesTokenWindow := selectorName_preservesTokenWindow context
  cursorLtOnSuccess := selectorName_cursor_lt_onSuccess context
  invariantFree := fun input _inputValid error =>
    selectorName_ne_invariant context input error
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.InvariantFreeProperties
/-! Compositional invariant-freedom laws for canonical parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.Parser

/-- Every valid input receives an ordinary success or rejection reply. -/
def InvariantFreeOnValid {alpha : Type} (parser : Parser alpha) : Prop :=
  ∀ input, input.ValidFor →
    (∃ value next, parser input = .ok value next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace InvariantFreeOnValid

/-- Valid-input ordinary classification excludes every invariant reply. -/
theorem ne_invariant {alpha : Type} {parser : Parser alpha}
    (invariantFree : InvariantFreeOnValid parser)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases invariantFree input inputValid with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end InvariantFreeOnValid

/-- Excluding every invariant constructor recovers ordinary classification. -/
theorem invariantFreeOnValid_of_ne_invariant {alpha : Type}
    {parser : Parser alpha}
    (noInvariant : ∀ input, input.ValidFor → ∀ error,
      parser input ≠ .invariant error) :
    InvariantFreeOnValid parser := by
  intro input inputValid
  cases result : parser input with
  | ok value next => exact Or.inl ⟨value, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      exact False.elim (noInvariant input inputValid error result)

/-- Ordinary classification and no-invariant formulations are equivalent. -/
theorem invariantFreeOnValid_iff_ne_invariant {alpha : Type}
    {parser : Parser alpha} :
    InvariantFreeOnValid parser ↔
      ∀ input, input.ValidFor → ∀ error,
        parser input ≠ .invariant error :=
  ⟨fun free => free.ne_invariant, invariantFreeOnValid_of_ne_invariant⟩

/-- An ordinary parser is invariant-free on the smaller valid-input domain. -/
theorem Ordinary.invariantFreeOnValid {alpha : Type}
    {parser : Parser alpha} (ordinary : Ordinary parser) :
    InvariantFreeOnValid parser :=
  fun input _inputValid => ordinary input

/-- Pure parsers are invariant-free on every valid input. -/
theorem pure_invariantFreeOnValid {alpha : Type} (value : alpha) :
    InvariantFreeOnValid (pure value : Parser alpha) := by
  intro input _inputValid
  exact Or.inl ⟨value, input, rfl⟩

/--
Bind is invariant-free when its first parser preserves valid states and both
stages are invariant-free on valid inputs.
-/
theorem bind_invariantFreeOnValid {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {firstValueValid : SourceFile → alpha → Prop}
    (firstValid : first.ValidFor firstValueValid)
    (firstFree : InvariantFreeOnValid first)
    (nextFree : ∀ value, InvariantFreeOnValid (next value)) :
    InvariantFreeOnValid (first >>= next) := by
  intro input inputValid
  rcases firstFree input inputValid with
    ⟨firstValue, afterFirst, firstResult⟩ |
    ⟨failure, rejected, firstResult⟩
  · have firstReply := firstValid input inputValid
    rw [firstResult] at firstReply
    rcases nextFree firstValue afterFirst firstReply.2.1 with
      ⟨value, final, nextResult⟩ | ⟨failure, final, nextResult⟩
    · exact Or.inl ⟨value, final, by
        simp only [bind, firstResult, nextResult]⟩
    · exact Or.inr ⟨failure, final, by
        simp only [bind, firstResult, nextResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [bind, firstResult]⟩

/-- Transactional choice is invariant-free when both alternatives are. -/
theorem orElse_invariantFreeOnValid {alpha : Type}
    {first second : Parser alpha}
    (firstFree : InvariantFreeOnValid first)
    (secondFree : InvariantFreeOnValid second) :
    InvariantFreeOnValid (orElse first second) := by
  intro input inputValid
  rcases firstFree input inputValid with
    ⟨value, next, firstResult⟩ | ⟨failure, rejected, firstResult⟩
  · exact Or.inl ⟨value, next, by
      simp only [orElse, firstResult]⟩
  · rcases secondFree input inputValid with
      ⟨value, next, secondResult⟩ | ⟨failure, next, secondResult⟩
    · exact Or.inl ⟨value, next, by
        simp only [orElse, firstResult, secondResult]⟩
    · exact Or.inr ⟨failure, next, by
        simp only [orElse, firstResult, secondResult]⟩

/-- Reading the parser state is invariant-free. -/
theorem getState_invariantFreeOnValid :
    InvariantFreeOnValid getState := by
  intro input _inputValid
  exact Or.inl ⟨input, input, rfl⟩

/-- Any total state update has an ordinary parser result. -/
theorem modifyState_invariantFreeOnValid (update : State → State) :
    InvariantFreeOnValid (modifyState update) := by
  intro input _inputValid
  exact Or.inl ⟨(), update input, rfl⟩

/-- Emitting one diagnostic is invariant-free. -/
theorem emitDiagnostic_invariantFreeOnValid
    (diagnostic : ParseDiagnostic) :
    InvariantFreeOnValid (emitDiagnostic diagnostic) := by
  unfold emitDiagnostic
  exact modifyState_invariantFreeOnValid _

/-- A parser that rejects at its input state is invariant-free. -/
theorem rejectAt_invariantFreeOnValid {alpha : Type}
    (expected : NonemptyList ParseExpectation) (context : ParseContext) :
    InvariantFreeOnValid (fun state =>
      rejectAt (α := alpha) state expected context) := by
  intro input _inputValid
  exact Or.inr ⟨_, input, rfl⟩

end Solcore.Syntax.Parser.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
/-! Primitive facts used by ordinary-rejection reflection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Positive symbol lookahead determines the following symbol parse exactly. -/
theorem symbol_eq_ok_of_isSymbol_eq_true (value : Symbol)
    (context : ParseContext) {input : State}
    (present : isSymbol input value = true) :
    ∃ token, symbol value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isSymbol State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .symbol value) = true at present
      refine ⟨token, ?_⟩
      unfold symbol acceptToken
      simp only [found, present, ↓reduceIte]

/-- Ordinary symbol rejection is exact evidence that the symbol is absent. -/
theorem symbol_reject_tokenKindAbsentAt (value : Symbol)
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : symbol value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol value) := by
  by_cases present : isSymbol input value = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true value context present with
      ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact symbolAbsentAt_of_isSymbol_eq_false value
      (Bool.eq_false_iff.mpr present)

/-- Ordinary symbol rejection retains the complete input state. -/
theorem symbol_reject_state_eq (value : Symbol) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : symbol value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.symbol value) context
    (· == .symbol value) result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedTailRejectionSoundnessProperties
/-! Exact ordinary-rejection reflection for the delimited tail loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem preferredCloseNotTaken_of_guard_false (closing : Symbol)
    (allowClose : Bool) {input : State}
    (guard : (allowClose && isSymbol input closing) = false) :
    DeclarativeGrammar.PreferredCloseNotTaken closing allowClose
      input.declarativeRemainder := by
  cases allowClose with
  | false => exact .disabled
  | true =>
      exact .absent (symbolAbsentAt_of_isSymbol_eq_false closing (by
        simpa using guard))

/-- Every ordinary tail rejection records the exact branch and failed state. -/
theorem afterDelimitedElement_reject_sound {α : Type}
    (element : Parser α)
    (ordinaryParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (elementSuccessSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
      ordinaryParses input.declarativeRemainder value
        next.declarativeRemainder)
    (elementRejectSound : ∀ {input rejected : State} {failure : Failure},
      element input = .reject failure rejected →
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder)
    (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input rejected failure,
      afterDelimitedElement element closing allowTrailing context phase
          opening fuel elementsRev input = .reject failure rejected →
      DeclarativeGrammar.DelimitedTailRejects closing allowTrailing
        ordinaryParses nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input rejected failure result
      simp [afterDelimitedElement] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input rejected failure result
      unfold afterDelimitedElement at result
      by_cases commaPresent : isSymbol input .comma = true
      · simp only [commaPresent, if_true] at result
        rcases symbol_eq_ok_of_isSymbol_eq_true .comma context commaPresent with
          ⟨comma, commaResult⟩
        simp only [commaResult] at result
        by_cases trailingClose :
            (allowTrailing && isSymbol
              { input with cursor := input.cursor + 1 } closing) = true
        · simp only [trailingClose, if_true] at result
          have closingPresent : isSymbol
              { input with cursor := input.cursor + 1 } closing = true :=
            by
              cases allowTrailing with
              | false => simp at trailingClose
              | true => simpa using trailingClose
          rcases symbol_eq_ok_of_isSymbol_eq_true closing context
              closingPresent with ⟨closingToken, closingResult⟩
          unfold closeDelimited at result
          simp [closingResult] at result
        · have trailingCloseFalse :
              (allowTrailing && isSymbol
                { input with cursor := input.cursor + 1 } closing) = false :=
            Bool.eq_false_iff.mpr trailingClose
          simp only [trailingCloseFalse, Bool.false_eq_true, if_false]
            at result
          cases elementResult : element
              { input with cursor := input.cursor + 1 } with
          | invariant error => simp [elementResult] at result
          | reject nestedFailure nestedFailed =>
              simp only [elementResult] at result
              cases result
              have commaToken :=
                (symbol_ok_tokenAt .comma context commaResult).1
              have continues := preferredCloseNotTaken_of_guard_false closing
                allowTrailing (input :=
                  { input with cursor := input.cursor + 1 }) trailingCloseFalse
              have nestedRejected := elementRejectSound elementResult
              exact .elementRejected comma.span commaToken
                (by simpa [State.declarativeRemainder] using
                  continues)
                (by simpa [State.declarativeRemainder] using
                  nestedRejected)
          | ok value afterElement =>
              simp only [elementResult] at result
              by_cases progressed : afterElement.cursor > input.cursor + 1
              · simp only [progressed, if_true] at result
                have commaToken :=
                  (symbol_ok_tokenAt .comma context commaResult).1
                have continues := preferredCloseNotTaken_of_guard_false
                  closing allowTrailing (input :=
                    { input with cursor := input.cursor + 1 })
                    trailingCloseFalse
                have ordinary := elementSuccessSound elementResult
                have tailRejected := inductionHypothesis (value :: elementsRev)
                  afterElement rejected failure result
                have continuesInput :
                    DeclarativeGrammar.PreferredCloseNotTaken closing
                      allowTrailing {
                        input.declarativeRemainder with
                          cursor := input.cursor + 1
                      } := by
                  simpa [State.declarativeRemainder] using continues
                have ordinaryInput : ordinaryParses {
                      input.declarativeRemainder with
                        cursor := input.cursor + 1
                    } value afterElement.declarativeRemainder := by
                  simpa [State.declarativeRemainder] using ordinary
                have progressInput : input.declarativeRemainder.cursor + 1 <
                    afterElement.declarativeRemainder.cursor := by
                  simpa [State.declarativeRemainder] using progressed
                exact .laterRejected comma.span commaToken
                  continuesInput ordinaryInput progressInput
                  tailRejected
              · simp [progressed] at result
      · have commaAbsent : isSymbol input .comma = false :=
          Bool.eq_false_iff.mpr commaPresent
        simp only [commaAbsent, Bool.false_eq_true, if_false] at result
        by_cases closingPresent : isSymbol input closing = true
        · simp only [closingPresent, if_true] at result
          rcases symbol_eq_ok_of_isSymbol_eq_true closing context
              closingPresent with ⟨closingToken, closingResult⟩
          unfold closeDelimited at result
          simp [closingResult] at result
        · have closingAbsent : isSymbol input closing = false :=
            Bool.eq_false_iff.mpr closingPresent
          simp only [closingAbsent, Bool.false_eq_true, if_false] at result
          unfold rejectAt at result
          cases result
          exact .delimiterMissing
            (symbolAbsentAt_of_isSymbol_eq_false .comma commaAbsent)
            (symbolAbsentAt_of_isSymbol_eq_false closing closingAbsent)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
/-! Exact ordinary-rejection reflection for complete delimited attempts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every ordinary delimited rejection records its exact failed remainder. -/
theorem delimitedWithPolicy_reject_sound {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α)
    (ordinaryParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSuccessSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
      ordinaryParses input.declarativeRemainder value
        next.declarativeRemainder)
    (elementRejectSound : ∀ {input rejected : State} {failure : Failure},
      element input = .reject failure rejected →
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : delimitedWithPolicy opening closing allowEmpty allowTrailing
      element context phase input = .reject failure rejected) :
    DeclarativeGrammar.DelimitedListRejects opening closing allowEmpty
      allowTrailing ordinaryParses nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingFailed =>
      have openingFailedEq := symbol_reject_state_eq opening context
        openingResult
      simp only [openingResult] at result
      subst openingFailed
      cases result
      exact .openingMissing (input := input.declarativeRemainder)
        (symbol_reject_tokenKindAbsentAt opening context openingResult)
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult] at result
      by_cases emptyClose :
          (allowEmpty && isSymbol afterOpening closing) = true
      · simp only [emptyClose, if_true] at result
        have closingPresent : isSymbol afterOpening closing = true := by
          cases allowEmpty with
          | false => simp at emptyClose
          | true => simpa using emptyClose
        rcases symbol_eq_ok_of_isSymbol_eq_true closing context
            closingPresent with ⟨closingToken, closingResult⟩
        unfold closeDelimited at result
        simp [closingResult] at result
      · have emptyCloseFalse :
            (allowEmpty && isSymbol afterOpening closing) = false :=
          Bool.eq_false_iff.mpr emptyClose
        simp only [emptyCloseFalse, Bool.false_eq_true, if_false] at result
        have continues := preferredCloseNotTaken_of_guard_false closing
          allowEmpty emptyCloseFalse
        cases elementResult : element afterOpening with
        | invariant error => simp [elementResult] at result
        | reject nestedFailure nestedFailed =>
            simp only [elementResult] at result
            cases result
            have nestedRejected := elementRejectSound elementResult
            exact .firstRejected openingToken.span openingSound.1
              (by simpa [openingSound.2, State.declarativeRemainder] using
                continues)
              (by simpa [openingSound.2, State.declarativeRemainder] using
                nestedRejected)
        | ok first afterFirst =>
            simp only [elementResult] at result
            by_cases progressed : afterFirst.cursor > afterOpening.cursor
            · simp only [progressed, if_true] at result
              have ordinary := elementSuccessSound elementResult
              have tailRejected := afterDelimitedElement_reject_sound element
                ordinaryParses nestedRejects elementSuccessSound
                  elementRejectSound closing allowTrailing context phase
                    openingToken (afterOpening.remainingCount + 1) [first]
                      afterFirst rejected failure result
              have continuesInput :
                  DeclarativeGrammar.PreferredCloseNotTaken closing allowEmpty {
                    input.declarativeRemainder with
                      cursor := input.cursor + 1
                  } := by
                simpa [openingSound.2, State.declarativeRemainder] using
                  continues
              have ordinaryInput : ordinaryParses {
                    input.declarativeRemainder with cursor := input.cursor + 1
                  } first afterFirst.declarativeRemainder := by
                simpa [openingSound.2, State.declarativeRemainder] using ordinary
              have progressInput : input.declarativeRemainder.cursor + 1 <
                  afterFirst.declarativeRemainder.cursor := by
                simpa [openingSound.2, State.declarativeRemainder] using
                  progressed
              exact .tailRejected openingToken.span openingSound.1
                continuesInput ordinaryInput progressInput tailRejected
            · simp [progressed] at result

/-- Trailing-comma wrapper rejection reflection. -/
theorem delimited_reject_sound {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (ordinaryParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSuccessSound : ∀ {input next : State} {value : α},
      element input = .ok value next → ordinaryParses
        input.declarativeRemainder value next.declarativeRemainder)
    (elementRejectSound : ∀ {input rejected : State} {failure : Failure},
      element input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : delimited opening closing allowEmpty element context phase input =
      .reject failure rejected) :
    DeclarativeGrammar.DelimitedListRejects opening closing allowEmpty true
      ordinaryParses nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  exact delimitedWithPolicy_reject_sound opening closing allowEmpty true
    element ordinaryParses nestedRejects context phase elementSuccessSound
      elementRejectSound result

/-- No-trailing wrapper rejection reflection. -/
theorem delimitedNoTrailing_reject_sound {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (ordinaryParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSuccessSound : ∀ {input next : State} {value : α},
      element input = .ok value next → ordinaryParses
        input.declarativeRemainder value next.declarativeRemainder)
    (elementRejectSound : ∀ {input rejected : State} {failure : Failure},
      element input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : delimitedNoTrailing opening closing allowEmpty element context
      phase input = .reject failure rejected) :
    DeclarativeGrammar.DelimitedListRejects opening closing allowEmpty false
      ordinaryParses nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  exact delimitedWithPolicy_reject_sound opening closing allowEmpty false
    element ordinaryParses nestedRejects context phase elementSuccessSound
      elementRejectSound result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedSoundnessProperties
/-! Success soundness for nonempty, trailing-comma delimited lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Closing fixes the final token, forward elements, cover, and remainder. -/
private theorem closeDelimited_success_sound {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) {input next : State}
    {values : DelimitedList α}
    (result : closeDelimited opening closing context elementsRev input =
      .ok values next) :
    ∃ closingSpan,
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        input.cursor {
          span := closingSpan
          value := .symbol closing
        } ∧
      next.declarativeRemainder = {
        input.declarativeRemainder with cursor := input.cursor + 1
      } ∧
      values.elements = elementsRev.reverse ∧
      values.span = SourceSpan.cover opening.span closingSpan := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok token afterClosing =>
      have sound := symbol_ok_tokenAt closing context closingResult
      simp only [closingResult] at result
      cases result
      refine ⟨token.span, sound.1, ?_, rfl, rfl⟩
      rw [sound.2]
      rfl

/-- Successful tail execution recovers its forward-order declarative suffix. -/
private theorem afterDelimitedElement_success_sound {α : Type}
    (element : Parser α)
    (elementParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase)
    (opening : Token) :
    ∀ fuel elementsRev input values next,
      afterDelimitedElement element closing true context phase opening
          fuel elementsRev input = .ok values next →
      ∃ suffix closingSpan,
        values.elements = elementsRev.reverse ++ suffix ∧
        values.span = SourceSpan.cover opening.span closingSpan ∧
        DeclarativeGrammar.TrailingDelimitedTailParses closing elementParses
          input.declarativeRemainder suffix closingSpan
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next result
      simp [afterDelimitedElement] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            have commaSound := symbol_ok_tokenAt .comma context commaResult
            simp only [commaResult] at result
            split at result
            · rcases closeDelimited_success_sound opening closing context
                elementsRev result with
                ⟨closingSpan, closingToken, finalEq,
                  elementsEq, spanEq⟩
              have closingTokenInput :
                  DeclarativeGrammar.TokenAt input.tokens
                    input.window.endIndex (input.cursor + 1) {
                      span := closingSpan
                      value := .symbol closing
                    } := by
                simpa only [commaSound.2, State.tokens, State.window,
                  State.cursor] using closingToken
              have finalEqInput : next.declarativeRemainder = {
                  input.declarativeRemainder with
                    cursor := input.cursor + 2
                } := by
                simpa only [commaSound.2, State.declarativeRemainder,
                  State.cursor, State.tokens, State.window, Nat.add_assoc]
                  using finalEq
              refine ⟨[], closingSpan, by simpa using elementsEq,
                spanEq, ?_⟩
              rw [finalEqInput]
              exact .trailing commaSound.1 closingTokenInput
            · have closingAbsentAfterComma :
                  isSymbol afterComma closing = false := by
                simp_all
              have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false
                closing closingAbsentAfterComma
              cases elementResult : element afterComma with
              | invariant error => simp [elementResult] at result
              | reject failure rejected => simp [elementResult] at result
              | ok value afterElement =>
                  have valueGrammar := elementSound elementResult
                  simp only [elementResult] at result
                  split at result
                  · rcases inductionHypothesis (value :: elementsRev)
                      afterElement values next result with
                      ⟨suffix, closingSpan, elementsEq, spanEq, tailGrammar⟩
                    have closingAbsentInput :
                        DeclarativeGrammar.TokenKindAbsentAt input.tokens
                          input.window.endIndex (input.cursor + 1)
                          (.symbol closing) := by
                      simpa only [commaSound.2, State.tokens, State.window,
                        State.cursor] using closingAbsent
                    have valueGrammarInput : elementParses {
                        input.declarativeRemainder with
                          cursor := input.cursor + 1
                      } value afterElement.declarativeRemainder := by
                      simpa only [commaSound.2, State.declarativeRemainder,
                        State.tokens, State.window, State.cursor] using
                        valueGrammar
                    have valueProgress :
                        afterComma.cursor < afterElement.cursor := by
                      assumption
                    have valueProgressInput :
                        input.cursor + 1 < afterElement.cursor := by
                      simpa only [commaSound.2, State.cursor] using
                        valueProgress
                    refine ⟨value :: suffix, closingSpan, ?_, spanEq, ?_⟩
                    · calc
                        values.elements =
                            (value :: elementsRev).reverse ++ suffix :=
                          elementsEq
                        _ = elementsRev.reverse ++ (value :: suffix) := by
                          simp [List.reverse_cons, List.append_assoc]
                    · exact .next commaSound.1 closingAbsentInput
                        valueGrammarInput valueProgressInput tailGrammar
                  · contradiction
      · have commaAbsentBool : isSymbol input .comma = false := by
          simp_all
        have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false .comma
          commaAbsentBool
        split at result
        · rcases closeDelimited_success_sound opening closing context
            elementsRev result with
            ⟨closingSpan, closingToken, finalEq, elementsEq, spanEq⟩
          refine ⟨[], closingSpan, by simpa using elementsEq, spanEq, ?_⟩
          rw [finalEq]
          exact .close commaAbsent closingToken
        · unfold rejectAt at result
          contradiction

/--
Every successful nonempty trailing-comma list follows the independent grammar.
Element parsers may emit diagnostics; only their successful syntax relation and
immutable token-window law are required.
-/
theorem delimited_nonempty_trailing_success_sound {α : Type}
    (opening closing : Symbol) (element : Parser α)
    (elementParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimited opening closing false element context phase input =
      .ok values next) :
    DeclarativeGrammar.NonemptyTrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  have outputShape := delimited_preservesTokenWindow opening closing false
    element context phase elementShape input
  rw [result] at outputShape
  unfold delimited delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.false_and, Bool.false_eq_true, if_false]
        at result
      cases elementResult : element afterOpening with
      | invariant error => simp [elementResult] at result
      | reject failure rejected => simp [elementResult] at result
      | ok first afterFirst =>
          have firstGrammar := elementSound elementResult
          simp only [elementResult] at result
          split at result
          · rcases afterDelimitedElement_success_sound element elementParses
              elementSound closing context phase openingToken
              (afterOpening.remainingCount + 1) [first] afterFirst values next
              result with
              ⟨rest, closingSpan, elementsEq, spanEq, tailGrammar⟩
            have firstGrammarInput : elementParses {
                input.declarativeRemainder with cursor := input.cursor + 1
              } first afterFirst.declarativeRemainder := by
              simpa only [openingSound.2, State.declarativeRemainder,
                State.tokens, State.window, State.cursor] using firstGrammar
            have firstProgress : afterOpening.cursor < afterFirst.cursor := by
              assumption
            have firstProgressInput :
                input.cursor + 1 < afterFirst.cursor := by
              simpa only [openingSound.2, State.cursor] using firstProgress
            unfold DeclarativeGrammar.NonemptyTrailingDelimitedListParses
            refine ⟨openingToken.span, first, afterFirst.declarativeRemainder,
              rest, closingSpan, outputShape.1,
              congrArg TokenWindow.endIndex outputShape.2, openingSound.1,
              firstGrammarInput, firstProgressInput, tailGrammar, ?_, spanEq⟩
            simpa using elementsEq
          · contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
/-! Success soundness for possibly empty, trailing-comma delimited lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Every successful list that allows both empty contents and a trailing comma
follows the independent prioritized grammar. Element parsers may diagnose.
-/
theorem delimited_allowEmpty_trailing_success_sound {α : Type}
    (opening closing : Symbol) (element : Parser α)
    (elementParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimited opening closing true element context phase input =
      .ok values next) :
    DeclarativeGrammar.TrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  unfold delimited delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.true_and] at result
      split at result
      next closingPresent =>
        unfold closeDelimited at result
        cases closingResult : symbol closing context afterOpening with
        | invariant error => simp [closingResult] at result
        | reject failure rejected => simp [closingResult] at result
        | ok closingToken afterClosing =>
            have closingSound := symbol_ok_tokenAt closing context
              closingResult
            simp only [closingResult] at result
            cases result
            have closingTokenInput :
                DeclarativeGrammar.TokenAt input.tokens
                  input.window.endIndex (input.cursor + 1) {
                    span := closingToken.span
                    value := .symbol closing
                  } := by
              simpa only [openingSound.2, State.tokens, State.window,
                State.cursor] using closingSound.1
            have grammar :=
              DeclarativeGrammar.TrailingDelimitedListParses.empty
                (opening := opening) (closing := closing)
                (elementParses := elementParses)
                (input := input.declarativeRemainder)
                openingToken.span closingToken.span openingSound.1
                closingTokenInput
            simpa only [closingSound.2, openingSound.2,
              State.declarativeRemainder, State.tokens, State.window,
              State.cursor, List.reverse_nil, Nat.add_assoc, Nat.reduceAdd]
              using grammar
      next closingAbsent =>
        have closingAbsentBool : isSymbol afterOpening closing = false := by
          simp_all
        have closingAbsentAtAfterOpening :=
          symbolAbsentAt_of_isSymbol_eq_false closing closingAbsentBool
        have closingAbsentAtInput :
            DeclarativeGrammar.TokenKindAbsentAt input.tokens
              input.window.endIndex (input.cursor + 1) (.symbol closing) := by
          simpa only [openingSound.2, State.tokens, State.window,
            State.cursor] using closingAbsentAtAfterOpening
        have nonemptyResult :
            delimited opening closing false element context phase input =
              .ok values next := by
          unfold delimited delimitedWithPolicy
          simp only [openingResult, Bool.false_and, Bool.false_eq_true,
            if_false]
          exact result
        exact DeclarativeGrammar.TrailingDelimitedListParses.nonempty
          closingAbsentAtInput
          (delimited_nonempty_trailing_success_sound opening closing element
            elementParses context phase elementSound elementShape
            nonemptyResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedAllowEmptyDiagnosticFreeSoundnessProperties
/-! Diagnostic-free soundness for possibly empty trailing-delimited lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeDelimited_diagnosticFree_success_sound {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) {input next : State} {values : DelimitedList α}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : closeDelimited opening closing context elementsRev input =
      .ok values next) :
    input.diagnosticsRev = [] ∧ ∃ closingSpan,
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        input.cursor { span := closingSpan, value := .symbol closing } ∧
      next.declarativeRemainder = {
        input.declarativeRemainder with cursor := input.cursor + 1
      } ∧ values.elements = elementsRev.reverse ∧
      values.span = SourceSpan.cover opening.span closingSpan := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok token afterClosing =>
      have sound := symbol_ok_tokenAt closing context closingResult
      simp only [closingResult] at result
      cases result
      refine ⟨?_, token.span, sound.1, ?_, rfl, rfl⟩
      · simpa [sound.2] using diagnosticFree
      · rw [sound.2]
        rfl

private theorem afterDelimitedElement_diagnosticFree_success_sound {α : Type}
    (element : Parser α)
    (elementParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (elementSound : ∀ {input next : State} {value : α},
      next.diagnosticsRev = [] → element input = .ok value next →
      elementParses input.declarativeRemainder value next.declarativeRemainder)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase)
    (opening : Token) : ∀ fuel elementsRev input values next,
      next.diagnosticsRev = [] →
      afterDelimitedElement element closing true context phase opening fuel
        elementsRev input = .ok values next →
      input.diagnosticsRev = [] ∧ ∃ suffix closingSpan,
        values.elements = elementsRev.reverse ++ suffix ∧
        values.span = SourceSpan.cover opening.span closingSpan ∧
        DeclarativeGrammar.TrailingDelimitedTailParses closing elementParses
          input.declarativeRemainder suffix closingSpan
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next diagnosticFree result
      simp [afterDelimitedElement] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next diagnosticFree result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            have commaSound := symbol_ok_tokenAt .comma context commaResult
            simp only [commaResult] at result
            split at result
            · rcases closeDelimited_diagnosticFree_success_sound opening
                closing context elementsRev diagnosticFree result with
                ⟨afterCommaFree, closingSpan, closingToken, finalEq,
                  elementsEq, spanEq⟩
              have inputFree := symbol_reflectsDiagnosticFreeOnSuccess .comma
                context input comma afterComma commaResult afterCommaFree
              have closingTokenInput : DeclarativeGrammar.TokenAt input.tokens
                  input.window.endIndex (input.cursor + 1) {
                    span := closingSpan, value := .symbol closing } := by
                simpa only [commaSound.2, State.tokens, State.window,
                  State.cursor] using closingToken
              have finalEqInput : next.declarativeRemainder = {
                  input.declarativeRemainder with cursor := input.cursor + 2
                } := by
                simpa only [commaSound.2, State.declarativeRemainder,
                  State.cursor, State.tokens, State.window, Nat.add_assoc]
                  using finalEq
              refine ⟨inputFree, [], closingSpan, by simpa using elementsEq,
                spanEq, ?_⟩
              rw [finalEqInput]
              exact .trailing commaSound.1 closingTokenInput
            · have closingAbsentAfterComma :
                  isSymbol afterComma closing = false := by simp_all
              have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false
                closing closingAbsentAfterComma
              cases elementResult : element afterComma with
              | invariant error => simp [elementResult] at result
              | reject failure rejected => simp [elementResult] at result
              | ok value afterElement =>
                  simp only [elementResult] at result
                  split at result
                  · rcases inductionHypothesis (value :: elementsRev)
                      afterElement values next diagnosticFree result with
                      ⟨afterElementFree, suffix, closingSpan, elementsEq,
                        spanEq, tailGrammar⟩
                    have afterCommaFree := elementReflects afterComma value
                      afterElement elementResult afterElementFree
                    have inputFree := symbol_reflectsDiagnosticFreeOnSuccess
                      .comma context input comma afterComma commaResult
                      afterCommaFree
                    have valueGrammar := elementSound afterElementFree
                      elementResult
                    have closingAbsentInput :
                        DeclarativeGrammar.TokenKindAbsentAt input.tokens
                          input.window.endIndex (input.cursor + 1)
                          (.symbol closing) := by
                      simpa only [commaSound.2, State.tokens, State.window,
                        State.cursor] using closingAbsent
                    have valueGrammarInput : elementParses {
                        input.declarativeRemainder with cursor := input.cursor + 1
                      } value afterElement.declarativeRemainder := by
                      simpa only [commaSound.2, State.declarativeRemainder,
                        State.tokens, State.window, State.cursor] using
                        valueGrammar
                    have valueProgressInput :
                        input.cursor + 1 < afterElement.cursor := by
                      have valueProgress :
                          afterComma.cursor < afterElement.cursor := by assumption
                      simpa only [commaSound.2, State.cursor] using valueProgress
                    refine ⟨inputFree, value :: suffix, closingSpan, ?_, spanEq,
                      .next commaSound.1 closingAbsentInput valueGrammarInput
                        valueProgressInput tailGrammar⟩
                    calc
                      values.elements =
                          (value :: elementsRev).reverse ++ suffix := elementsEq
                      _ = elementsRev.reverse ++ (value :: suffix) := by
                        simp [List.reverse_cons, List.append_assoc]
                  · contradiction
      · have commaAbsentBool : isSymbol input .comma = false := by simp_all
        have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false .comma
          commaAbsentBool
        split at result
        · rcases closeDelimited_diagnosticFree_success_sound opening closing
            context elementsRev diagnosticFree result with
            ⟨inputFree, closingSpan, closingToken, finalEq, elementsEq, spanEq⟩
          refine ⟨inputFree, [], closingSpan, by simpa using elementsEq,
            spanEq, ?_⟩
          rw [finalEq]
          exact .close commaAbsent closingToken
        · unfold rejectAt at result
          contradiction

private theorem delimited_nonempty_trailing_success_sound_of_diagnosticFree_variant
    {α : Type} (opening closing : Symbol) (element : Parser α)
    (elementParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      next.diagnosticsRev = [] → element input = .ok value next →
      elementParses input.declarativeRemainder value next.declarativeRemainder)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : delimited opening closing false element context phase input =
      .ok values next) :
    DeclarativeGrammar.NonemptyTrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  have outputShape := delimited_preservesTokenWindow opening closing false
    element context phase elementShape input
  rw [result] at outputShape
  unfold delimited delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.false_and, Bool.false_eq_true, if_false]
        at result
      cases elementResult : element afterOpening with
      | invariant error => simp [elementResult] at result
      | reject failure rejected => simp [elementResult] at result
      | ok first afterFirst =>
          simp only [elementResult] at result
          split at result
          · rcases afterDelimitedElement_diagnosticFree_success_sound element
              elementParses elementSound elementReflects closing context phase
              openingToken (afterOpening.remainingCount + 1) [first]
              afterFirst values next diagnosticFree result with
              ⟨afterFirstFree, rest, closingSpan, elementsEq, spanEq,
                tailGrammar⟩
            have firstGrammar := elementSound afterFirstFree elementResult
            have firstGrammarInput : elementParses {
                input.declarativeRemainder with cursor := input.cursor + 1
              } first afterFirst.declarativeRemainder := by
              simpa only [openingSound.2, State.declarativeRemainder,
                State.tokens, State.window, State.cursor] using firstGrammar
            have firstProgressInput : input.cursor + 1 < afterFirst.cursor := by
              have firstProgress : afterOpening.cursor < afterFirst.cursor := by
                assumption
              simpa only [openingSound.2, State.cursor] using firstProgress
            unfold DeclarativeGrammar.NonemptyTrailingDelimitedListParses
            refine ⟨openingToken.span, first, afterFirst.declarativeRemainder,
              rest, closingSpan, outputShape.1,
              congrArg TokenWindow.endIndex outputShape.2, openingSound.1,
              firstGrammarInput, firstProgressInput, tailGrammar, ?_, spanEq⟩
            simpa using elementsEq
          · contradiction

/--
A diagnostic-free successful allow-empty trailing list follows its independent
grammar when diagnostic freedom suffices for each element's soundness.
-/
theorem delimited_allowEmpty_trailing_success_sound_of_diagnosticFree
    {α : Type} (opening closing : Symbol) (element : Parser α)
    (elementParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      next.diagnosticsRev = [] → element input = .ok value next →
      elementParses input.declarativeRemainder value next.declarativeRemainder)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : delimited opening closing true element context phase input =
      .ok values next) :
    DeclarativeGrammar.TrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  unfold delimited delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.true_and] at result
      split at result
      next closingPresent =>
        unfold closeDelimited at result
        cases closingResult : symbol closing context afterOpening with
        | invariant error => simp [closingResult] at result
        | reject failure rejected => simp [closingResult] at result
        | ok closingToken afterClosing =>
            have closingSound := symbol_ok_tokenAt closing context closingResult
            simp only [closingResult] at result
            cases result
            have closingTokenInput : DeclarativeGrammar.TokenAt input.tokens
                input.window.endIndex (input.cursor + 1) {
                  span := closingToken.span, value := .symbol closing } := by
              simpa only [openingSound.2, State.tokens, State.window,
                State.cursor] using closingSound.1
            have grammar := DeclarativeGrammar.TrailingDelimitedListParses.empty
              (opening := opening) (closing := closing)
              (elementParses := elementParses)
              (input := input.declarativeRemainder) openingToken.span
              closingToken.span openingSound.1 closingTokenInput
            simpa only [closingSound.2, openingSound.2,
              State.declarativeRemainder, State.tokens, State.window,
              State.cursor, List.reverse_nil, Nat.add_assoc, Nat.reduceAdd]
              using grammar
      next closingAbsent =>
        have closingAbsentBool : isSymbol afterOpening closing = false := by
          simp_all
        have closingAbsentAtAfterOpening := symbolAbsentAt_of_isSymbol_eq_false
          closing closingAbsentBool
        have closingAbsentAtInput :
            DeclarativeGrammar.TokenKindAbsentAt input.tokens
              input.window.endIndex (input.cursor + 1) (.symbol closing) := by
          simpa only [openingSound.2, State.tokens, State.window, State.cursor]
            using closingAbsentAtAfterOpening
        have nonemptyResult : delimited opening closing false element context
            phase input = .ok values next := by
          unfold delimited delimitedWithPolicy
          simp only [openingResult, Bool.false_and, Bool.false_eq_true,
            if_false]
          exact result
        exact .nonempty closingAbsentAtInput
          (delimited_nonempty_trailing_success_sound_of_diagnosticFree_variant opening
            closing element elementParses context phase elementSound
            elementReflects elementShape diagnosticFree nonemptyResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNonemptyTrailingDiagnosticFreeSoundnessProperties
/-! Diagnostic-free soundness for required trailing-delimited lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeTrailingDiagnosticFreeSound {alpha : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List alpha) {input next : State}
    {values : DelimitedList alpha} (diagnosticFree : next.diagnosticsRev = [])
    (result : closeDelimited opening closing context elementsRev input =
      .ok values next) :
    input.diagnosticsRev = [] ∧ ∃ closingSpan,
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        input.cursor { span := closingSpan, value := .symbol closing } ∧
      next.declarativeRemainder = {
        input.declarativeRemainder with cursor := input.cursor + 1
      } ∧ values.elements = elementsRev.reverse ∧
      values.span = SourceSpan.cover opening.span closingSpan := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok token afterClosing =>
      have sound := symbol_ok_tokenAt closing context closingResult
      simp only [closingResult] at result
      cases result
      refine ⟨?_, token.span, sound.1, ?_, rfl, rfl⟩
      · simpa [sound.2] using diagnosticFree
      · rw [sound.2]
        rfl

private theorem afterTrailingElementDiagnosticFreeSound {alpha : Type}
    (element : Parser alpha)
    (elementParses : DeclarativeGrammar.Remainder → alpha →
      DeclarativeGrammar.Remainder → Prop)
    (elementSound : ∀ {input next : State} {value : alpha},
      next.diagnosticsRev = [] → element input = .ok value next →
      elementParses input.declarativeRemainder value next.declarativeRemainder)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase)
    (opening : Token) : ∀ fuel elementsRev input values next,
      next.diagnosticsRev = [] →
      afterDelimitedElement element closing true context phase opening fuel
        elementsRev input = .ok values next →
      input.diagnosticsRev = [] ∧ ∃ suffix closingSpan,
        values.elements = elementsRev.reverse ++ suffix ∧
        values.span = SourceSpan.cover opening.span closingSpan ∧
        DeclarativeGrammar.TrailingDelimitedTailParses closing elementParses
          input.declarativeRemainder suffix closingSpan
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next diagnosticFree result
      simp [afterDelimitedElement] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next diagnosticFree result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            have commaSound := symbol_ok_tokenAt .comma context commaResult
            simp only [commaResult] at result
            split at result
            · rcases closeTrailingDiagnosticFreeSound opening closing
                context elementsRev diagnosticFree result with
                ⟨afterCommaFree, closingSpan, closingToken, finalEq,
                  elementsEq, spanEq⟩
              have inputFree := symbol_reflectsDiagnosticFreeOnSuccess .comma
                context input comma afterComma commaResult afterCommaFree
              have closingTokenInput : DeclarativeGrammar.TokenAt input.tokens
                  input.window.endIndex (input.cursor + 1) {
                    span := closingSpan, value := .symbol closing } := by
                simpa only [commaSound.2, State.tokens, State.window,
                  State.cursor] using closingToken
              have finalEqInput : next.declarativeRemainder = {
                  input.declarativeRemainder with cursor := input.cursor + 2
                } := by
                simpa only [commaSound.2, State.declarativeRemainder,
                  State.cursor, State.tokens, State.window, Nat.add_assoc]
                  using finalEq
              refine ⟨inputFree, [], closingSpan, by simpa using elementsEq,
                spanEq, ?_⟩
              rw [finalEqInput]
              exact .trailing commaSound.1 closingTokenInput
            · have closingAbsentAfterComma :
                  isSymbol afterComma closing = false := by simp_all
              have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false
                closing closingAbsentAfterComma
              cases elementResult : element afterComma with
              | invariant error => simp [elementResult] at result
              | reject failure rejected => simp [elementResult] at result
              | ok value afterElement =>
                  simp only [elementResult] at result
                  split at result
                  · rcases inductionHypothesis (value :: elementsRev)
                      afterElement values next diagnosticFree result with
                      ⟨afterElementFree, suffix, closingSpan, elementsEq,
                        spanEq, tailGrammar⟩
                    have afterCommaFree := elementReflects afterComma value
                      afterElement elementResult afterElementFree
                    have inputFree := symbol_reflectsDiagnosticFreeOnSuccess
                      .comma context input comma afterComma commaResult
                        afterCommaFree
                    have valueGrammar := elementSound afterElementFree
                      elementResult
                    have closingAbsentInput :
                        DeclarativeGrammar.TokenKindAbsentAt input.tokens
                          input.window.endIndex (input.cursor + 1)
                          (.symbol closing) := by
                      simpa only [commaSound.2, State.tokens, State.window,
                        State.cursor] using closingAbsent
                    have valueGrammarInput : elementParses {
                        input.declarativeRemainder with
                          cursor := input.cursor + 1
                      } value afterElement.declarativeRemainder := by
                      simpa only [commaSound.2, State.declarativeRemainder,
                        State.tokens, State.window, State.cursor] using
                        valueGrammar
                    have valueProgressInput :
                        input.cursor + 1 < afterElement.cursor := by
                      have valueProgress :
                          afterComma.cursor < afterElement.cursor := by
                        assumption
                      simpa only [commaSound.2, State.cursor] using valueProgress
                    refine ⟨inputFree, value :: suffix, closingSpan, ?_,
                      spanEq, .next commaSound.1 closingAbsentInput
                        valueGrammarInput valueProgressInput tailGrammar⟩
                    calc
                      values.elements =
                          (value :: elementsRev).reverse ++ suffix := elementsEq
                      _ = elementsRev.reverse ++ (value :: suffix) := by
                        simp [List.reverse_cons, List.append_assoc]
                  · contradiction
      · have commaAbsentBool : isSymbol input .comma = false := by simp_all
        have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false .comma
          commaAbsentBool
        split at result
        · rcases closeTrailingDiagnosticFreeSound opening closing context
            elementsRev diagnosticFree result with
            ⟨inputFree, closingSpan, closingToken, finalEq, elementsEq,
              spanEq⟩
          refine ⟨inputFree, [], closingSpan, by simpa using elementsEq,
            spanEq, ?_⟩
          rw [finalEq]
          exact .close commaAbsent closingToken
        · unfold rejectAt at result
          contradiction

/-- A diagnostic-free required trailing list follows its exact grammar. -/
theorem delimited_nonempty_trailing_success_sound_of_diagnosticFree
    {alpha : Type} (opening closing : Symbol) (element : Parser alpha)
    (elementParses : DeclarativeGrammar.Remainder → alpha →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : alpha},
      next.diagnosticsRev = [] → element input = .ok value next →
      elementParses input.declarativeRemainder value next.declarativeRemainder)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList alpha}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : delimited opening closing false element context phase input =
      .ok values next) :
    DeclarativeGrammar.NonemptyTrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  have outputShape := delimited_preservesTokenWindow opening closing false
    element context phase elementShape input
  rw [result] at outputShape
  unfold delimited delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.false_and, Bool.false_eq_true, if_false]
        at result
      cases elementResult : element afterOpening with
      | invariant error => simp [elementResult] at result
      | reject failure rejected => simp [elementResult] at result
      | ok first afterFirst =>
          simp only [elementResult] at result
          split at result
          · rcases afterTrailingElementDiagnosticFreeSound element
                elementParses elementSound elementReflects closing context phase
                openingToken (afterOpening.remainingCount + 1) [first]
                afterFirst values next diagnosticFree result with
              ⟨afterFirstFree, rest, closingSpan, elementsEq, spanEq,
                tailGrammar⟩
            have firstGrammar := elementSound afterFirstFree elementResult
            have firstGrammarInput : elementParses {
                input.declarativeRemainder with cursor := input.cursor + 1
              } first afterFirst.declarativeRemainder := by
              simpa only [openingSound.2, State.declarativeRemainder,
                State.tokens, State.window, State.cursor] using firstGrammar
            have firstProgressInput : input.cursor + 1 < afterFirst.cursor := by
              have firstProgress : afterOpening.cursor < afterFirst.cursor := by
                assumption
              simpa only [openingSound.2, State.cursor] using firstProgress
            unfold DeclarativeGrammar.NonemptyTrailingDelimitedListParses
            refine ⟨openingToken.span, first, afterFirst.declarativeRemainder,
              rest, closingSpan, outputShape.1,
              congrArg TokenWindow.endIndex outputShape.2, openingSound.1,
              firstGrammarInput, firstProgressInput, tailGrammar, ?_, spanEq⟩
            simpa using elementsEq
          · contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNoTrailingSoundnessProperties
/-! Success soundness for nonempty lists that reject a trailing comma. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Closing fixes the final token, forward elements, cover, and remainder. -/
private theorem closeDelimited_noTrailing_success_sound {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) {input next : State}
    {values : DelimitedList α}
    (result : closeDelimited opening closing context elementsRev input =
      .ok values next) :
    ∃ closingSpan,
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        input.cursor {
          span := closingSpan
          value := .symbol closing
        } ∧
      next.declarativeRemainder = {
        input.declarativeRemainder with cursor := input.cursor + 1
      } ∧
      values.elements = elementsRev.reverse ∧
      values.span = SourceSpan.cover opening.span closingSpan := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok token afterClosing =>
      have sound := symbol_ok_tokenAt closing context closingResult
      simp only [closingResult] at result
      cases result
      refine ⟨token.span, sound.1, ?_, rfl, rfl⟩
      rw [sound.2]
      rfl

/-- Successful no-trailing tails recover their forward-order suffix. -/
private theorem afterDelimitedElement_noTrailing_success_sound {α : Type}
    (element : Parser α)
    (elementParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase)
    (opening : Token) :
    ∀ fuel elementsRev input values next,
      afterDelimitedElement element closing false context phase opening
          fuel elementsRev input = .ok values next →
      ∃ suffix closingSpan,
        values.elements = elementsRev.reverse ++ suffix ∧
        values.span = SourceSpan.cover opening.span closingSpan ∧
        DeclarativeGrammar.NoTrailingDelimitedTailParses closing
          elementParses input.declarativeRemainder suffix closingSpan
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next result
      simp [afterDelimitedElement] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            have commaSound := symbol_ok_tokenAt .comma context commaResult
            simp only [commaResult, Bool.false_and, Bool.false_eq_true,
              if_false] at result
            cases elementResult : element afterComma with
            | invariant error => simp [elementResult] at result
            | reject failure rejected => simp [elementResult] at result
            | ok value afterElement =>
                have valueGrammar := elementSound elementResult
                simp only [elementResult] at result
                split at result
                · rcases inductionHypothesis (value :: elementsRev)
                    afterElement values next result with
                    ⟨suffix, closingSpan, elementsEq, spanEq, tailGrammar⟩
                  have valueGrammarInput : elementParses {
                      input.declarativeRemainder with
                        cursor := input.cursor + 1
                    } value afterElement.declarativeRemainder := by
                    simpa only [commaSound.2, State.declarativeRemainder,
                      State.tokens, State.window, State.cursor] using
                      valueGrammar
                  have valueProgress :
                      afterComma.cursor < afterElement.cursor := by
                    assumption
                  have valueProgressInput :
                      input.cursor + 1 < afterElement.cursor := by
                    simpa only [commaSound.2, State.cursor] using valueProgress
                  refine ⟨value :: suffix, closingSpan, ?_, spanEq, ?_⟩
                  · calc
                      values.elements =
                          (value :: elementsRev).reverse ++ suffix :=
                        elementsEq
                      _ = elementsRev.reverse ++ (value :: suffix) := by
                        simp [List.reverse_cons, List.append_assoc]
                  · exact .next commaSound.1 valueGrammarInput
                      valueProgressInput tailGrammar
                · contradiction
      · have commaAbsentBool : isSymbol input .comma = false := by
          simp_all
        have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false .comma
          commaAbsentBool
        split at result
        · rcases closeDelimited_noTrailing_success_sound opening closing
              context elementsRev result with
            ⟨closingSpan, closingToken, finalEq, elementsEq, spanEq⟩
          refine ⟨[], closingSpan, by simpa using elementsEq, spanEq, ?_⟩
          rw [finalEq]
          exact .close commaAbsent closingToken
        · unfold rejectAt at result
          contradiction

/--
Every successful nonempty list that rejects a trailing comma follows the
independent grammar. Element parsers may emit diagnostics.
-/
theorem delimitedNoTrailing_nonempty_success_sound {α : Type}
    (opening closing : Symbol) (element : Parser α)
    (elementParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimitedNoTrailing opening closing false element context phase
      input = .ok values next) :
    DeclarativeGrammar.NonemptyNoTrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  have outputShape := delimitedWithPolicy_preservesTokenWindow opening closing
    false false element context phase elementShape input
  have policyResult : delimitedWithPolicy opening closing false false element
      context phase input = .ok values next := by
    simpa only [delimitedNoTrailing] using result
  rw [policyResult] at outputShape
  unfold delimitedNoTrailing delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.false_and, Bool.false_eq_true, if_false]
        at result
      cases elementResult : element afterOpening with
      | invariant error => simp [elementResult] at result
      | reject failure rejected => simp [elementResult] at result
      | ok first afterFirst =>
          have firstGrammar := elementSound elementResult
          simp only [elementResult] at result
          split at result
          · rcases afterDelimitedElement_noTrailing_success_sound element
                elementParses elementSound closing context phase openingToken
                (afterOpening.remainingCount + 1) [first] afterFirst values next
                result with
              ⟨rest, closingSpan, elementsEq, spanEq, tailGrammar⟩
            have firstGrammarInput : elementParses {
                input.declarativeRemainder with cursor := input.cursor + 1
              } first afterFirst.declarativeRemainder := by
              simpa only [openingSound.2, State.declarativeRemainder,
                State.tokens, State.window, State.cursor] using firstGrammar
            have firstProgress : afterOpening.cursor < afterFirst.cursor := by
              assumption
            have firstProgressInput :
                input.cursor + 1 < afterFirst.cursor := by
              simpa only [openingSound.2, State.cursor] using firstProgress
            unfold DeclarativeGrammar.NonemptyNoTrailingDelimitedListParses
            refine ⟨openingToken.span, first, afterFirst.declarativeRemainder,
              rest, closingSpan, outputShape.1,
              congrArg TokenWindow.endIndex outputShape.2, openingSound.1,
              firstGrammarInput, firstProgressInput, tailGrammar, ?_, spanEq⟩
            simpa using elementsEq
          · contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptySoundnessProperties
/-! Success soundness for possibly empty lists that reject a trailing comma. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Every successful list that allows empty contents but rejects a trailing comma
follows the independent prioritized grammar. Element parsers may diagnose.
-/
theorem delimitedNoTrailing_allowEmpty_success_sound {α : Type}
    (opening closing : Symbol) (element : Parser α)
    (elementParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimitedNoTrailing opening closing true element context phase
      input = .ok values next) :
    DeclarativeGrammar.NoTrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  unfold delimitedNoTrailing delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.true_and] at result
      split at result
      next closingPresent =>
        unfold closeDelimited at result
        cases closingResult : symbol closing context afterOpening with
        | invariant error => simp [closingResult] at result
        | reject failure rejected => simp [closingResult] at result
        | ok closingToken afterClosing =>
            have closingSound := symbol_ok_tokenAt closing context
              closingResult
            simp only [closingResult] at result
            cases result
            have closingTokenInput :
                DeclarativeGrammar.TokenAt input.tokens
                  input.window.endIndex (input.cursor + 1) {
                    span := closingToken.span
                    value := .symbol closing
                  } := by
              simpa only [openingSound.2, State.tokens, State.window,
                State.cursor] using closingSound.1
            have grammar :=
              DeclarativeGrammar.NoTrailingDelimitedListParses.empty
                (opening := opening) (closing := closing)
                (elementParses := elementParses)
                (input := input.declarativeRemainder)
                openingToken.span closingToken.span openingSound.1
                closingTokenInput
            simpa only [closingSound.2, openingSound.2,
              State.declarativeRemainder, State.tokens, State.window,
              State.cursor, List.reverse_nil, Nat.add_assoc, Nat.reduceAdd]
              using grammar
      next closingAbsent =>
        have closingAbsentBool : isSymbol afterOpening closing = false := by
          simp_all
        have closingAbsentAtAfterOpening :=
          symbolAbsentAt_of_isSymbol_eq_false closing closingAbsentBool
        have closingAbsentAtInput :
            DeclarativeGrammar.TokenKindAbsentAt input.tokens
              input.window.endIndex (input.cursor + 1) (.symbol closing) := by
          simpa only [openingSound.2, State.tokens, State.window,
            State.cursor] using closingAbsentAtAfterOpening
        have nonemptyResult :
            delimitedNoTrailing opening closing false element context phase
                input = .ok values next := by
          unfold delimitedNoTrailing delimitedWithPolicy
          simp only [openingResult, Bool.false_and, Bool.false_eq_true,
            if_false]
          exact result
        exact DeclarativeGrammar.NoTrailingDelimitedListParses.nonempty
          closingAbsentAtInput
          (delimitedNoTrailing_nonempty_success_sound opening closing element
            elementParses context phase elementSound elementShape
            nonemptyResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptyDiagnosticFreeSoundnessProperties
/-!
Diagnostic-free soundness for possibly empty lists that reject a trailing
comma.  This complements the unconditional generic theorem with the callback
shape used by recursive Core syntax.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeDelimited_noTrailing_diagnosticFree_sound {alpha : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List alpha) {input next : State}
    {values : DelimitedList alpha} (diagnosticFree : next.diagnosticsRev = [])
    (result : closeDelimited opening closing context elementsRev input =
      .ok values next) :
    input.diagnosticsRev = [] ∧ ∃ closingSpan,
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        input.cursor { span := closingSpan, value := .symbol closing } ∧
      next.declarativeRemainder = {
        input.declarativeRemainder with cursor := input.cursor + 1
      } ∧ values.elements = elementsRev.reverse ∧
      values.span = SourceSpan.cover opening.span closingSpan := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok token afterClosing =>
      have sound := symbol_ok_tokenAt closing context closingResult
      simp only [closingResult] at result
      cases result
      refine ⟨?_, token.span, sound.1, ?_, rfl, rfl⟩
      · simpa [sound.2] using diagnosticFree
      · rw [sound.2]
        rfl

private theorem afterDelimitedElement_noTrailing_diagnosticFree_sound
    {alpha : Type} (element : Parser alpha)
    (elementParses : DeclarativeGrammar.Remainder → alpha →
      DeclarativeGrammar.Remainder → Prop)
    (elementSound : ∀ {input next : State} {value : alpha},
      next.diagnosticsRev = [] → element input = .ok value next →
      elementParses input.declarativeRemainder value next.declarativeRemainder)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase)
    (opening : Token) : ∀ fuel elementsRev input values next,
      next.diagnosticsRev = [] →
      afterDelimitedElement element closing false context phase opening fuel
        elementsRev input = .ok values next →
      input.diagnosticsRev = [] ∧ ∃ suffix closingSpan,
        values.elements = elementsRev.reverse ++ suffix ∧
        values.span = SourceSpan.cover opening.span closingSpan ∧
        DeclarativeGrammar.NoTrailingDelimitedTailParses closing elementParses
          input.declarativeRemainder suffix closingSpan
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next diagnosticFree result
      simp [afterDelimitedElement] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next diagnosticFree result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            have commaSound := symbol_ok_tokenAt .comma context commaResult
            simp only [commaResult, Bool.false_and, Bool.false_eq_true,
              if_false] at result
            cases elementResult : element afterComma with
            | invariant error => simp [elementResult] at result
            | reject failure rejected => simp [elementResult] at result
            | ok value afterElement =>
                simp only [elementResult] at result
                split at result
                · rcases inductionHypothesis (value :: elementsRev)
                    afterElement values next diagnosticFree result with
                    ⟨afterElementFree, suffix, closingSpan, elementsEq,
                      spanEq, tailGrammar⟩
                  have afterCommaFree := elementReflects afterComma value
                    afterElement elementResult afterElementFree
                  have inputFree := symbol_reflectsDiagnosticFreeOnSuccess
                    .comma context input comma afterComma commaResult
                    afterCommaFree
                  have valueGrammar := elementSound afterElementFree
                    elementResult
                  have valueGrammarInput : elementParses {
                      input.declarativeRemainder with
                        cursor := input.cursor + 1
                    } value afterElement.declarativeRemainder := by
                    simpa only [commaSound.2, State.declarativeRemainder,
                      State.tokens, State.window, State.cursor] using
                      valueGrammar
                  have valueProgressInput :
                      input.cursor + 1 < afterElement.cursor := by
                    have valueProgress :
                        afterComma.cursor < afterElement.cursor := by assumption
                    simpa only [commaSound.2, State.cursor] using valueProgress
                  refine ⟨inputFree, value :: suffix, closingSpan, ?_, spanEq,
                    .next commaSound.1 valueGrammarInput valueProgressInput
                      tailGrammar⟩
                  calc
                    values.elements =
                        (value :: elementsRev).reverse ++ suffix := elementsEq
                    _ = elementsRev.reverse ++ (value :: suffix) := by
                      simp [List.reverse_cons, List.append_assoc]
                · contradiction
      · have commaAbsentBool : isSymbol input .comma = false := by simp_all
        have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false .comma
          commaAbsentBool
        split at result
        · rcases closeDelimited_noTrailing_diagnosticFree_sound opening
            closing context elementsRev diagnosticFree result with
            ⟨inputFree, closingSpan, closingToken, finalEq, elementsEq,
              spanEq⟩
          refine ⟨inputFree, [], closingSpan, by simpa using elementsEq,
            spanEq, ?_⟩
          rw [finalEq]
          exact .close commaAbsent closingToken
        · unfold rejectAt at result
          contradiction

private theorem delimitedNoTrailing_nonempty_sound_of_diagnosticFree
    {alpha : Type} (opening closing : Symbol) (element : Parser alpha)
    (elementParses : DeclarativeGrammar.Remainder → alpha →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : alpha},
      next.diagnosticsRev = [] → element input = .ok value next →
      elementParses input.declarativeRemainder value next.declarativeRemainder)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList alpha}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : delimitedNoTrailing opening closing false element context phase
      input = .ok values next) :
    DeclarativeGrammar.NonemptyNoTrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  have outputShape := delimitedWithPolicy_preservesTokenWindow opening closing
    false false element context phase elementShape input
  have policyResult : delimitedWithPolicy opening closing false false element
      context phase input = .ok values next := by
    simpa only [delimitedNoTrailing] using result
  rw [policyResult] at outputShape
  unfold delimitedNoTrailing delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.false_and, Bool.false_eq_true, if_false]
        at result
      cases elementResult : element afterOpening with
      | invariant error => simp [elementResult] at result
      | reject failure rejected => simp [elementResult] at result
      | ok first afterFirst =>
          simp only [elementResult] at result
          split at result
          · rcases afterDelimitedElement_noTrailing_diagnosticFree_sound
                element elementParses elementSound elementReflects closing
                context phase openingToken (afterOpening.remainingCount + 1)
                [first] afterFirst values next diagnosticFree result with
              ⟨afterFirstFree, rest, closingSpan, elementsEq, spanEq,
                tailGrammar⟩
            have firstGrammar := elementSound afterFirstFree elementResult
            have firstGrammarInput : elementParses {
                input.declarativeRemainder with cursor := input.cursor + 1
              } first afterFirst.declarativeRemainder := by
              simpa only [openingSound.2, State.declarativeRemainder,
                State.tokens, State.window, State.cursor] using firstGrammar
            have firstProgressInput : input.cursor + 1 < afterFirst.cursor := by
              have firstProgress : afterOpening.cursor < afterFirst.cursor := by
                assumption
              simpa only [openingSound.2, State.cursor] using firstProgress
            unfold DeclarativeGrammar.NonemptyNoTrailingDelimitedListParses
            refine ⟨openingToken.span, first, afterFirst.declarativeRemainder,
              rest, closingSpan, outputShape.1,
              congrArg TokenWindow.endIndex outputShape.2, openingSound.1,
              firstGrammarInput, firstProgressInput, tailGrammar, ?_, spanEq⟩
            simpa using elementsEq
          · contradiction

/--
A diagnostic-free successful allow-empty no-trailing list follows its exact
grammar when diagnostic freedom suffices for each element's soundness.
-/
theorem delimitedNoTrailing_allowEmpty_success_sound_of_diagnosticFree
    {alpha : Type} (opening closing : Symbol) (element : Parser alpha)
    (elementParses : DeclarativeGrammar.Remainder → alpha →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : alpha},
      next.diagnosticsRev = [] → element input = .ok value next →
      elementParses input.declarativeRemainder value next.declarativeRemainder)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList alpha}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : delimitedNoTrailing opening closing true element context phase
      input = .ok values next) :
    DeclarativeGrammar.NoTrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  unfold delimitedNoTrailing delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.true_and] at result
      split at result
      next closingPresent =>
        unfold closeDelimited at result
        cases closingResult : symbol closing context afterOpening with
        | invariant error => simp [closingResult] at result
        | reject failure rejected => simp [closingResult] at result
        | ok closingToken afterClosing =>
            have closingSound := symbol_ok_tokenAt closing context closingResult
            simp only [closingResult] at result
            cases result
            have closingTokenInput : DeclarativeGrammar.TokenAt input.tokens
                input.window.endIndex (input.cursor + 1) {
                  span := closingToken.span, value := .symbol closing } := by
              simpa only [openingSound.2, State.tokens, State.window,
                State.cursor] using closingSound.1
            have grammar :=
              DeclarativeGrammar.NoTrailingDelimitedListParses.empty
                (opening := opening) (closing := closing)
                (elementParses := elementParses)
                (input := input.declarativeRemainder) openingToken.span
                closingToken.span openingSound.1 closingTokenInput
            simpa only [closingSound.2, openingSound.2,
              State.declarativeRemainder, State.tokens, State.window,
              State.cursor, List.reverse_nil, Nat.add_assoc, Nat.reduceAdd]
              using grammar
      next closingAbsent =>
        have closingAbsentBool : isSymbol afterOpening closing = false := by
          simp_all
        have closingAbsentAtAfterOpening :=
          symbolAbsentAt_of_isSymbol_eq_false closing closingAbsentBool
        have closingAbsentAtInput : DeclarativeGrammar.TokenKindAbsentAt
            input.tokens input.window.endIndex (input.cursor + 1)
            (.symbol closing) := by
          simpa only [openingSound.2, State.tokens, State.window, State.cursor]
            using closingAbsentAtAfterOpening
        have nonemptyResult : delimitedNoTrailing opening closing false element
            context phase input = .ok values next := by
          unfold delimitedNoTrailing delimitedWithPolicy
          simp only [openingResult, Bool.false_and, Bool.false_eq_true,
            if_false]
          exact result
        exact .nonempty closingAbsentAtInput
          (delimitedNoTrailing_nonempty_sound_of_diagnosticFree opening closing
            element elementParses context phase elementSound elementReflects
            elementShape diagnosticFree nonemptyResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNoTrailingNonemptyDiagnosticFreeSoundnessProperties
/-! Diagnostic-free exact soundness for required no-trailing lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeNoTrailingDiagnosticFreeSound {alpha : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List alpha) {input next : State}
    {values : DelimitedList alpha} (diagnosticFree : next.diagnosticsRev = [])
    (result : closeDelimited opening closing context elementsRev input =
      .ok values next) :
    input.diagnosticsRev = [] ∧ ∃ closingSpan,
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        input.cursor { span := closingSpan, value := .symbol closing } ∧
      next.declarativeRemainder = {
        input.declarativeRemainder with cursor := input.cursor + 1
      } ∧ values.elements = elementsRev.reverse ∧
      values.span = SourceSpan.cover opening.span closingSpan := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok token afterClosing =>
      have sound := symbol_ok_tokenAt closing context closingResult
      simp only [closingResult] at result
      cases result
      refine ⟨?_, token.span, sound.1, ?_, rfl, rfl⟩
      · simpa [sound.2] using diagnosticFree
      · rw [sound.2]
        rfl

private theorem afterNoTrailingElementDiagnosticFreeSound {alpha : Type}
    (element : Parser alpha)
    (elementParses : DeclarativeGrammar.Remainder → alpha →
      DeclarativeGrammar.Remainder → Prop)
    (elementSound : ∀ {input next : State} {value : alpha},
      next.diagnosticsRev = [] → element input = .ok value next →
      elementParses input.declarativeRemainder value next.declarativeRemainder)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase)
    (opening : Token) : ∀ fuel elementsRev input values next,
      next.diagnosticsRev = [] →
      afterDelimitedElement element closing false context phase opening fuel
        elementsRev input = .ok values next →
      input.diagnosticsRev = [] ∧ ∃ suffix closingSpan,
        values.elements = elementsRev.reverse ++ suffix ∧
        values.span = SourceSpan.cover opening.span closingSpan ∧
        DeclarativeGrammar.NoTrailingDelimitedTailParses closing elementParses
          input.declarativeRemainder suffix closingSpan
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next diagnosticFree result
      simp [afterDelimitedElement] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next diagnosticFree result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            have commaSound := symbol_ok_tokenAt .comma context commaResult
            simp only [commaResult, Bool.false_and, Bool.false_eq_true,
              if_false] at result
            cases elementResult : element afterComma with
            | invariant error => simp [elementResult] at result
            | reject failure rejected => simp [elementResult] at result
            | ok value afterElement =>
                simp only [elementResult] at result
                split at result
                · rcases inductionHypothesis (value :: elementsRev)
                    afterElement values next diagnosticFree result with
                    ⟨afterElementFree, suffix, closingSpan, elementsEq,
                      spanEq, tailGrammar⟩
                  have afterCommaFree := elementReflects afterComma value
                    afterElement elementResult afterElementFree
                  have inputFree := symbol_reflectsDiagnosticFreeOnSuccess
                    .comma context input comma afterComma commaResult
                    afterCommaFree
                  have valueGrammar := elementSound afterElementFree
                    elementResult
                  have valueGrammarInput : elementParses {
                      input.declarativeRemainder with
                        cursor := input.cursor + 1
                    } value afterElement.declarativeRemainder := by
                    simpa only [commaSound.2, State.declarativeRemainder,
                      State.tokens, State.window, State.cursor] using
                      valueGrammar
                  have valueProgressInput :
                      input.cursor + 1 < afterElement.cursor := by
                    have valueProgress :
                        afterComma.cursor < afterElement.cursor := by assumption
                    simpa only [commaSound.2, State.cursor] using valueProgress
                  refine ⟨inputFree, value :: suffix, closingSpan, ?_, spanEq,
                    .next commaSound.1 valueGrammarInput valueProgressInput
                      tailGrammar⟩
                  calc
                    values.elements =
                        (value :: elementsRev).reverse ++ suffix := elementsEq
                    _ = elementsRev.reverse ++ (value :: suffix) := by
                      simp [List.reverse_cons, List.append_assoc]
                · contradiction
      · have commaAbsentBool : isSymbol input .comma = false := by simp_all
        have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false .comma
          commaAbsentBool
        split at result
        · rcases closeNoTrailingDiagnosticFreeSound opening closing context
            elementsRev diagnosticFree result with
            ⟨inputFree, closingSpan, closingToken, finalEq, elementsEq,
              spanEq⟩
          refine ⟨inputFree, [], closingSpan, by simpa using elementsEq,
            spanEq, ?_⟩
          rw [finalEq]
          exact .close commaAbsent closingToken
        · unfold rejectAt at result
          contradiction

/--
A diagnostic-free required no-trailing list follows the exact independent
grammar when diagnostic freedom suffices for each element's soundness.
-/
theorem delimitedNoTrailing_nonempty_success_sound_of_diagnosticFree
    {alpha : Type} (opening closing : Symbol) (element : Parser alpha)
    (elementParses : DeclarativeGrammar.Remainder → alpha →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : alpha},
      next.diagnosticsRev = [] → element input = .ok value next →
      elementParses input.declarativeRemainder value next.declarativeRemainder)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList alpha}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : delimitedNoTrailing opening closing false element context phase
      input = .ok values next) :
    DeclarativeGrammar.NonemptyNoTrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  have outputShape := delimitedWithPolicy_preservesTokenWindow opening closing
    false false element context phase elementShape input
  have policyResult : delimitedWithPolicy opening closing false false element
      context phase input = .ok values next := by
    simpa only [delimitedNoTrailing] using result
  rw [policyResult] at outputShape
  unfold delimitedNoTrailing delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.false_and, Bool.false_eq_true, if_false]
        at result
      cases elementResult : element afterOpening with
      | invariant error => simp [elementResult] at result
      | reject failure rejected => simp [elementResult] at result
      | ok first afterFirst =>
          simp only [elementResult] at result
          split at result
          · rcases afterNoTrailingElementDiagnosticFreeSound element
                elementParses elementSound elementReflects closing context phase
                openingToken (afterOpening.remainingCount + 1) [first]
                afterFirst values next diagnosticFree result with
              ⟨afterFirstFree, rest, closingSpan, elementsEq, spanEq,
                tailGrammar⟩
            have firstGrammar := elementSound afterFirstFree elementResult
            have firstGrammarInput : elementParses {
                input.declarativeRemainder with cursor := input.cursor + 1
              } first afterFirst.declarativeRemainder := by
              simpa only [openingSound.2, State.declarativeRemainder,
                State.tokens, State.window, State.cursor] using firstGrammar
            have firstProgressInput : input.cursor + 1 < afterFirst.cursor := by
              have firstProgress : afterOpening.cursor < afterFirst.cursor := by
                assumption
              simpa only [openingSound.2, State.cursor] using firstProgress
            unfold DeclarativeGrammar.NonemptyNoTrailingDelimitedListParses
            refine ⟨openingToken.span, first, afterFirst.declarativeRemainder,
              rest, closingSpan, outputShape.1,
              congrArg TokenWindow.endIndex outputShape.2, openingSound.1,
              firstGrammarInput, firstProgressInput, tailGrammar, ?_, spanEq⟩
            simpa using elementsEq
          · contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNonemptyProperties
/-! Nonempty-result laws for generic delimited parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeDelimited_elements_ne_nil_onSuccess {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) (accumulatorNonempty : elementsRev ≠ [])
    {input next : State} {values : DelimitedList α}
    (result : closeDelimited opening closing context elementsRev input =
      .ok values next) :
    values.elements ≠ [] := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | reject failure rejected => simp [closingResult] at result
  | invariant error => simp [closingResult] at result
  | ok token afterClosing =>
      simp only [closingResult] at result
      cases result
      simpa using accumulatorNonempty

/-- A successful tail loop preserves a nonempty reverse accumulator. -/
theorem afterDelimitedElement_elements_ne_nil_onSuccess {α : Type}
    (element : Parser α) (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input values next,
      elementsRev ≠ [] →
      afterDelimitedElement element closing allowTrailing context phase opening
        fuel elementsRev input = .ok values next →
      values.elements ≠ [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next accumulatorNonempty result
      simp [afterDelimitedElement] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next accumulatorNonempty result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | reject failure rejected => simp [commaResult] at result
        | invariant error => simp [commaResult] at result
        | ok comma afterComma =>
            simp only [commaResult] at result
            split at result
            · exact closeDelimited_elements_ne_nil_onSuccess opening closing
                context elementsRev accumulatorNonempty result
            · cases elementResult : element afterComma with
              | reject failure rejected => simp [elementResult] at result
              | invariant error => simp [elementResult] at result
              | ok value afterElement =>
                  simp only [elementResult] at result
                  split at result
                  · exact inductionHypothesis (value :: elementsRev)
                      afterElement values next (by simp) result
                  · contradiction
      · split at result
        · exact closeDelimited_elements_ne_nil_onSuccess opening closing
            context elementsRev accumulatorNonempty result
        · unfold rejectAt at result
          contradiction

/-- Disallowing an empty list makes every policy-parser success nonempty. -/
theorem delimitedWithPolicy_false_elements_ne_nil_onSuccess {α : Type}
    (opening closing : Symbol) (allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    {input next : State} {values : DelimitedList α}
    (result : delimitedWithPolicy opening closing false allowTrailing element
      context phase input = .ok values next) :
    values.elements ≠ [] := by
  unfold delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | reject failure rejected => simp [openingResult] at result
  | invariant error => simp [openingResult] at result
  | ok openingToken afterOpening =>
      simp only [openingResult, Bool.false_and, Bool.false_eq_true, if_false]
        at result
      cases elementResult : element afterOpening with
      | reject failure rejected => simp [elementResult] at result
      | invariant error => simp [elementResult] at result
      | ok value afterElement =>
          simp only [elementResult] at result
          split at result
          · exact afterDelimitedElement_elements_ne_nil_onSuccess element
              closing allowTrailing context phase openingToken
              (afterOpening.remainingCount + 1) [value] afterElement values
              next (by simp) result
          · contradiction

/-- A successful nonempty trailing-comma list contains an element. -/
theorem delimited_false_elements_ne_nil_onSuccess {α : Type}
    (opening closing : Symbol) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    {input next : State} {values : DelimitedList α}
    (result : delimited opening closing false element context phase input =
      .ok values next) :
    values.elements ≠ [] :=
  delimitedWithPolicy_false_elements_ne_nil_onSuccess opening closing true
    element context phase result

/-- A successful nonempty no-trailing-comma list contains an element. -/
theorem delimitedNoTrailing_false_elements_ne_nil_onSuccess {α : Type}
    (opening closing : Symbol) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    {input next : State} {values : DelimitedList α}
    (result : delimitedNoTrailing opening closing false element context phase
      input = .ok values next) :
    values.elements ≠ [] :=
  delimitedWithPolicy_false_elements_ne_nil_onSuccess opening closing false
    element context phase result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
/-!
Exact executable ordinary outcomes for the checked Core identifier primitive.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem rawIdentifier_reject_state_eq (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : rawIdentifier context input = .reject failure rejected) :
    rejected = input := by
  unfold rawIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      cases result
      rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; cases result; rfl }
      case identifier text => contradiction

/-- Checked-identifier rejection never consumes or otherwise changes state. -/
theorem identifier_reject_state_eq (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : identifier context input = .reject failure rejected) :
    rejected = input := by
  unfold identifier at result
  cases raw : rawIdentifier context input with
  | invariant error => simp [raw] at result
  | ok name afterName =>
      simp only [raw] at result
      split at result <;> contradiction
  | reject rejectedFailure rejectedState =>
      simp only [raw] at result
      cases result
      exact rawIdentifier_reject_state_eq context raw

/-- Checked-identifier rejection proves carrier-level identifier absence. -/
theorem identifier_reject_identifierAbsentAt (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : identifier context input = .reject failure rejected) :
    DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder := by
  rintro ⟨span, text, inside, atCursor⟩
  have found : input.peek? = some {
      span
      value := TokenKind.identifier text
    } := by
    unfold State.peek?
    change input.cursor < input.window.endIndex at inside
    change input.tokens[input.cursor]? = some {
      span
      value := TokenKind.identifier text
    } at atCursor
    simp only [inside, ↓reduceIte, atCursor]
  unfold identifier at result
  simp only [rawIdentifier, found] at result
  split at result <;> contradiction

/-- Every executable checked-identifier rejection follows the exact
non-consuming parser-independent rejection relation. -/
theorem identifier_reject_sound (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : identifier context input = .reject failure rejected) :
    DeclarativeGrammar.IdentifierRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  have rejectedEq := identifier_reject_state_eq context result
  subst rejectedEq
  exact .absent (identifier_reject_identifierAbsentAt context result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.RawIdentifierOrdinaryOutcomeSoundnessProperties
/-! Exact executable ordinary outcomes for the raw identifier primitive. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem rawIdentifier_reject_state_eq_forOutcome
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : rawIdentifier context input = .reject failure rejected) :
    rejected = input := by
  unfold rawIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      cases result
      rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; cases result; rfl }
      case identifier text => contradiction

private theorem rawIdentifier_reject_identifierAbsentAt
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : rawIdentifier context input = .reject failure rejected) :
    DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder := by
  rintro ⟨span, text, inside, atCursor⟩
  have found : input.peek? = some {
      span
      value := TokenKind.identifier text
    } := by
    unfold State.peek?
    change input.cursor < input.window.endIndex at inside
    change input.tokens[input.cursor]? = some {
      span
      value := TokenKind.identifier text
    } at atCursor
    simp only [inside, ↓reduceIte, atCursor]
  unfold rawIdentifier at result
  simp only [found] at result
  contradiction

/-- Raw-identifier success is one exact identifier transition. -/
theorem rawIdentifier_success_ordinaryOutcome_sound
    (context : ParseContext) {input output : State} {name : Identifier}
    (result : rawIdentifier context input = .ok name output) :
    DeclarativeGrammar.IdentifierParses input.declarativeRemainder name
      output.declarativeRemainder := by
  rcases rawIdentifier_ok_tokenAt context result with ⟨token, outputEq⟩
  subst output
  exact ⟨token, rfl, rfl, rfl⟩

/-- Raw-identifier rejection is exact and nonconsuming. -/
theorem rawIdentifier_reject_ordinaryOutcome_sound
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : rawIdentifier context input = .reject failure rejected) :
    DeclarativeGrammar.IdentifierRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  have rejectedEq := rawIdentifier_reject_state_eq_forOutcome context result
  subst rejected
  exact .absent (rawIdentifier_reject_identifierAbsentAt context result)

/-- Package raw-identifier success and exact rejection. -/
theorem rawIdentifier_ordinaryOutcome_sound (context : ParseContext) :
    (∀ {input output : State} {name : Identifier},
      rawIdentifier context input = .ok name output →
        DeclarativeGrammar.IdentifierParses input.declarativeRemainder name
          output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      rawIdentifier context input = .reject failure rejected →
        DeclarativeGrammar.IdentifierRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨rawIdentifier_success_ordinaryOutcome_sound context,
    rawIdentifier_reject_ordinaryOutcome_sound context⟩

/-- Raw identifiers reuse the deterministic identifier outcome contract. -/
theorem rawIdentifier_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.IdentifierParses
      DeclarativeGrammar.IdentifierRejects :=
  DeclarativeGrammar.identifierDeterministicOutcomeSpec

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PrimitiveRejectionDiagnosticProperties
/-! Exact diagnostic reports for current-input and identifier rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The executable current span and token realize the independent observation. -/
theorem currentInputAt_currentSpan_peekKind (input : State) :
    DeclarativeGrammar.CurrentInputAt input.file.id input.window.endByte
      input.declarativeRemainder input.currentSpan input.peekKind? := by
  cases found : input.peek? with
  | some token =>
      have observed := DeclarativeGrammar.CurrentInputAt.token
        (source := input.file.id) (endByte := input.window.endByte)
        (input := input.declarativeRemainder)
        (tokenAt_of_peek?_eq_some found)
      simpa only [State.currentSpan, State.peekKind?, found, Option.map_some]
        using observed
  | none =>
      by_cases inside : input.cursor < input.window.endIndex
      · have missing : input.tokens[input.cursor]? = none := by
          simpa only [State.peek?, inside, if_true] using found
        have observed := DeclarativeGrammar.CurrentInputAt.missingToken
          (source := input.file.id) (endByte := input.window.endByte)
          (input := input.declarativeRemainder) inside missing
        simpa only [State.currentSpan, State.peekKind?, found, Option.map_none,
          Lexer.sourceSpan] using observed
      · have observed := DeclarativeGrammar.CurrentInputAt.windowEnd
          (source := input.file.id) (endByte := input.window.endByte)
          (input := input.declarativeRemainder) (Nat.le_of_not_gt inside)
        simpa only [State.currentSpan, State.peekKind?, found, Option.map_none,
          Lexer.sourceSpan] using observed

/-- Independent observation fixes both executable fields, including EOF. -/
theorem currentInputAt_iff_currentSpan_peekKind
    {input : State} {span : SourceSpan} {found : Option TokenKind} :
    DeclarativeGrammar.CurrentInputAt input.file.id input.window.endByte
      input.declarativeRemainder span found ↔
      input.currentSpan = span ∧ input.peekKind? = found := by
  constructor
  · intro observed
    rcases observed.result_unique (currentInputAt_currentSpan_peekKind input) with
      ⟨spanEq, foundEq⟩
    exact ⟨spanEq.symm, foundEq.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact currentInputAt_currentSpan_peekKind input

/-- Converting an uncommitted failure retains every payload field exactly. -/
theorem Failure.toDiagnostic_injective : Function.Injective Failure.toDiagnostic := by
  intro left right equal
  cases left
  cases right
  simp only [Failure.toDiagnostic, ParseDiagnostic.mk.injEq,
    ParseDiagnosticKind.unexpected.injEq] at equal
  rcases equal with ⟨rfl, rfl, rfl, rfl⟩
  rfl

/-- Independent reports exactly identify the failure created by rejection.
No event is committed by this primitive, and its input state is retained. -/
theorem rejectAt_reports_iff {alpha : Type}
    {input : State} {expected : NonemptyList ParseExpectation}
    {context : ParseContext} {diagnostic : ParseDiagnostic} :
    DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
      expected context input.declarativeRemainder diagnostic ↔
      ∃ failure, rejectAt (α := alpha) input expected context =
        .reject failure input ∧ failure.toDiagnostic = diagnostic := by
  constructor
  · intro reported
    cases reported with
    | reported observed =>
        rcases currentInputAt_iff_currentSpan_peekKind.mp observed with
          ⟨spanEq, foundEq⟩
        refine ⟨_, rfl, ?_⟩
        simp only [Failure.toDiagnostic, spanEq, foundEq]
  · rintro ⟨failure, result, diagnosticEq⟩
    unfold rejectAt at result
    cases result
    subst diagnostic
    exact .reported (currentInputAt_currentSpan_peekKind input)

/-- Every primitive rejection has its independent report and adds no event. -/
theorem rejectAt_reject_reports {alpha : Type}
    {input rejected : State} {failure : Failure}
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (result : rejectAt (α := alpha) input expected context =
      .reject failure rejected) :
    DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        expected context input.declarativeRemainder failure.toDiagnostic ∧
      rejected.diagnostics = input.diagnostics := by
  unfold rejectAt at result
  cases result
  exact ⟨.reported (currentInputAt_currentSpan_peekKind input), rfl⟩

/-- An unavailable identifier selects the exact uncommitted rejection. -/
theorem rawIdentifier_eq_rejectAt_of_identifierAbsent (context : ParseContext)
    {input : State}
    (absent : DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder) :
    rawIdentifier context input =
      rejectAt input { head := .identifier, tail := [] } context := by
  unfold rawIdentifier
  cases found : input.peek? with
  | none => rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> try rfl
      case identifier text =>
        exact False.elim (absent ⟨span, text, tokenAt_of_peek?_eq_some found⟩)

/-- Checked names preserve the raw failure and cannot add a hyphen diagnostic. -/
theorem identifier_eq_rejectAt_of_identifierAbsent (context : ParseContext)
    {input : State}
    (absent : DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder) :
    identifier context input =
      rejectAt input { head := .identifier, tail := [] } context := by
  unfold identifier
  rw [rawIdentifier_eq_rejectAt_of_identifierAbsent context absent]
  rfl

/-- The raw-name rejection report is complete in either direction. -/
theorem rawIdentifier_reject_reports_iff (context : ParseContext)
    {input : State} {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .identifier, tail := [] } context
        input.declarativeRemainder diagnostic) ↔
      ∃ failure, rawIdentifier context input = .reject failure input ∧
        failure.toDiagnostic = diagnostic := by
  constructor
  · rintro ⟨absent, reported⟩
    rcases (rejectAt_reports_iff (alpha := Identifier)).mp reported with
      ⟨failure, result, reportEq⟩
    exact ⟨failure,
      (rawIdentifier_eq_rejectAt_of_identifierAbsent context absent).trans result,
      reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    have absent : DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder := by
      cases rawIdentifier_reject_ordinaryOutcome_sound context result with
      | absent missing => exact missing
    refine ⟨absent, (rejectAt_reports_iff (alpha := Identifier)).mpr ?_⟩
    exact ⟨failure,
      (rawIdentifier_eq_rejectAt_of_identifierAbsent context absent).symm.trans result,
      reportEq⟩

/-- Checked-name rejection has the same exact report as raw-name rejection. -/
theorem identifier_reject_reports_iff (context : ParseContext)
    {input : State} {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .identifier, tail := [] } context
        input.declarativeRemainder diagnostic) ↔
      ∃ failure, identifier context input = .reject failure input ∧
        failure.toDiagnostic = diagnostic := by
  constructor
  · rintro ⟨absent, reported⟩
    rcases (rejectAt_reports_iff (alpha := Identifier)).mp reported with
      ⟨failure, result, reportEq⟩
    exact ⟨failure,
      (identifier_eq_rejectAt_of_identifierAbsent context absent).trans result,
      reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    have absent := identifier_reject_identifierAbsentAt context result
    refine ⟨absent, (rejectAt_reports_iff (alpha := Identifier)).mpr ?_⟩
    exact ⟨failure,
      (identifier_eq_rejectAt_of_identifierAbsent context absent).symm.trans result,
      reportEq⟩

/-- Raw-name rejection preserves the complete existing diagnostic sequence. -/
theorem rawIdentifier_reject_diagnostics_eq (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : rawIdentifier context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics := by
  have absent : DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder := by
    have rejection := rawIdentifier_reject_ordinaryOutcome_sound context result
    generalize endpointEq : rejected.declarativeRemainder = endpoint at rejection
    cases rejection with
    | absent missing => exact missing
  rw [rawIdentifier_eq_rejectAt_of_identifierAbsent context absent] at result
  exact (rejectAt_reject_reports _ context result).2

/-- Checked-name rejection also preserves all earlier diagnostics. -/
theorem identifier_reject_diagnostics_eq (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : identifier context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics := by
  rw [identifier_reject_state_eq context result]

end Solcore.Syntax.Parser
end
