import Solcore.Syntax.Parser.Operator
import Solcore.Syntax.Parser.PrimitiveTotalityProperties

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
