import Solcore.Syntax.Parser.Delimited

/-! Conditional totality for generic delimited parser loops. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Minimal valid-input contract needed to exclude delimited-loop invariants. -/
structure ElementTotalityContract {α : Type} (element : Parser α) : Prop where
  validFor : element.ValidFor (fun _ _ => True)
  preservesTokenWindow : Parser.PreservesTokenWindow element
  cursorLtOnSuccess : ∀ {input next : State} {value : α},
    element input = .ok value next → input.cursor < next.cursor
  invariantFree : ∀ input, input.ValidFor → ∀ error,
    element input ≠ .invariant error

private theorem symbol_ordinary (value : Symbol) (context : ParseContext)
    (state : State) :
    (∃ token next, symbol value context state = .ok token next) ∨
      (∃ failure next, symbol value context state = .reject failure next) := by
  cases result : symbol value context state with
  | ok token next => exact Or.inl ⟨token, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold symbol acceptToken at result
      cases found : state.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          simp only [found] at result
          split at result <;> contradiction

private theorem symbol_ne_invariant (value : Symbol) (context : ParseContext)
    (state : State) (error : ParserInvariantError) :
    symbol value context state ≠ .invariant error := by
  intro failed
  rcases symbol_ordinary value context state with
    ⟨token, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

private theorem closeDelimited_ordinary {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) (state : State) :
    (∃ values next,
      closeDelimited opening closing context elementsRev state =
        .ok values next) ∨
      (∃ failure next,
        closeDelimited opening closing context elementsRev state =
          .reject failure next) := by
  unfold closeDelimited
  rcases symbol_ordinary closing context state with
    ⟨token, next, result⟩ | ⟨failure, next, result⟩
  · rw [result]
    exact Or.inl ⟨_, _, rfl⟩
  · rw [result]
    exact Or.inr ⟨_, _, rfl⟩

private theorem remainingCount_lt_after_strict_progress
    {input next : State} {fuel : Nat}
    (nextValid : next.ValidFor) (windowEq : next.window = input.window)
    (progress : input.cursor < next.cursor)
    (adequate : input.remainingCount < fuel + 1) :
    next.remainingCount < fuel := by
  have nextCursorBound : next.cursor ≤ input.window.endIndex := by
    simpa [windowEq] using nextValid.cursor_le_endIndex
  have endIndexEq : next.window.endIndex = input.window.endIndex :=
    congrArg TokenWindow.endIndex windowEq
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq]
  omega

/--
Adequate fuel makes the generic tail loop ordinary: it either closes the list
or reports a source rejection, but cannot exhaust fuel or fail progress.
-/
theorem afterDelimitedElement_ordinary_of_remainingCount_lt {α : Type}
    (element : Parser α) (contract : ElementTotalityContract element)
    (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev state,
      state.ValidFor → state.remainingCount < fuel →
      (∃ values next,
        afterDelimitedElement element closing allowTrailing context phase
          opening fuel elementsRev state = .ok values next) ∨
      (∃ failure next,
        afterDelimitedElement element closing allowTrailing context phase
          opening fuel elementsRev state = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev state stateValid adequate
      omega
  | succ fuel inductionHypothesis =>
      intro elementsRev state stateValid adequate
      unfold afterDelimitedElement
      split
      · cases commaResult : symbol .comma context state with
        | ok comma afterComma =>
          have commaValid := symbol_validFor .comma context state stateValid
          rw [commaResult] at commaValid
          dsimp only
          split
          · exact closeDelimited_ordinary opening closing context elementsRev
              afterComma
          · cases elementResult : element afterComma with
            | invariant error =>
                exact False.elim
                  (contract.invariantFree afterComma commaValid.2.1 error
                    elementResult)
            | reject failure rejected =>
                exact Or.inr ⟨failure, rejected, rfl⟩
            | ok value next =>
                have valueReply := contract.validFor afterComma commaValid.2.1
                rw [elementResult] at valueReply
                have valueWindow := contract.preservesTokenWindow afterComma
                rw [elementResult] at valueWindow
                have progress := contract.cursorLtOnSuccess elementResult
                dsimp only
                split
                · have afterCommaWindow : afterComma.window = state.window := by
                    rw [(symbol_ok_state_shape .comma context commaResult).2]
                  have nextWindow : next.window = state.window :=
                    valueWindow.2.trans afterCommaWindow
                  have commaProgress : state.cursor < afterComma.cursor := by
                    rw [(symbol_ok_state_shape .comma context commaResult).2]
                    simp
                  have nextAdequate :=
                    remainingCount_lt_after_strict_progress valueReply.2.1
                      nextWindow (Nat.lt_trans commaProgress progress) adequate
                  exact inductionHypothesis (value :: elementsRev) next
                    valueReply.2.1 nextAdequate
                · omega
        | reject failure rejected =>
          exact Or.inr ⟨failure, rejected, rfl⟩
        | invariant error =>
          exact False.elim
            (symbol_ne_invariant .comma context state error commaResult)
      · split
        · exact closeDelimited_ordinary opening closing context elementsRev
            state
        · exact Or.inr ⟨_, _, rfl⟩

/-- Adequate tail-loop fuel rules out every invariant result explicitly. -/
theorem afterDelimitedElement_ne_invariant_of_remainingCount_lt {α : Type}
    (element : Parser α) (contract : ElementTotalityContract element)
    (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α) (state : State)
    (stateValid : state.ValidFor) (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    afterDelimitedElement element closing allowTrailing context phase opening
      fuel elementsRev state ≠ .invariant error := by
  intro failed
  rcases afterDelimitedElement_ordinary_of_remainingCount_lt element contract
      closing allowTrailing context phase opening fuel elementsRev state
      stateValid adequate with
    ⟨values, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Delimiter-policy execution is ordinary on every valid input. -/
theorem delimitedWithPolicy_ordinary {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (contract : ElementTotalityContract element) (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next,
      delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase input = .ok values next) ∨
      (∃ failure next,
        delimitedWithPolicy opening closing allowEmpty allowTrailing element
          context phase input = .reject failure next) := by
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | ok openingToken afterOpening =>
    have openingValid := symbol_validFor opening context input inputValid
    rw [openingResult] at openingValid
    dsimp only
    split
    · exact closeDelimited_ordinary openingToken closing context [] afterOpening
    · cases elementResult : element afterOpening with
      | invariant error =>
          exact False.elim
            (contract.invariantFree afterOpening openingValid.2.1 error
              elementResult)
      | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
      | ok value next =>
          have valueReply := contract.validFor afterOpening openingValid.2.1
          rw [elementResult] at valueReply
          have valueWindow := contract.preservesTokenWindow afterOpening
          rw [elementResult] at valueWindow
          have progress := contract.cursorLtOnSuccess elementResult
          dsimp only
          split
          · have adequate :
                next.remainingCount < afterOpening.remainingCount + 1 := by
              apply remainingCount_lt_after_strict_progress valueReply.2.1
                valueWindow.2 progress
              omega
            exact afterDelimitedElement_ordinary_of_remainingCount_lt element
              contract closing allowTrailing context phase openingToken
              (afterOpening.remainingCount + 1) [value] next
              valueReply.2.1 adequate
          · omega
  | reject failure rejected =>
    exact Or.inr ⟨failure, rejected, rfl⟩
  | invariant error =>
    exact False.elim
      (symbol_ne_invariant opening context input error openingResult)

theorem delimitedWithPolicy_ne_invariant {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (contract : ElementTotalityContract element) (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    delimitedWithPolicy opening closing allowEmpty allowTrailing element
      context phase input ≠ .invariant error := by
  intro failed
  rcases delimitedWithPolicy_ordinary opening closing allowEmpty allowTrailing
      element context phase contract input inputValid with
    ⟨values, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

theorem delimited_ordinary {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (contract : ElementTotalityContract element) (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next,
      delimited opening closing allowEmpty element context phase input =
        .ok values next) ∨
      (∃ failure next,
        delimited opening closing allowEmpty element context phase input =
          .reject failure next) :=
  delimitedWithPolicy_ordinary opening closing allowEmpty true element context
    phase contract input inputValid

theorem delimited_ne_invariant {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (contract : ElementTotalityContract element) (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    delimited opening closing allowEmpty element context phase input ≠
      .invariant error :=
  delimitedWithPolicy_ne_invariant opening closing allowEmpty true element
    context phase contract input inputValid error

theorem delimitedNoTrailing_ordinary {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (contract : ElementTotalityContract element) (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next,
      delimitedNoTrailing opening closing allowEmpty element context phase
        input = .ok values next) ∨
      (∃ failure next,
        delimitedNoTrailing opening closing allowEmpty element context phase
          input = .reject failure next) :=
  delimitedWithPolicy_ordinary opening closing allowEmpty false element context
    phase contract input inputValid

theorem delimitedNoTrailing_ne_invariant {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (contract : ElementTotalityContract element) (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    delimitedNoTrailing opening closing allowEmpty element context phase input ≠
      .invariant error :=
  delimitedWithPolicy_ne_invariant opening closing allowEmpty false element
    context phase contract input inputValid error

end Solcore.Syntax.Parser
