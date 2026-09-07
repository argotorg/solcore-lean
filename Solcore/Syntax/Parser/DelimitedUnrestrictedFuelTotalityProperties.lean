import Solcore.Syntax.Parser.UnrestrictedFuelElementContract

/-! Actual delimited loops are ordinary on arbitrary states under the minimal
child fuel contract. Opening/comma tokens pay recursive units before child
execution; child success only preserves the resulting remaining-count bound. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeDelimited_unrestricted_ordinary {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext) (elementsRev : List α) :
    Parser.Ordinary (closeDelimited opening closing context elementsRev) := by
  intro input
  rcases symbol_ordinary closing context input with
    ⟨token, next, result⟩ | ⟨failure, next, result⟩
  · exact Or.inl ⟨{ span := SourceSpan.cover opening.span token.span, elements := elementsRev.reverse },
      next, by unfold closeDelimited; simp only [result]⟩
  · exact Or.inr ⟨failure, next, by unfold closeDelimited; simp only [result]⟩

theorem afterDelimitedElement_ordinary_of_unrestrictedElementFuel {α : Type}
    (element : Parser α) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract element elementFuel)
    (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ loopFuel elementsRev input,
      input.remainingCount < loopFuel → input.remainingCount < elementFuel →
      (∃ values next, afterDelimitedElement element closing allowTrailing context phase
        opening loopFuel elementsRev input = .ok values next) ∨
      (∃ failure next, afterDelimitedElement element closing allowTrailing context phase
        opening loopFuel elementsRev input = .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero => intro elementsRev input loopAdequate elementAdequate; omega
  | succ loopFuel ih =>
      intro elementsRev input loopAdequate elementAdequate
      unfold afterDelimitedElement
      split
      · cases commaResult : symbol .comma context input with
        | invariant error =>
            exact False.elim (symbol_ne_invariant .comma context input error commaResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok comma afterComma =>
            have commaLoopAdequate : afterComma.remainingCount < loopFuel :=
              symbol_remainingCount_lt_of_success .comma context commaResult loopAdequate
            have commaElementAdequate : afterComma.remainingCount < elementFuel :=
              symbol_remainingCount_lt_of_success .comma context commaResult (by omega)
            dsimp only
            split
            · exact closeDelimited_unrestricted_ordinary opening closing context elementsRev afterComma
            · cases elementResult : element afterComma with
              | invariant error =>
                  exact False.elim (contract.ne_invariant afterComma commaElementAdequate error elementResult)
              | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
              | ok value next =>
                  have progress := contract.cursorLtOnSuccess elementResult
                  dsimp only
                  split
                  · exact ih (value :: elementsRev) next
                      (contract.remainingCount_lt_of_success elementResult commaLoopAdequate)
                      (contract.remainingCount_lt_of_success elementResult commaElementAdequate)
                  · omega
      · split
        · exact closeDelimited_unrestricted_ordinary opening closing context elementsRev input
        · exact Or.inr ⟨_, input, rfl⟩

theorem delimitedWithPolicy_ordinary_of_unrestrictedElementFuel {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract element elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ values next, delimitedWithPolicy opening closing allowEmpty allowTrailing element
      context phase input = .ok values next) ∨
    (∃ failure next, delimitedWithPolicy opening closing allowEmpty allowTrailing element
      context phase input = .reject failure next) := by
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | invariant error => exact False.elim (symbol_ne_invariant opening context input error openingResult)
  | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
  | ok openingToken afterOpening =>
      have afterOpeningAdequate : afterOpening.remainingCount < elementFuel :=
        symbol_remainingCount_lt_of_success opening context openingResult adequate
      dsimp only
      split
      · exact closeDelimited_unrestricted_ordinary openingToken closing context [] afterOpening
      · cases elementResult : element afterOpening with
        | invariant error =>
            exact False.elim (contract.ne_invariant afterOpening afterOpeningAdequate error elementResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok value next =>
            have progress := contract.cursorLtOnSuccess elementResult
            dsimp only
            split
            · exact afterDelimitedElement_ordinary_of_unrestrictedElementFuel element elementFuel contract
                closing allowTrailing context phase openingToken (afterOpening.remainingCount + 1) [value] next
                (contract.remainingCount_lt_of_success elementResult (by omega))
                (contract.remainingCount_lt_of_success elementResult afterOpeningAdequate)
            · omega

theorem delimited_ordinary_of_unrestrictedElementFuel {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract element elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ values next, delimited opening closing allowEmpty element context phase input = .ok values next) ∨
    (∃ failure next, delimited opening closing allowEmpty element context phase input = .reject failure next) :=
  delimitedWithPolicy_ordinary_of_unrestrictedElementFuel opening closing allowEmpty true
    element context phase elementFuel contract input adequate

theorem delimited_ne_invariant_of_unrestrictedElementFuel {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract element elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) (error : ParserInvariantError) :
    delimited opening closing allowEmpty element context phase input ≠ .invariant error := by
  intro failed
  rcases delimited_ordinary_of_unrestrictedElementFuel opening closing allowEmpty element context phase
      elementFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

private theorem closeDelimited_endIndex_onSuccess {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext) (elementsRev : List α)
    {input output : State} {values : DelimitedList α}
    (result : closeDelimited opening closing context elementsRev input = .ok values output) :
    output.window.endIndex = input.window.endIndex := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok token next =>
      simp only [closingResult] at result
      cases result
      rw [(symbol_ok_state_shape closing context closingResult).2]

theorem afterDelimitedElement_endIndex_onSuccess {α : Type} {element : Parser α}
    (elementEndIndex : ∀ {input output : State} {value : α}, element input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (closing : Symbol) (allowTrailing : Bool) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input values output,
      afterDelimitedElement element closing allowTrailing context phase opening fuel elementsRev input =
        .ok values output → output.window.endIndex = input.window.endIndex := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input values output result; simp [afterDelimitedElement] at result
  | succ fuel ih =>
      intro elementsRev input values output result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok token afterComma =>
            have commaEndIndex : afterComma.window.endIndex = input.window.endIndex := by
              rw [(symbol_ok_state_shape .comma context commaResult).2]
            simp only [commaResult] at result
            split at result
            · exact (closeDelimited_endIndex_onSuccess opening closing context elementsRev result).trans commaEndIndex
            · cases elementResult : element afterComma with
              | invariant error => simp [elementResult] at result
              | reject failure rejected => simp [elementResult] at result
              | ok value next =>
                  simp only [elementResult] at result
                  split at result
                  · exact (ih (value :: elementsRev) next values output result).trans
                      ((elementEndIndex elementResult).trans commaEndIndex)
                  · contradiction
      · split at result
        · exact closeDelimited_endIndex_onSuccess opening closing context elementsRev result
        · unfold rejectAt at result; contradiction

theorem delimitedWithPolicy_endIndex_onSuccess {α : Type} {element : Parser α}
    (elementEndIndex : ∀ {input output : State} {value : α}, element input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool) (context : ParseContext) (phase : ParserPhase)
    {input output : State} {values : DelimitedList α}
    (result : delimitedWithPolicy opening closing allowEmpty allowTrailing element context phase input =
      .ok values output) : output.window.endIndex = input.window.endIndex := by
  unfold delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingEndIndex : afterOpening.window.endIndex = input.window.endIndex := by
        rw [(symbol_ok_state_shape opening context openingResult).2]
      simp only [openingResult] at result
      split at result
      · exact (closeDelimited_endIndex_onSuccess openingToken closing context [] result).trans openingEndIndex
      · cases elementResult : element afterOpening with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok first next =>
            simp only [elementResult] at result
            split at result
            · exact (afterDelimitedElement_endIndex_onSuccess elementEndIndex closing allowTrailing
                context phase openingToken _ [first] next values output result).trans
                ((elementEndIndex elementResult).trans openingEndIndex)
            · contradiction

theorem delimited_endIndex_onSuccess {α : Type} {element : Parser α}
    (elementEndIndex : ∀ {input output : State} {value : α}, element input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase)
    {input output : State} {values : DelimitedList α}
    (result : delimited opening closing allowEmpty element context phase input = .ok values output) :
    output.window.endIndex = input.window.endIndex :=
  delimitedWithPolicy_endIndex_onSuccess elementEndIndex opening closing allowEmpty true context phase result

end Solcore.Syntax.Parser
