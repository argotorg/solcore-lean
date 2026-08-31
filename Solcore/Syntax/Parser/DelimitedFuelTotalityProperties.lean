import Solcore.Syntax.Parser.DelimitedTotalityProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties

/-! Element-fuel-aware totality for recursive delimited parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
The element contract needed when invariant freedom holds only below a fixed
recursive-fuel bound. This is weaker than `ElementTotalityContract`: finite
recursive parsers need not be invariant-free on every valid state.
-/
structure FuelElementTotalityContract {α : Type}
    (element : Parser α) (fuel : Nat) : Prop where
  validFor : element.ValidFor (fun _ _ => True)
  preservesTokenWindow : Parser.PreservesTokenWindow element
  cursorLtOnSuccess : ∀ {input next : State} {value : α},
    element input = .ok value next → input.cursor < next.cursor
  ordinary : ∀ input, input.ValidFor → input.remainingCount < fuel →
    (∃ value next, element input = .ok value next) ∨
      (∃ failure next, element input = .reject failure next)

namespace FuelElementTotalityContract

theorem ne_invariant {α : Type} {element : Parser α} {fuel : Nat}
    (contract : FuelElementTotalityContract element fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    element input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end FuelElementTotalityContract

private theorem closeDelimited_ordinary {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) :
    Parser.Ordinary (closeDelimited opening closing context elementsRev) := by
  intro input
  rcases symbol_ordinary closing context input with
    ⟨token, next, result⟩ | ⟨failure, next, result⟩
  · exact Or.inl ⟨{
        span := SourceSpan.cover opening.span token.span
        elements := elementsRev.reverse
      }, next, by unfold closeDelimited; simp only [result]⟩
  · exact Or.inr ⟨failure, next, by
      unfold closeDelimited
      simp only [result]⟩

/-- Cursor-monotone steps in one token window preserve a remaining-count bound. -/
theorem remainingCount_lt_of_cursor_le
    {input next : State} {fuel : Nat}
    (windowEq : next.window = input.window)
    (cursorLe : input.cursor ≤ next.cursor)
    (adequate : input.remainingCount < fuel) :
    next.remainingCount < fuel := by
  have endIndexEq : next.window.endIndex = input.window.endIndex :=
    congrArg TokenWindow.endIndex windowEq
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq]
  omega

/-- One strict cursor step spends one unit of a remaining-count fuel bound. -/
theorem remainingCount_lt_after_strict_progress
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
The delimited tail loop remains ordinary when every element state is below the
fixed recursive-fuel bound, independently of the loop's own decreasing fuel.
-/
theorem afterDelimitedElement_ordinary_of_elementFuel {α : Type}
    (element : Parser α) (elementFuel : Nat)
    (contract : FuelElementTotalityContract element elementFuel)
    (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ loopFuel elementsRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < elementFuel →
      (∃ values next,
        afterDelimitedElement element closing allowTrailing context phase
          opening loopFuel elementsRev input = .ok values next) ∨
      (∃ failure next,
        afterDelimitedElement element closing allowTrailing context phase
          opening loopFuel elementsRev input = .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro elementsRev input inputValid loopAdequate elementAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro elementsRev input inputValid loopAdequate elementAdequate
      unfold afterDelimitedElement
      split
      · cases commaResult : symbol .comma context input with
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .comma context input error commaResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok comma afterComma =>
            have commaValid := symbol_validFor .comma context input inputValid
            rw [commaResult] at commaValid
            have commaWindow := symbol_preservesTokenWindow .comma context input
            rw [commaResult] at commaWindow
            have commaProgress : input.cursor < afterComma.cursor :=
              acceptToken_cursor_lt_onSuccess (.symbol .comma) context
                (· == .symbol .comma) commaResult
            have afterCommaAdequate :
                afterComma.remainingCount < elementFuel :=
              remainingCount_lt_after_strict_progress commaValid.2.1
                commaWindow.2 commaProgress (by omega)
            dsimp only
            split
            · exact closeDelimited_ordinary opening closing context elementsRev
                afterComma
            · cases elementResult : element afterComma with
              | invariant error =>
                  exact False.elim (contract.ne_invariant afterComma
                    commaValid.2.1 afterCommaAdequate error elementResult)
              | reject failure rejected =>
                  exact Or.inr ⟨failure, rejected, rfl⟩
              | ok value next =>
                  have valueValid := contract.validFor afterComma commaValid.2.1
                  rw [elementResult] at valueValid
                  have valueWindow := contract.preservesTokenWindow afterComma
                  rw [elementResult] at valueWindow
                  have valueProgress := contract.cursorLtOnSuccess elementResult
                  dsimp only
                  split
                  · have nextWindow : next.window = input.window :=
                      valueWindow.2.trans commaWindow.2
                    have nextLoopAdequate :
                        next.remainingCount < loopFuel :=
                      remainingCount_lt_after_strict_progress valueValid.2.1
                        nextWindow (Nat.lt_trans commaProgress valueProgress)
                        loopAdequate
                    have nextElementAdequate :
                        next.remainingCount < elementFuel :=
                      remainingCount_lt_after_strict_progress valueValid.2.1
                        valueWindow.2 valueProgress (by omega)
                    exact inductionHypothesis (value :: elementsRev) next
                      valueValid.2.1 nextLoopAdequate nextElementAdequate
                  · omega
      · split
        · exact closeDelimited_ordinary opening closing context elementsRev input
        · exact Or.inr ⟨_, input, rfl⟩

/--
One extra unit of recursive fuel at the delimited input pays for the opening
delimiter, after which every element call satisfies the fixed fuel bound.
-/
theorem delimitedWithPolicy_ordinary_of_elementFuel {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementFuel : Nat)
    (contract : FuelElementTotalityContract element elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ values next,
      delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase input = .ok values next) ∨
    (∃ failure next,
      delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase input = .reject failure next) := by
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | invariant error =>
      exact False.elim
        (symbol_ne_invariant opening context input error openingResult)
  | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
  | ok openingToken afterOpening =>
      have openingValid := symbol_validFor opening context input inputValid
      rw [openingResult] at openingValid
      have openingWindow := symbol_preservesTokenWindow opening context input
      rw [openingResult] at openingWindow
      have openingProgress : input.cursor < afterOpening.cursor :=
        acceptToken_cursor_lt_onSuccess (.symbol opening) context
          (· == .symbol opening) openingResult
      have afterOpeningAdequate :
          afterOpening.remainingCount < elementFuel :=
        remainingCount_lt_after_strict_progress openingValid.2.1
          openingWindow.2 openingProgress adequate
      dsimp only
      split
      · exact closeDelimited_ordinary openingToken closing context []
          afterOpening
      · cases elementResult : element afterOpening with
        | invariant error =>
            exact False.elim (contract.ne_invariant afterOpening
              openingValid.2.1 afterOpeningAdequate error elementResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok value next =>
            have valueValid := contract.validFor afterOpening openingValid.2.1
            rw [elementResult] at valueValid
            have valueWindow := contract.preservesTokenWindow afterOpening
            rw [elementResult] at valueWindow
            have valueProgress := contract.cursorLtOnSuccess elementResult
            dsimp only
            split
            · have nextLoopAdequate :
                  next.remainingCount < afterOpening.remainingCount + 1 :=
                remainingCount_lt_after_strict_progress valueValid.2.1
                  valueWindow.2 valueProgress (by omega)
              have nextElementAdequate :
                  next.remainingCount < elementFuel :=
                remainingCount_lt_after_strict_progress valueValid.2.1
                  valueWindow.2 valueProgress (by omega)
              exact afterDelimitedElement_ordinary_of_elementFuel element
                elementFuel contract closing allowTrailing context phase
                openingToken (afterOpening.remainingCount + 1) [value] next
                valueValid.2.1 nextLoopAdequate nextElementAdequate
            · omega

/-- Fuel-aware totality for the ordinary trailing-comma wrapper. -/
theorem delimited_ordinary_of_elementFuel {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementFuel : Nat)
    (contract : FuelElementTotalityContract element elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ values next,
      delimited opening closing allowEmpty element context phase input =
        .ok values next) ∨
    (∃ failure next,
      delimited opening closing allowEmpty element context phase input =
        .reject failure next) :=
  delimitedWithPolicy_ordinary_of_elementFuel opening closing allowEmpty true
    element context phase elementFuel contract input inputValid adequate

theorem delimited_ne_invariant_of_elementFuel {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementFuel : Nat)
    (contract : FuelElementTotalityContract element elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    delimited opening closing allowEmpty element context phase input ≠
      .invariant error := by
  intro failed
  rcases delimited_ordinary_of_elementFuel opening closing allowEmpty element
      context phase elementFuel contract input inputValid adequate with
    ⟨values, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
