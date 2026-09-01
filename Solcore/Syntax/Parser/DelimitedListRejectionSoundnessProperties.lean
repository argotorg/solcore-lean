import Solcore.Syntax.Parser.DelimitedTailRejectionSoundnessProperties

/-! Exact ordinary-rejection reflection for complete delimited attempts. -/

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
