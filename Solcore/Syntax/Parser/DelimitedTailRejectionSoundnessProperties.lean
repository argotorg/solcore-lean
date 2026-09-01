import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

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
