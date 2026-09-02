import Solcore.Syntax.DeclarativeDeriveTargetOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.DeriveTargetSoundnessProperties

/-! Exact ordinary-rejection reflection for dotted derive targets. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem reservedDeriveKeyword?_eq_some_of_allowed
    (keyword : HardKeyword)
    (allowed : DeclarativeGrammar.ReservedDeriveTargetKeyword keyword) :
    DeriveTargetInternals.reservedDeriveKeyword? (.keyword keyword) =
      some keyword := by
  cases keyword <;>
    simp [DeclarativeGrammar.ReservedDeriveTargetKeyword,
      DeriveTargetInternals.reservedDeriveKeyword?] at allowed ⊢

private theorem tokenKindAbsentAt_of_peek?_eq_none (kind : TokenKind)
    {input : State} (found : input.peek? = none) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor kind := by
  rintro ⟨span, present⟩
  unfold State.peek? at found
  simp only [present.1, ↓reduceIte, present.2] at found
  contradiction

private theorem identifierAbsentAt_of_peek?_eq_none {input : State}
    (found : input.peek? = none) :
    DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder := by
  rintro ⟨span, text, present⟩
  exact tokenKindAbsentAt_of_peek?_eq_none (.identifier text) found
    ⟨span, by simpa only [State.declarativeRemainder] using present⟩

private theorem deriveReservedComponentAbsentAt_of_lookup_none
    {input : State} {token : Token}
    (found : input.peek? = some token)
    (reserved : DeriveTargetInternals.reservedDeriveKeyword? token.value =
      none) :
    DeclarativeGrammar.DeriveReservedComponentAbsentAt
      input.declarativeRemainder := by
  intro keyword allowed
  rintro ⟨span, present⟩
  have current := tokenAt_of_peek?_eq_some found
  have tokenEq : token = { span, value := .keyword keyword } := by
    apply Option.some.inj
    exact current.2.symm.trans (by
      simpa only [State.declarativeRemainder] using present.2)
  subst token
  rw [reservedDeriveKeyword?_eq_some_of_allowed keyword allowed] at reserved
  contradiction

/-- Every executable derive-component rejection records that neither its
reserved-keyword branch nor its checked-identifier branch was available. -/
theorem deriveComponent_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : DeriveTargetInternals.deriveComponent input =
      .reject failure rejected) :
    DeclarativeGrammar.DeriveComponentRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold DeriveTargetInternals.deriveComponent at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      change rejectAt input { head := .identifier, tail := [] } .topItem =
        .reject failure rejected at result
      unfold rejectAt at result
      cases result
      exact .unavailable
        (fun keyword _ => tokenKindAbsentAt_of_peek?_eq_none
          (.keyword keyword) found)
        (.absent (identifierAbsentAt_of_peek?_eq_none found))
  | some token =>
      simp only [found] at result
      cases reserved :
          DeriveTargetInternals.reservedDeriveKeyword? token.value with
      | some keyword => simp [reserved] at result
      | none =>
          simp only [reserved] at result
          have rejectedEq := identifier_reject_state_eq .topItem result
          subst rejected
          exact .unavailable
            (deriveReservedComponentAbsentAt_of_lookup_none found reserved)
            (identifier_reject_sound .topItem result)

namespace DeriveTargetInternals

private theorem deriveTargetTail_reject_ordinaryOutcome_sound_recursive
    (first : Identifier) :
    ∀ fuel last tailRev input failure rejected,
      deriveTargetTail first fuel last tailRev input =
          .reject failure rejected →
        DeclarativeGrammar.DeriveTargetTailRejects
          input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input failure rejected result
      simp [deriveTargetTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input failure rejected result
      unfold deriveTargetTail at result
      split at result
      · have dotPresent : isSymbol input .dot = true := by assumption
        cases dotResult : symbol .dot .topItem input with
        | invariant error => simp [dotResult] at result
        | reject dotFailure afterDot =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .dot .topItem dotPresent
                with ⟨dot, parsed⟩
            rw [parsed] at dotResult
            contradiction
        | ok dot afterDot =>
            simp only [dotResult] at result
            have dotParsed := symbol_success_exactTokenParses .dot .topItem
              dotResult
            cases componentResult : deriveComponent afterDot with
            | invariant error => simp [componentResult] at result
            | reject componentFailure afterComponent =>
                simp only [componentResult] at result
                cases result
                exact .componentRejected dot.span dotParsed
                  (deriveComponent_reject_ordinaryOutcome_sound
                    componentResult)
            | ok component afterComponent =>
                simp only [componentResult] at result
                exact .laterRejected dot.span dotParsed
                  (deriveComponent_success_sound componentResult)
                  (inductionHypothesis component (component :: tailRev)
                    afterComponent failure rejected result)
      · simp [finishDeriveTarget] at result

/-- Rejection under the production fuel follows the exact dotted-tail trace. -/
theorem deriveTargetTail_production_reject_ordinaryOutcome_sound
    (first last : Identifier) (tailRev : List Identifier)
    {input rejected : State} {failure : Failure}
    (result : deriveTargetTail first (input.remainingCount + 1) last tailRev
      input = .reject failure rejected) :
    DeclarativeGrammar.DeriveTargetTailRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  deriveTargetTail_reject_ordinaryOutcome_sound_recursive first
    (input.remainingCount + 1) last tailRev input failure rejected result

end DeriveTargetInternals

/-- Every executable derive-target rejection is its first unavailable
component or an exact rejection in the maximal dotted tail. -/
theorem deriveTarget_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : deriveTarget input = .reject failure rejected) :
    DeclarativeGrammar.DeriveTargetRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold deriveTarget at result
  cases firstResult : DeriveTargetInternals.deriveComponent input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure afterFirst =>
      simp only [firstResult] at result
      cases result
      exact .firstRejected
        (deriveComponent_reject_ordinaryOutcome_sound firstResult)
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact .tailRejected (deriveComponent_success_sound firstResult)
        (DeriveTargetInternals.deriveTargetTail_production_reject_ordinaryOutcome_sound
          first first [] result)

end Solcore.Syntax.Parser
