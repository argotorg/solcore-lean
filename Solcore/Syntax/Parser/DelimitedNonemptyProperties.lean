import Solcore.Syntax.Parser.Delimited

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
