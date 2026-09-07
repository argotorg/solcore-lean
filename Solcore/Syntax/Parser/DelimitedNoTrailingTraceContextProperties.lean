import Solcore.Syntax.Parser.DelimitedNoTrailingTraceCompletenessProperties

/-! Successful no-trailing lists preserve source and the entire active window
under exactly the corresponding child law, independently of token carriers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {α : Type} {element : Parser α}

theorem afterDelimitedElement_noTrailing_success_context
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input values output,
      afterDelimitedElement element closing false context phase opening fuel elementsRev input =
        .ok values output → output.file = input.file ∧ output.window = input.window := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input values output result; simp [afterDelimitedElement] at result
  | succ fuel ih =>
      intro elementsRev input values output result
      unfold afterDelimitedElement at result
      by_cases commaPresent : isSymbol input .comma = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .comma context commaPresent with ⟨comma, commaResult⟩
        simp only [commaPresent, if_true, commaResult, Bool.false_and, Bool.false_eq_true, if_false]
          at result
        cases elementResult : element { input with cursor := input.cursor + 1 } with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok value next =>
            simp only [elementResult] at result
            split at result
            · have frame := contextFrame elementResult
              have tail := ih (value :: elementsRev) next values output result
              exact ⟨tail.1.trans frame.1, tail.2.trans frame.2⟩
            · contradiction
      · have commaFalse : isSymbol input .comma = false := Bool.eq_false_iff.mpr commaPresent
        simp only [commaFalse, Bool.false_eq_true, if_false] at result
        split at result
        · rcases closeDelimited_success_trace_sound opening closing context elementsRev result with
            ⟨_, _, _, stateEq⟩
          rw [stateEq]; exact ⟨rfl, rfl⟩
        · unfold rejectAt at result; contradiction

theorem delimitedNoTrailing_success_context
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase) :
    ParserSuccessContext (delimitedNoTrailing opening closing allowEmpty element context phase) := by
  intro input output values result
  unfold delimitedNoTrailing delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have stateEq := (symbol_ok_tokenAt opening context openingResult).2
      subst afterOpening
      simp only [openingResult] at result
      split at result
      · rcases closeDelimited_success_trace_sound openingToken closing context [] result with
          ⟨_, _, _, outputEq⟩
        rw [outputEq]; exact ⟨rfl, rfl⟩
      · cases elementResult : element { input with cursor := input.cursor + 1 } with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok first next =>
            simp only [elementResult] at result
            split at result
            · have frame := contextFrame elementResult
              have tail := afterDelimitedElement_noTrailing_success_context contextFrame
                closing context phase openingToken _ [first] next values output result
              exact ⟨tail.1.trans frame.1, tail.2.trans frame.2⟩
            · contradiction

end Solcore.Syntax.Parser
