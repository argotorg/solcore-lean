import Solcore.Syntax.DeclarativeYulNamesGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.YulNamesDiagnosticReflectionProperties

/-!
Exact diagnostic-free declarative soundness for inline-Yul name sequences.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Finishing fixes the first-to-last cover, forward name order, and unchanged
remainder. -/
theorem finishYulNames_success_sound
    (first last : YulIdentifier) (tailRev : List YulIdentifier)
    {input next : State} {names : YulNameSequence}
    (result : finishYulNames first last tailRev input = .ok names next) :
    DeclarativeGrammar.FinishYulNamesParses first last tailRev
      input.declarativeRemainder names.span names.names
        next.declarativeRemainder := by
  unfold finishYulNames at result
  cases result
  exact .parsed

/-- Every diagnostic-free tail success follows the exact comma-prioritized,
non-trailing grammar and retains each strict name advance. -/
theorem yulNamesTail_success_sound (first : YulIdentifier) :
    ∀ fuel last tailRev, ∀ {input next : State} {names : YulNameSequence},
      next.diagnosticsRev = [] →
      yulNamesTail first fuel last tailRev input = .ok names next →
      DeclarativeGrammar.YulNamesTailParses first input.declarativeRemainder
        last tailRev names.span names.names next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input next names diagnosticFree result
      simp [yulNamesTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input next names diagnosticFree result
      unfold yulNamesTail at result
      split at result
      next commaPresent =>
        cases commaResult : symbol .comma .yulStatement input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            simp only [commaResult] at result
            cases nameResult : yulName afterComma with
            | invariant error => simp [nameResult] at result
            | reject failure rejected => simp [nameResult] at result
            | ok name afterName =>
                simp only [nameResult] at result
                have afterNameFree :=
                  yulNamesTail_reflectsDiagnosticFreeOnSuccess first fuel name
                    (name :: tailRev) afterName names next result diagnosticFree
                have nameGrammar :=
                  yulName_success_sound_of_diagnosticFree afterNameFree
                    nameResult
                have tailGrammar := inductionHypothesis name
                  (name :: tailRev) diagnosticFree result
                rcases yulName_ok_state_shape nameResult with
                  ⟨token, found, spanEq, tokensEq, cursorEq⟩
                have progress : afterComma.cursor < afterName.cursor := by
                  rw [cursorEq]
                  exact Nat.lt_succ_self _
                exact .next comma.span
                  (symbol_success_exactTokenParses .comma .yulStatement
                    commaResult)
                  nameGrammar progress tailGrammar
      next commaAbsent =>
        have commaAbsentEq : isSymbol input .comma = false :=
          Bool.eq_false_iff.mpr commaAbsent
        exact .done
          (symbolAbsentAt_of_isSymbol_eq_false .comma commaAbsentEq)
          (finishYulNames_success_sound first last tailRev result)

/-- Every diagnostic-free public name-sequence success is nonempty, has no
trailing comma, preserves forward order, and follows the exact token window. -/
theorem yulNames_success_sound {input next : State}
    {names : YulNameSequence} (diagnosticFree : next.diagnosticsRev = [])
    (result : yulNames input = .ok names next) :
    DeclarativeGrammar.YulNamesParses input.declarativeRemainder names.span
      names.names next.declarativeRemainder := by
  unfold yulNames at result
  cases firstResult : yulName input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have afterFirstFree := yulNamesTail_reflectsDiagnosticFreeOnSuccess first
        (afterFirst.remainingCount + 1) first [] afterFirst names next result
          diagnosticFree
      have firstGrammar := yulName_success_sound_of_diagnosticFree
        afterFirstFree firstResult
      have tailGrammar := yulNamesTail_success_sound first
        (afterFirst.remainingCount + 1) first [] diagnosticFree result
      rcases yulName_ok_state_shape firstResult with
        ⟨token, found, spanEq, tokensEq, cursorEq⟩
      have progress : input.cursor < afterFirst.cursor := by
        rw [cursorEq]
        exact Nat.lt_succ_self _
      exact .parsed firstGrammar progress tailGrammar

end Solcore.Syntax.Parser
