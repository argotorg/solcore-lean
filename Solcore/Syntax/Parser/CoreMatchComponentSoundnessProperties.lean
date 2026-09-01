import Solcore.Syntax.DeclarativeCoreMatchStatementGrammar
import Solcore.Syntax.Parser.CoreMatchComponentDiagnosticReflectionProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-! Exact diagnostic-free soundness for Core-match structural components. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

private theorem bindOkComponents {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (result : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Successful scrutinee refinement fixes its nonempty carrier and state. -/
theorem requireScrutinees_success_sound
    {values : DelimitedList Expr} {input next : State}
    {scrutinees : NonemptyDelimitedList Expr}
    (result : requireScrutinees values input = .ok scrutinees next) :
    DeclarativeGrammar.RequireScrutineesParses values
      input.declarativeRemainder scrutinees next.declarativeRemainder := by
  rcases values with ⟨span, elements⟩
  unfold requireScrutinees at result
  cases elements with
  | nil => simp [rejectAt] at result
  | cons head tail =>
      simp only [pure] at result
      cases result
      exact .parsed

/-- One diagnostic-free case retains its keyword, pattern, body, and span. -/
theorem matchCase_success_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (patternParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value next.declarativeRemainder)
    (patternSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → pattern input = .ok value next →
      patternParses input.declarativeRemainder value next.declarativeRemainder)
    {input next : State} {arm : MatchCase}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : matchCase statement pattern input = .ok arm next) :
    DeclarativeGrammar.MatchCaseParses statementParses patternParses
      input.declarativeRemainder arm next.declarativeRemainder := by
  unfold matchCase at result
  rcases bindOkComponents result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bindOkComponents rest with
    ⟨retainedPattern, afterPattern, patternResult, rest⟩
  rcases bindOkComponents rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterPatternFree := coreBlock_reflectsDiagnosticFreeOnSuccess statement
    .require statementReflects afterPattern body next bodyResult
      diagnosticFree
  exact .parsed marker.span
    (keyword_success_exactTokenParses .caseKw .statement markerResult)
    (patternSound afterPatternFree patternResult)
    (coreBlock_success_sound statementParses statement .require
      statementReflects statementSound diagnosticFree bodyResult)

/-- The maximal case loop returns its new arms in exact forward order. -/
theorem matchCases_success_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (patternParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value next.declarativeRemainder)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern)
    (patternSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → pattern input = .ok value next →
      patternParses input.declarativeRemainder value next.declarativeRemainder) :
    ∀ fuel casesRev input cases next,
      next.diagnosticsRev = [] →
      matchCases statement pattern fuel casesRev input = .ok cases next →
      ∃ suffix,
        cases = casesRev.reverse ++ suffix ∧
        DeclarativeGrammar.MatchCasesParses statementParses patternParses
          input.declarativeRemainder suffix next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input cases next diagnosticFree result
      simp [matchCases] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input cases next diagnosticFree result
      unfold matchCases at result
      split at result
      · cases caseResult : matchCase statement pattern input with
        | invariant error => simp [caseResult] at result
        | reject failure rejected => simp [caseResult] at result
        | ok arm afterCase =>
            simp only [caseResult] at result
            split at result
            · rcases inductionHypothesis (arm :: casesRev) afterCase cases
                  next diagnosticFree result with
                ⟨suffix, casesEq, tailGrammar, afterCaseFree⟩
              have armGrammar := matchCase_success_sound statement pattern
                statementParses patternParses statementReflects statementSound
                  patternSound afterCaseFree caseResult
              have inputFree := matchCase_reflectsDiagnosticFreeOnSuccess
                statement pattern statementReflects patternReflects input arm
                  afterCase caseResult afterCaseFree
              refine ⟨arm :: suffix, ?_, .next armGrammar (by assumption)
                tailGrammar, inputFree⟩
              simpa [List.reverse_cons, List.append_assoc] using casesEq
            · contradiction
      · cases result
        exact ⟨[], by simp, .done
          (keywordAbsentAt_of_isKeyword_eq_false .caseKw
            (Bool.eq_false_iff.mpr (by assumption))), diagnosticFree⟩

/-- Optional default success preserves priority, body grammar, and remainder. -/
theorem optionalDefaultBody_success_sound
    (statement : Parser Statement)
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value next.declarativeRemainder)
    {input next : State} {body : Option Block}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalDefaultBody statement input = .ok body next) :
    DeclarativeGrammar.OptionalDefaultBodyParses statementParses
      input.declarativeRemainder body next.declarativeRemainder := by
  unfold optionalDefaultBody getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    rcases bindOkComponents result with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases bindOkComponents rest with
      ⟨retainedBody, afterBody, bodyResult, finished⟩
    cases finished
    exact .present marker.span
      (keyword_success_exactTokenParses .defaultKw .statement markerResult)
      (coreBlock_success_sound statementParses statement .require
        statementReflects statementSound diagnosticFree bodyResult)
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (keywordAbsentAt_of_isKeyword_eq_false .defaultKw absent)

end Solcore.Syntax.Parser.MatchInternals
