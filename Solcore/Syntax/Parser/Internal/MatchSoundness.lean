import Solcore.Syntax.Parser.Internal.SimpleStatementSoundness
import Solcore.Syntax.Parser.Terms
import Solcore.Syntax.Parser.Internal.PatternProofs
import Solcore.Syntax.Internal.StatementOutcomes
import Solcore.Syntax.Parser.Internal.BlockSoundness
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Grammar.Statements
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.ValidityBasics
import Solcore.Syntax.Validity
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Grammar.StatementLayer

/-!
Soundness of the parsers of `match` statements: each success and each rejection has its
declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForItemDiagnosticReflectionProperties
/-!
Backward propagation of diagnostic freedom through Core `for` header items.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

theorem forLetItem_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess (forLetItem expression) := by
  unfold forLetItem
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .letKw .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .statement)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalLetType_reflectsDiagnosticFreeOnSuccess
  intro type
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalLetInitializer_reflectsDiagnosticFreeOnSuccess expression
      expressionReflects)
  intro initializer
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem forAssignmentOrExpression_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (forAssignmentOrExpression expression) := by
  unfold forAssignmentOrExpression
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess expressionReflects
  intro left
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalAssignmentTail_reflectsDiagnosticFreeOnSuccess expression
      expressionReflects)
  intro tail
  cases tail with
  | none => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  | some tail =>
      cases tail <;> exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

theorem forItem_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess (forItem expression) := by
  intro input item next result diagnosticFree
  unfold forItem at result
  split at result
  · exact
      (StatementSimpleInternals.forLetItem_reflectsDiagnosticFreeOnSuccess
        expression expressionReflects) input item next result diagnosticFree
  · exact
      (StatementSimpleInternals.forAssignmentOrExpression_reflectsDiagnosticFreeOnSuccess
        expression expressionReflects) input item next result diagnosticFree

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchScrutineesOrdinaryOutcomeSoundnessProperties
/-! Executable outcomes for requiring nonempty Core match scrutinees. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Successful executable conversion preserves the exact nonempty elements
and input remainder. -/
theorem requireScrutinees_success_ordinary_sound
    (values : DelimitedList Expr) {input output : State}
    {scrutinees : NonemptyDelimitedList Expr}
    (result : requireScrutinees values input = .ok scrutinees output) :
    DeclarativeGrammar.RequireScrutineesOrdinaryParses values
      input.declarativeRemainder scrutinees output.declarativeRemainder := by
  rcases values with ⟨span, elements⟩
  unfold requireScrutinees at result
  cases elementsEq : elements with
  | nil => simp [elementsEq, rejectAt] at result
  | cons head tail =>
      simp only [elementsEq, pure] at result
      cases result
      exact .parsed

/-- Executable rejection occurs exactly for an empty element list and retains
the complete input state. -/
theorem requireScrutinees_reject_ordinary_sound
    (values : DelimitedList Expr) {input rejected : State} {failure : Failure}
    (result : requireScrutinees values input = .reject failure rejected) :
    DeclarativeGrammar.RequireScrutineesRejects values
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases values with ⟨span, elements⟩
  unfold requireScrutinees at result
  cases elementsEq : elements with
  | nil =>
      simp only [elementsEq] at result
      unfold rejectAt at result
      cases result
      exact .empty rfl
  | cons head tail => simp [elementsEq, pure] at result

/-- Package both executable nonempty-conversion outcomes. -/
theorem requireScrutinees_ordinaryOutcome_sound
    (values : DelimitedList Expr) :
    (∀ {input output : State}
      {scrutinees : NonemptyDelimitedList Expr},
      requireScrutinees values input = .ok scrutinees output →
        DeclarativeGrammar.RequireScrutineesOrdinaryParses values
          input.declarativeRemainder scrutinees
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      requireScrutinees values input = .reject failure rejected →
        DeclarativeGrammar.RequireScrutineesRejects values
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨requireScrutinees_success_ordinary_sound values,
    requireScrutinees_reject_ordinary_sound values⟩

/-- Re-export deterministic nonempty-conversion outcomes. -/
theorem requireScrutinees_ordinaryOutcomeSpec
    (values : DelimitedList Expr) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.RequireScrutineesOrdinaryParses values)
      (DeclarativeGrammar.RequireScrutineesRejects values) :=
  DeclarativeGrammar.requireScrutineesDeterministicOutcomeSpec values

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchComponentDiagnosticReflectionProperties
/-! Diagnostic reflection for Core-match parsing components. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Nonempty scrutinee refinement cannot erase diagnostics. -/
theorem requireScrutinees_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList Expr) :
    Parser.ReflectsDiagnosticFreeOnSuccess (requireScrutinees values) := by
  intro input scrutinees next result diagnosticFree
  unfold requireScrutinees at result
  cases elements : values.elements with
  | nil => simp [elements, rejectAt] at result
  | cons head tail =>
      simp only [elements, pure] at result
      cases result
      exact diagnosticFree

/-- One case reflects through its pattern and required-tail body. -/
theorem matchCase_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern) :
    Parser.ReflectsDiagnosticFreeOnSuccess (matchCase statement pattern) := by
  unfold matchCase
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .caseKw .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess patternReflects
  intro retainedPattern
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (coreBlock_reflectsDiagnosticFreeOnSuccess statement .require
      statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- The maximal case loop reflects through every parsed arm. -/
theorem matchCases_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern) :
    ∀ fuel casesRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (matchCases statement pattern fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input cases next result diagnosticFree
      simp [matchCases] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input cases next result diagnosticFree
      unfold matchCases at result
      split at result
      · cases caseResult : matchCase statement pattern input with
        | invariant error => simp [caseResult] at result
        | reject failure rejected => simp [caseResult] at result
        | ok arm afterCase =>
            simp only [caseResult] at result
            split at result
            · have afterCaseFree := inductionHypothesis (arm :: casesRev)
                afterCase cases next result diagnosticFree
              exact matchCase_reflectsDiagnosticFreeOnSuccess statement pattern
                statementReflects patternReflects input arm afterCase
                  caseResult afterCaseFree
            · contradiction
      · cases result
        exact diagnosticFree

/-- The statement-facing loop chooses its fuel from the current remainder. -/
theorem matchCasesFromCurrentState_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern) :
    Parser.ReflectsDiagnosticFreeOnSuccess (fun state =>
      matchCases statement pattern (state.remainingCount + 1) [] state) := by
  intro input cases next result diagnosticFree
  exact matchCases_reflectsDiagnosticFreeOnSuccess statement pattern
    statementReflects patternReflects (input.remainingCount + 1) [] input cases
      next result diagnosticFree

/-- Optional default parsing reflects through its required-tail block. -/
theorem optionalDefaultBody_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalDefaultBody statement) := by
  unfold optionalDefaultBody
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess .defaultKw .statement)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (coreBlock_reflectsDiagnosticFreeOnSuccess statement .require
        statementReflects)
    intro body
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchComponentSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchCaseOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary success and exact rejection for one Core match case. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Every executable match-case success retains its marker, pattern, raw
required block, span, and exact remainder. -/
theorem matchCase_success_ordinary_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {arm : MatchCase}
    (result : matchCase statement pattern input = .ok arm output) :
    DeclarativeGrammar.MatchCaseOrdinaryParses statementOrdinary
      patternOrdinary input.declarativeRemainder arm
        output.declarativeRemainder := by
  unfold matchCase at result
  cases markerResult : keyword .caseKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases patternResult : pattern afterMarker with
      | invariant error => simp [patternResult] at result
      | reject failure rejected => simp [patternResult] at result
      | ok retainedPattern afterPattern =>
          simp only [patternResult] at result
          cases bodyResult : coreBlock statement .require afterPattern with
          | invariant error => simp [bodyResult] at result
          | reject failure rejected => simp [bodyResult] at result
          | ok body afterBody =>
              simp only [bodyResult, pure] at result
              cases result
              exact .parsed marker.span
                (keyword_success_exactTokenParses .caseKw .statement
                  markerResult)
                (patternSuccessSound patternResult)
                ((coreBlock_ordinaryOutcome_sound statement .require
                  statementOrdinary statementRejects statementSuccessSound
                    statementRejectSound).1 bodyResult)

/-- Every executable match-case rejection records its first failing stage. -/
theorem matchCase_reject_ordinary_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : matchCase statement pattern input = .reject failure rejected) :
    DeclarativeGrammar.MatchCaseRejects statementOrdinary statementRejects
      patternOrdinary patternRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold matchCase at result
  cases markerResult : keyword .caseKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .caseKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .caseKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .caseKw .statement
        markerResult
      cases patternResult : pattern afterMarker with
      | invariant error => simp [patternResult] at result
      | reject patternFailure patternRejected =>
          simp only [patternResult] at result
          cases result
          exact .patternRejected marker.span markerParsed
            (patternRejectSound patternResult)
      | ok retainedPattern afterPattern =>
          simp only [patternResult] at result
          cases bodyResult : coreBlock statement .require afterPattern with
          | invariant error => simp [bodyResult] at result
          | reject bodyFailure bodyRejected =>
              simp only [bodyResult] at result
              cases result
              exact .bodyRejected marker.span markerParsed
                (patternSuccessSound patternResult)
                ((coreBlock_ordinaryOutcome_sound statement .require
                  statementOrdinary statementRejects statementSuccessSound
                    statementRejectSound).2 bodyResult)
          | ok body output => simp [bodyResult, pure] at result

/-- Package both executable match-case outcomes. -/
theorem matchCase_ordinaryOutcome_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {arm : MatchCase},
      matchCase statement pattern input = .ok arm output →
        DeclarativeGrammar.MatchCaseOrdinaryParses statementOrdinary
          patternOrdinary input.declarativeRemainder arm
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      matchCase statement pattern input = .reject failure rejected →
        DeclarativeGrammar.MatchCaseRejects statementOrdinary
          statementRejects patternOrdinary patternRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨matchCase_success_ordinary_sound statement pattern statementOrdinary
      statementRejects patternOrdinary statementSuccessSound
        statementRejectSound patternSuccessSound,
    matchCase_reject_ordinary_sound statement pattern statementOrdinary
      statementRejects patternRejects patternOrdinary statementSuccessSound
        statementRejectSound patternSuccessSound patternRejectSound⟩

/-- Re-export deterministic match-case outcomes. -/
theorem matchCase_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects)
    (patternOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      patternOrdinary patternRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.MatchCaseOrdinaryParses statementOrdinary
        patternOrdinary)
      (DeclarativeGrammar.MatchCaseRejects statementOrdinary statementRejects
        patternOrdinary patternRejects) :=
  DeclarativeGrammar.matchCaseDeterministicOutcomeSpec statementOutcomes
    patternOutcomes

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchCasesOrdinarySuccessSoundnessProperties
/-!
Diagnostic-inclusive success for the fuel-bounded, reverse-accumulating Core
match-case loop.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- An arbitrary successful loop retains the prior reverse accumulator and
describes its newly parsed suffix in forward source order. -/
theorem matchCasesWithFuel_success_ordinary_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder) :
    ∀ fuel casesRev input cases output,
      matchCases statement pattern fuel casesRev input = .ok cases output →
      ∃ suffix,
        cases = casesRev.reverse ++ suffix ∧
        DeclarativeGrammar.MatchCasesOrdinaryParses statementOrdinary
          patternOrdinary input.declarativeRemainder suffix
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input cases output result
      simp [matchCases] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input cases output result
      unfold matchCases at result
      cases casePresent : isKeyword input .caseKw with
      | false =>
          simp only [casePresent, Bool.false_eq_true, if_false] at result
          cases result
          exact ⟨[], by simp, .done
            (keywordAbsentAt_of_isKeyword_eq_false .caseKw casePresent)⟩
      | true =>
          simp only [casePresent, if_true] at result
          cases armResult : matchCase statement pattern input with
          | invariant error => simp [armResult] at result
          | reject failure rejected => simp [armResult] at result
          | ok arm afterArm =>
              simp only [armResult] at result
              by_cases progress : afterArm.cursor > input.cursor
              · simp only [progress, if_true] at result
                rcases inductionHypothesis (arm :: casesRev) afterArm cases
                    output result with ⟨suffix, casesEq, tailParsed⟩
                refine ⟨arm :: suffix, ?_, .next
                  (matchCase_success_ordinary_sound statement pattern
                    statementOrdinary statementRejects patternOrdinary
                      statementSuccessSound statementRejectSound
                        patternSuccessSound armResult)
                  (by simpa [State.declarativeRemainder] using progress)
                  tailParsed⟩
                simpa [List.reverse_cons, List.append_assoc] using casesEq
              · simp only [progress, if_false] at result
                contradiction

/-- The production fuel and empty accumulator expose the exact forward list. -/
theorem matchCases_success_ordinary_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {cases : List MatchCase}
    (result : matchCases statement pattern (input.remainingCount + 1) [] input
      = .ok cases output) :
    DeclarativeGrammar.MatchCasesOrdinaryParses statementOrdinary
      patternOrdinary input.declarativeRemainder cases
        output.declarativeRemainder := by
  rcases matchCasesWithFuel_success_ordinary_sound statement pattern
      statementOrdinary statementRejects patternOrdinary
      statementSuccessSound statementRejectSound patternSuccessSound
      (input.remainingCount + 1) [] input cases output result with
    ⟨suffix, casesEq, parsed⟩
  simp only [List.reverse_nil, List.nil_append] at casesEq
  subst cases
  exact parsed

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchCasesOrdinaryRejectionSoundnessProperties
/-! Exact rejection for the guarded Core match-case loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

private theorem keyword_eq_ok_of_isKeyword_eq_true (value : HardKeyword)
    (context : ParseContext) {input : State}
    (present : isKeyword input value = true) :
    ∃ token, keyword value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isKeyword State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .keyword value) = true at present
      refine ⟨token, ?_⟩
      unfold keyword acceptToken
      simp only [found, present, if_true]

private theorem keywordPresentAt_of_isKeyword_eq_true (value : HardKeyword)
    {input : State} (present : isKeyword input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword value } := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .statement present with
    ⟨token, result⟩
  have parsed := keyword_success_exactTokenParses value .statement result
  exact ⟨token.span, parsed.1⟩

/-- Every arbitrary-fuel rejection records the first rejected arm after the
exact ordinary prefix; the prior reverse accumulator does not affect it. -/
theorem matchCasesWithFuel_reject_ordinary_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    ∀ fuel casesRev input failure rejected,
      matchCases statement pattern fuel casesRev input =
        .reject failure rejected →
      DeclarativeGrammar.MatchCasesRejects statementOrdinary statementRejects
        patternOrdinary patternRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input failure rejected result
      simp [matchCases] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input failure rejected result
      unfold matchCases at result
      cases casePresent : isKeyword input .caseKw with
      | false => simp [casePresent] at result
      | true =>
          simp only [casePresent, if_true] at result
          cases armResult : matchCase statement pattern input with
          | invariant error => simp [armResult] at result
          | reject armFailure armRejected =>
              simp only [armResult] at result
              cases result
              exact .firstRejected
                (keywordPresentAt_of_isKeyword_eq_true .caseKw casePresent)
                (matchCase_reject_ordinary_sound statement pattern
                  statementOrdinary statementRejects patternRejects
                    patternOrdinary statementSuccessSound
                      statementRejectSound patternSuccessSound
                        patternRejectSound armResult)
          | ok arm afterArm =>
              simp only [armResult] at result
              by_cases progress : afterArm.cursor > input.cursor
              · simp only [progress, if_true] at result
                exact .laterRejected
                  (matchCase_success_ordinary_sound statement pattern
                    statementOrdinary statementRejects patternOrdinary
                      statementSuccessSound statementRejectSound
                        patternSuccessSound armResult)
                  (by simpa [State.declarativeRemainder] using progress)
                  (inductionHypothesis (arm :: casesRev) afterArm failure
                    rejected result)
              · simp only [progress, if_false] at result
                contradiction

/-- Production-sized loop rejection has the exact guarded relation. -/
theorem matchCases_reject_ordinary_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : matchCases statement pattern (input.remainingCount + 1) [] input
      = .reject failure rejected) :
    DeclarativeGrammar.MatchCasesRejects statementOrdinary statementRejects
      patternOrdinary patternRejects input.declarativeRemainder
        rejected.declarativeRemainder :=
  matchCasesWithFuel_reject_ordinary_sound statement pattern
    statementOrdinary statementRejects patternOrdinary patternRejects
    statementSuccessSound statementRejectSound patternSuccessSound
    patternRejectSound (input.remainingCount + 1) [] input failure rejected
    result

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchCasesOrdinaryOutcomeSoundnessProperties
/-! Packaged production outcomes for the Core match-case loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Package success and rejection for the exact production fuel selection. -/
theorem matchCases_ordinaryOutcome_sound
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {cases : List MatchCase},
      matchCases statement pattern (input.remainingCount + 1) [] input =
          .ok cases output →
        DeclarativeGrammar.MatchCasesOrdinaryParses statementOrdinary
          patternOrdinary input.declarativeRemainder cases
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      matchCases statement pattern (input.remainingCount + 1) [] input =
          .reject failure rejected →
        DeclarativeGrammar.MatchCasesRejects statementOrdinary
          statementRejects patternOrdinary patternRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨matchCases_success_ordinary_sound statement pattern statementOrdinary
      statementRejects patternOrdinary statementSuccessSound
        statementRejectSound patternSuccessSound,
    matchCases_reject_ordinary_sound statement pattern statementOrdinary
      statementRejects patternOrdinary patternRejects statementSuccessSound
        statementRejectSound patternSuccessSound patternRejectSound⟩

/-- Re-export deterministic match-case sequence outcomes. -/
theorem matchCases_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects)
    (patternOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      patternOrdinary patternRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.MatchCasesOrdinaryParses statementOrdinary
        patternOrdinary)
      (DeclarativeGrammar.MatchCasesRejects statementOrdinary
        statementRejects patternOrdinary patternRejects) :=
  DeclarativeGrammar.matchCasesDeterministicOutcomeSpec statementOutcomes
    patternOutcomes

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchValidationSoundnessProperties
/-! Diagnostic reflection and clean soundness of Core-match arity validation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

@[simp] theorem patternArity_eq_declarative (scrutineeCount : Nat)
    (pattern : Pattern) :
    patternArity scrutineeCount pattern =
      DeclarativeGrammar.matchPatternArity scrutineeCount pattern := by
  unfold patternArity DeclarativeGrammar.matchPatternArity
  rfl

/-- One arity check never removes diagnostics. -/
theorem validateMatchCaseArity_reflectsDiagnosticFreeOnSuccess
    (scrutineeCount : Nat) (arm : MatchCase) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (validateMatchCaseArity scrutineeCount arm) := by
  intro input checked next result diagnosticFree
  unfold validateMatchCaseArity at result
  split at result
  · cases result
    exact diagnosticFree
  · exact emitDiagnostic_reflectsDiagnosticFreeOnSuccess _ input checked
      next result diagnosticFree

/-- The full arity pass reflects through every case. -/
theorem validateMatchArities_reflectsDiagnosticFreeOnSuccess
    (scrutineeCount : Nat) : ∀ cases,
    Parser.ReflectsDiagnosticFreeOnSuccess
      (validateMatchArities scrutineeCount cases)
  | [] => Parser.pure_reflectsDiagnosticFreeOnSuccess ()
  | arm :: rest => by
      unfold validateMatchArities
      apply Parser.bind_reflectsDiagnosticFreeOnSuccess
        (validateMatchCaseArity_reflectsDiagnosticFreeOnSuccess
          scrutineeCount arm)
      intro checked
      exact validateMatchArities_reflectsDiagnosticFreeOnSuccess
        scrutineeCount rest

/-- A diagnostic-free single check proves exact arity equality. -/
theorem validateMatchCaseArity_success_sound
    (scrutineeCount : Nat) (arm : MatchCase) {input next : State}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : validateMatchCaseArity scrutineeCount arm input = .ok () next) :
    DeclarativeGrammar.matchPatternArity scrutineeCount arm.value.pattern =
        scrutineeCount ∧
      input.diagnosticsRev = [] ∧ next = input := by
  unfold validateMatchCaseArity at result
  split at result
  · cases result
    refine ⟨?_, diagnosticFree, rfl⟩
    rw [← patternArity_eq_declarative]
    exact beq_iff_eq.mp (by assumption)
  · unfold emitDiagnostic modifyState at result
    cases result
    simp [State.emit] at diagnosticFree

/-- Diagnostic-free validation proves every case has the scrutinee arity. -/
theorem validateMatchArities_success_sound (scrutineeCount : Nat) :
    ∀ cases input next,
      next.diagnosticsRev = [] →
      validateMatchArities scrutineeCount cases input = .ok () next →
      DeclarativeGrammar.MatchCaseAritiesValid scrutineeCount cases ∧
        input.diagnosticsRev = [] ∧ next = input := by
  intro cases
  induction cases with
  | nil =>
      intro input next diagnosticFree result
      simp only [validateMatchArities, pure] at result
      cases result
      exact ⟨by simp [DeclarativeGrammar.MatchCaseAritiesValid],
        diagnosticFree, rfl⟩
  | cons arm rest inductionHypothesis =>
      intro input next diagnosticFree result
      unfold validateMatchArities at result
      rcases bindOkComponents result with
        ⟨checked, afterCheck, checkResult, restResult⟩
      rcases inductionHypothesis afterCheck next diagnosticFree restResult with
        ⟨restValid, afterCheckFree, nextEq⟩
      rcases validateMatchCaseArity_success_sound scrutineeCount arm
          afterCheckFree checkResult with
        ⟨armValid, inputFree, afterCheckEq⟩
      refine ⟨?_, inputFree, nextEq.trans afterCheckEq⟩
      intro retained member
      rcases List.mem_cons.mp member with rfl | member
      · exact armValid
      · exact restValid retained member

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchStatementDiagnosticReflectionProperties
/-! Diagnostic reflection for complete canonical Core `match` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A complete Core `match` success cannot erase an earlier diagnostic. -/
theorem matchStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (matchStatement statement expression pattern) := by
  unfold matchStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .matchKw .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen false
      expression .expression .statement expressionReflects)
  intro values
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (MatchInternals.requireScrutinees_reflectsDiagnosticFreeOnSuccess values)
  intro scrutinees
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .statement)
  intro opening
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (MatchInternals.matchCasesFromCurrentState_reflectsDiagnosticFreeOnSuccess
      statement pattern statementReflects patternReflects)
  intro cases
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (MatchInternals.optionalDefaultBody_reflectsDiagnosticFreeOnSuccess
      statement statementReflects)
  intro defaultBody
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightBrace .statement)
  intro closing
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (MatchInternals.validateMatchArities_reflectsDiagnosticFreeOnSuccess
      scrutinees.elements.toList.length cases)
  intro checked
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
    intro emitted
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchStatementSoundnessProperties
/-! Exact diagnostic-free soundness for complete Core `match` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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

/-- Every clean Core `match` success follows the exact independent grammar. -/
theorem matchStatement_success_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (patternParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionShape : Parser.PreservesTokenWindow expression)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern)
    (patternSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → pattern input = .ok value next →
      patternParses input.declarativeRemainder value next.declarativeRemainder)
    {input next : State} {value : Statement}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : matchStatement statement expression pattern input =
      .ok value next) :
    DeclarativeGrammar.MatchStatementParses statementParses expressionParses
      patternParses input.declarativeRemainder value
        next.declarativeRemainder := by
  unfold matchStatement at result
  rcases bindOkComponents result with
    ⟨marker, afterMarker, markerResult, valuesStage⟩
  rcases bindOkComponents valuesStage with
    ⟨values, afterValues, valuesResult, scrutineesStage⟩
  rcases bindOkComponents scrutineesStage with
    ⟨scrutinees, afterScrutinees, scrutineesResult, openingStage⟩
  rcases bindOkComponents openingStage with
    ⟨opening, afterOpening, openingResult, casesStage⟩
  rcases bindOkComponents casesStage with
    ⟨cases, afterCases, casesResult, defaultStage⟩
  rcases bindOkComponents defaultStage with
    ⟨defaultBody, afterDefault, defaultResult, closingStage⟩
  rcases bindOkComponents closingStage with
    ⟨closing, afterClosing, closingResult, validationStage⟩
  rcases bindOkComponents validationStage with
    ⟨checked, afterValidation, validationResult, finished⟩
  by_cases missing : (cases.isEmpty && defaultBody.isNone) = true
  · simp only [missing, if_true] at finished
    rcases bindOkComponents finished with
      ⟨emitted, afterDiagnostic, emittedResult, finalResult⟩
    simp only [pure] at finalResult
    cases finalResult
    unfold emitDiagnostic modifyState at emittedResult
    cases emittedResult
    simp [State.emit] at diagnosticFree
  · have missingFalse : (cases.isEmpty && defaultBody.isNone) = false :=
      Bool.eq_false_iff.mpr missing
    have armsPresent : DeclarativeGrammar.MatchArmsPresent cases defaultBody :=
      missingFalse
    simp only [missingFalse, Bool.false_eq_true, if_false, pure] at finished
    cases finished
    rcases MatchInternals.validateMatchArities_success_sound
        scrutinees.elements.toList.length cases afterClosing next
          diagnosticFree validationResult with
      ⟨aritiesValid, afterClosingFree, nextEq⟩
    subst next
    have afterDefaultFree := symbol_reflectsDiagnosticFreeOnSuccess
      .rightBrace .statement afterDefault closing afterClosing closingResult
        afterClosingFree
    have afterCasesFree :=
      MatchInternals.optionalDefaultBody_reflectsDiagnosticFreeOnSuccess
        statement statementReflects afterCases defaultBody afterDefault
          defaultResult afterDefaultFree
    rcases MatchInternals.matchCases_success_sound statement pattern
        statementParses patternParses statementReflects statementSound
          patternReflects patternSound (afterOpening.remainingCount + 1) []
            afterOpening cases afterCases afterCasesFree casesResult with
      ⟨suffix, casesEq, casesGrammar, afterOpeningFree⟩
    have casesEqSuffix : cases = suffix := by simpa using casesEq
    subst suffix
    have afterScrutineesFree := symbol_reflectsDiagnosticFreeOnSuccess
      .leftBrace .statement afterScrutinees opening afterOpening openingResult
        afterOpeningFree
    have afterValuesFree :=
      MatchInternals.requireScrutinees_reflectsDiagnosticFreeOnSuccess values
        afterValues scrutinees afterScrutinees scrutineesResult
          afterScrutineesFree
    exact .parsed marker.span opening.span closing.span
      (keyword_success_exactTokenParses .matchKw .statement markerResult)
      (delimited_nonempty_trailing_success_sound_of_diagnosticFree
        .leftParen .rightParen expression expressionParses .expression
          .statement expressionSound expressionReflects expressionShape
            afterValuesFree valuesResult)
      (MatchInternals.requireScrutinees_success_sound scrutineesResult)
      (symbol_success_exactTokenParses .leftBrace .statement openingResult)
      casesGrammar
      (MatchInternals.optionalDefaultBody_success_sound statement
        statementParses statementReflects statementSound afterDefaultFree
          defaultResult)
      (symbol_success_exactTokenParses .rightBrace .statement closingResult)
      aritiesValid armsPresent

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Statement.MatchProperties
/-! Contracts for canonical Core match-statement components. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem matchBind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
      next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

namespace MatchInternals

/-- One `case` retains its pattern, recursive body, and outer source range. -/
theorem matchCase_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement)
    (patternValid : patternParser.ValidFor patternValueValid)
    (patternTokens : Parser.PreservesTokensOnSuccess patternParser)
    (patternCursor : Parser.CursorMonotoneOnSuccess patternParser) :
    (matchCase statement patternParser).ValidFor
      (MatchCase.ValidFor expressionValueValid patternValueValid
        yulValueValid) := by
  have bodyValid := coreBlock_validFor
    (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
    statement .require statementValid statementTokens
    (fun _ _ valid => valid.span_valid)
  have weak : (matchCase statement patternParser).ValidFor
      (fun _ _ => True) := by
    unfold matchCase
    apply Parser.bind_validFor (keyword_validFor .caseKw .statement)
    intro marker
    apply Parser.bind_validFor patternValid
    intro retainedPattern
    apply Parser.bind_validFor bodyValid
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakReply := weak input inputValid
  cases parsed : matchCase statement patternParser input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakReply
      exact weakReply
  | ok retainedCase final =>
      rw [parsed] at weakReply
      have stages := parsed
      unfold matchCase at stages
      rcases matchBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases matchBind_ok_components rest with
        ⟨retainedPattern, afterPattern, patternResult, rest⟩
      rcases matchBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerReply := keyword_validFor .caseKw .statement input inputValid
      rw [markerResult] at markerReply
      have patternReply := patternValid afterMarker markerReply.2.1
      rw [patternResult] at patternReply
      have bodyReply := bodyValid afterPattern patternReply.2.1
      rw [bodyResult] at bodyReply
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerReply.1
      have retainedPatternValid : patternValueValid input.file
          retainedPattern := by
        simpa [patternReply.2.2, markerReply.2.2] using patternReply.1
      have retainedBodyValid : Block.ValidFor
          (Statement.ValidFor expressionValueValid patternValueValid
            yulValueValid) input.file body := by
        simpa [bodyReply.2.2, patternReply.2.2,
          markerReply.2.2] using bodyReply.1
      rcases coreBlock_startsAtCurrentTokenOnSuccess statement .require
          afterPattern body afterBody bodyResult with
        ⟨bodyOpening, bodyOpeningFound, bodyStart⟩
      have markerAt := State.getElem?_eq_some_of_peek?_eq_some
        (acceptToken_ok_state_shape (.keyword .caseKw) .statement
          (fun kind => kind == .keyword .caseKw) markerResult).1
      have bodyOpeningAtAfter :=
        State.getElem?_eq_some_of_peek?_eq_some bodyOpeningFound
      have bodyOpeningAt : input.tokens[afterPattern.cursor]? =
          some bodyOpening := by
        simpa [keyword_preservesTokensOnSuccess .caseKw .statement input
          marker afterMarker markerResult,
          patternTokens afterMarker retainedPattern afterPattern patternResult]
            using bodyOpeningAtAfter
      have cursorOrder : input.cursor < afterPattern.cursor :=
        Nat.lt_of_lt_of_le
          (acceptToken_cursor_lt_onSuccess (.keyword .caseKw) .statement
            (fun kind => kind == .keyword .caseKw) markerResult)
          (patternCursor afterMarker retainedPattern afterPattern
            patternResult)
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        markerAt bodyOpeningAt cursorOrder
      have outerValid := SourceSpan.cover_validFor markerSpanValid
        retainedBodyValid.1 (by
          calc
            marker.span.startByte ≤ marker.span.endByte :=
              markerSpanValid.2.1
            _ ≤ bodyOpening.span.startByte := separated
            _ = body.span.startByte := bodyStart
            _ ≤ body.span.endByte := retainedBodyValid.1.2.1)
      cases finished
      exact ⟨MatchCase.ValidFor.arm outerValid retainedPatternValid
        retainedBodyValid.1 retainedBodyValid.2, weakReply.2.1,
        weakReply.2.2⟩

/-- One `case` preserves every ordinary token window. -/
theorem matchCase_preservesTokenWindow
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (patternWindow : Parser.PreservesTokenWindow patternParser) :
    Parser.PreservesTokenWindow (matchCase statement patternParser) := by
  unfold matchCase
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .caseKw .statement)
  intro marker
  apply Parser.bind_preservesTokenWindow patternWindow
  intro retainedPattern
  apply Parser.bind_preservesTokenWindow
    (coreBlock_preservesTokenWindow statement .require statementWindow)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- Successful `case` parsing preserves the immutable token carrier. -/
theorem matchCase_preservesTokensOnSuccess
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (patternWindow : Parser.PreservesTokenWindow patternParser) :
    Parser.PreservesTokensOnSuccess (matchCase statement patternParser) :=
  (matchCase_preservesTokenWindow statement patternParser statementWindow
    patternWindow).preservesTokensOnSuccess

/-- Successful `case` parsing never rewinds the token cursor. -/
theorem matchCase_cursorMonotoneOnSuccess
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (patternCursor : Parser.CursorMonotoneOnSuccess patternParser) :
    Parser.CursorMonotoneOnSuccess (matchCase statement patternParser) := by
  unfold matchCase
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .caseKw .statement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess patternCursor
  intro retainedPattern
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- One `case` starts at its `case` keyword token. -/
theorem matchCase_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) (patternParser : Parser Pattern) :
    Parser.StartsAtCurrentTokenOnSuccess
      (matchCase statement patternParser) (·.span) := by
  intro input retainedCase final parsed
  have stages := parsed
  unfold matchCase at stages
  rcases matchBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨retainedPattern, afterPattern, patternResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  rcases acceptToken_startsAtCurrentTokenOnSuccess (.keyword .caseKw)
      .statement (fun kind => kind == .keyword .caseKw) input marker
      afterMarker markerResult with ⟨token, found, starts⟩
  cases finished
  exact ⟨token, found, starts⟩

/-- The fuel loop retains every parsed and previously accumulated case. -/
theorem matchCases_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (caseValid : (matchCase statement patternParser).ValidFor
      (MatchCase.ValidFor expressionValueValid patternValueValid
        yulValueValid)) :
    ∀ fuel casesRev input,
      input.ValidFor →
      List.ValidFor
        (MatchCase.ValidFor expressionValueValid patternValueValid
          yulValueValid) input.file casesRev →
      (matchCases statement patternParser fuel casesRev input).ValidFor input
        (List.ValidFor (MatchCase.ValidFor expressionValueValid
          patternValueValid yulValueValid)) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro casesRev input inputValid accumulatedValid
      unfold matchCases
      split
      · cases caseResult : matchCase statement patternParser input with
        | invariant error => trivial
        | reject failure rejected =>
            have reply := caseValid input inputValid
            rw [caseResult] at reply
            exact reply
        | ok retainedCase next =>
            have reply := caseValid input inputValid
            rw [caseResult] at reply
            simp only
            split
            · have nextAccumulated : List.ValidFor
                  (MatchCase.ValidFor expressionValueValid patternValueValid
                    yulValueValid) next.file (retainedCase :: casesRev) := by
                intro item member
                rcases List.mem_cons.mp member with rfl | member
                · simpa [reply.2.2] using reply.1
                · have prior := accumulatedValid item member
                  simpa [reply.2.2] using prior
              exact (inductionHypothesis (retainedCase :: casesRev) next
                reply.2.1 nextAccumulated).of_file_eq reply.2.2
            · trivial
      · exact ⟨by
          intro item member
          exact accumulatedValid item (by simpa using member), inputValid,
            rfl⟩

/-- The case loop preserves every ordinary token window. -/
theorem matchCases_preservesTokenWindow
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (caseWindow : Parser.PreservesTokenWindow
      (matchCase statement patternParser)) :
    ∀ fuel casesRev,
      Parser.PreservesTokenWindow
        (matchCases statement patternParser fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero => intro casesRev input; trivial
  | succ fuel inductionHypothesis =>
      intro casesRev input
      unfold matchCases
      split
      · have replyShape := caseWindow input
        cases caseResult : matchCase statement patternParser input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [caseResult] at replyShape
            exact replyShape
        | ok retainedCase next =>
            rw [caseResult] at replyShape
            simp only
            split
            · exact (inductionHypothesis (retainedCase :: casesRev)
                next).trans replyShape
            · trivial
      · exact ⟨rfl, rfl⟩

/-- Successful case-loop parsing preserves the immutable token carrier. -/
theorem matchCases_preservesTokensOnSuccess
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (caseWindow : Parser.PreservesTokenWindow
      (matchCase statement patternParser)) (fuel : Nat)
    (casesRev : List MatchCase) :
    Parser.PreservesTokensOnSuccess
      (matchCases statement patternParser fuel casesRev) :=
  (matchCases_preservesTokenWindow statement patternParser caseWindow fuel
    casesRev).preservesTokensOnSuccess

/-- The case loop either stays put or advances through complete cases. -/
theorem matchCases_cursorMonotoneOnSuccess
    (statement : Parser Statement) (patternParser : Parser Pattern) :
    ∀ fuel casesRev,
      Parser.CursorMonotoneOnSuccess
        (matchCases statement patternParser fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input value final parsed
      contradiction
  | succ fuel inductionHypothesis =>
      intro casesRev input value final parsed
      unfold matchCases at parsed
      split at parsed
      · cases caseResult : matchCase statement patternParser input with
        | invariant error => simp [caseResult] at parsed
        | reject failure rejected => simp [caseResult] at parsed
        | ok retainedCase next =>
            simp only [caseResult] at parsed
            split at parsed
            · exact Nat.le_trans (Nat.le_of_lt (by assumption))
                (inductionHypothesis (retainedCase :: casesRev) next value
                  final parsed)
            · contradiction
      · cases parsed
        exact Nat.le_refl _

/-- An optional `default` body retains its complete recursive block validity. -/
theorem optionalDefaultBody_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement) :
    (optionalDefaultBody statement).ValidFor
      (Option.ValidFor (Block.ValidFor
        (Statement.ValidFor expressionValueValid patternValueValid
          yulValueValid))) := by
  have bodyValid := coreBlock_validFor
    (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
    statement .require statementValid statementTokens
    (fun _ _ valid => valid.span_valid)
  unfold optionalDefaultBody
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_validFor (keyword_validFor .defaultKw .statement)
    intro marker
    apply Parser.bind_validFor_of_value bodyValid
    intro body next nextValid retainedValid
    exact ⟨by simpa only [Option.ValidFor] using retainedValid,
      nextValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional `default` parsing preserves every ordinary token window. -/
theorem optionalDefaultBody_preservesTokenWindow
    (statement : Parser Statement)
    (statementWindow : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (optionalDefaultBody statement) := by
  unfold optionalDefaultBody
  have getWindow : Parser.PreservesTokenWindow getState := by
    intro input
    exact ⟨rfl, rfl⟩
  apply Parser.bind_preservesTokenWindow getWindow
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow .defaultKw .statement)
    intro marker
    apply Parser.bind_preservesTokenWindow
      (coreBlock_preservesTokenWindow statement .require statementWindow)
    intro body
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

/-- Present or absent `default` bodies preserve the token carrier. -/
theorem optionalDefaultBody_preservesTokensOnSuccess
    (statement : Parser Statement)
    (statementWindow : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokensOnSuccess (optionalDefaultBody statement) :=
  (optionalDefaultBody_preservesTokenWindow statement
    statementWindow).preservesTokensOnSuccess

/-- Optional `default` parsing never rewinds the token cursor. -/
theorem optionalDefaultBody_cursorMonotoneOnSuccess
    (statement : Parser Statement) :
    Parser.CursorMonotoneOnSuccess (optionalDefaultBody statement) := by
  unfold optionalDefaultBody
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (keyword_cursorMonotoneOnSuccess .defaultKw .statement)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      (coreBlock_cursorMonotoneOnSuccess statement .require)
    intro body
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A present `default` body starts at the brace following its keyword. -/
theorem optionalDefaultBody_some_startsAfterKeyword
    (statement : Parser Statement) {input final : State} {body : Block}
    (parsed : optionalDefaultBody statement input = .ok (some body) final) :
    ∃ marker afterMarker opening,
      keyword .defaultKw .statement input = .ok marker afterMarker ∧
      afterMarker.peek? = some opening ∧
      opening.span.startByte = body.span.startByte := by
  unfold optionalDefaultBody getState at parsed
  simp only [bind] at parsed
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at parsed
    rcases matchBind_ok_components parsed with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases matchBind_ok_components rest with
      ⟨parsedBody, afterBody, bodyResult, finished⟩
    have bodyEq : parsedBody = body := by
      cases finished
      rfl
    subst parsedBody
    rcases coreBlock_startsAtCurrentTokenOnSuccess statement .require
        afterMarker body afterBody bodyResult with
      ⟨opening, found, starts⟩
    exact ⟨marker, afterMarker, opening, markerResult, found, starts⟩
  · simp only [present] at parsed
    change Reply.ok none input = .ok (some body) final at parsed
    cases parsed

/-- Requiring scrutinees converts a valid nonempty delimited list exactly. -/
theorem requireScrutinees_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (values : DelimitedList Expr) (input : State)
    (inputValid : input.ValidFor)
    (valuesValid : DelimitedList.ValidFor expressionValueValid
      input.file values) :
    (requireScrutinees values input).ValidFor input
      (NonemptyDelimitedList.ValidFor expressionValueValid) := by
  unfold requireScrutinees
  cases elements : values.elements with
  | nil =>
      unfold rejectAt Reply.ValidFor
      exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
  | cons head tail =>
      simp only [pure, Reply.ValidFor, NonemptyDelimitedList.ValidFor]
      refine ⟨⟨valuesValid.1, ?_⟩, inputValid, trivial⟩
      intro expression member
      exact valuesValid.2 expression (by
        simpa [NonemptyList.toList, elements] using member)

/-- Requiring a nonempty scrutinee list does not alter the token window. -/
theorem requireScrutinees_preservesTokenWindow
    (values : DelimitedList Expr) :
    Parser.PreservesTokenWindow (requireScrutinees values) := by
  intro input
  unfold requireScrutinees
  cases values.elements with
  | nil => exact rejectAt_preservesTokenWindow input _ _
  | cons head tail => exact ⟨rfl, rfl⟩

/-- Requiring a nonempty scrutinee list never rewinds the cursor. -/
theorem requireScrutinees_cursorMonotoneOnSuccess
    (values : DelimitedList Expr) :
    Parser.CursorMonotoneOnSuccess (requireScrutinees values) := by
  intro input scrutinees final parsed
  unfold requireScrutinees at parsed
  cases elements : values.elements with
  | nil =>
      rw [elements] at parsed
      contradiction
  | cons head tail =>
      rw [elements] at parsed
      cases parsed
      exact Nat.le_refl _

/-- One arity check preserves the complete token window. -/
theorem validateMatchCaseArity_preservesTokenWindow
    (scrutineeCount : Nat) (retainedCase : MatchCase) :
    Parser.PreservesTokenWindow
      (validateMatchCaseArity scrutineeCount retainedCase) := by
  unfold validateMatchCaseArity
  simp only
  split
  · exact Parser.pure_preservesTokenWindow ()
  · exact emitDiagnostic_preservesTokenWindow _

/-- One arity check leaves the cursor in place. -/
theorem validateMatchCaseArity_cursorMonotoneOnSuccess
    (scrutineeCount : Nat) (retainedCase : MatchCase) :
    Parser.CursorMonotoneOnSuccess
      (validateMatchCaseArity scrutineeCount retainedCase) := by
  unfold validateMatchCaseArity
  simp only
  split
  · exact Parser.pure_cursorMonotoneOnSuccess ()
  · exact emitDiagnostic_cursorMonotoneOnSuccess _

/-- Checking every retained case preserves the complete token window. -/
theorem validateMatchArities_preservesTokenWindow
    (scrutineeCount : Nat) : ∀ cases,
    Parser.PreservesTokenWindow
      (validateMatchArities scrutineeCount cases)
  | [] => Parser.pure_preservesTokenWindow ()
  | retainedCase :: rest => by
      unfold validateMatchArities
      apply Parser.bind_preservesTokenWindow
        (validateMatchCaseArity_preservesTokenWindow scrutineeCount
          retainedCase)
      intro _
      exact validateMatchArities_preservesTokenWindow scrutineeCount rest

/-- Checking every retained case leaves the cursor in place. -/
theorem validateMatchArities_cursorMonotoneOnSuccess
    (scrutineeCount : Nat) : ∀ cases,
    Parser.CursorMonotoneOnSuccess
      (validateMatchArities scrutineeCount cases)
  | [] => Parser.pure_cursorMonotoneOnSuccess ()
  | retainedCase :: rest => by
      unfold validateMatchArities
      apply Parser.bind_cursorMonotoneOnSuccess
        (validateMatchCaseArity_cursorMonotoneOnSuccess scrutineeCount
          retainedCase)
      intro _
      exact validateMatchArities_cursorMonotoneOnSuccess scrutineeCount rest

/-- Arity validation preserves validity when every case range is valid. -/
theorem validateMatchArities_validFor (scrutineeCount : Nat) :
    ∀ cases input, input.ValidFor →
      List.ValidFor (fun file retainedCase => retainedCase.span.ValidFor file)
        input.file cases →
      (validateMatchArities scrutineeCount cases input).ValidFor input (fun _ _ => True)
  | [], input, inputValid, _ => ⟨trivial, inputValid, rfl⟩
  | retainedCase :: rest, input, inputValid, spansValid => by
      unfold validateMatchArities validateMatchCaseArity
      simp only
      split
      · exact validateMatchArities_validFor scrutineeCount rest input inputValid
          (fun item member => spansValid item (by simp [member]))
      · exact (validateMatchArities_validFor scrutineeCount rest (input.emit _)
          (inputValid.emit_validFor _ (spansValid retainedCase (by simp)))
          (fun item member => spansValid item (by simp [member]))).of_file_eq rfl

end MatchInternals

/-- Complete `match` parsing retains only source-valid syntax and diagnostics. -/
theorem matchStatement_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (expression : Parser Expr) (pattern : Parser Pattern)
    (statementValid : statement.ValidFor (Statement.ValidFor expressionValueValid
      patternValueValid yulValueValid))
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionTokens : Parser.PreservesTokensOnSuccess expression)
    (patternValid : pattern.ValidFor patternValueValid)
    (patternWindow : Parser.PreservesTokenWindow pattern)
    (patternCursor : Parser.CursorMonotoneOnSuccess pattern) :
    (matchStatement statement expression pattern).ValidFor (Statement.ValidFor
      expressionValueValid patternValueValid yulValueValid) := by
  have statementTokens := statementWindow.preservesTokensOnSuccess
  have patternTokens := patternWindow.preservesTokensOnSuccess
  have caseValid := MatchInternals.matchCase_validFor expressionValueValid
    patternValueValid yulValueValid statement pattern statementValid statementTokens
    patternValid patternTokens patternCursor
  have caseWindow := MatchInternals.matchCase_preservesTokenWindow statement pattern
    statementWindow patternWindow
  have valuesValid := delimited_validFor expressionValueValid .leftParen .rightParen
    false expression .expression .statement expressionValid expressionTokens
  have defaultValid := MatchInternals.optionalDefaultBody_validFor expressionValueValid
    patternValueValid yulValueValid statement statementValid statementTokens
  intro input inputValid
  unfold matchStatement
  cases markerResult : keyword .matchKw .statement input with
  | invariant error => simp only [bind, markerResult, Reply.ValidFor]
  | reject failure rejected =>
      have reply := keyword_validFor .matchKw .statement input inputValid
      rw [markerResult] at reply
      simpa only [bind, markerResult, Reply.ValidFor] using reply
  | ok marker afterMarker =>
      have markerReply := keyword_validFor .matchKw .statement input inputValid
      rw [markerResult] at markerReply
      have markerFile : afterMarker.file = input.file := markerReply.2.2
      simp only [bind, markerResult]
      cases valuesResult : delimited .leftParen .rightParen false expression .expression
          .statement afterMarker with
      | invariant error => trivial
      | reject failure rejected =>
          have reply := valuesValid afterMarker markerReply.2.1
          rw [valuesResult] at reply
          simpa only [Reply.ValidFor] using reply.of_file_eq markerReply.2.2
      | ok values afterValues =>
          have valuesReply := valuesValid afterMarker markerReply.2.1
          rw [valuesResult] at valuesReply
          simp only
          have valuesFile : afterValues.file = input.file := valuesReply.2.2.trans markerFile
          have requiredReply := MatchInternals.requireScrutinees_validFor expressionValueValid
            values afterValues valuesReply.2.1 (by simpa [valuesReply.2.2] using valuesReply.1)
          cases requiredResult : MatchInternals.requireScrutinees values afterValues with
          | invariant error => trivial
          | reject failure rejected =>
              rw [requiredResult] at requiredReply
              simpa only [Reply.ValidFor] using requiredReply.of_file_eq valuesFile
          | ok scrutinees afterScrutinees =>
              rw [requiredResult] at requiredReply
              simp only
              have requiredFile : afterScrutinees.file = input.file := requiredReply.2.2.trans valuesFile
              cases openingResult : symbol .leftBrace .statement afterScrutinees with
              | invariant error => trivial
              | reject failure rejected =>
                  have reply := symbol_validFor .leftBrace .statement
                    afterScrutinees requiredReply.2.1
                  rw [openingResult] at reply
                  simpa only [Reply.ValidFor] using reply.of_file_eq requiredFile
              | ok opening afterOpening =>
                  have openingReply := symbol_validFor .leftBrace .statement
                    afterScrutinees requiredReply.2.1
                  rw [openingResult] at openingReply
                  simp only
                  have openingFile : afterOpening.file = input.file := openingReply.2.2.trans requiredFile
                  have casesContract := MatchInternals.matchCases_validFor expressionValueValid
                    patternValueValid yulValueValid statement pattern caseValid
                    (afterOpening.remainingCount + 1) [] afterOpening openingReply.2.1
                    (by intro item member; simp at member)
                  cases casesResult : MatchInternals.matchCases statement pattern
                      (afterOpening.remainingCount + 1) [] afterOpening with
                  | invariant error => trivial
                  | reject failure rejected =>
                      rw [casesResult] at casesContract
                      simpa only [Reply.ValidFor] using casesContract.of_file_eq openingFile
                  | ok cases afterCases =>
                      rw [casesResult] at casesContract
                      simp only
                      have casesFile : afterCases.file = input.file := casesContract.2.2.trans openingFile
                      cases defaultResult : MatchInternals.optionalDefaultBody statement afterCases with
                      | invariant error => trivial
                      | reject failure rejected =>
                          have reply := defaultValid afterCases
                            casesContract.2.1
                          rw [defaultResult] at reply
                          simpa only [Reply.ValidFor] using reply.of_file_eq casesFile
                      | ok defaultBody afterDefault =>
                          have defaultReply := defaultValid afterCases
                            casesContract.2.1
                          rw [defaultResult] at defaultReply
                          simp only
                          have defaultFile : afterDefault.file = input.file := defaultReply.2.2.trans casesFile
                          cases closingResult : symbol .rightBrace .statement afterDefault with
                          | invariant error => trivial
                          | reject failure rejected =>
                              have reply := symbol_validFor .rightBrace
                                .statement afterDefault defaultReply.2.1
                              rw [closingResult] at reply
                              simpa only [Reply.ValidFor] using reply.of_file_eq defaultFile
                          | ok closing afterClosing =>
                              have closingReply := symbol_validFor .rightBrace
                                .statement afterDefault defaultReply.2.1
                              rw [closingResult] at closingReply
                              simp only
                              have closingFile : afterClosing.file = input.file := closingReply.2.2.trans defaultFile
                              have caseSpans : List.ValidFor (fun file retainedCase =>
                                  retainedCase.span.ValidFor file) afterClosing.file cases := by
                                intro retained member
                                have retainedValid := casesContract.1 retained member
                                cases retainedValid with
                                | arm spanValid _ _ _ =>
                                    simpa [closingReply.2.2, defaultReply.2.2,
                                      casesContract.2.2] using spanValid
                              have validationReply := MatchInternals.validateMatchArities_validFor
                                scrutinees.elements.toList.length cases afterClosing
                                closingReply.2.1 caseSpans
                              cases validationResult : MatchInternals.validateMatchArities
                                  scrutinees.elements.toList.length cases afterClosing with
                              | invariant error => trivial
                              | reject failure rejected =>
                                  rw [validationResult] at validationReply
                                  simpa only [Reply.ValidFor] using validationReply.of_file_eq closingFile
                              | ok validated afterValidation =>
                                  rw [validationResult] at validationReply
                                  simp only
                                  have validationFile : afterValidation.file = input.file :=
                                    validationReply.2.2.trans closingFile
                                  have markerAt := State.getElem?_eq_some_of_peek?_eq_some
                                    (acceptToken_ok_state_shape (.keyword .matchKw) .statement
                                      (fun kind => kind == .keyword .matchKw) markerResult).1
                                  have openingAt := State.getElem?_eq_some_of_peek?_eq_some
                                    (symbol_ok_state_shape .leftBrace .statement openingResult).1
                                  have closingAt := State.getElem?_eq_some_of_peek?_eq_some
                                    (symbol_ok_state_shape .rightBrace .statement closingResult).1
                                  have casesTokens := MatchInternals.matchCases_preservesTokensOnSuccess
                                    statement pattern caseWindow (afterOpening.remainingCount + 1) []
                                    afterOpening cases afterCases casesResult
                                  have defaultTokens := MatchInternals.optionalDefaultBody_preservesTokensOnSuccess
                                    statement statementWindow afterCases defaultBody afterDefault defaultResult
                                  have openTokens := symbol_preservesTokensOnSuccess .leftBrace .statement
                                    afterScrutinees opening afterOpening openingResult
                                  have requireTokens :=
                                    (MatchInternals.requireScrutinees_preservesTokenWindow values).preservesTokensOnSuccess
                                      afterValues scrutinees afterScrutinees requiredResult
                                  have valuesTokens := delimited_preservesTokensOnSuccess .leftParen .rightParen
                                    false expression .expression .statement expressionTokens afterMarker values
                                    afterValues valuesResult
                                  have markerTokens := keyword_preservesTokensOnSuccess .matchKw .statement
                                    input marker afterMarker markerResult
                                  have openingAtDefault :
                                      afterDefault.tokens[afterScrutinees.cursor]? =
                                        some opening := by
                                    simpa [defaultTokens, casesTokens, openTokens] using openingAt
                                  have markerAtDefault :
                                      afterDefault.tokens[input.cursor]? =
                                        some marker := by
                                    simpa [defaultTokens, casesTokens, openTokens, requireTokens,
                                      valuesTokens, markerTokens] using markerAt
                                  have openCursor := acceptToken_cursor_lt_onSuccess
                                    (.symbol .leftBrace) .statement
                                    (fun kind => kind == .symbol .leftBrace) openingResult
                                  have casesCursor := MatchInternals.matchCases_cursorMonotoneOnSuccess
                                    statement pattern (afterOpening.remainingCount + 1) [] afterOpening cases
                                    afterCases casesResult
                                  have defaultCursor := MatchInternals.optionalDefaultBody_cursorMonotoneOnSuccess
                                    statement afterCases defaultBody afterDefault defaultResult
                                  have markerCursor := acceptToken_cursor_lt_onSuccess
                                    (.keyword .matchKw) .statement
                                    (fun kind => kind == .keyword .matchKw) markerResult
                                  have valuesCursor := delimited_cursorMonotoneOnSuccess .leftParen
                                    .rightParen false expression .expression .statement afterMarker values
                                    afterValues valuesResult
                                  have requiredCursor := MatchInternals.requireScrutinees_cursorMonotoneOnSuccess
                                    values afterValues scrutinees afterScrutinees requiredResult
                                  have openingBefore : afterScrutinees.cursor <
                                      afterDefault.cursor := by
                                    exact Nat.lt_of_lt_of_le openCursor
                                      (Nat.le_trans casesCursor defaultCursor)
                                  have markerBefore : input.cursor <
                                      afterDefault.cursor := by
                                    exact Nat.lt_trans (Nat.lt_of_lt_of_le markerCursor
                                      (Nat.le_trans valuesCursor requiredCursor)) openingBefore
                                  have markerSeparated :=
                                    defaultReply.2.1.token_end_le_token_start_of_getElem?_lt
                                      markerAtDefault closingAt markerBefore
                                  have openingSeparated :=
                                    defaultReply.2.1.token_end_le_token_start_of_getElem?_lt
                                      openingAtDefault closingAt openingBefore
                                  have markerSpan : marker.span.ValidFor
                                      input.file := by
                                    simpa only [Located.ValidFor] using
                                      markerReply.1
                                  have openingSpan : opening.span.ValidFor
                                      input.file := by
                                    simpa only [Located.ValidFor,
                                      requiredFile] using openingReply.1
                                  have closingSpan : closing.span.ValidFor
                                      input.file := by
                                    simpa only [Located.ValidFor,
                                      defaultFile] using closingReply.1
                                  have outerSpan := SourceSpan.cover_validFor
                                    markerSpan closingSpan (Nat.le_trans
                                      markerSpan.2.1 (Nat.le_trans
                                        markerSeparated closingSpan.2.1))
                                  have armsSpan := SourceSpan.cover_validFor
                                    openingSpan closingSpan (Nat.le_trans
                                      openingSpan.2.1 (Nat.le_trans
                                        openingSeparated closingSpan.2.1))
                                  have scrutineesValid :
                                      NonemptyDelimitedList.ValidFor
                                        expressionValueValid input.file
                                        scrutinees := by
                                    simpa [valuesFile] using requiredReply.1
                                  have casesValid : List.ValidFor
                                      (MatchCase.ValidFor expressionValueValid
                                        patternValueValid yulValueValid)
                                      input.file cases := by
                                    simpa [openingFile] using casesContract.1
                                  have defaultBodyValid : Option.ValidFor
                                      (Block.ValidFor (Statement.ValidFor
                                        expressionValueValid patternValueValid
                                        yulValueValid)) input.file
                                      defaultBody := by
                                    simpa [casesFile] using defaultReply.1
                                  have armsValid : MatchArms.ValidFor
                                      expressionValueValid patternValueValid
                                      yulValueValid input.file {
                                        span := SourceSpan.cover opening.span
                                          closing.span
                                        value := { cases, defaultBody }
                                      } := by
                                    cases defaultBody with
                                    | none => exact MatchArms.ValidFor.arms (defaultBody := none) armsSpan casesValid (by simp) (by simp)
                                    | some body =>
                                        simp only [Option.ValidFor] at defaultBodyValid
                                        exact MatchArms.ValidFor.arms (defaultBody := some body) armsSpan casesValid (by simpa using defaultBodyValid.1) (by simpa using defaultBodyValid.2)
                                  have retainedValid :=
                                    Statement.ValidFor.matchWith outerSpan
                                      scrutineesValid.1 scrutineesValid.2
                                      armsValid
                                  by_cases missing :
                                      cases.isEmpty && defaultBody.isNone
                                  · simp only [missing, if_true]
                                    have emitted := emitDiagnostic_reply_validFor
                                      (diagnostic := { span := SourceSpan.cover marker.span closing.span, kind := .constraintViolation .matchRequiresArm }) validationReply.2.1 (by
                                        simpa [validationFile] using outerSpan)
                                    cases emittedResult : emitDiagnostic { span := SourceSpan.cover marker.span closing.span, kind := .constraintViolation .matchRequiresArm }
                                        afterValidation with
                                    | invariant error => trivial
                                    | reject failure rejected =>
                                        rw [emittedResult] at emitted
                                        simpa only [bind, emittedResult,
                                          Reply.ValidFor] using
                                            emitted.of_file_eq validationFile
                                    | ok value afterEmit =>
                                        rw [emittedResult] at emitted
                                        simp only
                                        exact ⟨by simpa [emitted.2.2,
                                          validationFile] using retainedValid,
                                          emitted.2.1,
                                          emitted.2.2.trans validationFile⟩
                                  · simp only [missing]
                                    exact ⟨by simpa [validationFile] using
                                      retainedValid, validationReply.2.1,
                                        validationFile⟩

/-- Complete `match` parsing preserves every ordinary token window. -/
theorem matchStatement_preservesTokenWindow
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (patternWindow : Parser.PreservesTokenWindow pattern) :
    Parser.PreservesTokenWindow
      (matchStatement statement expression pattern) := by
  have caseWindow := MatchInternals.matchCase_preservesTokenWindow
    statement pattern statementWindow patternWindow
  have casesWindow : Parser.PreservesTokenWindow (fun input =>
      MatchInternals.matchCases statement pattern
        (input.remainingCount + 1) [] input) := by
    intro input
    exact MatchInternals.matchCases_preservesTokenWindow statement pattern
      caseWindow (input.remainingCount + 1) [] input
  unfold matchStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .matchKw .statement)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftParen .rightParen false expression
      .expression .statement expressionWindow)
  intro values
  apply Parser.bind_preservesTokenWindow
    (MatchInternals.requireScrutinees_preservesTokenWindow values)
  intro scrutinees
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .leftBrace .statement)
  intro opening
  apply Parser.bind_preservesTokenWindow casesWindow
  intro cases
  apply Parser.bind_preservesTokenWindow
    (MatchInternals.optionalDefaultBody_preservesTokenWindow statement
      statementWindow)
  intro defaultBody
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightBrace .statement)
  intro closing
  apply Parser.bind_preservesTokenWindow
    (MatchInternals.validateMatchArities_preservesTokenWindow
      scrutinees.elements.toList.length cases)
  intro _
  by_cases missing : cases.isEmpty && defaultBody.isNone
  · simp only [missing, if_true]
    apply Parser.bind_preservesTokenWindow
      (emitDiagnostic_preservesTokenWindow _)
    intro _
    exact Parser.pure_preservesTokenWindow _
  · simp only [missing]
    exact Parser.pure_preservesTokenWindow _

/-- Successful `match` parsing preserves the immutable token carrier. -/
theorem matchStatement_preservesTokensOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (patternWindow : Parser.PreservesTokenWindow pattern) :
    Parser.PreservesTokensOnSuccess
      (matchStatement statement expression pattern) :=
  (matchStatement_preservesTokenWindow statement expression pattern
    statementWindow expressionWindow patternWindow).preservesTokensOnSuccess

/-- A successful `match` statement never rewinds the token cursor. -/
theorem matchStatement_cursorMonotoneOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern) :
    Parser.CursorMonotoneOnSuccess
      (matchStatement statement expression pattern) := by
  have casesCursor : Parser.CursorMonotoneOnSuccess (fun input =>
      MatchInternals.matchCases statement pattern
        (input.remainingCount + 1) [] input) := by
    intro input cases final parsed
    exact MatchInternals.matchCases_cursorMonotoneOnSuccess statement pattern
      (input.remainingCount + 1) [] input cases final parsed
  unfold matchStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .matchKw .statement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftParen .rightParen false
      expression .expression .statement)
  intro values
  apply Parser.bind_cursorMonotoneOnSuccess
    (MatchInternals.requireScrutinees_cursorMonotoneOnSuccess values)
  intro scrutinees
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftBrace .statement)
  intro opening
  apply Parser.bind_cursorMonotoneOnSuccess casesCursor
  intro cases
  apply Parser.bind_cursorMonotoneOnSuccess
    (MatchInternals.optionalDefaultBody_cursorMonotoneOnSuccess statement)
  intro defaultBody
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightBrace .statement)
  intro closing
  apply Parser.bind_cursorMonotoneOnSuccess
    (MatchInternals.validateMatchArities_cursorMonotoneOnSuccess
      scrutinees.elements.toList.length cases)
  intro _
  by_cases missing : cases.isEmpty && defaultBody.isNone
  · simp only [missing, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (emitDiagnostic_cursorMonotoneOnSuccess _)
    intro _
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [missing]
    exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful `match` statement strictly consumes its leading marker. -/
theorem matchStatement_cursor_lt_onSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern) {input final : State}
    {retainedStatement : Statement}
    (parsed : matchStatement statement expression pattern input =
      .ok retainedStatement final) :
    input.cursor < final.cursor := by
  have stages := parsed
  unfold matchStatement at stages
  rcases matchBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨values, afterValues, valuesResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨scrutinees, afterScrutinees, scrutineesResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨cases, afterCases, casesResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨defaultBody, afterDefault, defaultResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨closing, afterClosing, closingResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨validated, afterValidation, validationResult, rest⟩
  have markerStrict : input.cursor < afterMarker.cursor :=
    acceptToken_cursor_lt_onSuccess (.keyword .matchKw) .statement
      (fun kind => kind == .keyword .matchKw) markerResult
  have tailMonotone : afterMarker.cursor ≤ afterValidation.cursor := by
    calc
      afterMarker.cursor ≤ afterValues.cursor :=
        delimited_cursorMonotoneOnSuccess .leftParen .rightParen false
          expression .expression .statement afterMarker values afterValues
            valuesResult
      _ ≤ afterScrutinees.cursor :=
        MatchInternals.requireScrutinees_cursorMonotoneOnSuccess values
          afterValues scrutinees afterScrutinees scrutineesResult
      _ ≤ afterOpening.cursor := symbol_cursorMonotoneOnSuccess
        .leftBrace .statement afterScrutinees opening afterOpening openingResult
      _ ≤ afterCases.cursor :=
        MatchInternals.matchCases_cursorMonotoneOnSuccess statement pattern
          (afterOpening.remainingCount + 1) [] afterOpening cases afterCases
            casesResult
      _ ≤ afterDefault.cursor :=
        MatchInternals.optionalDefaultBody_cursorMonotoneOnSuccess statement
          afterCases defaultBody afterDefault defaultResult
      _ ≤ afterClosing.cursor := symbol_cursorMonotoneOnSuccess
        .rightBrace .statement afterDefault closing afterClosing closingResult
      _ ≤ afterValidation.cursor :=
        MatchInternals.validateMatchArities_cursorMonotoneOnSuccess
          scrutinees.elements.toList.length cases afterClosing validated
            afterValidation validationResult
  by_cases missing : cases.isEmpty && defaultBody.isNone
  · simp only [missing, if_true] at rest
    rcases matchBind_ok_components rest with
      ⟨presence, afterPresence, presenceResult, finished⟩
    cases finished
    exact Nat.lt_of_lt_of_le markerStrict (Nat.le_trans tailMonotone
      (emitDiagnostic_cursorMonotoneOnSuccess _ afterValidation presence
        final presenceResult))
  · simp only [missing] at rest
    cases rest
    exact Nat.lt_of_lt_of_le markerStrict tailMonotone

/-- A complete `match` statement starts at its `match` keyword token. -/
theorem matchStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern) :
    Parser.StartsAtCurrentTokenOnSuccess
      (matchStatement statement expression pattern) (·.span) := by
  unfold matchStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .matchKw)
      .statement (fun kind => kind == .keyword .matchKw))
  intro marker input parsedStatement final parsed
  rcases matchBind_ok_components parsed with
    ⟨values, afterValues, valuesResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨scrutinees, afterScrutinees, scrutineesResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨cases, afterCases, casesResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨defaultBody, afterDefault, defaultResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨closing, afterClosing, closingResult, rest⟩
  rcases matchBind_ok_components rest with
    ⟨validated, afterValidation, validationResult, rest⟩
  by_cases missing : cases.isEmpty && defaultBody.isNone
  · simp only [missing, if_true] at rest
    rcases matchBind_ok_components rest with
      ⟨presence, afterPresence, presenceResult, finished⟩
    cases finished
    rfl
  · simp only [missing] at rest
    cases rest
    rfl

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchValidationOrdinaryStabilityProperties
/-! Ordinary stability of diagnostic-only Core match validation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- One arity check always succeeds without changing the declarative
remainder. -/
theorem validateMatchCaseArity_succeeds_stable
    (scrutineeCount : Nat) (arm : MatchCase) (input : State) :
    ∃ output,
      validateMatchCaseArity scrutineeCount arm input = .ok () output ∧
        output.declarativeRemainder = input.declarativeRemainder := by
  unfold validateMatchCaseArity
  split
  · exact ⟨input, rfl, rfl⟩
  · exact ⟨input.emit _, rfl, rfl⟩

/-- The complete arity pass always succeeds and changes diagnostics only. -/
theorem validateMatchArities_succeeds_stable (scrutineeCount : Nat) :
    ∀ cases input, ∃ output,
      validateMatchArities scrutineeCount cases input = .ok () output ∧
        output.declarativeRemainder = input.declarativeRemainder := by
  intro cases
  induction cases with
  | nil =>
      intro input
      exact ⟨input, rfl, rfl⟩
  | cons arm rest inductionHypothesis =>
      intro input
      rcases validateMatchCaseArity_succeeds_stable scrutineeCount arm input
          with ⟨afterArm, armResult, afterArmStable⟩
      rcases inductionHypothesis afterArm with
        ⟨output, restResult, outputStable⟩
      refine ⟨output, ?_, outputStable.trans afterArmStable⟩
      simp only [validateMatchArities, bind, armResult, restResult]

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchDefaultOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for prioritized optional Core default. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Optional default success follows its negative guard or exact marker and
raw required-block outcome. -/
theorem optionalDefaultBody_success_ordinary_sound
    (statement : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input output : State} {body : Option Block}
    (result : optionalDefaultBody statement input = .ok body output) :
    DeclarativeGrammar.OptionalDefaultBodyOrdinaryParses statementOrdinary
      input.declarativeRemainder body output.declarativeRemainder := by
  unfold optionalDefaultBody getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    cases markerResult : keyword .defaultKw .statement input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected =>
        rcases keyword_eq_ok_of_isKeyword_eq_true .defaultKw .statement
          present with ⟨marker, parsed⟩
        rw [parsed] at markerResult
        contradiction
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases bodyResult : coreBlock statement .require afterMarker with
        | invariant error => simp [bodyResult] at result
        | reject failure rejected => simp [bodyResult] at result
        | ok value afterBody =>
            simp only [bodyResult, pure] at result
            cases result
            exact .present marker.span
              (keyword_success_exactTokenParses .defaultKw .statement
                markerResult)
              ((coreBlock_ordinaryOutcome_sound statement .require
                statementOrdinary statementRejects statementSuccessSound
                  statementRejectSound).1 bodyResult)
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (keywordAbsentAt_of_isKeyword_eq_false .defaultKw absent)

/-- Optional default rejection is possible only through its positively
guarded raw required body. -/
theorem optionalDefaultBody_reject_ordinary_sound
    (statement : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalDefaultBody statement input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalDefaultBodyRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalDefaultBody getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    cases markerResult : keyword .defaultKw .statement input with
    | invariant error => simp [markerResult] at result
    | reject markerFailure markerRejected =>
        rcases keyword_eq_ok_of_isKeyword_eq_true .defaultKw .statement
          present with ⟨marker, parsed⟩
        rw [parsed] at markerResult
        contradiction
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases bodyResult : coreBlock statement .require afterMarker with
        | invariant error => simp [bodyResult] at result
        | ok body output => simp [bodyResult, pure] at result
        | reject bodyFailure bodyRejected =>
            simp only [bodyResult] at result
            cases result
            exact .bodyRejected marker.span
              (keyword_success_exactTokenParses .defaultKw .statement
                markerResult)
              ((coreBlock_ordinaryOutcome_sound statement .require
                statementOrdinary statementRejects statementSuccessSound
                  statementRejectSound).2 bodyResult)
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package both executable optional-default outcomes. -/
theorem optionalDefaultBody_ordinaryOutcome_sound
    (statement : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {body : Option Block},
      optionalDefaultBody statement input = .ok body output →
        DeclarativeGrammar.OptionalDefaultBodyOrdinaryParses
          statementOrdinary input.declarativeRemainder body
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      optionalDefaultBody statement input = .reject failure rejected →
        DeclarativeGrammar.OptionalDefaultBodyRejects statementOrdinary
          statementRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨optionalDefaultBody_success_ordinary_sound statement statementOrdinary
      statementRejects statementSuccessSound statementRejectSound,
    optionalDefaultBody_reject_ordinary_sound statement statementOrdinary
      statementRejects statementSuccessSound statementRejectSound⟩

/-- Re-export deterministic optional-default outcomes. -/
theorem optionalDefaultBody_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.OptionalDefaultBodyOrdinaryParses
        statementOrdinary)
      (DeclarativeGrammar.OptionalDefaultBodyRejects statementOrdinary
        statementRejects) :=
  DeclarativeGrammar.optionalDefaultBodyDeterministicOutcomeSpec
    statementOutcomes

end Solcore.Syntax.Parser.MatchInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchStatementOrdinarySuccessSoundnessProperties
/-! Diagnostic-inclusive executable success for complete Core matches. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every complete executable match success preserves the exact structural
trace; validation diagnostics do not restrict ordinary syntax. -/
theorem matchStatement_success_ordinary_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {value : Statement}
    (result : matchStatement statement expression pattern input =
      .ok value output) :
    DeclarativeGrammar.MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input.declarativeRemainder value
        output.declarativeRemainder := by
  unfold matchStatement at result
  rcases bindOkComponents result with
    ⟨marker, afterMarker, markerResult, valuesStage⟩
  rcases bindOkComponents valuesStage with
    ⟨values, afterValues, valuesResult, scrutineesStage⟩
  rcases bindOkComponents scrutineesStage with
    ⟨scrutinees, afterScrutinees, scrutineesResult, openingStage⟩
  rcases bindOkComponents openingStage with
    ⟨opening, afterOpening, openingResult, casesStage⟩
  rcases bindOkComponents casesStage with
    ⟨cases, afterCases, casesResult, defaultStage⟩
  rcases bindOkComponents defaultStage with
    ⟨defaultBody, afterDefault, defaultResult, closingStage⟩
  rcases bindOkComponents closingStage with
    ⟨closing, afterClosing, closingResult, validationStage⟩
  have parsed :
      DeclarativeGrammar.MatchStatementOrdinaryParses statementOrdinary
        expressionOrdinary patternOrdinary input.declarativeRemainder {
          span := SourceSpan.cover marker.span closing.span
          value := .matchWith scrutinees {
            span := SourceSpan.cover opening.span closing.span
            value := { cases, defaultBody }
          }
        } afterClosing.declarativeRemainder :=
    .parsed marker.span opening.span closing.span
      (keyword_success_exactTokenParses .matchKw .statement markerResult)
      (MatchInternals.matchScrutineeList_success_ordinary_sound expression
        expressionOrdinary expressionSuccessSound expressionWindow
          valuesResult)
      (MatchInternals.requireScrutinees_success_ordinary_sound values
        scrutineesResult)
      (symbol_success_exactTokenParses .leftBrace .statement openingResult)
      (MatchInternals.matchCases_success_ordinary_sound statement pattern
        statementOrdinary statementRejects patternOrdinary
          statementSuccessSound statementRejectSound patternSuccessSound
            casesResult)
      (MatchInternals.optionalDefaultBody_success_ordinary_sound statement
        statementOrdinary statementRejects statementSuccessSound
          statementRejectSound defaultResult)
      (symbol_success_exactTokenParses .rightBrace .statement closingResult)
  rcases MatchInternals.validateMatchArities_succeeds_stable
      scrutinees.elements.toList.length cases afterClosing with
    ⟨afterValidation, validationResult, validationStable⟩
  rcases bindOkComponents validationStage with
    ⟨checked, actualAfterValidation, actualValidationResult, finished⟩
  rw [validationResult] at actualValidationResult
  cases actualValidationResult
  by_cases missing : (cases.isEmpty && defaultBody.isNone) = true
  · simp only [missing, if_true] at finished
    rcases bindOkComponents finished with
      ⟨emitted, afterDiagnostic, emittedResult, finalResult⟩
    simp only [pure] at finalResult
    cases finalResult
    unfold emitDiagnostic modifyState at emittedResult
    cases emittedResult
    have emitStable : ∀ diagnostic : ParseDiagnostic,
        (afterValidation.emit diagnostic).declarativeRemainder =
          afterClosing.declarativeRemainder := by
      intro diagnostic
      simpa [State.emit, State.declarativeRemainder] using validationStable
    rw [emitStable {
      span := SourceSpan.cover marker.span closing.span
      kind := .constraintViolation .matchRequiresArm
    }]
    exact parsed
  · have missingFalse : (cases.isEmpty && defaultBody.isNone) = false :=
      Bool.eq_false_iff.mpr missing
    simp only [missingFalse, Bool.false_eq_true, if_false, pure] at finished
    cases finished
    rw [validationStable]
    exact parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchStatementOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection for complete Core matches. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable match rejection records the first rejecting structural
stage; diagnostic-only validation cannot reject. -/
theorem matchStatement_reject_ordinary_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : matchStatement statement expression pattern input =
      .reject failure rejected) :
    DeclarativeGrammar.MatchStatementRejects statementOrdinary
      statementRejects expressionOrdinary expressionRejects patternOrdinary
        patternRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  unfold matchStatement at result
  cases markerResult : keyword .matchKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .matchKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .matchKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .matchKw
        .statement markerResult
      cases valuesResult : delimited .leftParen .rightParen false expression
          .expression .statement afterMarker with
      | invariant error => simp [valuesResult] at result
      | reject valuesFailure valuesRejected =>
          simp only [valuesResult] at result
          cases result
          exact .valuesRejected marker.span markerParsed
            (MatchInternals.matchScrutineeList_reject_ordinary_sound
              expression expressionOrdinary expressionRejects
                expressionSuccessSound expressionRejectSound valuesResult)
      | ok values afterValues =>
          simp only [valuesResult] at result
          have valuesParsed :=
            MatchInternals.matchScrutineeList_success_ordinary_sound expression
              expressionOrdinary expressionSuccessSound expressionWindow
                valuesResult
          cases scrutineesResult : MatchInternals.requireScrutinees values
              afterValues with
          | invariant error => simp [scrutineesResult] at result
          | reject scrutineeFailure scrutineesRejected =>
              simp only [scrutineesResult] at result
              cases result
              exact .scrutineesRejected marker.span markerParsed valuesParsed
                (MatchInternals.requireScrutinees_reject_ordinary_sound values
                  scrutineesResult)
          | ok scrutinees afterScrutinees =>
              simp only [scrutineesResult] at result
              have scrutineesRequired :=
                MatchInternals.requireScrutinees_success_ordinary_sound values
                  scrutineesResult
              cases openingResult : symbol .leftBrace .statement
                  afterScrutinees with
              | invariant error => simp [openingResult] at result
              | reject openingFailure openingRejected =>
                  have rejectedEq := symbol_reject_state_eq .leftBrace
                    .statement openingResult
                  subst openingRejected
                  simp only [openingResult] at result
                  cases result
                  exact .openingMissing marker.span markerParsed valuesParsed
                    scrutineesRequired
                    (symbol_reject_tokenKindAbsentAt .leftBrace .statement
                      openingResult)
              | ok opening afterOpening =>
                  simp only [openingResult] at result
                  have openingParsed := symbol_success_exactTokenParses
                    .leftBrace .statement openingResult
                  cases casesResult : MatchInternals.matchCases statement
                      pattern (afterOpening.remainingCount + 1) []
                        afterOpening with
                  | invariant error => simp [casesResult] at result
                  | reject casesFailure casesRejected =>
                      simp only [casesResult] at result
                      cases result
                      exact .casesRejected marker.span opening.span
                        markerParsed valuesParsed scrutineesRequired
                          openingParsed
                          (MatchInternals.matchCases_reject_ordinary_sound
                            statement pattern statementOrdinary
                              statementRejects patternOrdinary patternRejects
                                statementSuccessSound statementRejectSound
                                  patternSuccessSound patternRejectSound
                                    casesResult)
                  | ok cases afterCases =>
                      simp only [casesResult] at result
                      have casesParsed :=
                        MatchInternals.matchCases_success_ordinary_sound
                          statement pattern statementOrdinary statementRejects
                            patternOrdinary statementSuccessSound
                              statementRejectSound patternSuccessSound
                                casesResult
                      cases defaultResult :
                          MatchInternals.optionalDefaultBody statement
                            afterCases with
                      | invariant error => simp [defaultResult] at result
                      | reject defaultFailure defaultRejected =>
                          simp only [defaultResult] at result
                          cases result
                          exact .defaultRejected marker.span opening.span
                            markerParsed valuesParsed scrutineesRequired
                              openingParsed casesParsed
                              (MatchInternals.optionalDefaultBody_reject_ordinary_sound
                                statement statementOrdinary statementRejects
                                  statementSuccessSound statementRejectSound
                                    defaultResult)
                      | ok defaultBody afterDefault =>
                          simp only [defaultResult] at result
                          have defaultParsed :=
                            MatchInternals.optionalDefaultBody_success_ordinary_sound
                              statement statementOrdinary statementRejects
                                statementSuccessSound statementRejectSound
                                  defaultResult
                          cases closingResult : symbol .rightBrace .statement
                              afterDefault with
                          | invariant error => simp [closingResult] at result
                          | reject closingFailure closingRejected =>
                              have rejectedEq := symbol_reject_state_eq
                                .rightBrace .statement closingResult
                              subst closingRejected
                              simp only [closingResult] at result
                              cases result
                              exact .closingMissing marker.span opening.span
                                markerParsed valuesParsed scrutineesRequired
                                  openingParsed casesParsed defaultParsed
                                  (symbol_reject_tokenKindAbsentAt .rightBrace
                                    .statement closingResult)
                          | ok closing afterClosing =>
                              simp only [closingResult] at result
                              rcases MatchInternals.validateMatchArities_succeeds_stable
                                  scrutinees.elements.toList.length cases
                                    afterClosing with
                                ⟨afterValidation, validationResult,
                                  validationStable⟩
                              rw [validationResult] at result
                              by_cases missing :
                                  (cases.isEmpty && defaultBody.isNone) = true
                              · simp [missing, emitDiagnostic, modifyState,
                                  pure] at result
                              · have missingFalse :
                                    (cases.isEmpty && defaultBody.isNone) =
                                      false := Bool.eq_false_iff.mpr missing
                                simp [missingFalse, pure] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreMatchStatementOrdinaryOutcomeSoundnessProperties
/-! Packaged executable ordinary outcomes for complete Core matches. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package complete Core match success and exact rejection. -/
theorem matchStatement_ordinaryOutcome_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {value : Statement},
      matchStatement statement expression pattern input = .ok value output →
        DeclarativeGrammar.MatchStatementOrdinaryParses statementOrdinary
          expressionOrdinary patternOrdinary input.declarativeRemainder value
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      matchStatement statement expression pattern input =
          .reject failure rejected →
        DeclarativeGrammar.MatchStatementRejects statementOrdinary
          statementRejects expressionOrdinary expressionRejects
            patternOrdinary patternRejects input.declarativeRemainder
              rejected.declarativeRemainder) :=
  ⟨matchStatement_success_ordinary_sound statement expression pattern
      statementOrdinary statementRejects expressionOrdinary patternOrdinary
        statementSuccessSound statementRejectSound expressionSuccessSound
          expressionWindow patternSuccessSound,
    matchStatement_reject_ordinary_sound statement expression pattern
      statementOrdinary statementRejects expressionOrdinary expressionRejects
        patternOrdinary patternRejects statementSuccessSound
          statementRejectSound expressionSuccessSound expressionRejectSound
            expressionWindow patternSuccessSound patternRejectSound⟩

/-- Re-export deterministic complete Core match outcomes. -/
theorem matchStatement_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects)
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (patternOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      patternOrdinary patternRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.MatchStatementOrdinaryParses statementOrdinary
        expressionOrdinary patternOrdinary)
      (DeclarativeGrammar.MatchStatementRejects statementOrdinary
        statementRejects expressionOrdinary expressionRejects
          patternOrdinary patternRejects) :=
  DeclarativeGrammar.matchStatementDeterministicOutcomeSpec
    statementOutcomes expressionOutcomes patternOutcomes

end Solcore.Syntax.Parser
end
