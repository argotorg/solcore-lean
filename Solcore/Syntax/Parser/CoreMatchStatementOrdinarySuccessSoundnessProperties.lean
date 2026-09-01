import Solcore.Syntax.DeclarativeCoreMatchStatementOutcomeProperties
import Solcore.Syntax.Parser.CoreMatchCasesOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreMatchDefaultOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreMatchScrutineeListOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreMatchScrutineesOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreMatchValidationOrdinaryStabilityProperties

/-! Diagnostic-inclusive executable success for complete Core matches. -/

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
