import Solcore.Syntax.Parser.CoreMatchComponentSoundnessProperties
import Solcore.Syntax.Parser.CoreMatchStatementDiagnosticReflectionProperties
import Solcore.Syntax.Parser.DelimitedNonemptyTrailingDiagnosticFreeSoundnessProperties

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
