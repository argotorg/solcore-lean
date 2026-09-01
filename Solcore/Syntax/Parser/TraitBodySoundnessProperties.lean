import Solcore.Syntax.Parser.TraitMethodSoundnessProperties

/-! Diagnostic-free success soundness for the fuel-bounded trait body. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
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

private theorem closeTraitBody_success_sound_and_reflects
    (opening : Token) (methodsRev : List TraitMethod)
    {input next : State} {body : TraitBody}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : closeTraitBody opening methodsRev input = .ok body next) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        methods := methodsRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan next.declarativeRemainder ∧
      input.diagnosticsRev = [] := by
  unfold closeTraitBody at result
  rcases bind_ok_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  have afterClosingFree : afterClosing.diagnosticsRev = [] := by
    cases finished
    exact diagnosticFree
  have inputFree : input.diagnosticsRev = [] :=
    symbol_reflectsDiagnosticFreeOnSuccess .rightBrace .topItem input closing
      afterClosing closingResult afterClosingFree
  cases finished
  exact ⟨closing.span, rfl,
    symbol_success_exactTokenParses .rightBrace .topItem closingResult,
    inputFree⟩

private theorem traitMethods_success_sound_strong (opening : Token) :
    ∀ fuel methodsRev input body next,
      next.diagnosticsRev = [] →
      traitMethods opening fuel methodsRev input = .ok body next →
      ∃ methods closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          methods := methodsRev.reverse ++ methods
        } ∧
        DeclarativeGrammar.TraitMethodTailParses
          input.declarativeRemainder methods closingSpan
            next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input body next diagnosticFree result
      simp [traitMethods] at result
  | succ fuel inductionHypothesis =>
      intro methodsRev input body next diagnosticFree result
      unfold traitMethods at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeTraitBody_success_sound_and_reflects opening methodsRev
              diagnosticFree result with
            ⟨closingSpan, bodyEq, closingGrammar, inputFree⟩
          exact ⟨[], closingSpan, by simpa using bodyEq,
            .close closingSpan closingGrammar, inputFree⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases methodPresent : isKeyword input .functionKw with
          | false => simp [methodPresent, rejectAt] at result
          | true =>
              simp only [methodPresent, if_true] at result
              cases methodResult : traitMethod input with
              | invariant error => simp [methodResult] at result
              | reject failure rejected => simp [methodResult] at result
              | ok method afterMethod =>
                  simp only [methodResult] at result
                  by_cases progress : afterMethod.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (method :: methodsRev)
                        afterMethod body next diagnosticFree result with
                      ⟨methods, closingSpan, bodyEq, tailGrammar,
                        afterMethodFree⟩
                    have methodGrammar := traitMethod_success_sound
                      afterMethodFree methodResult
                    have inputFree :=
                      traitMethod_reflectsDiagnosticFreeOnSuccess input method
                        afterMethod methodResult afterMethodFree
                    refine ⟨method :: methods, closingSpan, ?_,
                      .next
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        methodGrammar tailGrammar,
                      inputFree⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction

/-- Every diagnostic-free trait body follows its exact forward method grammar. -/
theorem traitBody_success_sound {input next : State} {body : TraitBody}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitBody input = .ok body next) :
    DeclarativeGrammar.TraitBodyParses input.declarativeRemainder body.span
      body.methods next.declarativeRemainder := by
  unfold traitBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases traitMethods_success_sound_strong opening
          (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨methods, closingSpan, bodyEq, tailGrammar, afterOpeningFree⟩
      rw [bodyEq]
      simpa using DeclarativeGrammar.TraitBodyParses.parsed opening.span
        closingSpan
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        tailGrammar

/-- Trait-body parsing cannot erase an incoming diagnostic. -/
theorem traitBody_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess traitBody := by
  intro input body next result diagnosticFree
  unfold traitBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases traitMethods_success_sound_strong opening
          (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨methods, closingSpan, bodyEq, tailGrammar, afterOpeningFree⟩
      exact symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .topItem input
        opening afterOpening openingResult afterOpeningFree

/-- Trait-body grammar soundness composes with retained-source validity. -/
theorem traitBody_success_sound_and_validFor {input next : State}
    {body : TraitBody} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitBody input = .ok body next) :
    DeclarativeGrammar.TraitBodyParses input.declarativeRemainder body.span
        body.methods next.declarativeRemainder ∧
      TraitBody.ValidFor input.file body := by
  refine ⟨traitBody_success_sound diagnosticFree result, ?_⟩
  have valid := traitBody_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.TraitInternals
