import Solcore.Syntax.Parser.ImplMethodSoundnessProperties

/-! Parametric diagnostic-free soundness for the fuel-bounded implementation body. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

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

private theorem closeImplBody_success_sound_and_reflects
    (opening : Token) (methodsRev : List ImplMethod)
    {input next : State} {body : ImplBody}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : closeImplBody opening methodsRev input = .ok body next) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        methods := methodsRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan next.declarativeRemainder ∧
      input.diagnosticsRev = [] := by
  unfold closeImplBody at result
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

private theorem implMethods_reflectsDiagnosticFreeOnSuccess
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow))) (opening : Token) :
    ∀ fuel methodsRev input body next,
      implMethods opening fuel methodsRev input = .ok body next →
      next.diagnosticsRev = [] → input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input body next result diagnosticFree
      simp [implMethods] at result
  | succ fuel inductionHypothesis =>
      intro methodsRev input body next result diagnosticFree
      unfold implMethods at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeImplBody_success_sound_and_reflects opening methodsRev
              diagnosticFree result with
            ⟨closingSpan, bodyEq, closingGrammar, inputFree⟩
          exact inputFree
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases methodPresent : isKeyword input .functionKw with
          | false => simp [methodPresent, rejectAt] at result
          | true =>
              simp only [methodPresent, if_true] at result
              cases methodResult : implMethod input with
              | invariant error => simp [methodResult] at result
              | reject failure rejected => simp [methodResult] at result
              | ok method afterMethod =>
                  simp only [methodResult] at result
                  by_cases progress : afterMethod.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    have afterMethodFree := inductionHypothesis
                      (method :: methodsRev) afterMethod body next result
                        diagnosticFree
                    exact implMethod_reflectsDiagnosticFreeOnSuccess
                      bodyReflects input method afterMethod methodResult
                        afterMethodFree
                  · simp only [progress, if_false] at result
                    contradiction

/-- Implementation-body parsing cannot erase an incoming diagnostic. -/
theorem implBody_reflectsDiagnosticFreeOnSuccess
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow))) :
    Parser.ReflectsDiagnosticFreeOnSuccess implBody := by
  intro input body next result diagnosticFree
  unfold implBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have afterOpeningFree := implMethods_reflectsDiagnosticFreeOnSuccess
        bodyReflects opening (afterOpening.remainingCount + 1) []
          afterOpening body next result diagnosticFree
      exact symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .topItem input
        opening afterOpening openingResult afterOpeningFree

private theorem implMethods_success_sound_strong
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (opening : Token) :
    ∀ fuel methodsRev input body next,
      next.diagnosticsRev = [] →
      implMethods opening fuel methodsRev input = .ok body next →
      ∃ methods closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          methods := methodsRev.reverse ++ methods
        } ∧
        DeclarativeGrammar.ImplMethodTailParses bodyParses
          input.declarativeRemainder methods closingSpan
            next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input body next diagnosticFree result
      simp [implMethods] at result
  | succ fuel inductionHypothesis =>
      intro methodsRev input body next diagnosticFree result
      unfold implMethods at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeImplBody_success_sound_and_reflects opening methodsRev
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
              cases methodResult : implMethod input with
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
                    have methodGrammar := implMethod_success_sound bodyParses
                      bodyReflects bodySound afterMethodFree methodResult
                    have inputFree := implMethod_reflectsDiagnosticFreeOnSuccess
                      bodyReflects input method afterMethod methodResult
                        afterMethodFree
                    refine ⟨method :: methods, closingSpan, ?_,
                      .next
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        methodGrammar progress tailGrammar,
                      inputFree⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction

/-!
Every diagnostic-free implementation body follows the supplied exact block
grammar, including brace spans, method order, branch priority, and progress.
-/
theorem implBody_success_sound
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {body : ImplBody}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implBody input = .ok body next) :
    DeclarativeGrammar.ImplBodyParses bodyParses input.declarativeRemainder
      body.span body.methods next.declarativeRemainder := by
  unfold implBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases implMethods_success_sound_strong bodyParses bodyReflects bodySound
          opening (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨methods, closingSpan, bodyEq, tailGrammar, afterOpeningFree⟩
      rw [bodyEq]
      simpa using DeclarativeGrammar.ImplBodyParses.parsed opening.span
        closingSpan
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        tailGrammar

/-- Implementation-body grammar soundness composes with source validity. -/
theorem implBody_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {body : ImplBody}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implBody input = .ok body next) :
    DeclarativeGrammar.ImplBodyParses bodyParses input.declarativeRemainder
        body.span body.methods next.declarativeRemainder ∧
      ImplBody.ValidFor statementValid input.file body := by
  refine ⟨implBody_success_sound bodyParses bodyReflects bodySound
    diagnosticFree result, ?_⟩
  have valid := implBody_validFor statementValid bodyValid bodyWindow
    input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.ImplInternals
