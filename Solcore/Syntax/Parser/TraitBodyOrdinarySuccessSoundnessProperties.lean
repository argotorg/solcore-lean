import Solcore.Syntax.DeclarativeTraitBodyOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.TraitMethodOrdinaryOutcomeSoundnessProperties

/-! Broad ordinary-success soundness for the custom trait-body loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

private theorem functionPresent_of_isKeyword_eq_true {input : State}
    (present : isKeyword input .functionKw = true) :
    DeclarativeGrammar.TraitMethodStartAt input.declarativeRemainder := by
  rcases keyword_eq_ok_of_isKeyword_eq_true .functionKw .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses .functionKw .topItem result).1⟩

private theorem closeTraitBody_success_ordinary_sound (opening : Token)
    (methodsRev : List TraitMethod) {input output : State} {body : TraitBody}
    (result : closeTraitBody opening methodsRev input = .ok body output) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        methods := methodsRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan output.declarativeRemainder := by
  unfold closeTraitBody at result
  rcases bind_ok_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  cases finished
  exact ⟨closing.span, rfl,
    symbol_success_exactTokenParses .rightBrace .topItem closingResult⟩

private theorem traitMethods_success_ordinary_sound_strong
    (opening : Token) :
    ∀ fuel methodsRev input body output,
      traitMethods opening fuel methodsRev input = .ok body output →
      ∃ methods closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          methods := methodsRev.reverse ++ methods
        } ∧
        DeclarativeGrammar.TraitMethodTailOrdinaryParses
          input.declarativeRemainder methods closingSpan
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input body output result
      simp [traitMethods] at result
  | succ fuel inductionHypothesis =>
      intro methodsRev input body output result
      unfold traitMethods at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeTraitBody_success_ordinary_sound opening methodsRev
              result with ⟨closingSpan, bodyEq, closingParsed⟩
          exact ⟨[], closingSpan, by simpa using bodyEq,
            .close closingSpan closingParsed⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases functionPresent : isKeyword input .functionKw with
          | false => simp [functionPresent, rejectAt] at result
          | true =>
              simp only [functionPresent, if_true] at result
              cases methodResult : traitMethod input with
              | invariant error => simp [methodResult] at result
              | reject failure rejected => simp [methodResult] at result
              | ok method afterMethod =>
                  simp only [methodResult] at result
                  by_cases progress : afterMethod.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (method :: methodsRev)
                        afterMethod body output result with
                      ⟨methods, closingSpan, bodyEq, tailParsed⟩
                    refine ⟨method :: methods, closingSpan, ?_,
                      .next
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        (functionPresent_of_isKeyword_eq_true functionPresent)
                        (traitMethod_success_ordinaryOutcome_sound
                          methodResult)
                        progress tailParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp [progress] at result

/-- Every executable trait-body success records the exact brace span, forward
ordinary methods, and final remainder without a diagnostic-free premise. -/
theorem traitBody_success_ordinaryOutcome_sound
    {input output : State} {body : TraitBody}
    (result : traitBody input = .ok body output) :
    DeclarativeGrammar.TraitBodyOrdinaryOutcomeParses
      input.declarativeRemainder (body.span, body.methods)
        output.declarativeRemainder := by
  unfold traitBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases traitMethods_success_ordinary_sound_strong opening
          (afterOpening.remainingCount + 1) [] afterOpening body output result
        with ⟨methods, closingSpan, bodyEq, methodsParsed⟩
      rw [bodyEq]
      exact .parsed opening.span closingSpan
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        methodsParsed

end Solcore.Syntax.Parser.TraitInternals
