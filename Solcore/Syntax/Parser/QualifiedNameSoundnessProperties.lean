import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Name

/-! Success soundness of canonical qualified-name parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem qualifiedNameTail_success_sound
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input name next,
      QualifiedNameInternals.qualifiedNameTail context phase first fuel last
          tailRev input = .ok name next →
      ∃ components,
        name.value.components.head = first ∧
        name.value.components.tail = tailRev.reverse ++ components ∧
        DeclarativeGrammar.DottedIdentifierTailParses input.tokens
          input.window.endIndex input.cursor components next.cursor ∧
        name.span = SourceSpan.cover first.span
          (DeclarativeGrammar.finalIdentifier last components).span ∧
        next.tokens = input.tokens ∧ next.window = input.window := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input name next result
      simp [QualifiedNameInternals.qualifiedNameTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input name next result
      unfold QualifiedNameInternals.qualifiedNameTail at result
      split at result
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            have dotSound := symbol_ok_tokenAt .dot context dotResult
            simp only [dotResult] at result
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                have componentSound := identifier_ok_tokenAt context
                  componentResult
                simp only [componentResult] at result
                rcases inductionHypothesis component (component :: tailRev)
                    afterComponent name next result with
                  ⟨components, headEq, componentsEq, tailGrammar, spanEq,
                    nextTokens, nextWindow⟩
                have componentToken :
                    DeclarativeGrammar.TokenAt input.tokens
                      input.window.endIndex (input.cursor + 1) {
                        span := component.span
                        value := .identifier component.value
                      } := by
                  simpa only [dotSound.2, State.tokens, State.window,
                    State.cursor] using componentSound.1
                have recursiveTail :
                    DeclarativeGrammar.DottedIdentifierTailParses input.tokens
                      input.window.endIndex (input.cursor + 2) components
                      next.cursor := by
                  simpa only [componentSound.2.1, componentSound.2.2.1,
                    componentSound.2.2.2, dotSound.2, State.tokens,
                    State.window, State.cursor, Nat.add_assoc] using tailGrammar
                refine ⟨component :: components, headEq, ?_,
                  .next dot.span dotSound.1 componentToken recursiveTail,
                  ?_, ?_, ?_⟩
                · calc
                    name.value.components.tail =
                        (component :: tailRev).reverse ++ components :=
                      componentsEq
                    _ = tailRev.reverse ++ (component :: components) := by
                      simp [List.reverse_cons, List.append_assoc]
                · simpa only [DeclarativeGrammar.finalIdentifier] using spanEq
                · exact nextTokens.trans
                    (componentSound.2.1.trans (by rw [dotSound.2]))
                · exact nextWindow.trans
                    (componentSound.2.2.1.trans (by rw [dotSound.2]))
      · have absent : isSymbol input .dot = false :=
          Bool.eq_false_iff.mpr (by assumption)
        have stopped := symbolAbsentAt_of_isSymbol_eq_false .dot
          (input := input) absent
        unfold QualifiedNameInternals.finishQualifiedName at result
        cases result
        exact ⟨[], rfl, by simp,
          .done input.cursor stopped, by simp [DeclarativeGrammar.finalIdentifier],
          rfl, rfl⟩

/-- Every successful qualified-name parse follows the independent token grammar. -/
theorem qualifiedName_success_sound (context : ParseContext)
    (phase : ParserPhase) {input next : State} {name : QualifiedName}
    (result : qualifiedName context phase input = .ok name next) :
    DeclarativeGrammar.QualifiedNameParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      have firstSound := identifier_ok_tokenAt context firstResult
      simp only [firstResult] at result
      rcases qualifiedNameTail_success_sound context phase first
          (afterFirst.remainingCount + 1) first [] afterFirst name next result with
        ⟨components, headEq, componentsEq, tailGrammar, spanEq,
          nextTokens, nextWindow⟩
      have tailEq : name.value.components.tail = components := by
        simpa using componentsEq
      unfold DeclarativeGrammar.QualifiedNameParses
        State.declarativeRemainder
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact nextTokens.trans firstSound.2.1
      · exact congrArg TokenWindow.endIndex
          (nextWindow.trans firstSound.2.2.1)
      · simpa only [headEq] using firstSound.1
      · simpa only [firstSound.2.1, firstSound.2.2.1,
          firstSound.2.2.2, tailEq] using tailGrammar
      · simpa only [headEq, tailEq] using spanEq

/-- Success soundness composes with the established source-provenance contract. -/
theorem qualifiedName_success_sound_and_validFor (context : ParseContext)
    (phase : ParserPhase) {input next : State} {name : QualifiedName}
    (inputValid : input.ValidFor)
    (result : qualifiedName context phase input = .ok name next) :
    DeclarativeGrammar.QualifiedNameParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      name.ValidFor input.file := by
  refine ⟨qualifiedName_success_sound context phase result, ?_⟩
  have valid := qualifiedName_validFor context phase input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
