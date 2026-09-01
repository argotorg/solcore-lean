import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.ExportProperties

/-! Success soundness of maximal canonical export paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Failed composite lookahead excludes exactly a dot-identifier pair. -/
private theorem dotIdentifierAbsentAt_of_continuesExportPath_eq_false
    {input : State}
    (stopped : ExportInternals.continuesExportPath input = false) :
    DeclarativeGrammar.DotIdentifierAbsentAt input.tokens
      input.window.endIndex input.cursor := by
  rintro ⟨dotSpan, componentSpan, text, dotAt, componentAt⟩
  have dotPresent : isSymbol input .dot = true := by
    unfold isSymbol State.peekKind? State.peek?
    simp only [dotAt.1, ↓reduceIte, dotAt.2, Option.map_some]
    rfl
  have componentPresent :
      input.peekOffsetKind? 1 = some (.identifier text) := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [componentAt.1, ↓reduceIte, componentAt.2, Option.map_some]
  unfold ExportInternals.continuesExportPath at stopped
  rw [dotPresent, componentPresent] at stopped
  contradiction

/-- Successful tail execution recovers its forward-order declarative suffix. -/
private theorem exportPathTail_success_sound (first : Identifier) :
    ∀ fuel last tailRev input path next,
      ExportInternals.exportPathTail first fuel last tailRev input =
          .ok path next →
      ∃ components,
        path.value.components.head = first ∧
        path.value.components.tail = tailRev.reverse ++ components ∧
        DeclarativeGrammar.ExportPathTailParses input.tokens
          input.window.endIndex input.cursor components next.cursor ∧
        path.span = SourceSpan.cover first.span
          (DeclarativeGrammar.finalIdentifier last components).span ∧
        next.tokens = input.tokens ∧ next.window = input.window := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input path next result
      simp [ExportInternals.exportPathTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input path next result
      unfold ExportInternals.exportPathTail at result
      split at result
      next continues =>
        cases dotResult : symbol .dot .exportDecl input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            have dotSound := symbol_ok_tokenAt .dot .exportDecl dotResult
            simp only [dotResult] at result
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                have componentSound := identifier_ok_tokenAt .exportDecl
                  componentResult
                simp only [componentResult] at result
                rcases inductionHypothesis component (component :: tailRev)
                    afterComponent path next result with
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
                    DeclarativeGrammar.ExportPathTailParses input.tokens
                      input.window.endIndex (input.cursor + 2) components
                      next.cursor := by
                  simpa only [componentSound.2.1, componentSound.2.2.1,
                    componentSound.2.2.2, dotSound.2, State.tokens,
                    State.window, State.cursor, Nat.add_assoc] using tailGrammar
                refine ⟨component :: components, headEq, ?_,
                  .next dot.span dotSound.1 componentToken recursiveTail,
                  ?_, ?_, ?_⟩
                · calc
                    path.value.components.tail =
                        (component :: tailRev).reverse ++ components :=
                      componentsEq
                    _ = tailRev.reverse ++ (component :: components) := by
                      simp [List.reverse_cons, List.append_assoc]
                · simpa only [DeclarativeGrammar.finalIdentifier] using spanEq
                · exact nextTokens.trans
                    (componentSound.2.1.trans (by rw [dotSound.2]))
                · exact nextWindow.trans
                    (componentSound.2.2.1.trans (by rw [dotSound.2]))
      next stopped =>
        have stoppedFalse :
            ExportInternals.continuesExportPath input = false := by
          cases found : ExportInternals.continuesExportPath input <;> simp_all
        have absent :=
          dotIdentifierAbsentAt_of_continuesExportPath_eq_false stoppedFalse
        unfold ExportInternals.finishExportPath at result
        cases result
        exact ⟨[], rfl, by simp, .done input.cursor absent,
          by simp [DeclarativeGrammar.finalIdentifier], rfl, rfl⟩

/-- Every successful export path follows the maximal declarative path grammar. -/
theorem exportPath_success_sound {input next : State}
    {path : QualifiedName}
    (result : ExportInternals.exportPath input = .ok path next) :
    DeclarativeGrammar.ExportPathParses input.declarativeRemainder path
      next.declarativeRemainder := by
  unfold ExportInternals.exportPath at result
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      have firstSound := identifier_ok_tokenAt .exportDecl firstResult
      simp only [firstResult] at result
      rcases exportPathTail_success_sound first
          (afterFirst.remainingCount + 1) first [] afterFirst path next result with
        ⟨components, headEq, componentsEq, tailGrammar, spanEq,
          nextTokens, nextWindow⟩
      have tailEq : path.value.components.tail = components := by
        simpa using componentsEq
      unfold DeclarativeGrammar.ExportPathParses State.declarativeRemainder
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact nextTokens.trans firstSound.2.1
      · exact congrArg TokenWindow.endIndex
          (nextWindow.trans firstSound.2.2.1)
      · simpa only [headEq] using firstSound.1
      · simpa only [firstSound.2.1, firstSound.2.2.1,
          firstSound.2.2.2, tailEq] using tailGrammar
      · simpa only [headEq, tailEq] using spanEq

/-- Export-path grammar soundness composes with source validity. -/
theorem exportPath_success_sound_and_validFor {input next : State}
    {path : QualifiedName} (inputValid : input.ValidFor)
    (result : ExportInternals.exportPath input = .ok path next) :
    DeclarativeGrammar.ExportPathParses input.declarativeRemainder path
        next.declarativeRemainder ∧
      path.ValidFor input.file := by
  refine ⟨exportPath_success_sound result, ?_⟩
  have valid := exportPath_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
