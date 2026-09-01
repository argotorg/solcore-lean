import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties

/-! Diagnostic-free soundness for required trailing-delimited lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeTrailingDiagnosticFreeSound {alpha : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List alpha) {input next : State}
    {values : DelimitedList alpha} (diagnosticFree : next.diagnosticsRev = [])
    (result : closeDelimited opening closing context elementsRev input =
      .ok values next) :
    input.diagnosticsRev = [] ∧ ∃ closingSpan,
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        input.cursor { span := closingSpan, value := .symbol closing } ∧
      next.declarativeRemainder = {
        input.declarativeRemainder with cursor := input.cursor + 1
      } ∧ values.elements = elementsRev.reverse ∧
      values.span = SourceSpan.cover opening.span closingSpan := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok token afterClosing =>
      have sound := symbol_ok_tokenAt closing context closingResult
      simp only [closingResult] at result
      cases result
      refine ⟨?_, token.span, sound.1, ?_, rfl, rfl⟩
      · simpa [sound.2] using diagnosticFree
      · rw [sound.2]
        rfl

private theorem afterTrailingElementDiagnosticFreeSound {alpha : Type}
    (element : Parser alpha)
    (elementParses : DeclarativeGrammar.Remainder → alpha →
      DeclarativeGrammar.Remainder → Prop)
    (elementSound : ∀ {input next : State} {value : alpha},
      next.diagnosticsRev = [] → element input = .ok value next →
      elementParses input.declarativeRemainder value next.declarativeRemainder)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase)
    (opening : Token) : ∀ fuel elementsRev input values next,
      next.diagnosticsRev = [] →
      afterDelimitedElement element closing true context phase opening fuel
        elementsRev input = .ok values next →
      input.diagnosticsRev = [] ∧ ∃ suffix closingSpan,
        values.elements = elementsRev.reverse ++ suffix ∧
        values.span = SourceSpan.cover opening.span closingSpan ∧
        DeclarativeGrammar.TrailingDelimitedTailParses closing elementParses
          input.declarativeRemainder suffix closingSpan
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next diagnosticFree result
      simp [afterDelimitedElement] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next diagnosticFree result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            have commaSound := symbol_ok_tokenAt .comma context commaResult
            simp only [commaResult] at result
            split at result
            · rcases closeTrailingDiagnosticFreeSound opening closing
                context elementsRev diagnosticFree result with
                ⟨afterCommaFree, closingSpan, closingToken, finalEq,
                  elementsEq, spanEq⟩
              have inputFree := symbol_reflectsDiagnosticFreeOnSuccess .comma
                context input comma afterComma commaResult afterCommaFree
              have closingTokenInput : DeclarativeGrammar.TokenAt input.tokens
                  input.window.endIndex (input.cursor + 1) {
                    span := closingSpan, value := .symbol closing } := by
                simpa only [commaSound.2, State.tokens, State.window,
                  State.cursor] using closingToken
              have finalEqInput : next.declarativeRemainder = {
                  input.declarativeRemainder with cursor := input.cursor + 2
                } := by
                simpa only [commaSound.2, State.declarativeRemainder,
                  State.cursor, State.tokens, State.window, Nat.add_assoc]
                  using finalEq
              refine ⟨inputFree, [], closingSpan, by simpa using elementsEq,
                spanEq, ?_⟩
              rw [finalEqInput]
              exact .trailing commaSound.1 closingTokenInput
            · have closingAbsentAfterComma :
                  isSymbol afterComma closing = false := by simp_all
              have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false
                closing closingAbsentAfterComma
              cases elementResult : element afterComma with
              | invariant error => simp [elementResult] at result
              | reject failure rejected => simp [elementResult] at result
              | ok value afterElement =>
                  simp only [elementResult] at result
                  split at result
                  · rcases inductionHypothesis (value :: elementsRev)
                      afterElement values next diagnosticFree result with
                      ⟨afterElementFree, suffix, closingSpan, elementsEq,
                        spanEq, tailGrammar⟩
                    have afterCommaFree := elementReflects afterComma value
                      afterElement elementResult afterElementFree
                    have inputFree := symbol_reflectsDiagnosticFreeOnSuccess
                      .comma context input comma afterComma commaResult
                        afterCommaFree
                    have valueGrammar := elementSound afterElementFree
                      elementResult
                    have closingAbsentInput :
                        DeclarativeGrammar.TokenKindAbsentAt input.tokens
                          input.window.endIndex (input.cursor + 1)
                          (.symbol closing) := by
                      simpa only [commaSound.2, State.tokens, State.window,
                        State.cursor] using closingAbsent
                    have valueGrammarInput : elementParses {
                        input.declarativeRemainder with
                          cursor := input.cursor + 1
                      } value afterElement.declarativeRemainder := by
                      simpa only [commaSound.2, State.declarativeRemainder,
                        State.tokens, State.window, State.cursor] using
                        valueGrammar
                    have valueProgressInput :
                        input.cursor + 1 < afterElement.cursor := by
                      have valueProgress :
                          afterComma.cursor < afterElement.cursor := by
                        assumption
                      simpa only [commaSound.2, State.cursor] using valueProgress
                    refine ⟨inputFree, value :: suffix, closingSpan, ?_,
                      spanEq, .next commaSound.1 closingAbsentInput
                        valueGrammarInput valueProgressInput tailGrammar⟩
                    calc
                      values.elements =
                          (value :: elementsRev).reverse ++ suffix := elementsEq
                      _ = elementsRev.reverse ++ (value :: suffix) := by
                        simp [List.reverse_cons, List.append_assoc]
                  · contradiction
      · have commaAbsentBool : isSymbol input .comma = false := by simp_all
        have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false .comma
          commaAbsentBool
        split at result
        · rcases closeTrailingDiagnosticFreeSound opening closing context
            elementsRev diagnosticFree result with
            ⟨inputFree, closingSpan, closingToken, finalEq, elementsEq,
              spanEq⟩
          refine ⟨inputFree, [], closingSpan, by simpa using elementsEq,
            spanEq, ?_⟩
          rw [finalEq]
          exact .close commaAbsent closingToken
        · unfold rejectAt at result
          contradiction

/-- A diagnostic-free required trailing list follows its exact grammar. -/
theorem delimited_nonempty_trailing_success_sound_of_diagnosticFree
    {alpha : Type} (opening closing : Symbol) (element : Parser alpha)
    (elementParses : DeclarativeGrammar.Remainder → alpha →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : alpha},
      next.diagnosticsRev = [] → element input = .ok value next →
      elementParses input.declarativeRemainder value next.declarativeRemainder)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList alpha}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : delimited opening closing false element context phase input =
      .ok values next) :
    DeclarativeGrammar.NonemptyTrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  have outputShape := delimited_preservesTokenWindow opening closing false
    element context phase elementShape input
  rw [result] at outputShape
  unfold delimited delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.false_and, Bool.false_eq_true, if_false]
        at result
      cases elementResult : element afterOpening with
      | invariant error => simp [elementResult] at result
      | reject failure rejected => simp [elementResult] at result
      | ok first afterFirst =>
          simp only [elementResult] at result
          split at result
          · rcases afterTrailingElementDiagnosticFreeSound element
                elementParses elementSound elementReflects closing context phase
                openingToken (afterOpening.remainingCount + 1) [first]
                afterFirst values next diagnosticFree result with
              ⟨afterFirstFree, rest, closingSpan, elementsEq, spanEq,
                tailGrammar⟩
            have firstGrammar := elementSound afterFirstFree elementResult
            have firstGrammarInput : elementParses {
                input.declarativeRemainder with cursor := input.cursor + 1
              } first afterFirst.declarativeRemainder := by
              simpa only [openingSound.2, State.declarativeRemainder,
                State.tokens, State.window, State.cursor] using firstGrammar
            have firstProgressInput : input.cursor + 1 < afterFirst.cursor := by
              have firstProgress : afterOpening.cursor < afterFirst.cursor := by
                assumption
              simpa only [openingSound.2, State.cursor] using firstProgress
            unfold DeclarativeGrammar.NonemptyTrailingDelimitedListParses
            refine ⟨openingToken.span, first, afterFirst.declarativeRemainder,
              rest, closingSpan, outputShape.1,
              congrArg TokenWindow.endIndex outputShape.2, openingSound.1,
              firstGrammarInput, firstProgressInput, tailGrammar, ?_, spanEq⟩
            simpa using elementsEq
          · contradiction

end Solcore.Syntax.Parser
