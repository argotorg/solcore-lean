import Solcore.Syntax.DeclarativeYulBlockGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.YulBlockDiagnosticReflectionProperties

/-!
Exact diagnostic-free soundness for raw Yul block closing, item iteration,
and the public braced block parser.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Closing retains the reversed accumulator and consumes its exact brace. -/
theorem closeYulBlock_success_sound (opening : Token)
    (bodyRev : List YulStmt) {input next : State} {body : YulParsedBlock}
    (result : closeYulBlock opening bodyRev input = .ok body next) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        body := bodyRev.reverse
      } ∧
      DeclarativeGrammar.CloseYulBlockParses opening.span bodyRev.reverse
        input.declarativeRemainder
          (SourceSpan.cover opening.span closingSpan)
            next.declarativeRemainder ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan next.declarativeRemainder := by
  unfold closeYulBlock at result
  cases closingResult : symbol .rightBrace .yulStatement input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok closing afterClosing =>
      simp only [closingResult] at result
      cases result
      have closingParsed := symbol_success_exactTokenParses .rightBrace
        .yulStatement closingResult
      exact ⟨closing.span, rfl, .parsed closing.span closingParsed,
        closingParsed⟩

/--
Successful iteration recovers the forward suffix following its existing
reverse accumulator, together with the exact block span and closing brace.
-/
theorem yulBlockItems_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (opening : Token) : ∀ fuel bodyRev input body next,
      next.diagnosticsRev = [] →
      yulBlockItems statement opening fuel bodyRev input = .ok body next →
      ∃ bodySpan suffix,
        body = {
          span := bodySpan
          body := bodyRev.reverse ++ suffix
        } ∧
        DeclarativeGrammar.YulBlockItemsParses statementParses opening.span
          input.declarativeRemainder bodySpan suffix
            next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input body next diagnosticFree result
      simp [yulBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input body next diagnosticFree result
      unfold yulBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeYulBlock_success_sound opening bodyRev result with
            ⟨closingSpan, bodyEq, _closeGrammar, closingParsed⟩
          have inputFree := closeYulBlock_reflectsDiagnosticFreeOnSuccess
            opening bodyRev input body next result diagnosticFree
          exact ⟨SourceSpan.cover opening.span closingSpan, [],
            by simpa using bodyEq, .close closingSpan closingParsed,
            inputFree⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .yulStatement input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok item afterItem =>
                  simp only [statementResult] at result
                  by_cases progress : afterItem.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (item :: bodyRev) afterItem
                        body next diagnosticFree result with
                      ⟨bodySpan, suffix, bodyEq, tailGrammar,
                        afterItemFree⟩
                    have itemGrammar := statementSound afterItemFree
                      statementResult
                    have inputFree := statementReflects input item afterItem
                      statementResult afterItemFree
                    have notAtEnd : input.cursor < input.window.endIndex := by
                      simpa [State.atEnd] using ended
                    refine ⟨bodySpan, item :: suffix, ?_,
                      .next notAtEnd
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        itemGrammar progress tailGrammar,
                      inputFree⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction

/-- Every diagnostic-free public success follows the abstract block grammar. -/
theorem yulBlock_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {body : YulParsedBlock}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulBlock statement input = .ok body next) :
    DeclarativeGrammar.YulBlockParses statementParses
      input.declarativeRemainder body.span body.body
        next.declarativeRemainder := by
  unfold yulBlock at result
  cases openingResult : symbol .leftBrace .yulStatement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases yulBlockItems_success_sound statement statementParses
          statementReflects statementSound opening
          (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨bodySpan, suffix, bodyEq, bodyGrammar, afterOpeningFree⟩
      rw [bodyEq]
      simpa using DeclarativeGrammar.YulBlockParses.parsed opening.span
        (symbol_success_exactTokenParses .leftBrace .yulStatement
          openingResult) bodyGrammar

end Solcore.Syntax.Parser
