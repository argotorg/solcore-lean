import Solcore.Syntax.Parser.Block

/-!
Diagnostic reflection and exact declarative soundness for raw Core blocks.

This module covers `coreBlock` inside one active token window.  Balanced-block
isolation is intentionally handled by a separate grammar bridge.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Successful block-loop execution recovers the forward suffix appended after its
existing reverse accumulator, together with exact closing-brace recognition.
-/
private theorem coreBlockItems_success_sound_strong
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statement : Parser Statement)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {statementInput statementNext : State}
      {value : Statement}, statementNext.diagnosticsRev = [] →
      statement statementInput = .ok value statementNext →
      statementParses statementInput.declarativeRemainder value
        statementNext.declarativeRemainder)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input body next,
      next.diagnosticsRev = [] →
      coreBlockItems statement opening policy fuel bodyRev input =
        .ok body next →
      ∃ statements closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          value := bodyRev.reverse ++ statements
        } ∧
        DeclarativeGrammar.CoreBlockItemsParses statementParses
          input.declarativeRemainder statements closingSpan
            next.declarativeRemainder ∧
        DeclarativeGrammar.CoreBlockTailsValid policy.declarative
          (bodyRev.reverse ++ statements) ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input body next diagnosticFree result
      simp [coreBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input body next diagnosticFree result
      unfold coreBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeCoreBlock_success_sound_and_reflects opening policy
              bodyRev diagnosticFree result with
            ⟨closingSpan, bodyEq, closingGrammar, tailsValid, inputFree⟩
          exact ⟨[], closingSpan, by simpa using bodyEq,
            .close closingSpan closingGrammar, by simpa using tailsValid,
            inputFree⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .statement input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok value afterStatement =>
                  simp only [statementResult] at result
                  by_cases progress : afterStatement.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (value :: bodyRev)
                        afterStatement body next diagnosticFree result with
                      ⟨statements, closingSpan, bodyEq, tailGrammar,
                        tailsValid, afterStatementFree⟩
                    have statementGrammar :=
                      statementSound afterStatementFree statementResult
                    have inputFree := statementReflects input value
                      afterStatement statementResult afterStatementFree
                    have notAtEnd :
                        input.cursor < input.window.endIndex := by
                      simpa [State.atEnd] using ended
                    refine ⟨value :: statements, closingSpan, ?_,
                      .next notAtEnd
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        statementGrammar progress tailGrammar,
                      ?_, inputFree⟩
                    · simpa [List.reverse_cons, List.append_assoc] using bodyEq
                    · simpa [List.reverse_cons, List.append_assoc] using
                        tailsValid
                  · simp only [progress, if_false] at result
                    contradiction

/-- Raw Core-block parsing cannot erase an incoming diagnostic. -/
theorem coreBlock_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess (coreBlock statement policy) := by
  intro input body next result diagnosticFree
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      let trivialParses : DeclarativeGrammar.Remainder → Statement →
          DeclarativeGrammar.Remainder → Prop := fun _ _ _ => True
      have trivialSound : ∀ {statementInput statementNext : State}
          {value : Statement}, statementNext.diagnosticsRev = [] →
          statement statementInput = .ok value statementNext →
          trivialParses statementInput.declarativeRemainder value
            statementNext.declarativeRemainder := by
        intro statementInput statementNext value outputFree parsed
        trivial
      rcases coreBlockItems_success_sound_strong trivialParses statement
          statementReflects trivialSound opening policy
          (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨statements, closingSpan, bodyEq, tailGrammar, tailsValid,
          afterOpeningFree⟩
      exact symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .statement input
        opening afterOpening openingResult afterOpeningFree

/--
Every diagnostic-free successful raw Core block follows the exact braced
statement grammar and satisfies its executable tail-semicolon policy.
-/
theorem coreBlock_success_sound
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {statementInput statementNext : State}
      {value : Statement}, statementNext.diagnosticsRev = [] →
      statement statementInput = .ok value statementNext →
      statementParses statementInput.declarativeRemainder value
        statementNext.declarativeRemainder)
    {input next : State} {body : Block}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : coreBlock statement policy input = .ok body next) :
    DeclarativeGrammar.CoreBlockParses statementParses policy.declarative
      input.declarativeRemainder body next.declarativeRemainder := by
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases coreBlockItems_success_sound_strong statementParses statement
          statementReflects statementSound opening policy
          (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨statements, closingSpan, bodyEq, bodyGrammar, tailsValid,
          afterOpeningFree⟩
      rw [bodyEq]
      simpa using DeclarativeGrammar.CoreBlockParses.parsed opening.span
        closingSpan
        (symbol_success_exactTokenParses .leftBrace .statement openingResult)
        bodyGrammar tailsValid

end Solcore.Syntax.Parser
