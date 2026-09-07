import Solcore.Syntax.Parser.StatementDiagnosticTraceContracts
import Solcore.Syntax.Parser.CoreBlockClosingTraceProperties

/-! Raw Core success traces from explicit statement soundness and context laws.
All statement events precede the single final whole-body validation pass. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Statement →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

/-- An arbitrary-fuel successful item loop preserves its reverse prefix and
records only fresh statement events, followed by validation of the entire body. -/
theorem coreBlockItems_success_trace_sound
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input body output,
      coreBlockItems statement opening policy fuel bodyRev input = .ok body output →
      ∃ closingSpan suffix statementEvents validationEvents,
        body = { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse ++ suffix } ∧
        DeclarativeGrammar.CoreBlockItemsTraceParses statementTrace input.file.id input.window.endByte
          input.declarativeRemainder suffix closingSpan output.declarativeRemainder statementEvents ∧
        DeclarativeGrammar.CoreBlockTailsDiagnosticTrace policy.declarative
          (bodyRev.reverse ++ suffix) validationEvents ∧
        output.diagnostics = input.diagnostics ++ (statementEvents ++ validationEvents) := by
  intro fuel
  induction fuel with
  | zero => intro bodyRev input body output result; simp [coreBlockItems] at result
  | succ fuel ih =>
      intro bodyRev input body output result
      unfold coreBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeCoreBlock_success_ordinary_sound opening policy bodyRev result with
            ⟨closingSpan, bodyEq, closingParsed⟩
          rcases closeCoreBlock_success_trace_sound opening policy bodyRev result with
            ⟨validationEvents, validated, diagnostics⟩
          refine ⟨closingSpan, [], [], validationEvents, ?_, .close closingSpan closingParsed, ?_, ?_⟩
          · simpa only [List.append_nil] using bodyEq
          · simpa only [List.append_nil] using validated
          · simpa only [List.nil_append] using diagnostics
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .statement input <;> simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok value next =>
                  simp only [statementResult] at result
                  by_cases progress : next.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases ih (value :: bodyRev) next body output result with
                      ⟨closingSpan, suffix, tailEvents, validationEvents, bodyEq,
                        tailParsed, validated, tailEq⟩
                    rcases successSound statementResult with ⟨headEvents, headParsed, headEq⟩
                    have frame := contextFrame statementResult
                    have tailAtInput : DeclarativeGrammar.CoreBlockItemsTraceParses
                        statementTrace input.file.id input.window.endByte next.declarativeRemainder
                        suffix closingSpan output.declarativeRemainder tailEvents := by
                      simpa only [frame.1, frame.2] using tailParsed
                    refine ⟨closingSpan, value :: suffix, headEvents ++ tailEvents,
                      validationEvents, ?_, .next (by
                        simpa [State.atEnd, State.declarativeRemainder] using ended)
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace closingPresent)
                        headParsed progress tailAtInput, ?_, ?_⟩
                    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using bodyEq
                    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using validated
                    · rw [tailEq, headEq]
                      simp only [List.append_assoc]
                  · simp only [progress, if_false] at result
                    contradiction

/-- Raw Core success has an independent exact block trace under abstract
statement contracts; no statement or block rejection premise is necessary. -/
theorem coreBlock_success_trace_sound
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy) :
    BlockTraceSuccessSound (coreBlock statement policy)
      (DeclarativeGrammar.CoreBlockTraceParses statementTrace policy.declarative) := by
  intro input output body result
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases coreBlockItems_success_trace_sound successSound contextFrame opening policy
          (afterOpening.remainingCount + 1) [] afterOpening body output result with
        ⟨closingSpan, suffix, statementEvents, validationEvents, bodyEq,
          itemsParsed, validated, diagnostics⟩
      have openingShape := (symbol_ok_tokenAt .leftBrace .statement openingResult).2
      have openingParsed := symbol_success_exactTokenParses .leftBrace .statement openingResult
      simp only [List.reverse_nil, List.nil_append] at bodyEq validated
      subst body
      refine ⟨statementEvents ++ validationEvents, .parsed opening.span closingSpan openingParsed ?_
        validated, ?_⟩
      · simpa only [openingShape] using itemsParsed
      · simpa only [openingShape, State.diagnostics] using diagnostics

end Solcore.Syntax.Parser
