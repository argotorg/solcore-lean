import Solcore.Syntax.Parser.CoreBlockTraceSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Exact raw Core success traces from explicit statement completeness and
context laws. Production fuel suffices by strict cursor progress alone. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Statement →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem closing_present {input : State} {span : SourceSpan}
    {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
      input.declarativeRemainder span after) : isSymbol input .rightBrace = true := by
  have token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .rightBrace } := parsed.1
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  rfl

private theorem closing_absent {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol .rightBrace)) : isSymbol input .rightBrace = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .statement present with ⟨token, result⟩
  exact absent ⟨token.span, (symbol_ok_tokenAt .rightBrace .statement result).1⟩

/-- Sufficient remaining-token fuel executes any independent successful suffix.
The existing reverse prefix participates once in the final whole-body check. -/
theorem coreBlockItems_trace_success_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy)
    (fuel : Nat) (bodyRev : List Statement)
    {input : State} {suffix : List Statement} {closingSpan : SourceSpan}
    {remainder : DeclarativeGrammar.Remainder}
    {statementEvents validationEvents : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.CoreBlockItemsTraceParses statementTrace
      input.file.id input.window.endByte input.declarativeRemainder suffix
      closingSpan remainder statementEvents)
    (validated : DeclarativeGrammar.CoreBlockTailsDiagnosticTrace
      policy.declarative (bodyRev.reverse ++ suffix) validationEvents)
    (adequate : input.remainingCount < fuel) :
    ∃ output, coreBlockItems statement opening policy fuel bodyRev input = .ok {
        span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse ++ suffix
      } output ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ (statementEvents ++ validationEvents) := by
  induction fuel generalizing bodyRev input suffix closingSpan remainder
      statementEvents validationEvents with
  | zero => omega
  | succ fuel ih =>
      cases parsed with
      | close span closing =>
          rcases (closeCoreBlock_trace_success_iff opening policy bodyRev).mp
              ⟨⟨closingSpan, closing, rfl⟩, by simpa only [List.append_nil] using validated⟩ with
            ⟨output, result, after, diagnostics⟩
          refine ⟨output, ?_, after, ?_⟩
          · simpa only [coreBlockItems, closing_present closing, if_true, List.append_nil]
              using result
          · simpa only [List.nil_append] using diagnostics
      | next inside absent headParsed progress tailParsed =>
          rename_i afterStatement head tail headEvents tailEvents
          rcases successComplete headParsed with ⟨next, headResult, afterEq, headEq⟩
          have frame := contextFrame headResult
          have nextProgress : input.cursor < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have notEnded : input.atEnd = false :=
            decide_eq_false (Nat.not_le_of_gt inside)
          have tailAtNext : DeclarativeGrammar.CoreBlockItemsTraceParses statementTrace
              next.file.id next.window.endByte next.declarativeRemainder tail
              closingSpan remainder tailEvents := by
            simpa only [frame.1, frame.2, afterEq] using tailParsed
          have nextAdequate : next.remainingCount < fuel := by
            change input.cursor < input.window.endIndex at inside
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          have tailValidated : DeclarativeGrammar.CoreBlockTailsDiagnosticTrace
              policy.declarative ((head :: bodyRev).reverse ++ tail) validationEvents := by
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using validated
          rcases ih (head :: bodyRev) tailAtNext tailValidated nextAdequate with
            ⟨output, tailResult, outputAfter, outputEq⟩
          refine ⟨output, ?_, outputAfter, ?_⟩
          · simp only [coreBlockItems, closing_absent absent, Bool.false_eq_true, if_false,
              notEnded, headResult, nextProgress, if_true]
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using tailResult
          · rw [outputEq, headEq]
            simp only [List.append_assoc]

/-- The production loop bound suffices without valid-state or initially empty
diagnostic assumptions, and retains every appended event in its written order. -/
theorem coreBlockItems_production_trace_success_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {suffix : List Statement} {closingSpan : SourceSpan}
    {remainder : DeclarativeGrammar.Remainder}
    {statementEvents validationEvents : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.CoreBlockItemsTraceParses statementTrace
      input.file.id input.window.endByte input.declarativeRemainder suffix
      closingSpan remainder statementEvents)
    (validated : DeclarativeGrammar.CoreBlockTailsDiagnosticTrace
      policy.declarative (bodyRev.reverse ++ suffix) validationEvents) :
    ∃ output, coreBlockItems statement opening policy (input.remainingCount + 1) bodyRev input =
      .ok { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse ++ suffix }
        output ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ (statementEvents ++ validationEvents) :=
  coreBlockItems_trace_success_complete successComplete contextFrame opening policy
    (input.remainingCount + 1) bodyRev parsed validated (by omega)

/-- Independent raw-block traces execute exactly under the explicit inner
statement completeness and source/full-window context contracts. -/
theorem coreBlock_trace_success_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy) :
    BlockTraceSuccessComplete (coreBlock statement policy)
      (DeclarativeGrammar.CoreBlockTraceParses statementTrace policy.declarative) := by
  intro input body remainder trace parsed
  cases parsed with
  | parsed opening closing openingParsed itemsParsed validated =>
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftBrace .statement openingParsed
      rcases openingParsed with ⟨openingToken, rfl⟩
      rcases coreBlockItems_production_trace_success_complete successComplete contextFrame
          { span := opening, value := .symbol .leftBrace } policy []
          (input := { input with cursor := input.cursor + 1 })
          itemsParsed (by simpa only [List.reverse_nil, List.nil_append] using validated) with
        ⟨output, result, afterEq, diagnostics⟩
      refine ⟨output, ?_, afterEq, ?_⟩
      · simpa only [coreBlock, openingResult, List.reverse_nil, List.nil_append] using result
      · exact diagnostics

/-- Complete raw Core success is equivalent to its independent AST, remainder,
and appended trace. All assumptions are explicit abstract statement contracts. -/
theorem coreBlock_trace_success_iff
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy)
    {input : State} {body : Block} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.CoreBlockTraceParses statementTrace policy.declarative
      input.file.id input.window.endByte input.declarativeRemainder body remainder trace ↔
    ∃ output, coreBlock statement policy input = .ok body output ∧
      output.declarativeRemainder = remainder ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact coreBlock_trace_success_complete successComplete contextFrame policy
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases coreBlock_success_trace_sound successSound contextFrame policy result with
      ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

/-- The item loop also has an exact production-fuel equivalence, retaining its
arbitrary reverse prefix and the split between fresh and final-check events. -/
theorem coreBlockItems_production_trace_success_iff
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {body : Block} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    (∃ closingSpan suffix statementEvents validationEvents,
      body = { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse ++ suffix } ∧
      DeclarativeGrammar.CoreBlockItemsTraceParses statementTrace input.file.id input.window.endByte
        input.declarativeRemainder suffix closingSpan remainder statementEvents ∧
      DeclarativeGrammar.CoreBlockTailsDiagnosticTrace policy.declarative
        (bodyRev.reverse ++ suffix) validationEvents ∧ trace = statementEvents ++ validationEvents) ↔
    ∃ output, coreBlockItems statement opening policy (input.remainingCount + 1) bodyRev input =
      .ok body output ∧ output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨closingSpan, suffix, statementEvents, validationEvents, rfl, parsed, validated, rfl⟩
    exact coreBlockItems_production_trace_success_complete successComplete contextFrame
      opening policy bodyRev parsed validated
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases coreBlockItems_success_trace_sound successSound contextFrame opening policy
        (input.remainingCount + 1) bodyRev input body output result with
      ⟨closingSpan, suffix, statementEvents, validationEvents, bodyEq, parsed, validated, actualEq⟩
    exact ⟨closingSpan, suffix, statementEvents, validationEvents, bodyEq,
      afterEq ▸ parsed, validated, List.append_cancel_left (diagnostics.symm.trans actualEq)⟩

end Solcore.Syntax.Parser
