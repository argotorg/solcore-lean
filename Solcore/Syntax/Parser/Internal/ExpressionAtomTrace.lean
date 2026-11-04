import Solcore.Syntax.Internal.ExpressionTrace
import Solcore.Syntax.Parser.Internal.ExpressionProofs
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Internal.NameTrace
import Solcore.Syntax.Parser.Internal.TypeTrace
import Solcore.Syntax.Parser.Internal.BlockTrace
import Solcore.Syntax.Parser.Internal.ExpressionAtomProofs
import Solcore.Syntax.Internal.DotConstructorTrace
import Solcore.Syntax.Parser.Internal.DelimitedTrace
import Solcore.Syntax.Parser.Internal.LambdaTrace
import Solcore.Syntax.Parser.Internal.ParenthesizedTrace
import Solcore.Syntax.Internal.BlockTrace
import Solcore.Syntax.Parser.Internal.PostfixTrace

/-!
Parser side of the traces of expression atoms and names: the parsers produce exactly the
events of the trace grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.LiteralSuccessTraceProperties
/-! Exact ASTs, silent traces, and one-token state updates for literal leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem peek_of_token {input : State} {token : Token}
    (present : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor token) :
    input.peek? = some token := by
  simp only [State.peek?, present.1, if_true, present.2]

theorem coreLiteral_eq_ok_of_ordinary
    {input : State} {literal : CoreLiteral} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.CoreLiteralParses input.declarativeRemainder literal after) :
    coreLiteral input = .ok literal { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | decimal token => simp only [coreLiteral, peek_of_token token]
  | hexadecimal token => simp only [coreLiteral, peek_of_token token]
  | string token => simp only [coreLiteral, peek_of_token token]

theorem booleanIdentifier_eq_ok_of_ordinary
    {input : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.BooleanIdentifierParses input.declarativeRemainder name after) :
    booleanIdentifier input = .ok name { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | trueKeyword token => simp only [booleanIdentifier, peek_of_token token]
  | falseKeyword token => simp only [booleanIdentifier, peek_of_token token]

theorem coreLiteral_success_diagnostics_eq
    {input output : State} {literal : CoreLiteral}
    (result : coreLiteral input = .ok literal output) : output.diagnostics = input.diagnostics := by
  rw [coreLiteral_ok_state_shape result]
  rfl

theorem booleanIdentifier_success_diagnostics_eq
    {input output : State} {name : Identifier}
    (result : booleanIdentifier input = .ok name output) : output.diagnostics = input.diagnostics := by
  rw [booleanIdentifier_ok_state_shape result]
  rfl

theorem coreLiteral_trace_success_iff
    {input : State} {literal : CoreLiteral} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.CoreLiteralTraceParses input.file.id input.window.endByte
      input.declarativeRemainder literal after trace ↔
    ∃ output, coreLiteral input = .ok literal output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨parsed, rfl⟩
    exact ⟨_, coreLiteral_eq_ok_of_ordinary parsed,
      (DeclarativeGrammar.CoreLiteralOrdinaryParses.output_eq parsed).symm,
      by simp only [List.append_nil, State.diagnostics]⟩
  · rintro ⟨output, result, afterEq, diagnostics⟩
    refine ⟨afterEq ▸ coreLiteral_success_sound result, ?_⟩
    apply List.append_cancel_left (as := input.diagnostics)
    simpa only [List.append_nil] using diagnostics.symm.trans (coreLiteral_success_diagnostics_eq result)

theorem booleanIdentifier_trace_success_iff
    {input : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BooleanIdentifierTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace ↔
    ∃ output, booleanIdentifier input = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨parsed, rfl⟩
    refine ⟨_, booleanIdentifier_eq_ok_of_ordinary parsed, ?_,
      by simp only [List.append_nil, State.diagnostics]⟩
    cases parsed <;> rfl
  · rintro ⟨output, result, afterEq, diagnostics⟩
    refine ⟨afterEq ▸ booleanIdentifier_success_sound result, ?_⟩
    apply List.append_cancel_left (as := input.diagnostics)
    simpa only [List.append_nil] using
      diagnostics.symm.trans (booleanIdentifier_success_diagnostics_eq result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLiteralRejectionTraceProperties
/-! Exact silent Core-literal rejection, retaining the complete input state. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem coreLiteral_eq_rejectAt_of_absence {input : State}
    (absent : DeclarativeGrammar.CoreLiteralAbsentAt input.declarativeRemainder) :
    coreLiteral input = rejectAt input { head := .coreLiteral, tail := [] } .expression := by
  unfold coreLiteral
  cases found : input.peek? with
  | none => rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> try rfl
      case decimalLiteral spelling =>
        exact False.elim (absent.1 ⟨span, spelling, tokenAt_of_peek?_eq_some found⟩)
      case hexadecimalLiteral spelling =>
        exact False.elim (absent.2.1 ⟨span, spelling, tokenAt_of_peek?_eq_some found⟩)
      case stringLiteral spelling =>
        exact False.elim (absent.2.2 ⟨span, spelling, tokenAt_of_peek?_eq_some found⟩)

theorem coreLiteral_reject_trace_sound {input rejected : State} {failure : Failure}
    (result : coreLiteral input = .reject failure rejected) :
    DeclarativeGrammar.CoreLiteralTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic [] ∧ rejected = input := by
  have same := coreLiteral_reject_state_eq result
  subst rejected
  have absent := coreLiteral_reject_coreLiteralAbsentAt result
  have direct := (coreLiteral_eq_rejectAt_of_absence absent).symm.trans result
  exact ⟨⟨.absent absent, (rejectAt_reports_iff (alpha := CoreLiteral)).mpr
    ⟨failure, direct, rfl⟩, rfl⟩, rfl⟩

/-- Exact rejection fixes the whole retained state, empty emitted trace,
remainder, and full report under the literal-specific expectation. -/
theorem coreLiteral_trace_reject_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.CoreLiteralTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure, coreLiteral input = .reject failure input ∧
      after = input.declarativeRemainder ∧ failure.toDiagnostic = diagnostic ∧ trace = [] := by
  constructor
  · rintro ⟨ordinary, reported, events⟩
    cases ordinary with
    | absent absent =>
        rcases (rejectAt_reports_iff (alpha := CoreLiteral)).mp reported with ⟨failure, result, reportEq⟩
        exact ⟨failure, (coreLiteral_eq_rejectAt_of_absence absent).trans result, rfl, reportEq, events⟩
  · rintro ⟨failure, result, rfl, rfl, rfl⟩
    exact (coreLiteral_reject_trace_sound result).1

theorem coreLiteral_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.CoreLiteralTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    coreLiteral input = .reject failure input ∧ after = input.declarativeRemainder ∧ trace = [] := by
  constructor
  · intro traced
    rcases coreLiteral_trace_reject_iff.mp traced with ⟨actual, result, afterEq, reportEq, events⟩
    have same := Failure.toDiagnostic_injective reportEq
    subst actual
    exact ⟨result, afterEq, events⟩
  · rintro ⟨result, afterEq, events⟩
    exact coreLiteral_trace_reject_iff.mpr ⟨failure, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.LiteralExpressionTraceProperties
/-! Five unconditional expression trace contracts for the real literal leaf. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem literalExpression_eq_ok_of_ordinary
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.LiteralExpressionParses input.declarativeRemainder value after) :
    literalExpression input = .ok value { input with cursor := input.cursor + 1 } := by
  cases parsed with
  | parsed literalParsed =>
      simp only [literalExpression, bind, coreLiteral_eq_ok_of_ordinary literalParsed, pure]

theorem literalExpression_success_state_shape
    {input output : State} {value : Expr}
    (result : literalExpression input = .ok value output) :
    output = { input with cursor := input.cursor + 1 } := by
  have actual := literalExpression_eq_ok_of_ordinary (literalExpression_success_sound result)
  rw [result] at actual
  exact (Reply.ok.inj actual).2

theorem literalExpression_trace_success_sound :
    ExpressionTraceSuccessSound literalExpression DeclarativeGrammar.LiteralExpressionTraceParses := by
  intro input output value result
  refine ⟨[], ⟨literalExpression_success_sound result, rfl⟩, ?_⟩
  rw [literalExpression_success_state_shape result]
  simp only [List.append_nil, State.diagnostics]

theorem literalExpression_trace_success_complete :
    ExpressionTraceSuccessComplete literalExpression DeclarativeGrammar.LiteralExpressionTraceParses := by
  intro input value after trace traced
  rcases traced with ⟨parsed, rfl⟩
  exact ⟨_, literalExpression_eq_ok_of_ordinary parsed,
    (DeclarativeGrammar.LiteralExpressionOrdinaryParses.output_eq parsed).symm,
    by simp only [List.append_nil, State.diagnostics]⟩

theorem literalExpression_success_context : ExpressionSuccessContext literalExpression := by
  intro input output value result
  rw [literalExpression_success_state_shape result]
  exact ⟨rfl, rfl⟩

theorem literalExpression_reject_iff_coreLiteral
    {input rejected : State} {failure : Failure} :
    literalExpression input = .reject failure rejected ↔
      coreLiteral input = .reject failure rejected := by
  cases result : coreLiteral input <;>
    simp only [literalExpression, bind, result, pure, reduceCtorEq, Reply.reject.injEq, iff_self]

theorem literalExpression_trace_reject_sound :
    ExpressionTraceRejectSound literalExpression DeclarativeGrammar.LiteralExpressionTraceRejects := by
  intro input rejected failure result
  have raw := literalExpression_reject_iff_coreLiteral.mp result
  have traced := coreLiteral_reject_trace_sound raw
  exact ⟨[], traced.1, by rw [traced.2]; simp only [List.append_nil]⟩

theorem literalExpression_trace_reject_complete :
    ExpressionTraceRejectComplete literalExpression DeclarativeGrammar.LiteralExpressionTraceRejects := by
  intro input after diagnostic trace traced
  rcases coreLiteral_trace_reject_iff.mp traced with ⟨failure, result, afterEq, reportEq, rfl⟩
  exact ⟨failure, input, literalExpression_reject_iff_coreLiteral.mpr result, afterEq.symm,
    reportEq, by simp only [List.append_nil]⟩

theorem literalExpression_trace_success_iff
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.LiteralExpressionTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, literalExpression input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact literalExpression_trace_success_complete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases literalExpression_trace_success_sound result with ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

/-- The real expression wrapper retains the primitive's full failure and input
state, including the literal-specific expectation and all prior diagnostics. -/
theorem literalExpression_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.LiteralExpressionTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    literalExpression input = .reject failure input ∧
      after = input.declarativeRemainder ∧ trace = [] := by
  rw [literalExpression_reject_iff_coreLiteral]
  exact coreLiteral_trace_reject_failure_iff

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.BooleanIdentifierRejectionTraceProperties
/-! Exact Boolean rejection retains the whole input and expression expectation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem booleanIdentifier_eq_rejectAt_of_absence {input : State}
    (absent : DeclarativeGrammar.BooleanPatternAbsentAt input.declarativeRemainder) :
    booleanIdentifier input = rejectAt input { head := .expression, tail := [] } .expression := by
  unfold booleanIdentifier
  cases found : input.peek? with
  | none => rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> try rfl
      case keyword keyword =>
        cases keyword <;> try rfl
        case trueKw => exact False.elim (absent.1 ⟨span, tokenAt_of_peek?_eq_some found⟩)
        case falseKw => exact False.elim (absent.2 ⟨span, tokenAt_of_peek?_eq_some found⟩)

theorem booleanIdentifier_reject_absent {input rejected : State} {failure : Failure}
    (result : booleanIdentifier input = .reject failure rejected) :
    DeclarativeGrammar.BooleanPatternAbsentAt input.declarativeRemainder := by
  constructor
  · rintro ⟨span, token⟩
    have success := booleanIdentifier_eq_ok_of_ordinary (.trueKeyword token)
    rw [success] at result
    contradiction
  · rintro ⟨span, token⟩
    have success := booleanIdentifier_eq_ok_of_ordinary (.falseKeyword token)
    rw [success] at result
    contradiction

theorem booleanIdentifier_reject_state_eq {input rejected : State} {failure : Failure}
    (result : booleanIdentifier input = .reject failure rejected) : rejected = input := by
  rw [booleanIdentifier_eq_rejectAt_of_absence (booleanIdentifier_reject_absent result)] at result
  unfold rejectAt at result
  cases result
  rfl

theorem booleanIdentifier_reject_trace_sound {input rejected : State} {failure : Failure}
    (result : booleanIdentifier input = .reject failure rejected) :
    DeclarativeGrammar.BooleanIdentifierTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic [] ∧ rejected = input := by
  have same := booleanIdentifier_reject_state_eq result
  subst rejected
  have absent := booleanIdentifier_reject_absent result
  have direct := (booleanIdentifier_eq_rejectAt_of_absence absent).symm.trans result
  exact ⟨⟨absent, rfl, (rejectAt_reports_iff (alpha := Identifier)).mpr
    ⟨failure, direct, rfl⟩, rfl⟩, rfl⟩

theorem booleanIdentifier_trace_reject_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BooleanIdentifierTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure, booleanIdentifier input = .reject failure input ∧
      after = input.declarativeRemainder ∧ failure.toDiagnostic = diagnostic ∧ trace = [] := by
  constructor
  · rintro ⟨absent, rfl, reported, events⟩
    rcases (rejectAt_reports_iff (alpha := Identifier)).mp reported with ⟨failure, result, reportEq⟩
    exact ⟨failure, (booleanIdentifier_eq_rejectAt_of_absence absent).trans result, rfl, reportEq, events⟩
  · rintro ⟨failure, result, rfl, rfl, rfl⟩
    exact (booleanIdentifier_reject_trace_sound result).1

theorem booleanIdentifier_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BooleanIdentifierTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    booleanIdentifier input = .reject failure input ∧ after = input.declarativeRemainder ∧ trace = [] := by
  constructor
  · intro traced
    rcases booleanIdentifier_trace_reject_iff.mp traced with ⟨actual, result, afterEq, reportEq, events⟩
    have same := Failure.toDiagnostic_injective reportEq
    subst actual
    exact ⟨result, afterEq, events⟩
  · rintro ⟨result, afterEq, events⟩
    exact booleanIdentifier_trace_reject_iff.mpr ⟨failure, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionNameTraceProperties
/-! Exact Boolean-first expression-name success with checked spelling events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem isBooleanValue_true_of_booleanParses
    {input : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.BooleanIdentifierParses input.declarativeRemainder name after) :
    isBooleanValue input = true := by
  cases parsed with
  | trueKeyword token =>
      rename_i span
      change input.cursor < input.window.endIndex ∧
        input.tokens[input.cursor]? = some { span, value := .keyword .trueKw } at token
      have found : input.peek? = some { span, value := .keyword .trueKw } := by
        simp only [State.peek?, token.1, if_true, token.2]
      simp only [isBooleanValue, isKeyword, State.peekKind?, found, Option.map_some]
      rfl
  | falseKeyword token =>
      rename_i span
      change input.cursor < input.window.endIndex ∧
        input.tokens[input.cursor]? = some { span, value := .keyword .falseKw } at token
      have found : input.peek? = some { span, value := .keyword .falseKw } := by
        simp only [State.peek?, token.1, if_true, token.2]
      simp only [isBooleanValue, isKeyword, State.peekKind?, found, Option.map_some]
      rfl

theorem isBooleanValue_false_of_absent {input : State}
    (absent : DeclarativeGrammar.BooleanPatternAbsentAt input.declarativeRemainder) :
    isBooleanValue input = false := by
  unfold isBooleanValue isKeyword State.peekKind?
  cases found : input.peek? with
  | none => rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> try rfl
      case keyword keyword =>
        cases keyword <;> try rfl
        case trueKw => exact False.elim (absent.1 ⟨span, tokenAt_of_peek?_eq_some found⟩)
        case falseKw => exact False.elim (absent.2 ⟨span, tokenAt_of_peek?_eq_some found⟩)

theorem booleanAbsent_of_isBooleanValue_false {input : State}
    (absent : isBooleanValue input = false) :
    DeclarativeGrammar.BooleanPatternAbsentAt input.declarativeRemainder := by
  have both := Bool.or_eq_false_iff.mp absent
  exact ⟨keywordAbsentAt_of_isKeyword_eq_false .trueKw both.1,
    keywordAbsentAt_of_isKeyword_eq_false .falseKw both.2⟩

theorem expressionName_eq_identifier_of_booleanAbsent {input : State}
    (absent : DeclarativeGrammar.BooleanPatternAbsentAt input.declarativeRemainder) :
    expressionName input = identifier .expression input := by
  simp only [expressionName, isBooleanValue_false_of_absent absent, Bool.false_eq_true, if_false]

theorem expressionName_success_trace_sound
    {input output : State} {name : Identifier}
    (result : expressionName input = .ok name output) :
    ∃ trace, DeclarativeGrammar.ExpressionNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  unfold expressionName at result
  cases present : isBooleanValue input with
  | true =>
      simp only [present, if_true] at result
      exact ⟨[], .boolean ⟨booleanIdentifier_success_sound result, rfl⟩,
        by simpa only [List.append_nil] using booleanIdentifier_success_diagnostics_eq result⟩
  | false =>
      simp only [present, Bool.false_eq_true, if_false] at result
      rcases identifier_success_trace_sound .expression result with ⟨trace, parsed, events⟩
      exact ⟨trace, .identifier (booleanAbsent_of_isBooleanValue_false present) parsed, events⟩

theorem expressionName_trace_success_complete
    {input : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.ExpressionNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace) :
    ∃ output, expressionName input = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  cases parsed with
  | boolean parsed =>
      rcases booleanIdentifier_trace_success_iff.mp parsed with ⟨output, result, afterEq, events⟩
      exact ⟨output, by simp only [expressionName, isBooleanValue_true_of_booleanParses parsed.1,
        if_true, result], afterEq, events⟩
  | identifier absent parsed =>
      rcases (identifier_trace_success_iff .expression).mp parsed with ⟨output, result, afterEq, events⟩
      exact ⟨output, (expressionName_eq_identifier_of_booleanAbsent absent).trans result, afterEq, events⟩

theorem expressionName_success_context_eq
    {input output : State} {name : Identifier}
    (result : expressionName input = .ok name output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold expressionName at result
  split at result
  · rw [booleanIdentifier_ok_state_shape result]; exact ⟨rfl, rfl⟩
  · exact identifier_success_context_eq .expression result

theorem expressionName_trace_success_iff
    {input : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ExpressionNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace ↔
    ∃ output, expressionName input = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionName_trace_success_complete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases expressionName_success_trace_sound result with ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

/-- An independent name trace fixes the entire output state: exactly one
token advance and the reversed fresh trace prepended to prior reverse events. -/
theorem expressionName_success_state_eq_of_trace
    {input output : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (result : expressionName input = .ok name output)
    (parsed : DeclarativeGrammar.ExpressionNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace) :
    output = { input with
      cursor := input.cursor + 1
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases expressionName_success_trace_sound result with ⟨actualTrace, actual, actualEq⟩
  have same := actual.result_unique parsed
  have remaining := actual.output_eq
  have tokensEq : output.tokens = input.tokens :=
    congrArg DeclarativeGrammar.Remainder.tokens remaining
  have cursorEq : output.cursor = input.cursor + 1 :=
    congrArg DeclarativeGrammar.Remainder.cursor remaining
  have frame := expressionName_success_context_eq result
  have events := congrArg List.reverse actualEq
  have diagnosticsEq : output.diagnosticsRev = trace.reverse ++ input.diagnosticsRev := by
    simpa only [same.2.2, State.diagnostics, List.reverse_append, List.reverse_reverse] using events
  cases input
  cases output
  simp_all only [State.declarativeRemainder]

theorem expressionName_eq_ok_of_trace
    {input : State} {name : Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.ExpressionNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace) :
    expressionName input = .ok name { input with
      cursor := input.cursor + 1
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases expressionName_trace_success_complete parsed with ⟨output, result, _, _⟩
  exact expressionName_success_state_eq_of_trace result parsed ▸ result

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionNameRejectionTraceProperties
/-! Exact identifier fallback failure after both Boolean guards are absent. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem expressionName_reject_trace_sound
    {input rejected : State} {failure : Failure}
    (result : expressionName input = .reject failure rejected) :
    DeclarativeGrammar.ExpressionNameTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic [] ∧ rejected = input := by
  have ordinary := expressionName_reject_ordinary_sound result
  have classify : ∀ {before after : DeclarativeGrammar.Remainder},
      DeclarativeGrammar.ExpressionNameRejects before after →
        DeclarativeGrammar.BooleanPatternAbsentAt before := by
    intro before after rejected
    cases rejected with
    | absent missing => exact ⟨missing.1, missing.2.1⟩
  have absent := classify ordinary
  have checked := (expressionName_eq_identifier_of_booleanAbsent absent).symm.trans result
  have shape := identifier_reject_state_eq .expression checked
  subst rejected
  have reported := (identifier_reject_reports_iff .expression).mpr ⟨failure, checked, rfl⟩
  exact ⟨⟨absent, .absent reported.1, reported.2, rfl⟩, rfl⟩

/-- Boolean-first rejection retains the entire input state, reports an
identifier expectation in expression context, and emits no spelling event. -/
theorem expressionName_trace_reject_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ExpressionNameTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure, expressionName input = .reject failure input ∧
      after = input.declarativeRemainder ∧ failure.toDiagnostic = diagnostic ∧ trace = [] := by
  constructor
  · rintro ⟨booleanAbsent, nameRejected, reported, events⟩
    cases nameRejected with
    | absent absent =>
        rcases (identifier_reject_reports_iff .expression).mp ⟨absent, reported⟩ with
          ⟨failure, result, reportEq⟩
        exact ⟨failure, (expressionName_eq_identifier_of_booleanAbsent booleanAbsent).trans result,
          rfl, reportEq, events⟩
  · rintro ⟨failure, result, rfl, rfl, rfl⟩
    exact (expressionName_reject_trace_sound result).1

theorem expressionName_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ExpressionNameTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    expressionName input = .reject failure input ∧ after = input.declarativeRemainder ∧ trace = [] := by
  constructor
  · intro traced
    rcases expressionName_trace_reject_iff.mp traced with ⟨actual, result, afterEq, reportEq, events⟩
    have same := Failure.toDiagnostic_injective reportEq
    subst actual
    exact ⟨result, afterEq, events⟩
  · rintro ⟨result, afterEq, events⟩
    exact expressionName_trace_reject_iff.mpr ⟨failure, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.IdentifierExpressionTraceProperties
/-! Unconditional trace contracts for the real Boolean/identifier expression
leaf. This does not assert contracts for general recursive Core expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem identifierExpression_eq_ok_of_trace
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.IdentifierExpressionTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    identifierExpression input = .ok value { input with
      cursor := input.cursor + 1
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases parsed with
  | parsed nameParsed =>
      simp only [identifierExpression, bind, expressionName_eq_ok_of_trace nameParsed, pure]

theorem identifierExpression_success_state_eq_of_trace
    {input output : State} {value : Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (result : identifierExpression input = .ok value output)
    (parsed : DeclarativeGrammar.IdentifierExpressionTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    output = { input with
      cursor := input.cursor + 1
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  have expected := identifierExpression_eq_ok_of_trace parsed
  rw [result] at expected
  exact (Reply.ok.inj expected).2

theorem identifierExpression_trace_success_sound :
    ExpressionTraceSuccessSound identifierExpression DeclarativeGrammar.IdentifierExpressionTraceParses := by
  intro input output value result
  unfold identifierExpression at result
  cases nameResult : expressionName input with
  | invariant error => simp [bind, nameResult] at result
  | reject failure rejected => simp [bind, nameResult] at result
  | ok name next =>
      simp only [bind, nameResult, pure] at result
      cases result
      rcases expressionName_success_trace_sound nameResult with ⟨trace, parsed, events⟩
      exact ⟨trace, .parsed parsed, events⟩

theorem identifierExpression_trace_success_complete :
    ExpressionTraceSuccessComplete identifierExpression DeclarativeGrammar.IdentifierExpressionTraceParses := by
  intro input value after trace parsed
  refine ⟨_, identifierExpression_eq_ok_of_trace parsed, ?_, ?_⟩
  · cases parsed with
    | parsed nameParsed => exact nameParsed.output_eq.symm
  · simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem identifierExpression_success_context : ExpressionSuccessContext identifierExpression := by
  intro input output value result
  rcases identifierExpression_trace_success_sound result with ⟨trace, parsed, _⟩
  rw [identifierExpression_success_state_eq_of_trace result parsed]
  exact ⟨rfl, rfl⟩

theorem identifierExpression_reject_iff_expressionName
    {input rejected : State} {failure : Failure} :
    identifierExpression input = .reject failure rejected ↔
      expressionName input = .reject failure rejected := by
  cases result : expressionName input <;>
    simp only [identifierExpression, bind, result, pure, reduceCtorEq, Reply.reject.injEq, iff_self]

theorem identifierExpression_trace_reject_sound :
    ExpressionTraceRejectSound identifierExpression DeclarativeGrammar.IdentifierExpressionTraceRejects := by
  intro input rejected failure result
  have raw := identifierExpression_reject_iff_expressionName.mp result
  have traced := expressionName_reject_trace_sound raw
  exact ⟨[], traced.1, by rw [traced.2]; simp only [List.append_nil]⟩

theorem identifierExpression_trace_reject_complete :
    ExpressionTraceRejectComplete identifierExpression DeclarativeGrammar.IdentifierExpressionTraceRejects := by
  intro input after diagnostic trace traced
  rcases expressionName_trace_reject_iff.mp traced with ⟨failure, result, afterEq, reportEq, rfl⟩
  exact ⟨failure, input, identifierExpression_reject_iff_expressionName.mpr result, afterEq.symm,
    reportEq, by simp only [List.append_nil]⟩

theorem identifierExpression_trace_success_iff
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.IdentifierExpressionTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, identifierExpression input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact identifierExpression_trace_success_complete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases identifierExpression_trace_success_sound result with ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

theorem identifierExpression_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.IdentifierExpressionTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    identifierExpression input = .reject failure input ∧
      after = input.declarativeRemainder ∧ trace = [] := by
  rw [identifierExpression_reject_iff_expressionName]
  exact expressionName_trace_reject_failure_iff

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionCollectionRejectionContextProperties
/-! Collection rejection preserves the file and any chosen window observation.
Taking the identity observes the full window; taking endByte allows endIndex
to change on rejection. Children may replace tokens, move arbitrarily, or
return invariants. No validity, diagnostic, ordinary, or carrier law is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {β : Type} {view : TokenWindow → β}

private def KeepsContext {α : Type} (reply : Reply α) (input : State) : Prop :=
  match reply with
  | .ok _ output | .reject _ output => output.file = input.file ∧ view output.window = view input.window
  | .invariant _ => True

private theorem context_trans {α : Type} {reply : Reply α} {middle input : State}
    (held : KeepsContext (view := view) reply middle)
    (frame : middle.file = input.file ∧ view middle.window = view input.window) : KeepsContext (view := view) reply input := by
  cases reply with
  | ok value output => exact ⟨held.1.trans frame.1, held.2.trans frame.2⟩
  | reject failure output => exact ⟨held.1.trans frame.1, held.2.trans frame.2⟩
  | invariant error => trivial

private theorem context_bind {α β : Type} {first : Parser α} {next : α → Parser β}
    (firstFrame : ∀ input, KeepsContext (view := view) (first input) input)
    (nextFrame : ∀ value input, KeepsContext (view := view) (next value input) input) :
    ∀ input, KeepsContext (view := view) ((first >>= next) input) input := by
  intro input
  have held := firstFrame input
  change KeepsContext (view := view) (match first input with
    | .ok value middle => next value middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) input
  cases result : first input with
  | invariant error => trivial
  | reject failure rejected => simpa only [result, KeepsContext] using held
  | ok value middle => exact context_trans (view := view) (nextFrame value middle) (by simpa only [result, KeepsContext] using held)

private theorem symbol_context (kind : Symbol) (context : ParseContext) (input : State) :
    KeepsContext (view := view) (symbol kind context input) input := by
  cases result : symbol kind context input with
  | invariant error => trivial
  | reject failure rejected => rw [symbol_reject_state_eq kind context result]; exact ⟨rfl, rfl⟩
  | ok value output => rw [(symbol_ok_tokenAt kind context result).2]; exact ⟨rfl, rfl⟩

private theorem closeDelimited_context {α : Type} (opening : Token) (closing : Symbol)
    (context : ParseContext) (values : List α) (input : State) :
    KeepsContext (view := view) (closeDelimited opening closing context values input) input := by
  have frame := symbol_context (view := view) closing context input
  unfold closeDelimited
  cases result : symbol closing context input <;> simp only [result, KeepsContext] at frame ⊢ <;> exact frame

private theorem delimitedTail_context {α : Type} (element : Parser α)
    (child : ∀ input, KeepsContext (view := view) (element input) input)
    (closing : Symbol) (trailing : Bool) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel values input, KeepsContext (view := view) (afterDelimitedElement element closing trailing context phase opening
      fuel values input) input := by
  intro fuel
  induction fuel with
  | zero => intro values input; trivial
  | succ fuel ih =>
      intro values input
      unfold afterDelimitedElement
      split
      · have commaFrame := symbol_context (view := view) .comma context input
        cases commaResult : symbol .comma context input with
        | invariant error => trivial
        | reject failure rejected => simpa only [commaResult, KeepsContext] using commaFrame
        | ok comma afterComma =>
            rw [commaResult] at commaFrame
            simp only
            split
            · exact context_trans (view := view) (closeDelimited_context (view := view) opening closing context values afterComma) commaFrame
            · have childFrame := child afterComma
              cases childResult : element afterComma with
              | invariant error => trivial
              | reject failure rejected =>
                  exact context_trans (view := view) (by simpa only [childResult, KeepsContext] using childFrame) commaFrame
              | ok value next =>
                  rw [childResult] at childFrame
                  simp only
                  split
                  · exact context_trans (view := view) (context_trans (view := view) (ih (value :: values) next) childFrame) commaFrame
                  · trivial
      · split
        · exact closeDelimited_context (view := view) opening closing context values input
        · exact ⟨rfl, rfl⟩

private theorem delimited_context {α : Type} (element : Parser α)
    (child : ∀ input, KeepsContext (view := view) (element input) input)
    (opening closing : Symbol) (empty trailing : Bool) (context : ParseContext) (phase : ParserPhase)
    (input : State) :
    KeepsContext (view := view) (delimitedWithPolicy opening closing empty trailing element context phase input) input := by
  have openingFrame := symbol_context (view := view) opening context input
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | invariant error => trivial
  | reject failure rejected => simpa only [openingResult, KeepsContext] using openingFrame
  | ok marker afterOpening =>
      rw [openingResult] at openingFrame
      simp only
      split
      · exact context_trans (view := view) (closeDelimited_context (view := view) marker closing context [] afterOpening) openingFrame
      · have childFrame := child afterOpening
        cases childResult : element afterOpening with
        | invariant error => trivial
        | reject failure rejected =>
            exact context_trans (view := view) (by simpa only [childResult, KeepsContext] using childFrame) openingFrame
        | ok value next =>
            rw [childResult] at childFrame
            simp only
            split
            · exact context_trans (view := view) (context_trans (view := view) (delimitedTail_context (view := view) element child closing trailing context phase
                marker (afterOpening.remainingCount + 1) [value] next) childFrame) openingFrame
            · trivial

private theorem closeTuple_context (opening : Token) (values : List Expr) (input : State) :
    KeepsContext (view := view) (closeTuple opening values input) input := by
  unfold closeTuple
  apply context_bind (view := view) (symbol_context (view := view) .rightParen .expression)
  intro closing next
  split <;> exact ⟨rfl, rfl⟩

private theorem tupleTail_context (nested : Parser Expr)
    (child : ∀ input, KeepsContext (view := view) (nested input) input) (opening : Token) :
    ∀ fuel values input, KeepsContext (view := view) (tupleTail nested opening fuel values input) input := by
  intro fuel
  induction fuel with
  | zero => intro values input; trivial
  | succ fuel ih =>
      intro values input
      have commaFrame := symbol_context (view := view) .comma .expression input
      unfold tupleTail
      cases commaResult : symbol .comma .expression input with
      | invariant error => trivial
      | reject failure rejected => simpa only [commaResult, KeepsContext] using commaFrame
      | ok comma afterComma =>
          rw [commaResult] at commaFrame
          simp only
          split
          · exact context_trans (view := view) (closeTuple_context (view := view) opening values afterComma) commaFrame
          · have childFrame := child afterComma
            cases childResult : nested afterComma with
            | invariant error => trivial
            | reject failure rejected =>
                exact context_trans (view := view) (by simpa only [childResult, KeepsContext] using childFrame) commaFrame
            | ok value next =>
                rw [childResult] at childFrame
                simp only
                split
                · split
                  · exact context_trans (view := view) (context_trans (view := view) (ih (value :: values) next) childFrame) commaFrame
                  · exact context_trans (view := view) (context_trans (view := view) (closeTuple_context (view := view) opening (value :: values) next)
                      childFrame) commaFrame
                · trivial

private theorem parenthesized_context (nested : Parser Expr)
    (child : ∀ input, KeepsContext (view := view) (nested input) input) (input : State) :
    KeepsContext (view := view) (parenthesized nested input) input := by
  have openingFrame := symbol_context (view := view) .leftParen .expression input
  unfold parenthesized
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => trivial
  | reject failure rejected => simpa only [openingResult, KeepsContext] using openingFrame
  | ok opening afterOpening =>
      rw [openingResult] at openingFrame
      simp only
      split
      · exact context_trans (view := view) (closeTuple_context (view := view) opening [] afterOpening) openingFrame
      · have childFrame := child afterOpening
        cases childResult : nested afterOpening with
        | invariant error => trivial
        | reject failure rejected =>
            exact context_trans (view := view) (by simpa only [childResult, KeepsContext] using childFrame) openingFrame
        | ok first next =>
            rw [childResult] at childFrame
            simp only
            split
            · trivial
            · split
              · exact context_trans (view := view) (context_trans (view := view) (tupleTail_context (view := view) nested child opening
                  (next.remainingCount + 1) [first] next) childFrame) openingFrame
              · exact context_trans (view := view) (context_trans (view := view) (closeTuple_context (view := view) opening [first] next) childFrame) openingFrame

private theorem optionalArguments_context (nested : Parser Expr)
    (child : ∀ input, KeepsContext (view := view) (nested input) input) (input : State) :
    KeepsContext (view := view) (optionalDotConstructorArguments nested input) input := by
  unfold optionalDotConstructorArguments
  simp only [bind, getState]
  split
  · apply context_bind (view := view) (delimited_context (view := view) nested child .leftParen .rightParen true false .expression .expression)
    intro value next; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem expressionName_context (input : State) : KeepsContext (view := view) (expressionName input) input := by
  cases result : expressionName input with
  | invariant error => trivial
  | ok value output =>
      have frame := expressionName_success_context_eq result
      exact ⟨frame.1, congrArg view frame.2⟩
  | reject failure rejected => rw [(expressionName_reject_trace_sound result).2]; exact ⟨rfl, rfl⟩

private theorem child_context {nested : Parser Expr} (success : ∀ {input output value}, nested input = .ok value output →
      output.file = input.file ∧ view output.window = view input.window)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window) (input : State) :
    KeepsContext (view := view) (nested input) input := by
  cases result : nested input with
  | invariant error => trivial
  | ok value output => exact success result
  | reject failure rejected => exact reject result

variable {nested : Parser Expr}

private theorem projected_success (success : ExpressionSuccessContext nested)
    {input output : State} {value : Expr} (result : nested input = .ok value output) :
    output.file = input.file ∧ view output.window = view input.window :=
  ⟨(success result).1, congrArg view (success result).2⟩

theorem parenthesized_reject_context_of_windowProjection (success : ExpressionSuccessContext nested)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure} (result : parenthesized nested input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  have frame := parenthesized_context (view := view) nested
    (child_context (view := view) (projected_success success) reject) input
  simpa only [result, KeepsContext] using frame

theorem arrayLiteral_reject_context_of_windowProjection (success : ExpressionSuccessContext nested)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure} (result : arrayLiteral nested input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  have frame : KeepsContext (view := view) (arrayLiteral nested input) input := by
    unfold arrayLiteral
    apply context_bind (view := view) (delimited_context (view := view) nested
      (child_context (view := view) (projected_success success) reject)
      .leftBracket .rightBracket true false .expression .expression)
    intro value next; exact ⟨rfl, rfl⟩
  simpa only [result, KeepsContext] using frame

theorem dotConstructor_reject_context_of_windowProjection (success : ExpressionSuccessContext nested)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure} (result : dotConstructor nested input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  have frame : KeepsContext (view := view) (dotConstructor nested input) input := by
    unfold dotConstructor
    apply context_bind (view := view) (symbol_context (view := view) .dot .expression)
    intro dot
    apply context_bind (view := view) (expressionName_context (view := view))
    intro name
    apply context_bind (view := view) (optionalArguments_context (view := view) nested
      (child_context (view := view) (projected_success success) reject))
    intro value next; exact ⟨rfl, rfl⟩
  simpa only [result, KeepsContext] using frame

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.OptionalDotConstructorArgumentsRejectionTraceProperties
/-! Exact optional-argument rejection under explicit child expression laws.
The left-parenthesis guard commits to the raw list result without changing its
failure, rejected state, or events; absent arguments cannot reject. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem optionalDotConstructorArguments_reject_iff_list
    {input rejected : State} {failure : Failure} :
    optionalDotConstructorArguments nested input = .reject failure rejected ↔
    isSymbol input .leftParen = true ∧
      delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input =
        .reject failure rejected := by
  cases guard : isSymbol input .leftParen with
  | false => simp [optionalDotConstructorArguments, getState, bind, guard, pure]
  | true =>
      cases result : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input <;>
        simp [optionalDotConstructorArguments, getState, bind, guard, pure, result]

theorem optionalDotConstructorArguments_reject_trace_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) :
    ParserTraceRejectSound (optionalDotConstructorArguments nested)
      (DeclarativeGrammar.OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  rcases optionalDotConstructorArguments_reject_iff_list.mp result with ⟨selected, raw⟩
  rcases delimitedNoTrailing_reject_trace_sound successSound rejectSound contextFrame
      .leftParen .rightParen true .expression .expression raw with ⟨trace, rejection, events⟩
  rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression selected with ⟨opening, openingResult⟩
  exact ⟨trace, .present opening.span (symbol_success_exactTokenParses .leftParen .expression openingResult).1
    rejection, events⟩

theorem optionalDotConstructorArguments_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) :
    ParserTraceRejectComplete (optionalDotConstructorArguments nested)
      (DeclarativeGrammar.OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects) := by
  intro input after diagnostic trace rejection
  cases rejection with
  | present span opening arguments =>
      have selected := DelimitedTraceInternals.symbol_present .leftParen (input := input)
        (after := { input.declarativeRemainder with cursor := input.cursor + 1 }) ⟨opening, rfl⟩
      rcases delimitedNoTrailing_trace_reject_complete successComplete rejectComplete contextFrame
          .leftParen .rightParen true .expression .expression arguments with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, optionalDotConstructorArguments_reject_iff_list.mpr ⟨selected, result⟩,
        afterEq, reportEq, events⟩

theorem optionalDotConstructorArguments_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, optionalDotConstructorArguments nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact optionalDotConstructorArguments_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases optionalDotConstructorArguments_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem optionalDotConstructorArguments_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, optionalDotConstructorArguments nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [optionalDotConstructorArguments_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.DotConstructorRejectionTraceProperties
/-! Exact raw leading-dot rejection through the real Boolean-first name
parser and conditional child expression contracts. Dispatcher selection is not
assumed; the first dot/name/argument report and preceding events remain exact. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem dotConstructor_reject_trace_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceRejectSound (dotConstructor nested)
      (DeclarativeGrammar.DotConstructorTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  unfold dotConstructor at result
  cases dotResult : symbol .dot .expression input with
  | invariant error => simp [bind, dotResult] at result
  | reject dotFailure dotRejected =>
      have shape := symbol_reject_state_eq .dot .expression dotResult
      subst dotRejected
      simp only [bind, dotResult] at result
      cases result
      have reported := (symbol_reject_reports_iff .dot .expression).mpr ⟨failure, dotResult, rfl⟩
      exact ⟨[], .dotMissing reported.1 reported.2, by simp⟩
  | ok dot afterDot =>
      have dotParsed := symbol_success_exactTokenParses .dot .expression dotResult
      have dotShape := (symbol_ok_tokenAt .dot .expression dotResult).2
      simp only [bind, dotResult] at result
      cases nameResult : expressionName afterDot with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          have nameTrace := expressionName_reject_trace_sound nameResult
          refine ⟨[], .nameRejected dot.span dotParsed ?_, ?_⟩
          · simpa only [dotShape] using nameTrace.1
          · rw [nameTrace.2, dotShape]; simp only [State.diagnostics, List.append_nil]
      | ok name afterName =>
          simp only [nameResult] at result
          cases argumentsResult : optionalDotConstructorArguments nested afterName with
          | invariant error => simp [argumentsResult] at result
          | ok arguments output => simp [argumentsResult, pure] at result
          | reject argumentsFailure argumentsRejected =>
              simp only [argumentsResult] at result
              cases result
              rcases expressionName_success_trace_sound nameResult with ⟨nameEvents, nameParsed, nameEq⟩
              have frame := expressionName_success_context_eq nameResult
              rcases optionalDotConstructorArguments_reject_trace_sound successSound rejectSound contextFrame
                  argumentsResult with ⟨argumentEvents, argumentsRejected, argumentsEq⟩
              refine ⟨nameEvents ++ argumentEvents, .argumentsRejected (name := name)
                (afterName := afterName.declarativeRemainder) dot.span dotParsed ?_ ?_, ?_⟩
              · simpa only [dotShape] using nameParsed
              · simpa only [frame.1, frame.2, dotShape] using argumentsRejected
              · rw [argumentsEq, nameEq, List.append_assoc]
                simp only [dotShape, State.diagnostics]

theorem dotConstructor_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceRejectComplete (dotConstructor nested)
      (DeclarativeGrammar.DotConstructorTraceRejects elementTrace elementRejects) := by
  intro input after diagnostic trace rejection
  cases rejection with
  | dotMissing absent reported =>
      rcases (symbol_reject_reports_iff .dot .expression).mp ⟨absent, reported⟩ with ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [dotConstructor, bind, result], rfl, reportEq, by simp⟩
  | nameRejected dotSpan dotParsed nameRejected =>
      have dotResult := symbol_eq_ok_of_exactTokenParses .dot .expression dotParsed
      rcases dotParsed with ⟨dotToken, rfl⟩
      rcases (expressionName_trace_reject_iff (input := { input with cursor := input.cursor + 1 })).mp
          nameRejected with ⟨failure, nameResult, afterEq, reportEq, events⟩
      exact ⟨failure, { input with cursor := input.cursor + 1 }, by
        simp only [dotConstructor, bind, dotResult, nameResult], afterEq.symm, reportEq,
        by simp only [events, State.diagnostics, List.append_nil]⟩
  | argumentsRejected dotSpan dotParsed nameParsed argumentsRejected =>
      rename_i afterDot afterName name nameEvents argumentEvents
      have dotResult := symbol_eq_ok_of_exactTokenParses .dot .expression dotParsed
      rcases dotParsed with ⟨dotToken, rfl⟩
      rcases expressionName_trace_success_complete (input := { input with cursor := input.cursor + 1 })
          nameParsed with ⟨next, nameResult, nextAfter, nameEq⟩
      have frame := expressionName_success_context_eq nameResult
      have argumentsAtNext : DeclarativeGrammar.OptionalDotConstructorArgumentsTraceRejects
          elementTrace elementRejects next.file.id next.window.endByte next.declarativeRemainder
          after diagnostic argumentEvents := by
        simpa only [frame.1, frame.2, nextAfter] using argumentsRejected
      rcases optionalDotConstructorArguments_trace_reject_complete successComplete rejectComplete contextFrame
          argumentsAtNext with ⟨failure, rejected, argumentsResult, afterEq, reportEq, argumentsEq⟩
      refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
      · simp only [dotConstructor, bind, dotResult, nameResult, argumentsResult]
      · rw [argumentsEq, nameEq, List.append_assoc]
        rfl

theorem dotConstructor_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DotConstructorTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, dotConstructor nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact dotConstructor_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases dotConstructor_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem dotConstructor_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DotConstructorTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, dotConstructor nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [dotConstructor_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.DotConstructorSuccessTraceProperties
/-! Exact success of the real leading-dot constructor wrapper. The real
Boolean-first checked name needs no child assumption; only argument expressions
use explicit success trace and source/full-window contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem bind_ok_parts {α β : Type} {first : Parser α} {next : α → Parser β}
    {input output : State} {value : β} (result : (first >>= next) input = .ok value output) :
    ∃ item after, first input = .ok item after ∧ next item after = .ok value output := by
  cases firstResult : first input <;> simp only [bind, firstResult] at result
  case ok item after => exact ⟨item, after, rfl, result⟩
  case reject => contradiction
  case invariant => contradiction

/-- This seam retains all three exact intermediate successes and the AST mapping. -/
theorem dotConstructor_success_iff_components {input output : State} {value : Expr} :
    dotConstructor nested input = .ok value output ↔
    ∃ dot afterDot name afterName arguments,
      symbol .dot .expression input = .ok dot afterDot ∧
      expressionName afterDot = .ok name afterName ∧
      optionalDotConstructorArguments nested afterName = .ok arguments output ∧
      value = {
        span := SourceSpan.cover dot.span (arguments.map (fun values => values.span) |>.getD name.span)
        value := .dotConstructor dot.span name arguments } := by
  constructor
  · intro result
    unfold dotConstructor at result
    rcases bind_ok_parts result with ⟨dot, afterDot, dotResult, rest⟩
    rcases bind_ok_parts rest with ⟨name, afterName, nameResult, rest⟩
    rcases bind_ok_parts rest with ⟨arguments, afterArguments, argsResult, finished⟩
    cases finished
    exact ⟨dot, afterDot, name, afterName, arguments, dotResult, nameResult, argsResult, rfl⟩
  · rintro ⟨dot, afterDot, name, afterName, arguments, dotResult, nameResult, argsResult, rfl⟩
    simp only [dotConstructor, bind, dotResult, nameResult, argsResult, pure]

theorem dotConstructor_trace_success_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceSuccessSound (dotConstructor nested)
      (DeclarativeGrammar.DotConstructorTraceParses elementTrace) := by
  intro input output value result
  rcases dotConstructor_success_iff_components.mp result with
    ⟨dot, afterDot, name, afterName, arguments, dotResult, nameResult, argsResult, rfl⟩
  have dotParsed := symbol_success_exactTokenParses .dot .expression dotResult
  have dotState := (symbol_ok_tokenAt .dot .expression dotResult).2
  subst afterDot
  rcases expressionName_success_trace_sound nameResult with ⟨nameEvents, nameParsed, nameEq⟩
  have nameFrame := expressionName_success_context_eq nameResult
  rcases optionalDotConstructorArguments_trace_success_sound successSound contextFrame argsResult with
    ⟨argEvents, argsParsed, argsEq⟩
  refine ⟨nameEvents ++ argEvents, .parsed dot.span dotParsed nameParsed ?_, ?_⟩
  · simpa only [nameFrame.1, nameFrame.2] using argsParsed
  · rw [argsEq, nameEq]; exact List.append_assoc _ _ _

theorem dotConstructor_trace_success_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceSuccessComplete (dotConstructor nested)
      (DeclarativeGrammar.DotConstructorTraceParses elementTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed dotSpan dotParsed nameParsed argsParsed =>
      rename_i afterDot afterName name arguments nameEvents argEvents
      have dotResult := symbol_eq_ok_of_exactTokenParses .dot .expression dotParsed
      rcases dotParsed with ⟨_, rfl⟩
      rcases expressionName_trace_success_complete
          (input := { input with cursor := input.cursor + 1 }) nameParsed with
        ⟨next, nameResult, afterEq, nameEq⟩
      have frame := expressionName_success_context_eq nameResult
      have argsAtNext : DeclarativeGrammar.OptionalDotConstructorArgumentsTraceParses elementTrace
          next.file.id next.window.endByte next.declarativeRemainder arguments after argEvents := by
        simpa only [frame.1, frame.2, afterEq] using argsParsed
      rcases optionalDotConstructorArguments_trace_success_complete successComplete contextFrame argsAtNext with
        ⟨output, argsResult, finalEq, argsEq⟩
      refine ⟨output, dotConstructor_success_iff_components.mpr
        ⟨_, _, name, next, arguments, dotResult, nameResult, argsResult, rfl⟩, finalEq, ?_⟩
      rw [argsEq, nameEq]; exact List.append_assoc _ _ _

theorem dotConstructor_success_context
    (contextFrame : ExpressionSuccessContext nested) : ExpressionSuccessContext (dotConstructor nested) := by
  intro input output value result
  rcases dotConstructor_success_iff_components.mp result with
    ⟨dot, afterDot, name, afterName, arguments, dotResult, nameResult, argsResult, _⟩
  have dotState := (symbol_ok_tokenAt .dot .expression dotResult).2
  have nameFrame := expressionName_success_context_eq nameResult
  have argFrame := optionalDotConstructorArguments_success_context contextFrame argsResult
  rw [dotState] at nameFrame
  exact ⟨argFrame.1.trans nameFrame.1, argFrame.2.trans nameFrame.2⟩

theorem dotConstructor_trace_success_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DotConstructorTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, dotConstructor nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact dotConstructor_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases dotConstructor_trace_success_sound successSound contextFrame result with
      ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomDispatchSuccessTraceProperties
/-! One atom-core layer composes exact raw successes. Nested-expression
success frames remain explicit; the final lambda body needs only its own
success contract. These laws do not assert recursive outcome existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {elementTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}

namespace ExpressionAtomDispatchTraceInternals

theorem raw_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceSuccessSound block blockTrace) (branch : ExpressionAtomDispatchBranch) :
    ParserTraceSuccessSound (rawParser nested block branch)
      (ExpressionAtomDispatchRawTraceParses elementTrace blockTrace branch) := by
  cases branch with
  | literal => exact literalExpression_trace_success_sound
  | name => exact identifierExpression_trace_success_sound
  | dotConstructor => exact dotConstructor_trace_success_sound successSound contextFrame
  | proxy => exact proxyExpression_concrete_trace_success_sound
  | parenthesized => exact parenthesized_trace_success_sound successSound contextFrame
  | array => exact arrayLiteral_trace_success_sound successSound contextFrame
  | lambda => exact lambdaExpression_trace_success_sound blockSound
  | final => intro input output value result; simp [rawParser, rejectAt] at result

theorem raw_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    (blockComplete : ParserTraceSuccessComplete block blockTrace) (branch : ExpressionAtomDispatchBranch) :
    ParserTraceSuccessComplete (rawParser nested block branch)
      (ExpressionAtomDispatchRawTraceParses elementTrace blockTrace branch) := by
  cases branch with
  | literal => exact literalExpression_trace_success_complete
  | name => exact identifierExpression_trace_success_complete
  | dotConstructor => exact dotConstructor_trace_success_complete successComplete contextFrame
  | proxy => exact proxyExpression_concrete_trace_success_complete
  | parenthesized => exact parenthesized_trace_success_complete successComplete contextFrame
  | array => exact arrayLiteral_trace_success_complete successComplete contextFrame
  | lambda => exact lambdaExpression_trace_success_complete blockComplete
  | final => intro input value after trace parsed; exact False.elim parsed

theorem raw_success_context (contextFrame : ParserSuccessContext nested)
    (blockFrame : ParserSuccessContext block) (branch : ExpressionAtomDispatchBranch) :
    ParserSuccessContext (rawParser nested block branch) := by
  cases branch with
  | literal => exact literalExpression_success_context
  | name => exact identifierExpression_success_context
  | dotConstructor => exact dotConstructor_success_context contextFrame
  | proxy => exact proxyExpression_concrete_success_context
  | parenthesized => exact parenthesized_success_context contextFrame
  | array => exact arrayLiteral_success_context contextFrame
  | lambda => exact lambdaExpression_success_context blockFrame
  | final => intro input output value result; simp [rawParser, rejectAt] at result

end ExpressionAtomDispatchTraceInternals

open ExpressionAtomDispatchTraceInternals

theorem ExpressionAtomInternals.expressionAtomCore_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceSuccessSound block blockTrace) :
    ParserTraceSuccessSound (expressionAtomCore nested block) (ExpressionAtomDispatchTraceParses elementTrace blockTrace) := by
  intro input output value result
  rw [expressionAtomCore_eq_selected_raw] at result
  rcases raw_trace_success_sound successSound contextFrame blockSound (selectedBranch input) result with
    ⟨trace, parsed, events⟩
  exact ⟨trace, .selected (selectedBranch input) (selectedBranch_selects input) parsed, events⟩

theorem ExpressionAtomInternals.expressionAtomCore_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    (blockComplete : ParserTraceSuccessComplete block blockTrace) :
    ParserTraceSuccessComplete (expressionAtomCore nested block) (ExpressionAtomDispatchTraceParses elementTrace blockTrace) := by
  intro input value after trace parsed
  cases parsed with
  | selected branch selection raw =>
      rcases raw_trace_success_complete successComplete contextFrame blockComplete branch raw with
        ⟨output, result, afterEq, events⟩
      exact ⟨output, (expressionAtomCore_eq_raw_of_selection nested block selection).trans result, afterEq, events⟩

theorem ExpressionAtomInternals.expressionAtomCore_trace_success_context
    (contextFrame : ParserSuccessContext nested) (blockFrame : ParserSuccessContext block) :
    ParserSuccessContext (expressionAtomCore nested block) := by
  intro input output value result
  rw [expressionAtomCore_eq_selected_raw] at result
  exact raw_success_context contextFrame blockFrame (selectedBranch input) result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomDispatchRejectionTraceProperties
/-! Exact rejection of one selected atom-core layer. Only executed nested
successes require a context frame; the final lambda body forwards its rejection
directly. No rejection-frame, progress, validity, or ordinary premise is hidden. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {elementTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

namespace ExpressionAtomDispatchTraceInternals

theorem raw_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceRejectSound block blockRejects) (branch : ExpressionAtomDispatchBranch) :
    ParserTraceRejectSound (rawParser nested block branch)
      (ExpressionAtomDispatchRawTraceRejects elementTrace elementRejects blockRejects branch) := by
  cases branch with
  | literal => exact literalExpression_trace_reject_sound
  | name => exact identifierExpression_trace_reject_sound
  | dotConstructor => exact dotConstructor_reject_trace_sound successSound rejectSound contextFrame
  | proxy => exact proxyExpression_concrete_reject_trace_sound
  | parenthesized => exact parenthesized_reject_trace_sound successSound rejectSound contextFrame
  | array => exact arrayLiteral_trace_reject_sound successSound rejectSound contextFrame
  | lambda => exact lambdaExpression_reject_trace_sound blockSound
  | final =>
      intro input rejected failure result
      have reported := rejectAt_reject_reports { head := .expression, tail := [] } .expression result
      have same : rejected = input := by unfold rawParser rejectAt at result; cases result; rfl
      subst rejected
      exact ⟨[], .rejected reported.1, by simp only [List.append_nil]⟩

theorem raw_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockComplete : ParserTraceRejectComplete block blockRejects) (branch : ExpressionAtomDispatchBranch) :
    ParserTraceRejectComplete (rawParser nested block branch)
      (ExpressionAtomDispatchRawTraceRejects elementTrace elementRejects blockRejects branch) := by
  cases branch with
  | literal => exact literalExpression_trace_reject_complete
  | name => exact identifierExpression_trace_reject_complete
  | dotConstructor => exact dotConstructor_trace_reject_complete successComplete rejectComplete contextFrame
  | proxy => exact proxyExpression_concrete_trace_reject_complete
  | parenthesized => exact parenthesized_trace_reject_complete successComplete rejectComplete contextFrame
  | array => exact arrayLiteral_trace_reject_complete successComplete rejectComplete contextFrame
  | lambda => exact lambdaExpression_trace_reject_complete blockComplete
  | final =>
      intro input after report trace rejection
      cases rejection with
      | rejected reported =>
          rcases (rejectAt_reports_iff (alpha := Expr)).mp reported with ⟨failure, result, reportEq⟩
          exact ⟨failure, input, result, rfl, reportEq, by simp only [List.append_nil]⟩

end ExpressionAtomDispatchTraceInternals

open ExpressionAtomDispatchTraceInternals

theorem ExpressionAtomInternals.expressionAtomCore_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceRejectSound block blockRejects) :
    ParserTraceRejectSound (expressionAtomCore nested block)
      (ExpressionAtomDispatchTraceRejects elementTrace elementRejects blockRejects) := by
  intro input rejected failure result
  rw [expressionAtomCore_eq_selected_raw] at result
  rcases raw_reject_trace_sound successSound rejectSound contextFrame blockSound (selectedBranch input) result with
    ⟨trace, rejection, events⟩
  exact ⟨trace, .selected (selectedBranch input) (selectedBranch_selects input) rejection, events⟩

theorem ExpressionAtomInternals.expressionAtomCore_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockComplete : ParserTraceRejectComplete block blockRejects) :
    ParserTraceRejectComplete (expressionAtomCore nested block)
      (ExpressionAtomDispatchTraceRejects elementTrace elementRejects blockRejects) := by
  intro input after report trace rejection
  cases rejection with
  | selected branch selection raw =>
      rcases raw_trace_reject_complete successComplete rejectComplete contextFrame blockComplete branch raw with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, (expressionAtomCore_eq_raw_of_selection nested block selection).trans result,
        afterEq, reportEq, events⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomDispatchTraceCorrespondenceProperties
/-! Exact trace suffixes and complete State reconstruction for one atom-core
layer. Rejected States need an explicit file/end-byte frame, not preservation
of the token carrier or end index. No trace outcome existence is inferred. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {elementTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionAtomCore_trace_success_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceSuccessSound block blockTrace)
    (blockComplete : ParserTraceSuccessComplete block blockTrace)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionAtomDispatchTraceParses elementTrace blockTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, expressionAtomCore nested block input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionAtomCore_trace_success_complete successComplete contextFrame blockComplete
  · rintro ⟨output, result, afterEq, events⟩
    rcases expressionAtomCore_trace_success_sound successSound contextFrame blockSound result with
      ⟨actual, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

theorem expressionAtomCore_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceRejectSound block blockRejects)
    (blockComplete : ParserTraceRejectComplete block blockRejects)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionAtomDispatchTraceRejects elementTrace elementRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, expressionAtomCore nested block input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionAtomCore_trace_reject_complete successComplete rejectComplete contextFrame blockComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases expressionAtomCore_reject_trace_sound successSound rejectSound contextFrame blockSound result with
      ⟨actual, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem expressionAtomCore_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceRejectSound block blockRejects)
    (blockComplete : ParserTraceRejectComplete block blockRejects)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionAtomDispatchTraceRejects elementTrace elementRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, expressionAtomCore nested block input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [expressionAtomCore_trace_reject_iff successSound rejectSound successComplete rejectComplete
    contextFrame blockSound blockComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem expressionAtomCore_trace_success_state_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceSuccessSound block blockTrace)
    (blockComplete : ParserTraceSuccessComplete block blockTrace)
    (blockFrame : ParserSuccessContext block)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionAtomDispatchTraceParses elementTrace blockTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      expressionAtomCore nested block input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases expressionAtomCore_trace_success_complete successComplete contextFrame blockComplete parsed with
      ⟨output, result, afterEq, events⟩
    have frame := expressionAtomCore_trace_success_context contextFrame blockFrame result
    exact State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events ▸ result
  · intro result
    exact (expressionAtomCore_trace_success_iff successSound successComplete contextFrame blockSound blockComplete).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionAtomCore_trace_reject_failure_state_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceRejectSound block blockRejects)
    (blockComplete : ParserTraceRejectComplete block blockRejects)
    (rejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionAtomDispatchTraceRejects elementTrace elementRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      expressionAtomCore nested block input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (expressionAtomCore_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete
      contextFrame blockSound blockComplete).mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := rejectFrame result
    exact State.eq_traceResult_of_fields frame.1 frame.2 afterEq events ▸ result
  · intro result
    exact (expressionAtomCore_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete
      contextFrame blockSound blockComplete).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionAtomCore_trace_reject_state_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceRejectSound block blockRejects)
    (blockComplete : ParserTraceRejectComplete block blockRejects)
    (rejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionAtomDispatchTraceRejects elementTrace elementRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, expressionAtomCore nested block input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases expressionAtomCore_trace_reject_complete successComplete rejectComplete contextFrame blockComplete rejection with
      ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (expressionAtomCore_trace_reject_failure_state_iff successSound rejectSound successComplete rejectComplete
      contextFrame blockSound blockComplete rejectFrame).mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (expressionAtomCore_trace_reject_failure_state_iff successSound rejectSound successComplete rejectComplete
      contextFrame blockSound blockComplete rejectFrame).mpr result

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomDispatchRejectionContextProperties
/-! Atom-core rejection keeps the file and an explicitly chosen window
observation. Both full-window and endByte-only specializations are provided.
Separate successful/rejected child context laws suffice: no token carrier,
block success frame, trace, validity, progress, or ordinary premise is needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem literalExpression_reject_context {input rejected : State} {failure : Failure}
    (result : literalExpression input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have same := (coreLiteral_reject_trace_sound (literalExpression_reject_iff_coreLiteral.mp result)).2
  rw [same]
  exact ⟨rfl, rfl⟩

theorem identifierExpression_reject_context {input rejected : State} {failure : Failure}
    (result : identifierExpression input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  rw [(expressionName_reject_trace_sound (identifierExpression_reject_iff_expressionName.mp result)).2]
  exact ⟨rfl, rfl⟩

theorem proxyExpression_reject_context {input rejected : State} {failure : Failure}
    (result : proxyExpression input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  unfold proxyExpression at result
  cases markerResult : symbol .at .expression input with
  | invariant error => simp [bind, markerResult] at result
  | reject actual next =>
      simp only [bind, markerResult] at result
      cases result
      rw [symbol_reject_state_eq .at .expression markerResult]
      exact ⟨rfl, rfl⟩
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases typeResult : typeExpr afterMarker with
      | invariant error => simp [typeResult] at result
      | ok type next => simp [typeResult, pure] at result
      | reject actual next =>
          simp only [typeResult] at result
          cases result
          have window := typeExpr_preservesTokenWindow afterMarker
          rw [typeResult] at window
          have file := typeExpr_preservesFile.file_eq_of_reject typeResult
          have markerState := (symbol_ok_tokenAt .at .expression markerResult).2
          rw [markerState] at file window
          exact ⟨file, window.2⟩

theorem lambdaExpression_reject_context_of_windowProjection {β : Type} {view : TokenWindow → β}
    {block : Parser Block}
    (blockReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure}
    (result : lambdaExpression block input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  unfold lambdaExpression at result
  cases markerResult : keyword .lamKw .expression input with
  | invariant error => simp [bind, markerResult] at result
  | reject actual next =>
      simp only [bind, markerResult] at result
      cases result
      have same := acceptToken_reject_state_shape (.keyword .lamKw) .expression
        (· == .keyword .lamKw) markerResult
      exact ⟨congrArg State.file same, congrArg (fun state => view state.window) same⟩
  | ok marker afterMarker =>
      have markerState := (keyword_ok_tokenAt .lamKw .expression markerResult).2
      subst afterMarker
      simp only [bind, markerResult] at result
      cases parametersResult : delimited .leftParen .rightParen true lambdaParameter .parameter .expression
          { input with cursor := input.cursor + 1 } with
      | invariant error => simp [parametersResult] at result
      | reject actual next =>
          simp only [parametersResult] at result
          cases result
          have frame := lambdaParameters_reject_context parametersResult
          exact ⟨frame.1, congrArg view frame.2⟩
      | ok parameters afterParameters =>
          simp only [parametersResult] at result
          have parameterFrame := lambdaParameters_success_context parametersResult
          cases returnResult : optionalLambdaReturnType afterParameters with
          | invariant error => simp [returnResult] at result
          | reject actual next =>
              simp only [returnResult] at result
              cases result
              have frame := optionalLambdaReturnType_reject_context returnResult
              exact ⟨frame.1.trans parameterFrame.1, congrArg view (frame.2.trans parameterFrame.2)⟩
          | ok returnType afterReturn =>
              simp only [returnResult] at result
              have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
              cases bodyResult : block afterReturn with
              | invariant error => simp [bodyResult] at result
              | ok body next => simp [bodyResult, pure] at result
              | reject actual next =>
                  simp only [bodyResult] at result
                  cases result
                  have frame := blockReject bodyResult
                  exact ⟨frame.1.trans (returnFrame.1.trans parameterFrame.1),
                    frame.2.trans (congrArg view (returnFrame.2.trans parameterFrame.2))⟩

theorem expressionAtomCore_reject_context_of_windowProjection
    {β : Type} {view : TokenWindow → β} {nested : Parser Expr} {block : Parser Block}
    (nestedSuccess : ExpressionSuccessContext nested)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    (blockReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure}
    (result : expressionAtomCore nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  rw [ExpressionAtomDispatchTraceInternals.expressionAtomCore_eq_selected_raw] at result
  generalize chosen : ExpressionAtomDispatchTraceInternals.selectedBranch input = branch at result
  cases branch with
  | literal =>
      have frame := literalExpression_reject_context result
      exact ⟨frame.1, congrArg view frame.2⟩
  | name =>
      have frame := identifierExpression_reject_context result
      exact ⟨frame.1, congrArg view frame.2⟩
  | dotConstructor => exact dotConstructor_reject_context_of_windowProjection nestedSuccess nestedReject result
  | proxy =>
      have frame := proxyExpression_reject_context result
      exact ⟨frame.1, congrArg view frame.2⟩
  | parenthesized => exact parenthesized_reject_context_of_windowProjection nestedSuccess nestedReject result
  | array => exact arrayLiteral_reject_context_of_windowProjection nestedSuccess nestedReject result
  | lambda => exact lambdaExpression_reject_context_of_windowProjection blockReject result
  | final =>
      change Reply.reject _ input = Reply.reject failure rejected at result
      cases result
      exact ⟨rfl, rfl⟩

theorem expressionAtomCore_reject_context {nested : Parser Expr} {block : Parser Block}
    (nestedSuccess : ExpressionSuccessContext nested)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    (blockReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input rejected : State} {failure : Failure}
    (result : expressionAtomCore nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window :=
  expressionAtomCore_reject_context_of_windowProjection (view := id) nestedSuccess nestedReject blockReject result

/-- Rejection may change both tokens and endIndex. Only its file and byte end
are needed to reconstruct a whole State from its exact traced remainder. -/
theorem expressionAtomCore_reject_source_endByte {nested : Parser Expr} {block : Parser Block}
    (nestedSuccess : ExpressionSuccessContext nested)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input rejected : State} {failure : Failure}
    (result : expressionAtomCore nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte :=
  expressionAtomCore_reject_context_of_windowProjection (view := TokenWindow.endByte)
    nestedSuccess nestedReject blockReject result

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomLayerTraceProperties
/-! Public atom traces instantiate the actual selected core and recovery.
Only recursive expression/body contracts remain supplied. Rejected child
frames preserve file/endByte, not the token carrier or numeric endIndex. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionAtom_layer_trace_success_sound
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSuccessSound : ParserTraceSuccessSound block blockTrace)
    (blockRejectSound : ParserTraceRejectSound block blockRejects)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceSuccessSound (expressionAtom nested block)
      (ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects) :=
  expressionAtom_trace_success_sound
    (expressionAtomCore_trace_success_sound successSound contextFrame blockSuccessSound)
    (expressionAtomCore_reject_trace_sound successSound rejectSound contextFrame blockRejectSound)
    (expressionAtomCore_reject_source_endByte contextFrame nestedRejectFrame blockRejectFrame)

theorem expressionAtom_layer_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockRejectSound : ParserTraceRejectSound block blockRejects)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceRejectSound (expressionAtom nested block)
      (ExpressionAtomLayerTraceRejects nestedTrace nestedRejects blockRejects) :=
  expressionAtom_reject_trace_sound
    (expressionAtomCore_reject_trace_sound successSound rejectSound contextFrame blockRejectSound)
    (expressionAtomCore_reject_source_endByte contextFrame nestedRejectFrame blockRejectFrame)

theorem expressionAtom_layer_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested nestedTrace)
    (rejectComplete : ParserTraceRejectComplete nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSuccessComplete : ParserTraceSuccessComplete block blockTrace)
    (blockRejectComplete : ParserTraceRejectComplete block blockRejects)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceSuccessComplete (expressionAtom nested block)
      (ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects) :=
  expressionAtom_trace_success_complete
    (expressionAtomCore_trace_success_complete successComplete contextFrame blockSuccessComplete)
    (expressionAtomCore_trace_reject_complete successComplete rejectComplete contextFrame blockRejectComplete)
    (expressionAtomCore_reject_source_endByte contextFrame nestedRejectFrame blockRejectFrame)

theorem expressionAtom_layer_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested nestedTrace)
    (rejectComplete : ParserTraceRejectComplete nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockRejectComplete : ParserTraceRejectComplete block blockRejects)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceRejectComplete (expressionAtom nested block)
      (ExpressionAtomLayerTraceRejects nestedTrace nestedRejects blockRejects) :=
  expressionAtom_trace_reject_complete
    (expressionAtomCore_trace_reject_complete successComplete rejectComplete contextFrame blockRejectComplete)
    (expressionAtomCore_reject_source_endByte contextFrame nestedRejectFrame blockRejectFrame)

/-- Full-window success context has stronger rejection premises than the trace
laws: recovery is allowed to succeed on the carrier/window returned by a child. -/
theorem expressionAtom_layer_success_context
    (contextFrame : ParserSuccessContext nested) (blockFrame : ParserSuccessContext block)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window) :
    ParserSuccessContext (expressionAtom nested block) :=
  expressionAtom_success_context (expressionAtomCore_trace_success_context contextFrame blockFrame)
    (expressionAtomCore_reject_context contextFrame nestedRejectFrame blockRejectFrame)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomLayerTraceExistenceProperties
/-! Non-vacuous trace existence for a bounded atom layer follows ordinary
execution and soundness. The strict-progress/end-index child contract is explicit;
no independent exactness or completeness premise substitutes for totality. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionAtomCore_exists_trace_outcome_of_unrestrictedElementFuel
    (nestedFuel : Nat) (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSuccessSound : ParserTraceSuccessSound block blockTrace)
    (blockRejectSound : ParserTraceRejectSound block blockRejects)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value output trace,
      expressionAtomCore nested block input = .ok value output ∧
      ExpressionAtomDispatchTraceParses nestedTrace blockTrace input.file.id input.window.endByte
        input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      expressionAtomCore nested block input = .reject failure rejected ∧
      ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases expressionAtomCore_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract blockOrdinary input adequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases expressionAtomCore_trace_success_sound successSound contextFrame blockSuccessSound result with
      ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases expressionAtomCore_reject_trace_sound successSound rejectSound contextFrame blockRejectSound result with
      ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem expressionAtom_layer_exists_trace_outcome_of_unrestrictedElementFuel
    (nestedFuel : Nat) (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSuccessSound : ParserTraceSuccessSound block blockTrace)
    (blockRejectSound : ParserTraceRejectSound block blockRejects)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value output trace,
      expressionAtom nested block input = .ok value output ∧
      ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects input.file.id input.window.endByte
        input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      expressionAtom nested block input = .reject failure rejected ∧
      ExpressionAtomLayerTraceRejects nestedTrace nestedRejects blockRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases expressionAtom_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract blockOrdinary input adequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases expressionAtom_layer_trace_success_sound successSound rejectSound contextFrame blockSuccessSound blockRejectSound
      nestedRejectFrame blockRejectFrame result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases expressionAtom_layer_reject_trace_sound successSound rejectSound contextFrame blockRejectSound
      nestedRejectFrame blockRejectFrame result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem expressionAtomLayerTrace_outcome_exists_of_unrestrictedElementFuel
    (nestedFuel : Nat) (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSuccessSound : ParserTraceSuccessSound block blockTrace)
    (blockRejectSound : ParserTraceRejectSound block blockRejects)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (source : SourceId) (endByte : Nat) (input : Remainder)
    (adequate : input.endIndex - input.cursor < nestedFuel + 1) :
    (∃ value output trace, ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects
      source endByte input value output trace) ∨
    (∃ rejected report trace, ExpressionAtomLayerTraceRejects nestedTrace nestedRejects blockRejects
      source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }, tokens := input.tokens, cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }, diagnosticsRev := []
  }
  rcases expressionAtom_layer_exists_trace_outcome_of_unrestrictedElementFuel nestedFuel contract blockOrdinary
      successSound rejectSound contextFrame blockSuccessSound blockRejectSound nestedRejectFrame blockRejectFrame
      state adequate with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, rejection⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionPostfixLayerTraceProperties
/-! Actual selected-core/recovery/postfix trace soundness with only recursive
expression/body contracts left supplied. Successful atom framing is explicit:
the full rejected child windows used here also frame recovered atom successes.
No completeness, totality, or recursive closure is inferred from these laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (successSound : ParserTraceSuccessSound nested nestedTrace)
  (rejectSound : ParserTraceRejectSound nested nestedRejects)
  (contextFrame : ParserSuccessContext nested)
  (blockSuccessSound : ParserTraceSuccessSound block blockTrace)
  (blockRejectSound : ParserTraceRejectSound block blockRejects)
  (blockContext : ParserSuccessContext block)
  (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
    rejected.file = input.file ∧ rejected.window = input.window)
  (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
    rejected.file = input.file ∧ rejected.window = input.window)

include successSound rejectSound contextFrame blockSuccessSound blockRejectSound blockContext
  nestedRejectFrame blockRejectFrame

theorem expressionPostfix_layer_trace_success_sound :
    ParserTraceSuccessSound (expressionPostfix nested block)
      (ExpressionPostfixLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects) :=
  expressionPostfix_trace_success_sound
    (expressionAtom_layer_trace_success_sound successSound rejectSound contextFrame blockSuccessSound blockRejectSound
      (fun result => ⟨(nestedRejectFrame result).1, congrArg TokenWindow.endByte (nestedRejectFrame result).2⟩)
      (fun result => ⟨(blockRejectFrame result).1, congrArg TokenWindow.endByte (blockRejectFrame result).2⟩))
    (expressionAtom_layer_success_context contextFrame blockContext nestedRejectFrame blockRejectFrame)
    successSound contextFrame

theorem expressionPostfix_layer_reject_trace_sound :
    ParserTraceRejectSound (expressionPostfix nested block)
      (ExpressionPostfixLayerTraceRejects nestedTrace nestedRejects blockTrace blockRejects) :=
  expressionPostfix_reject_trace_sound
    (expressionAtom_layer_trace_success_sound successSound rejectSound contextFrame blockSuccessSound blockRejectSound
      (fun result => ⟨(nestedRejectFrame result).1, congrArg TokenWindow.endByte (nestedRejectFrame result).2⟩)
      (fun result => ⟨(blockRejectFrame result).1, congrArg TokenWindow.endByte (blockRejectFrame result).2⟩))
    (expressionAtom_layer_reject_trace_sound successSound rejectSound contextFrame blockRejectSound
      (fun result => ⟨(nestedRejectFrame result).1, congrArg TokenWindow.endByte (nestedRejectFrame result).2⟩)
      (fun result => ⟨(blockRejectFrame result).1, congrArg TokenWindow.endByte (blockRejectFrame result).2⟩))
    (expressionAtom_layer_success_context contextFrame blockContext nestedRejectFrame blockRejectFrame)
    successSound rejectSound contextFrame

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionPostfixLayerTraceExistenceProperties
/-! Child-only bounded existence for the concrete selected/recovering
atom-plus-postfix layer. Ordinary execution constructs its atom contract;
soundness supplies the independent trace. Neither joint exactness nor child
completeness is used to stand in for outcome existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (successSound : ParserTraceSuccessSound nested nestedTrace)
  (rejectSound : ParserTraceRejectSound nested nestedRejects)
  (contextFrame : ParserSuccessContext nested)
  (blockSuccessSound : ParserTraceSuccessSound block blockTrace)
  (blockRejectSound : ParserTraceRejectSound block blockRejects)
  (blockContext : ParserSuccessContext block)
  (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
    rejected.file = input.file ∧ rejected.window = input.window)
  (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
    rejected.file = input.file ∧ rejected.window = input.window)
  (nestedFuel bodyFuel : Nat)
  (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
  (bodyContract : UnrestrictedFuelElementContract block bodyFuel)

include successSound rejectSound contextFrame blockSuccessSound blockRejectSound blockContext
  nestedRejectFrame blockRejectFrame nestedContract bodyContract

theorem expressionPostfix_layer_exists_trace_outcome_of_unrestrictedChildFuels
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) :
    (∃ value output trace,
      expressionPostfix nested block input = .ok value output ∧
      ExpressionPostfixLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects
        input.file.id input.window.endByte input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      expressionPostfix nested block input = .reject failure rejected ∧
      ExpressionPostfixLayerTraceRejects nestedTrace nestedRejects blockTrace blockRejects
        input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases expressionPostfix_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
      nestedContract bodyContract
      (fun result => congrArg TokenWindow.endIndex (nestedRejectFrame result).2)
      (fun result => congrArg TokenWindow.endIndex (blockRejectFrame result).2)
      input nestedAdequate bodyAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases expressionPostfix_layer_trace_success_sound successSound rejectSound contextFrame
      blockSuccessSound blockRejectSound blockContext nestedRejectFrame blockRejectFrame result with
        ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases expressionPostfix_layer_reject_trace_sound successSound rejectSound contextFrame
      blockSuccessSound blockRejectSound blockContext nestedRejectFrame blockRejectFrame result with
        ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem expressionPostfixLayerTrace_outcome_exists_of_unrestrictedChildFuels
    (source : SourceId) (endByte : Nat) (input : Remainder)
    (nestedAdequate : input.endIndex - input.cursor < nestedFuel + 1)
    (bodyAdequate : input.endIndex - input.cursor < bodyFuel + 1) :
    (∃ value after trace, ExpressionPostfixLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects
      source endByte input value after trace) ∨
    (∃ rejected report trace, ExpressionPostfixLayerTraceRejects nestedTrace nestedRejects blockTrace blockRejects
      source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }, tokens := input.tokens, cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }, diagnosticsRev := []
  }
  rcases expressionPostfix_layer_exists_trace_outcome_of_unrestrictedChildFuels successSound rejectSound contextFrame
      blockSuccessSound blockRejectSound blockContext nestedRejectFrame blockRejectFrame nestedFuel bodyFuel
      nestedContract bodyContract state nestedAdequate bodyAdequate with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, rejection⟩

end Solcore.Syntax.Parser
end
