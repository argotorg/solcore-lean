import Solcore.Syntax.Internal.ExpressionTrace
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.ExpressionAtomProofs
import Solcore.Syntax.Parser.Internal.TypeTrace
import Solcore.Syntax.Internal.TypeTrace
import Solcore.Syntax.Internal.DotConstructorTrace
import Solcore.Syntax.Parser.Internal.DelimitedTrace
import Solcore.Syntax.Parser.Internal.ParameterListTrace
import Solcore.Syntax.Parser.Internal.ParenthesizedTrace
import Solcore.Syntax.Parser.Internal.ExpressionTotality
import Solcore.Syntax.Parser.Internal.BlockTrace
import Solcore.Syntax.Parser.Internal.PostfixTrace

/-!
Parser side of the traces of lambda expressions and proxy expressions: the parsers produce
exactly the events of the trace grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.ProxyExpressionRejectionTraceProperties
/-! Exact raw proxy rejection uses contracts for the actual type parser.
The marker contributes no event, and nested failures preserve their complete
Failure and returned State without requiring successful context or token laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {typeRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem proxyExpression_reject_iff_components {input rejected : State} {failure : Failure} :
    proxyExpression input = .reject failure rejected ↔
    symbol .at .expression input = .reject failure rejected ∨
      ∃ marker afterMarker, symbol .at .expression input = .ok marker afterMarker ∧
        typeExpr afterMarker = .reject failure rejected := by
  constructor
  · intro result
    unfold proxyExpression at result
    cases markerResult : symbol .at .expression input with
    | invariant => simp only [bind, markerResult] at result; contradiction
    | reject markerFailure markerRejected =>
        simp only [bind, markerResult] at result
        cases result
        exact .inl rfl
    | ok marker afterMarker =>
        simp only [bind, markerResult] at result
        cases typeResult : typeExpr afterMarker with
        | invariant => simp only [typeResult] at result; contradiction
        | ok => simp only [typeResult, pure] at result; contradiction
        | reject typeFailure typeRejected =>
            simp only [typeResult] at result
            cases result
            exact .inr ⟨marker, afterMarker, rfl, typeResult⟩
  · rintro (markerResult | ⟨marker, afterMarker, markerResult, typeResult⟩)
    · simp only [proxyExpression, bind, markerResult]
    · simp only [proxyExpression, bind, markerResult, typeResult]

theorem proxyExpression_reject_trace_sound
    (rejectSound : ParserTraceRejectSound typeExpr typeRejects) :
    ExpressionTraceRejectSound proxyExpression (DeclarativeGrammar.ProxyExpressionTraceRejects typeRejects) := by
  intro input rejected failure result
  rcases proxyExpression_reject_iff_components.mp result with markerResult |
      ⟨marker, afterMarker, markerResult, typeResult⟩
  · have same := symbol_reject_state_eq .at .expression markerResult
    subst rejected
    have reported := (symbol_reject_reports_iff .at .expression).mpr ⟨failure, markerResult, rfl⟩
    exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  · have markerParsed := symbol_success_exactTokenParses .at .expression markerResult
    have markerState := (symbol_ok_tokenAt .at .expression markerResult).2
    subst afterMarker
    rcases rejectSound typeResult with ⟨trace, typed, events⟩
    exact ⟨trace, .typeRejected marker.span markerParsed typed, events⟩

theorem proxyExpression_trace_reject_complete
    (rejectComplete : ParserTraceRejectComplete typeExpr typeRejects) :
    ExpressionTraceRejectComplete proxyExpression (DeclarativeGrammar.ProxyExpressionTraceRejects typeRejects) := by
  intro input after report trace rejection
  cases rejection with
  | markerMissing absent reported =>
      rcases (symbol_reject_reports_iff .at .expression).mp ⟨absent, reported⟩ with
        ⟨failure, markerResult, reportEq⟩
      exact ⟨failure, input, proxyExpression_reject_iff_components.mpr (.inl markerResult),
        rfl, reportEq, by simp⟩
  | typeRejected markerSpan marker typed =>
      have markerResult := symbol_eq_ok_of_exactTokenParses .at .expression marker
      rcases marker with ⟨_, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) typed with
        ⟨failure, rejected, typeResult, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, proxyExpression_reject_iff_components.mpr
        (.inr ⟨_, _, markerResult, typeResult⟩), afterEq, reportEq, events⟩

theorem proxyExpression_trace_reject_iff
    (rejectSound : ParserTraceRejectSound typeExpr typeRejects)
    (rejectComplete : ParserTraceRejectComplete typeExpr typeRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ProxyExpressionTraceRejects typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, proxyExpression input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact proxyExpression_trace_reject_complete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases proxyExpression_reject_trace_sound rejectSound result with ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem proxyExpression_trace_reject_failure_iff
    (rejectSound : ParserTraceRejectSound typeExpr typeRejects)
    (rejectComplete : ParserTraceRejectComplete typeExpr typeRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ProxyExpressionTraceRejects typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, proxyExpression input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [proxyExpression_trace_reject_iff rejectSound rejectComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ProxyExpressionSuccessTraceProperties
/-! The real proxy parser preserves every nested type event. Its execution
contracts are conditional on the real type parser, whose diagnostics are not
assumed silent. Source/full-window preservation is a separate child contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {typeTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem proxyExpression_success_iff_components {input output : State} {value : Expr} :
    proxyExpression input = .ok value output ↔
    ∃ marker afterMarker type,
      symbol .at .expression input = .ok marker afterMarker ∧
      typeExpr afterMarker = .ok type output ∧
      value = { span := SourceSpan.cover marker.span type.span, value := .proxy marker.span type } := by
  constructor
  · intro result
    unfold proxyExpression at result
    cases markerResult : symbol .at .expression input with
    | reject => simp only [bind, markerResult] at result; contradiction
    | invariant => simp only [bind, markerResult] at result; contradiction
    | ok marker afterMarker =>
        simp only [bind, markerResult] at result
        cases typeResult : typeExpr afterMarker with
        | reject => simp only [typeResult] at result; contradiction
        | invariant => simp only [typeResult] at result; contradiction
        | ok type next =>
            simp only [typeResult, pure] at result
            cases result
            exact ⟨marker, afterMarker, type, rfl, typeResult, rfl⟩
  · rintro ⟨marker, afterMarker, type, markerResult, typeResult, rfl⟩
    simp only [proxyExpression, bind, markerResult, typeResult, pure]

theorem proxyExpression_trace_success_sound
    (successSound : ParserTraceSuccessSound typeExpr typeTrace) :
    ExpressionTraceSuccessSound proxyExpression (DeclarativeGrammar.ProxyExpressionTraceParses typeTrace) := by
  intro input output value result
  rcases proxyExpression_success_iff_components.mp result with
    ⟨marker, afterMarker, type, markerResult, typeResult, rfl⟩
  have markerParsed := symbol_success_exactTokenParses .at .expression markerResult
  have markerState := (symbol_ok_tokenAt .at .expression markerResult).2
  subst afterMarker
  rcases successSound typeResult with ⟨trace, typed, events⟩
  exact ⟨trace, .parsed marker.span markerParsed typed, events⟩

theorem proxyExpression_trace_success_complete
    (successComplete : ParserTraceSuccessComplete typeExpr typeTrace) :
    ExpressionTraceSuccessComplete proxyExpression (DeclarativeGrammar.ProxyExpressionTraceParses typeTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed markerSpan marker typed =>
      have markerResult := symbol_eq_ok_of_exactTokenParses .at .expression marker
      rcases marker with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) typed with
        ⟨output, typeResult, afterEq, events⟩
      exact ⟨output, proxyExpression_success_iff_components.mpr
        ⟨_, _, _, markerResult, typeResult, rfl⟩, afterEq, events⟩

theorem proxyExpression_success_context (contextFrame : ParserSuccessContext typeExpr) :
    ExpressionSuccessContext proxyExpression := by
  intro input output value result
  rcases proxyExpression_success_iff_components.mp result with
    ⟨marker, afterMarker, type, markerResult, typeResult, _⟩
  have frame := contextFrame typeResult
  rw [(symbol_ok_tokenAt .at .expression markerResult).2] at frame
  exact frame

theorem proxyExpression_trace_success_iff
    (successSound : ParserTraceSuccessSound typeExpr typeTrace)
    (successComplete : ParserTraceSuccessComplete typeExpr typeTrace)
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ProxyExpressionTraceParses typeTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, proxyExpression input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact proxyExpression_trace_success_complete successComplete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases proxyExpression_trace_success_sound successSound result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans diagnostics)
    simpa only [afterEq, same] using parsed

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ProxyExpressionTypeTraceProperties
/-! Concrete recursive-type specialization of the raw proxy-expression trace.
All five execution contracts hold on arbitrary states without caller-supplied
type laws. The marker is silent, nested events remain ordered, and a terminal
Failure is not committed. This does not describe the full expression dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

theorem proxyExpression_concrete_trace_success_sound :
    ExpressionTraceSuccessSound proxyExpression (ProxyExpressionTraceParses TypeExprTraceParses) :=
  proxyExpression_trace_success_sound typeExpr_trace_success_sound

theorem proxyExpression_concrete_trace_success_complete :
    ExpressionTraceSuccessComplete proxyExpression (ProxyExpressionTraceParses TypeExprTraceParses) :=
  proxyExpression_trace_success_complete typeExpr_trace_success_complete

theorem proxyExpression_concrete_success_context : ExpressionSuccessContext proxyExpression :=
  proxyExpression_success_context typeExpr_success_context

theorem proxyExpression_concrete_reject_trace_sound :
    ExpressionTraceRejectSound proxyExpression (ProxyExpressionTraceRejects TypeExprTraceRejects) :=
  proxyExpression_reject_trace_sound typeExpr_reject_trace_sound

theorem proxyExpression_concrete_trace_reject_complete :
    ExpressionTraceRejectComplete proxyExpression (ProxyExpressionTraceRejects TypeExprTraceRejects) :=
  proxyExpression_trace_reject_complete typeExpr_trace_reject_complete

theorem proxyExpression_concrete_trace_success_iff
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ProxyExpressionTraceParses TypeExprTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, proxyExpression input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  proxyExpression_trace_success_iff typeExpr_trace_success_sound typeExpr_trace_success_complete

theorem proxyExpression_concrete_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ProxyExpressionTraceRejects TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, proxyExpression input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  proxyExpression_trace_reject_iff typeExpr_reject_trace_sound typeExpr_trace_reject_complete

theorem proxyExpression_concrete_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ProxyExpressionTraceRejects TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, proxyExpression input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  proxyExpression_trace_reject_failure_iff typeExpr_reject_trace_sound typeExpr_trace_reject_complete

/-- Independent exactness of the specialized relations; this bundle expresses
uniqueness and disjointness, not existence of an outcome. -/
theorem proxyExpression_concrete_trace_exactOutcomeSpec {source : SourceId} {endByte : Nat} :
    ExpressionTraceExactOutcomeSpec (ProxyExpressionTraceParses TypeExprTraceParses)
      (ProxyExpressionTraceRejects TypeExprTraceRejects) source endByte :=
  proxyExpressionTraceExactOutcomeSpec typeExprTraceExactOutcomeSpec

theorem proxyExpression_concrete_trace_success_cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Expr} {trace : List ParseDiagnostic}
    (parsed : ProxyExpressionTraceParses TypeExprTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  parsed.cascadeFilters (fun child => child.cascadeFilters text lexical)

/-- Only emitted events are protected, not the separate terminal report. -/
theorem proxyExpression_concrete_trace_reject_cascadeFilters
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyExpressionTraceRejects TypeExprTraceRejects source endByte
      input rejected report trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  rejection.cascadeFilters (fun child => child.cascadeFilters text lexical)

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.OptionalDotConstructorArgumentsTraceProperties
/-! Exact optional-argument success. The absent branch never calls the child;
the present branch is the actual no-trailing list, with explicit child laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem optionalDotConstructorArguments_eq_none_of_absent (nested : Parser Expr)
    {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol .leftParen)) :
    optionalDotConstructorArguments nested input = .ok none input := by
  simp only [optionalDotConstructorArguments, getState, bind,
    DelimitedTraceInternals.symbol_absent .leftParen absent, Bool.false_eq_true, if_false, pure]

theorem optionalDotConstructorArguments_eq_of_present (nested : Parser Expr)
    {input : State} {span : SourceSpan}
    (opening : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .leftParen }) :
    optionalDotConstructorArguments nested input =
      match delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input with
      | .ok arguments output => .ok (some arguments) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  have present := DelimitedTraceInternals.symbol_present .leftParen
    (input := input) (after := { input.declarativeRemainder with cursor := input.cursor + 1 }) ⟨opening, rfl⟩
  simp only [optionalDotConstructorArguments, getState, bind, present, if_true, pure]
  cases delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input <;> rfl

theorem optionalDotConstructorArguments_trace_success_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) :
    ParserTraceSuccessSound (optionalDotConstructorArguments nested)
      (DeclarativeGrammar.OptionalDotConstructorArgumentsTraceParses elementTrace) := by
  intro input output arguments result
  by_cases present : isSymbol input .leftParen = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression present with ⟨token, tokenResult⟩
    rw [optionalDotConstructorArguments_eq_of_present nested
      (symbol_ok_tokenAt .leftParen .expression tokenResult).1] at result
    cases argsResult : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input with
    | invariant error => simp [argsResult] at result
    | reject failure rejected => simp [argsResult] at result
    | ok values next =>
        simp only [argsResult] at result
        cases result
        rcases delimitedNoTrailing_success_trace_sound successSound contextFrame
          .leftParen .rightParen true .expression .expression argsResult with ⟨trace, parsed, diagnostics⟩
        exact ⟨trace, .present parsed, diagnostics⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .leftParen (Bool.eq_false_iff.mpr present)
    rw [optionalDotConstructorArguments_eq_none_of_absent nested absent] at result
    cases result
    exact ⟨[], .absent absent, by simp only [List.append_nil]⟩

theorem optionalDotConstructorArguments_trace_success_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) :
    ParserTraceSuccessComplete (optionalDotConstructorArguments nested)
      (DeclarativeGrammar.OptionalDotConstructorArgumentsTraceParses elementTrace) := by
  intro input arguments after trace parsed
  cases parsed with
  | absent absent =>
      exact ⟨input, optionalDotConstructorArguments_eq_none_of_absent nested absent, rfl,
        by simp only [List.append_nil]⟩
  | present parsed =>
      rcases (DeclarativeGrammar.OptionalDotConstructorArgumentsTraceParses.present parsed).present_token with
        ⟨span, opening⟩
      rcases delimitedNoTrailing_trace_success_complete successComplete contextFrame
          .leftParen .rightParen true .expression .expression parsed with ⟨output, result, afterEq, diagnostics⟩
      exact ⟨output, by rw [optionalDotConstructorArguments_eq_of_present nested opening, result],
        afterEq, diagnostics⟩

theorem optionalDotConstructorArguments_success_context
    (contextFrame : ExpressionSuccessContext nested) :
    ParserSuccessContext (optionalDotConstructorArguments nested) := by
  intro input output arguments result
  by_cases present : isSymbol input .leftParen = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression present with ⟨token, tokenResult⟩
    rw [optionalDotConstructorArguments_eq_of_present nested
      (symbol_ok_tokenAt .leftParen .expression tokenResult).1] at result
    cases argsResult : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input with
    | invariant error => simp [argsResult] at result
    | reject failure rejected => simp [argsResult] at result
    | ok values next =>
        simp only [argsResult] at result
        cases result
        exact delimitedNoTrailing_success_context contextFrame .leftParen .rightParen true
          .expression .expression argsResult
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .leftParen (Bool.eq_false_iff.mpr present)
    rw [optionalDotConstructorArguments_eq_none_of_absent nested absent] at result
    cases result
    exact ⟨rfl, rfl⟩

theorem optionalDotConstructorArguments_trace_success_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {arguments : Option (DelimitedList Expr)}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalDotConstructorArgumentsTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder arguments after trace ↔
    ∃ output, optionalDotConstructorArguments nested input = .ok arguments output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact optionalDotConstructorArguments_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases optionalDotConstructorArguments_trace_success_sound successSound contextFrame result with
      ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.OptionalLambdaReturnTypeTraceProperties
/-! Exact optional-return execution under explicit trace laws for the actual
type parser. The arrow is silent. Source/full-window preservation is a
separate conditional theorem and is not needed for these single-child laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {typeTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem optionalLambdaReturnType_eq_none_of_absent {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol .arrow)) :
    optionalLambdaReturnType input = .ok none input := by
  simp only [optionalLambdaReturnType, getState, bind,
    DelimitedTraceInternals.symbol_absent .arrow absent, Bool.false_eq_true, if_false, pure]

theorem optionalLambdaReturnType_eq_of_present {input : State} {span : SourceSpan}
    (arrow : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .arrow }) :
    optionalLambdaReturnType input =
      match typeExpr { input with cursor := input.cursor + 1 } with
      | .ok type output => .ok (some type) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  have parsed : DeclarativeGrammar.ExactTokenParses (.symbol .arrow)
      input.declarativeRemainder span
      { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨arrow, rfl⟩
  have selected := DelimitedTraceInternals.symbol_present .arrow parsed
  have arrowResult := symbol_eq_ok_of_exactTokenParses .arrow .typeExpr parsed
  simp only [optionalLambdaReturnType, getState, bind, selected, if_true, arrowResult, pure]
  cases typeExpr { input with cursor := input.cursor + 1 } <;> rfl

theorem optionalLambdaReturnType_trace_success_sound
    (successSound : ParserTraceSuccessSound typeExpr typeTrace) :
    ParserTraceSuccessSound optionalLambdaReturnType
      (DeclarativeGrammar.OptionalLambdaReturnTypeTraceParses typeTrace) := by
  intro input output value result
  by_cases present : isSymbol input .arrow = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .typeExpr present with ⟨arrow, arrowResult⟩
    rw [optionalLambdaReturnType_eq_of_present
      (symbol_ok_tokenAt .arrow .typeExpr arrowResult).1] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | reject failure rejected => simp [typeResult] at result
    | ok type next =>
        simp only [typeResult] at result
        cases result
        rcases successSound typeResult with ⟨trace, parsed, events⟩
        exact ⟨trace, .present arrow.span
          (symbol_success_exactTokenParses .arrow .typeExpr arrowResult) parsed, events⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .arrow (Bool.eq_false_iff.mpr present)
    rw [optionalLambdaReturnType_eq_none_of_absent absent] at result
    cases result
    exact ⟨[], .absent absent, by simp only [List.append_nil]⟩

theorem optionalLambdaReturnType_trace_success_complete
    (successComplete : ParserTraceSuccessComplete typeExpr typeTrace) :
    ParserTraceSuccessComplete optionalLambdaReturnType
      (DeclarativeGrammar.OptionalLambdaReturnTypeTraceParses typeTrace) := by
  intro input value after trace parsed
  cases parsed with
  | absent absent =>
      exact ⟨input, optionalLambdaReturnType_eq_none_of_absent absent, rfl,
        by simp only [List.append_nil]⟩
  | present span arrow type =>
      have equation := optionalLambdaReturnType_eq_of_present arrow.1
      rcases arrow with ⟨token, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) type with
        ⟨output, result, afterEq, events⟩
      exact ⟨output, by rw [equation, result], afterEq, events⟩

theorem optionalLambdaReturnType_success_context
    (contextFrame : ParserSuccessContext typeExpr) :
    ParserSuccessContext optionalLambdaReturnType := by
  intro input output value result
  by_cases present : isSymbol input .arrow = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .typeExpr present with ⟨arrow, arrowResult⟩
    rw [optionalLambdaReturnType_eq_of_present
      (symbol_ok_tokenAt .arrow .typeExpr arrowResult).1] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | reject failure rejected => simp [typeResult] at result
    | ok type next =>
        simp only [typeResult] at result
        cases result
        have frame := contextFrame typeResult
        exact frame
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .arrow (Bool.eq_false_iff.mpr present)
    rw [optionalLambdaReturnType_eq_none_of_absent absent] at result
    cases result
    exact ⟨rfl, rfl⟩

theorem optionalLambdaReturnType_trace_success_iff
    (successSound : ParserTraceSuccessSound typeExpr typeTrace)
    (successComplete : ParserTraceSuccessComplete typeExpr typeTrace)
    {input : State} {value : Option TypeExpr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalLambdaReturnTypeTraceParses typeTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, optionalLambdaReturnType input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact optionalLambdaReturnType_trace_success_complete successComplete
  · rintro ⟨output, result, afterEq, events⟩
    rcases optionalLambdaReturnType_trace_success_sound successSound result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.OptionalLambdaReturnTypeRejectionTraceProperties
/-! A selected arrow propagates the actual type rejection unchanged. The
arrow-absent branch cannot reject, so there is no raw missing-arrow report. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {typeRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem optionalLambdaReturnType_reject_iff_type
    {input rejected : State} {failure : Failure} :
    optionalLambdaReturnType input = .reject failure rejected ↔
    isSymbol input .arrow = true ∧
      typeExpr { input with cursor := input.cursor + 1 } = .reject failure rejected := by
  by_cases present : isSymbol input .arrow = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .typeExpr present with ⟨arrow, arrowResult⟩
    rw [optionalLambdaReturnType_eq_of_present (symbol_ok_tokenAt .arrow .typeExpr arrowResult).1]
    cases typeExpr { input with cursor := input.cursor + 1 } <;> simp [present]
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .arrow (Bool.eq_false_iff.mpr present)
    rw [optionalLambdaReturnType_eq_none_of_absent absent]
    simp [present]

theorem optionalLambdaReturnType_reject_trace_sound
    (rejectSound : ParserTraceRejectSound typeExpr typeRejects) :
    ParserTraceRejectSound optionalLambdaReturnType
      (DeclarativeGrammar.OptionalLambdaReturnTypeTraceRejects typeRejects) := by
  intro input rejected failure result
  rcases optionalLambdaReturnType_reject_iff_type.mp result with ⟨present, typeResult⟩
  rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .typeExpr present with ⟨arrow, arrowResult⟩
  rcases rejectSound typeResult with ⟨trace, rejection, events⟩
  exact ⟨trace, .typeRejected arrow.span
    (symbol_success_exactTokenParses .arrow .typeExpr arrowResult) rejection, events⟩

theorem optionalLambdaReturnType_trace_reject_complete
    (rejectComplete : ParserTraceRejectComplete typeExpr typeRejects) :
    ParserTraceRejectComplete optionalLambdaReturnType
      (DeclarativeGrammar.OptionalLambdaReturnTypeTraceRejects typeRejects) := by
  intro input after diagnostic trace rejection
  cases rejection with
  | typeRejected span arrow type =>
      have selected := DelimitedTraceInternals.symbol_present .arrow arrow
      rcases arrow with ⟨token, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) type with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, optionalLambdaReturnType_reject_iff_type.mpr ⟨selected, result⟩,
        afterEq, reportEq, events⟩

theorem optionalLambdaReturnType_trace_reject_iff
    (rejectSound : ParserTraceRejectSound typeExpr typeRejects)
    (rejectComplete : ParserTraceRejectComplete typeExpr typeRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalLambdaReturnTypeTraceRejects typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, optionalLambdaReturnType input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact optionalLambdaReturnType_trace_reject_complete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases optionalLambdaReturnType_reject_trace_sound rejectSound result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem optionalLambdaReturnType_trace_reject_failure_iff
    (rejectSound : ParserTraceRejectSound typeExpr typeRejects)
    (rejectComplete : ParserTraceRejectComplete typeExpr typeRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalLambdaReturnTypeTraceRejects typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, optionalLambdaReturnType input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [optionalLambdaReturnType_trace_reject_iff rejectSound rejectComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.OptionalLambdaReturnTypeConcreteTraceProperties
/-! Concrete recursive-type specialization of an optional lambda return type.
The absent arrow returns none without changing state; a present arrow carries
exactly the recursive type events or complete Failure. No caller-supplied child
law or state validity is required. These are not full-lambda parser contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

theorem optionalLambdaReturnType_concrete_trace_success_sound :
    ParserTraceSuccessSound optionalLambdaReturnType
      (OptionalLambdaReturnTypeTraceParses TypeExprTraceParses) :=
  optionalLambdaReturnType_trace_success_sound typeExpr_trace_success_sound

theorem optionalLambdaReturnType_concrete_trace_success_complete :
    ParserTraceSuccessComplete optionalLambdaReturnType
      (OptionalLambdaReturnTypeTraceParses TypeExprTraceParses) :=
  optionalLambdaReturnType_trace_success_complete typeExpr_trace_success_complete

theorem optionalLambdaReturnType_concrete_success_context :
    ParserSuccessContext optionalLambdaReturnType :=
  optionalLambdaReturnType_success_context typeExpr_success_context

theorem optionalLambdaReturnType_concrete_reject_trace_sound :
    ParserTraceRejectSound optionalLambdaReturnType
      (OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects) :=
  optionalLambdaReturnType_reject_trace_sound typeExpr_reject_trace_sound

theorem optionalLambdaReturnType_concrete_trace_reject_complete :
    ParserTraceRejectComplete optionalLambdaReturnType
      (OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects) :=
  optionalLambdaReturnType_trace_reject_complete typeExpr_trace_reject_complete

theorem optionalLambdaReturnType_concrete_trace_success_iff
    {input : State} {value : Option TypeExpr} {after : Remainder} {trace : List ParseDiagnostic} :
    OptionalLambdaReturnTypeTraceParses TypeExprTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, optionalLambdaReturnType input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  optionalLambdaReturnType_trace_success_iff typeExpr_trace_success_sound typeExpr_trace_success_complete

theorem optionalLambdaReturnType_concrete_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, optionalLambdaReturnType input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  optionalLambdaReturnType_trace_reject_iff typeExpr_reject_trace_sound typeExpr_trace_reject_complete

theorem optionalLambdaReturnType_concrete_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, optionalLambdaReturnType input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  optionalLambdaReturnType_trace_reject_failure_iff typeExpr_reject_trace_sound typeExpr_trace_reject_complete

/-- Independent uniqueness and disjointness after fixing the child relations;
the bundle itself is not an outcome-existence claim. -/
theorem optionalLambdaReturnType_concrete_trace_exactOutcomeSpec {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec (OptionalLambdaReturnTypeTraceParses TypeExprTraceParses)
      (OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects) source endByte :=
  optionalLambdaReturnTypeTraceExactOutcomeSpec typeExprTraceExactOutcomeSpec

theorem optionalLambdaReturnType_concrete_trace_success_cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Option TypeExpr} {trace : List ParseDiagnostic}
    (parsed : OptionalLambdaReturnTypeTraceParses TypeExprTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  parsed.cascadeFilters (fun child => child.cascadeFilters text lexical)

/-- Only emitted events are protected, not the separate terminal report. -/
theorem optionalLambdaReturnType_concrete_trace_reject_cascadeFilters
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects source endByte
      input rejected report trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  rejection.cascadeFilters (fun child => child.cascadeFilters text lexical)

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaExpressionSuccessTraceProperties
/-! Raw lambda success composes the silent marker, recovering parameter list,
optional return type, and supplied block. All parameter recovery events remain
before return and body events. Only the final whole-state context law needs a
successful-block frame; trace soundness and completeness do not need one. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {block : Parser Block}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}

private theorem lambda_bind_ok_parts {α β : Type} {first : Parser α} {next : α → Parser β}
    {input output : State} {value : β} (result : (first >>= next) input = .ok value output) :
    ∃ item after, first input = .ok item after ∧ next item after = .ok value output := by
  cases firstResult : first input <;> simp only [bind, firstResult] at result
  case ok item after => exact ⟨item, after, rfl, result⟩
  case reject => contradiction
  case invariant => contradiction

theorem lambdaExpression_success_iff_components {input output : State} {value : Expr} :
    lambdaExpression block input = .ok value output ↔
    ∃ marker afterMarker parameters afterParameters returnType afterReturn body,
      keyword .lamKw .expression input = .ok marker afterMarker ∧
      (delimited .leftParen .rightParen true lambdaParameter .parameter .expression)
        afterMarker = .ok parameters afterParameters ∧
      optionalLambdaReturnType afterParameters = .ok returnType afterReturn ∧
      block afterReturn = .ok body output ∧
      value = lambdaExpressionTraceValue marker.span parameters returnType body := by
  constructor
  · intro result
    unfold lambdaExpression at result
    rcases lambda_bind_ok_parts result with ⟨marker, afterMarker, markerResult, rest⟩
    rcases lambda_bind_ok_parts rest with ⟨parameters, afterParameters, parametersResult, rest⟩
    rcases lambda_bind_ok_parts rest with ⟨returnType, afterReturn, returnResult, rest⟩
    rcases lambda_bind_ok_parts rest with ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    exact ⟨marker, afterMarker, parameters, afterParameters, returnType, afterReturn, body,
      markerResult, parametersResult, returnResult, bodyResult, rfl⟩
  · rintro ⟨marker, afterMarker, parameters, afterParameters, returnType, afterReturn, body,
      markerResult, parametersResult, returnResult, bodyResult, rfl⟩
    simp only [lambdaExpression, bind, markerResult, parametersResult, returnResult, bodyResult,
      pure, lambdaExpressionTraceValue]

theorem lambdaExpression_trace_success_sound
    (successSound : ParserTraceSuccessSound block blockTrace) :
    ParserTraceSuccessSound (lambdaExpression block) (LambdaExpressionTraceParses blockTrace) := by
  intro input output value result
  rcases lambdaExpression_success_iff_components.mp result with
    ⟨marker, afterMarker, parameters, afterParameters, returnType, afterReturn, body,
      markerResult, parametersResult, returnResult, bodyResult, rfl⟩
  have markerParsed := keyword_success_exactTokenParses .lamKw .expression markerResult
  have markerState := (keyword_ok_tokenAt .lamKw .expression markerResult).2
  subst afterMarker
  rcases lambdaParameters_trace_success_sound parametersResult with ⟨parameterEvents, parametersParsed, parameterEq⟩
  have parameterFrame := lambdaParameters_success_context parametersResult
  rcases optionalLambdaReturnType_concrete_trace_success_sound returnResult with ⟨returnEvents, returnParsed, returnEq⟩
  have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
  rcases successSound bodyResult with ⟨bodyEvents, bodyParsed, bodyEq⟩
  refine ⟨(parameterEvents ++ returnEvents) ++ bodyEvents,
    .parsed marker.span markerParsed parametersParsed
      (by simpa only [parameterFrame.1, parameterFrame.2] using returnParsed)
      (by simpa only [returnFrame.1, returnFrame.2, parameterFrame.1, parameterFrame.2] using bodyParsed), ?_⟩
  change afterParameters.diagnostics = input.diagnostics ++ parameterEvents at parameterEq
  rw [bodyEq, returnEq, parameterEq]
  simp only [List.append_assoc]

theorem lambdaExpression_trace_success_complete
    (successComplete : ParserTraceSuccessComplete block blockTrace) :
    ParserTraceSuccessComplete (lambdaExpression block) (LambdaExpressionTraceParses blockTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed markerSpan marker parametersParsed returnParsed bodyParsed =>
      rename_i afterMarker afterParameters afterReturn parameters returnType body parameterEvents returnEvents bodyEvents
      have markerResult := keyword_eq_ok_of_exactTokenParses .lamKw .expression marker
      rcases marker with ⟨_, rfl⟩
      rcases lambdaParameters_trace_success_complete
          (input := { input with cursor := input.cursor + 1 }) parametersParsed with
        ⟨afterParametersState, parametersResult, parametersAfterEq, parameterEq⟩
      have parameterFrame := lambdaParameters_success_context parametersResult
      have returnAtParameters : OptionalLambdaReturnTypeTraceParses TypeExprTraceParses
          afterParametersState.file.id afterParametersState.window.endByte
          afterParametersState.declarativeRemainder returnType afterReturn returnEvents := by
        simpa only [parameterFrame.1, parameterFrame.2, parametersAfterEq] using returnParsed
      rcases optionalLambdaReturnType_concrete_trace_success_complete returnAtParameters with
        ⟨afterReturnState, returnResult, returnAfterEq, returnEq⟩
      have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
      have bodyAtReturn : blockTrace afterReturnState.file.id afterReturnState.window.endByte
          afterReturnState.declarativeRemainder body after bodyEvents := by
        simpa only [returnFrame.1, returnFrame.2, parameterFrame.1, parameterFrame.2, returnAfterEq] using bodyParsed
      rcases successComplete bodyAtReturn with ⟨output, bodyResult, outputAfterEq, bodyEq⟩
      refine ⟨output, lambdaExpression_success_iff_components.mpr
        ⟨_, _, _, _, _, _, _, markerResult, parametersResult, returnResult, bodyResult, rfl⟩,
        outputAfterEq, ?_⟩
      change afterParametersState.diagnostics = input.diagnostics ++ parameterEvents at parameterEq
      rw [bodyEq, returnEq, parameterEq]
      simp only [List.append_assoc]

theorem lambdaExpression_success_context
    (contextFrame : ParserSuccessContext block) : ParserSuccessContext (lambdaExpression block) := by
  intro input output value result
  rcases lambdaExpression_success_iff_components.mp result with
    ⟨marker, afterMarker, parameters, afterParameters, returnType, afterReturn, body,
      markerResult, parametersResult, returnResult, bodyResult, _⟩
  have markerState := (keyword_ok_tokenAt .lamKw .expression markerResult).2
  subst afterMarker
  have parameterFrame := lambdaParameters_success_context parametersResult
  have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
  have bodyFrame := contextFrame bodyResult
  exact ⟨bodyFrame.1.trans (returnFrame.1.trans parameterFrame.1),
    bodyFrame.2.trans (returnFrame.2.trans parameterFrame.2)⟩

theorem lambdaExpression_trace_success_iff
    (successSound : ParserTraceSuccessSound block blockTrace)
    (successComplete : ParserTraceSuccessComplete block blockTrace)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaExpressionTraceParses blockTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, lambdaExpression block input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact lambdaExpression_trace_success_complete successComplete
  · rintro ⟨output, result, afterEq, events⟩
    rcases lambdaExpression_trace_success_sound successSound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem lambdaExpression_trace_success_state_iff
    (successSound : ParserTraceSuccessSound block blockTrace)
    (successComplete : ParserTraceSuccessComplete block blockTrace)
    (contextFrame : ParserSuccessContext block)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaExpressionTraceParses blockTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      lambdaExpression block input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases lambdaExpression_trace_success_complete successComplete parsed with ⟨output, result, afterEq, events⟩
    have frame := lambdaExpression_success_context contextFrame result
    have same := State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact (lambdaExpression_trace_success_iff successSound successComplete).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaExpressionRejectionTraceProperties
/-! Raw lambda first failures preserve parameter/return events and the exact
separate terminal report. Only the supplied block's rejection contract is
assumed; concrete parameter and type parsers need no validity premises. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {block : Parser Block}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem lambdaExpression_reject_trace_sound
    (blockSound : ParserTraceRejectSound block blockRejects) :
    ParserTraceRejectSound (lambdaExpression block) (LambdaExpressionTraceRejects blockRejects) := by
  intro input rejected failure result
  unfold lambdaExpression at result
  cases markerResult : keyword .lamKw .expression input with
  | invariant error => simp [bind, markerResult] at result
  | reject actual next =>
      simp only [bind, markerResult] at result
      cases result
      have same := acceptToken_reject_state_shape (.keyword .lamKw) .expression
        (· == .keyword .lamKw) markerResult
      subst rejected
      have reported := (keyword_reject_reports_iff .lamKw .expression).mpr ⟨failure, markerResult, rfl⟩
      exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  | ok marker afterMarker =>
      have markerParsed := keyword_success_exactTokenParses .lamKw .expression markerResult
      have markerState := (keyword_ok_tokenAt .lamKw .expression markerResult).2
      subst afterMarker
      simp only [bind, markerResult] at result
      cases parametersResult : delimited .leftParen .rightParen true lambdaParameter .parameter .expression
          { input with cursor := input.cursor + 1 } with
      | invariant error => simp [parametersResult] at result
      | reject actual next =>
          simp only [parametersResult] at result
          cases result
          rcases lambdaParameters_reject_trace_sound parametersResult with ⟨trace, rejection, events⟩
          exact ⟨trace, .parametersRejected marker.span markerParsed rejection, events⟩
      | ok parameters afterParameters =>
          simp only [parametersResult] at result
          rcases lambdaParameters_trace_success_sound parametersResult with ⟨parameterEvents, parameterList, parameterDiag⟩
          have parameterFrame := lambdaParameters_success_context parametersResult
          cases returnResult : optionalLambdaReturnType afterParameters with
          | invariant error => simp [returnResult] at result
          | reject actual next =>
              simp only [returnResult] at result
              cases result
              rcases optionalLambdaReturnType_concrete_reject_trace_sound returnResult with ⟨returnEvents, rejection, events⟩
              refine ⟨parameterEvents ++ returnEvents, .returnTypeRejected marker.span markerParsed parameterList ?_, ?_⟩
              · simpa only [parameterFrame.1, parameterFrame.2] using rejection
              · rw [events, parameterDiag]
                exact List.append_assoc _ _ _
          | ok returnType afterReturn =>
              simp only [returnResult] at result
              rcases optionalLambdaReturnType_concrete_trace_success_sound returnResult with ⟨returnEvents, returnParsed, returnDiag⟩
              have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
              cases bodyResult : block afterReturn with
              | invariant error => simp [bodyResult] at result
              | ok body next => simp [bodyResult, pure] at result
              | reject actual next =>
                  simp only [bodyResult] at result
                  cases result
                  rcases blockSound bodyResult with ⟨bodyEvents, rejection, events⟩
                  refine ⟨(parameterEvents ++ returnEvents) ++ bodyEvents,
                    .bodyRejected (returnType := returnType) (afterReturn := afterReturn.declarativeRemainder)
                      marker.span markerParsed parameterList ?_ ?_, ?_⟩
                  · simpa only [parameterFrame.1, parameterFrame.2] using returnParsed
                  · simpa only [returnFrame.1, returnFrame.2, parameterFrame.1, parameterFrame.2] using rejection
                  · rw [events, returnDiag, parameterDiag]
                    simp only [List.append_assoc, State.diagnostics]

theorem lambdaExpression_trace_reject_complete
    (blockComplete : ParserTraceRejectComplete block blockRejects) :
    ParserTraceRejectComplete (lambdaExpression block) (LambdaExpressionTraceRejects blockRejects) := by
  intro input after report trace rejection
  cases rejection with
  | markerMissing absent reported =>
      rcases (keyword_reject_reports_iff .lamKw .expression).mp ⟨absent, reported⟩ with ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [lambdaExpression, bind, result], rfl, reportEq, by simp⟩
  | parametersRejected markerSpan marker parameters =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .lamKw .expression marker
      rcases marker with ⟨_, rfl⟩
      rcases lambdaParameters_trace_reject_complete (input := { input with cursor := input.cursor + 1 }) parameters with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, by simp only [lambdaExpression, bind, markerResult, result], afterEq, reportEq, events⟩
  | returnTypeRejected markerSpan marker parameterList returnRejected =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .lamKw .expression marker
      rcases marker with ⟨_, rfl⟩
      rcases lambdaParameters_trace_success_complete (input := { input with cursor := input.cursor + 1 }) parameterList with
        ⟨afterParameters, parametersResult, parametersEq, parameterEvents⟩
      have frame := lambdaParameters_success_context parametersResult
      have returnTrace := returnRejected
      have ownerEq : afterParameters.file.id = input.file.id := congrArg (·.id) frame.1
      have endEq : afterParameters.window.endByte = input.window.endByte := congrArg (·.endByte) frame.2
      rw [← parametersEq, ← ownerEq, ← endEq] at returnTrace
      rcases optionalLambdaReturnType_concrete_trace_reject_complete returnTrace with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      refine ⟨failure, rejected, by simp only [lambdaExpression, bind, markerResult, parametersResult, result],
        afterEq, reportEq, ?_⟩
      rw [events, parameterEvents]
      exact List.append_assoc _ _ _
  | bodyRejected markerSpan marker parameterList returnParsed bodyRejected =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .lamKw .expression marker
      rcases marker with ⟨_, rfl⟩
      rcases lambdaParameters_trace_success_complete (input := { input with cursor := input.cursor + 1 }) parameterList with
        ⟨afterParameters, parametersResult, parametersEq, parameterEvents⟩
      have parameterFrame := lambdaParameters_success_context parametersResult
      have returnTrace := returnParsed
      have ownerEq : afterParameters.file.id = input.file.id := congrArg (·.id) parameterFrame.1
      have endEq : afterParameters.window.endByte = input.window.endByte := congrArg (·.endByte) parameterFrame.2
      rw [← parametersEq, ← ownerEq, ← endEq] at returnTrace
      rcases optionalLambdaReturnType_concrete_trace_success_complete returnTrace with
        ⟨afterReturn, returnResult, returnEq, returnEvents⟩
      have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
      have bodyTrace := bodyRejected
      have bodyOwner : afterReturn.file.id = input.file.id := (congrArg (·.id) returnFrame.1).trans ownerEq
      have bodyEnd : afterReturn.window.endByte = input.window.endByte := (congrArg (·.endByte) returnFrame.2).trans endEq
      rw [← returnEq, ← bodyOwner, ← bodyEnd] at bodyTrace
      rcases blockComplete bodyTrace with ⟨failure, rejected, result, afterEq, reportEq, events⟩
      refine ⟨failure, rejected,
        by simp only [lambdaExpression, bind, markerResult, parametersResult, returnResult, result], afterEq, reportEq, ?_⟩
      rw [events, returnEvents, parameterEvents]
      simp only [List.append_assoc, State.diagnostics]

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaExpressionRejectionTraceStateProperties
/-! Raw lambda rejection is exact at the suffix and complete-Failure boundary.
Whole-State reconstruction additionally states the final block's rejection
frame explicitly; it is not smuggled into the raw trace contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {block : Parser Block}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem lambdaExpression_eq_reject_of_marker
    {input rejected : State} {failure : Failure}
    (markerResult : keyword .lamKw .expression input = .reject failure rejected) :
    lambdaExpression block input = .reject failure rejected := by
  simp only [lambdaExpression, bind, markerResult]

theorem lambdaExpression_eq_reject_of_parameters
    {input afterMarker rejected : State} {marker : Token} {failure : Failure}
    (markerResult : keyword .lamKw .expression input = .ok marker afterMarker)
    (parametersResult : (delimited .leftParen .rightParen true lambdaParameter .parameter .expression)
      afterMarker = .reject failure rejected) :
    lambdaExpression block input = .reject failure rejected := by
  simp only [lambdaExpression, bind, markerResult, parametersResult]

theorem lambdaExpression_eq_reject_of_return
    {input afterMarker afterParameters rejected : State} {marker : Token}
    {parameters : DelimitedList LambdaParameter} {failure : Failure}
    (markerResult : keyword .lamKw .expression input = .ok marker afterMarker)
    (parametersResult : (delimited .leftParen .rightParen true lambdaParameter .parameter .expression)
      afterMarker = .ok parameters afterParameters)
    (returnResult : optionalLambdaReturnType afterParameters = .reject failure rejected) :
    lambdaExpression block input = .reject failure rejected := by
  simp only [lambdaExpression, bind, markerResult, parametersResult, returnResult]

theorem lambdaExpression_eq_reject_of_body
    {input afterMarker afterParameters afterReturn rejected : State} {marker : Token}
    {parameters : DelimitedList LambdaParameter} {returnType : Option TypeExpr} {failure : Failure}
    (markerResult : keyword .lamKw .expression input = .ok marker afterMarker)
    (parametersResult : (delimited .leftParen .rightParen true lambdaParameter .parameter .expression)
      afterMarker = .ok parameters afterParameters)
    (returnResult : optionalLambdaReturnType afterParameters = .ok returnType afterReturn)
    (bodyResult : block afterReturn = .reject failure rejected) :
    lambdaExpression block input = .reject failure rejected := by
  simp only [lambdaExpression, bind, markerResult, parametersResult, returnResult, bodyResult]

theorem optionalLambdaReturnType_reject_context {input rejected : State} {failure : Failure}
    (result : optionalLambdaReturnType input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have typeResult := (optionalLambdaReturnType_reject_iff_type.mp result).2
  have window := typeExpr_preservesTokenWindow { input with cursor := input.cursor + 1 }
  rw [typeResult] at window
  exact ⟨typeExpr_preservesFile.file_eq_of_reject
    (input := { input with cursor := input.cursor + 1 }) typeResult, window.2⟩

theorem lambdaExpression_reject_context
    (contextFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input rejected : State} {failure : Failure}
    (result : lambdaExpression block input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  unfold lambdaExpression at result
  cases markerResult : keyword .lamKw .expression input with
  | invariant error => simp [bind, markerResult] at result
  | reject actual next =>
      simp only [bind, markerResult] at result
      cases result
      have same := acceptToken_reject_state_shape (.keyword .lamKw) .expression
        (· == .keyword .lamKw) markerResult
      exact ⟨congrArg State.file same, congrArg State.window same⟩
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
          exact lambdaParameters_reject_context (input := { input with cursor := input.cursor + 1 }) parametersResult
      | ok parameters afterParameters =>
          simp only [parametersResult] at result
          have parameterFrame := lambdaParameters_success_context parametersResult
          cases returnResult : optionalLambdaReturnType afterParameters with
          | invariant error => simp [returnResult] at result
          | reject actual next =>
              simp only [returnResult] at result
              cases result
              have frame := optionalLambdaReturnType_reject_context returnResult
              exact ⟨frame.1.trans parameterFrame.1, frame.2.trans parameterFrame.2⟩
          | ok returnType afterReturn =>
              simp only [returnResult] at result
              have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
              cases bodyResult : block afterReturn with
              | invariant error => simp [bodyResult] at result
              | ok body next => simp [bodyResult, pure] at result
              | reject actual next =>
                  simp only [bodyResult] at result
                  cases result
                  have frame := contextFrame bodyResult
                  exact ⟨frame.1.trans (returnFrame.1.trans parameterFrame.1),
                    frame.2.trans (returnFrame.2.trans parameterFrame.2)⟩

theorem lambdaExpression_trace_reject_iff
    (rejectSound : ParserTraceRejectSound block blockRejects)
    (rejectComplete : ParserTraceRejectComplete block blockRejects)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    LambdaExpressionTraceRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, lambdaExpression block input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact lambdaExpression_trace_reject_complete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases lambdaExpression_reject_trace_sound rejectSound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem lambdaExpression_trace_reject_failure_iff
    (rejectSound : ParserTraceRejectSound block blockRejects)
    (rejectComplete : ParserTraceRejectComplete block blockRejects)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    LambdaExpressionTraceRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, lambdaExpression block input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [lambdaExpression_trace_reject_iff rejectSound rejectComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem lambdaExpression_trace_reject_failure_state_iff
    (rejectSound : ParserTraceRejectSound block blockRejects)
    (rejectComplete : ParserTraceRejectComplete block blockRejects)
    (contextFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    LambdaExpressionTraceRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      lambdaExpression block input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (lambdaExpression_trace_reject_failure_iff rejectSound rejectComplete).mp rejection with
      ⟨rejected, result, afterEq, events⟩
    have frame := lambdaExpression_reject_context contextFrame result
    have same := State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact (lambdaExpression_trace_reject_failure_iff rejectSound rejectComplete).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem lambdaExpression_trace_reject_state_iff
    (rejectSound : ParserTraceRejectSound block blockRejects)
    (rejectComplete : ParserTraceRejectComplete block blockRejects)
    (contextFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    LambdaExpressionTraceRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, lambdaExpression block input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases lambdaExpression_trace_reject_complete rejectComplete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (lambdaExpression_trace_reject_failure_state_iff rejectSound rejectComplete contextFrame).mp
      (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (lambdaExpression_trace_reject_failure_state_iff rejectSound rejectComplete contextFrame).mpr result

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaExpressionTraceProperties
/-! Raw lambda outcome existence follows from ordinary execution of the
supplied block and the concrete parameter/type parsers. It is not inferred
from independent uniqueness or disjointness. Body context, carrier, progress,
and completeness laws are unnecessary for these existence results. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {block : Parser Block}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem ordinary_bind {α β : Type} {first : Parser α} {next : α → Parser β}
    (firstOrdinary : Parser.Ordinary first) (nextOrdinary : ∀ value, Parser.Ordinary (next value)) :
    Parser.Ordinary (first >>= next) := by
  intro input
  rcases firstOrdinary input with ⟨value, after, result⟩ | ⟨failure, rejected, result⟩
  · rcases nextOrdinary value after with ⟨value, output, nextResult⟩ | ⟨failure, rejected, nextResult⟩
    · exact .inl ⟨value, output, by simp only [bind, result, nextResult]⟩
    · exact .inr ⟨failure, rejected, by simp only [bind, result, nextResult]⟩
  · exact .inr ⟨failure, rejected, by simp only [bind, result]⟩

/-- Optional return parsing has an ordinary result on every State, even when
the active window or backing tokens are noncanonical. -/
theorem optionalLambdaReturnType_ordinary_unrestricted : Parser.Ordinary optionalLambdaReturnType := by
  intro input
  by_cases present : isSymbol input .arrow = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .typeExpr present with ⟨arrow, arrowResult⟩
    have equation := optionalLambdaReturnType_eq_of_present (symbol_ok_tokenAt .arrow .typeExpr arrowResult).1
    rcases typeExpr_ordinary { input with cursor := input.cursor + 1 } with
      ⟨type, output, result⟩ | ⟨failure, rejected, result⟩
    · exact .inl ⟨some type, output, by rw [equation, result]⟩
    · exact .inr ⟨failure, rejected, by rw [equation, result]⟩
  · exact .inl ⟨none, input, optionalLambdaReturnType_eq_none_of_absent
      (symbolAbsentAt_of_isSymbol_eq_false .arrow (Bool.eq_false_iff.mpr present))⟩

theorem optionalLambdaReturnType_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    optionalLambdaReturnType input ≠ .invariant error :=
  optionalLambdaReturnType_ordinary_unrestricted.ne_invariant input error

/-- Every ordinary block parser produces an ordinary raw lambda parser. The
body need not preserve the input source, window, or token carrier for this law. -/
theorem lambdaExpression_ordinary_unrestricted (blockOrdinary : Parser.Ordinary block) :
    Parser.Ordinary (lambdaExpression block) := by
  unfold lambdaExpression
  apply ordinary_bind (keyword_ordinary .lamKw .expression)
  intro marker
  apply ordinary_bind lambdaParameters_ordinary_unrestricted
  intro parameters
  apply ordinary_bind optionalLambdaReturnType_ordinary_unrestricted
  intro returnType
  apply ordinary_bind blockOrdinary
  intro body input
  exact .inl ⟨_, input, rfl⟩

theorem lambdaExpression_ne_invariant_unrestricted
    (blockOrdinary : Parser.Ordinary block) (input : State) (error : ParserInvariantError) :
    lambdaExpression block input ≠ .invariant error :=
  (lambdaExpression_ordinary_unrestricted blockOrdinary).ne_invariant input error

/-- Concrete ordinary execution supplies the witness; the two body soundness
contracts supply its exact raw trace. No body completeness or frame is used. -/
theorem lambdaExpression_exists_trace_outcome
    (successSound : ParserTraceSuccessSound block blockTrace)
    (rejectSound : ParserTraceRejectSound block blockRejects)
    (blockOrdinary : Parser.Ordinary block) (input : State) :
    (∃ value output trace,
      lambdaExpression block input = .ok value output ∧
      LambdaExpressionTraceParses blockTrace input.file.id input.window.endByte
        input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      lambdaExpression block input = .reject failure rejected ∧
      LambdaExpressionTraceRejects blockRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases lambdaExpression_ordinary_unrestricted blockOrdinary input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases lambdaExpression_trace_success_sound successSound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases lambdaExpression_reject_trace_sound rejectSound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

/-- The same execution argument witnesses an outcome for every independent
source/endByte/remainder, without imposing a valid token window or source file. -/
theorem lambdaExpressionTrace_outcome_exists
    (successSound : ParserTraceSuccessSound block blockTrace)
    (rejectSound : ParserTraceRejectSound block blockRejects)
    (blockOrdinary : Parser.Ordinary block) (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, LambdaExpressionTraceParses blockTrace source endByte input value output trace) ∨
    (∃ rejected report trace, LambdaExpressionTraceRejects blockRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }, tokens := input.tokens, cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }, diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases lambdaExpression_exists_trace_outcome successSound rejectSound blockOrdinary state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomUnrestrictedFuelTotalityProperties
/-! One atom layer is ordinary under an explicit remaining-count bound and
the minimal three-field nested contract. Blocks need only ordinary execution.
Public recovery preserves this bounded result without inspecting child frames;
no global ordinary contract or recursive trace existence is inferred. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar ExpressionAtomDispatchTraceInternals

private theorem literal_ordinary : Parser.Ordinary literalExpression := by
  unfold literalExpression
  apply ordinary_bind coreLiteral_ordinary
  intro literal input
  exact .inl ⟨_, input, rfl⟩

private theorem name_ordinary : Parser.Ordinary identifierExpression := by
  unfold identifierExpression
  apply ordinary_bind expressionName_ordinary
  intro name input
  exact .inl ⟨_, input, rfl⟩

private theorem proxy_ordinary : Parser.Ordinary proxyExpression := by
  unfold proxyExpression
  apply ordinary_bind (symbol_ordinary .at .expression)
  intro marker
  apply ordinary_bind typeExpr_ordinary
  intro type input
  exact .inl ⟨_, input, rfl⟩

private theorem raw_ordinary (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block) (branch : ExpressionAtomDispatchBranch)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, rawParser nested block branch input = .ok value next) ∨
    (∃ failure next, rawParser nested block branch input = .reject failure next) := by
  cases branch with
  | literal => exact literal_ordinary input
  | name => exact name_ordinary input
  | dotConstructor => exact dotConstructor_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate
  | proxy => exact proxy_ordinary input
  | parenthesized => exact parenthesized_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate
  | array => exact arrayLiteral_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate
  | lambda => exact lambdaExpression_ordinary_unrestricted blockOrdinary input
  | final => exact .inr ⟨_, input, rfl⟩

theorem expressionAtomCore_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, expressionAtomCore nested block input = .ok value next) ∨
    (∃ failure next, expressionAtomCore nested block input = .reject failure next) := by
  rw [expressionAtomCore_eq_selected_raw]
  exact raw_ordinary nested block nestedFuel contract blockOrdinary (selectedBranch input) input adequate

theorem expressionAtomCore_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    expressionAtomCore nested block input ≠ .invariant error := by
  intro failed
  rcases expressionAtomCore_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract blockOrdinary input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

/-- Recovery needs no bound on a failed child's replacement carrier: its
standalone parser is ordinary on every rewound and report-extended State. -/
theorem expressionAtom_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, expressionAtom nested block input = .ok value next) ∨
    (∃ failure next, expressionAtom nested block input = .reject failure next) := by
  rcases expressionAtomCore_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract blockOrdinary input adequate with
    ⟨value, next, result⟩ | ⟨failure, failed, result⟩
  · exact .inl ⟨value, next, by simp only [expressionAtom, result]⟩
  · simp only [expressionAtom, result]
    split
    · exact .inr ⟨_, _, rfl⟩
    · exact recoverAtom_ordinary _

theorem expressionAtom_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    expressionAtom nested block input ≠ .invariant error := by
  intro failed
  rcases expressionAtom_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract blockOrdinary input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomBoundedBodyFuelTotalityProperties
/-! Both expression and block children may have only bounded ordinary
execution. A real lam marker pays one unit before its concrete parameter and
return parsers. This layer adds no child success/rejection frame or validity
premise and does not construct an atom success-progress/end-index contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar ExpressionAtomDispatchTraceInternals

/-- Only the block contract's bounded ordinary field is used here. Concrete
prefix parsers transfer its budget without constraining the body result State. -/
theorem lambdaExpression_ordinary_of_unrestrictedBodyFuel
    (block : Parser Block) (bodyFuel : Nat)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (input : State) (adequate : input.remainingCount < bodyFuel + 1) :
    (∃ value output, lambdaExpression block input = .ok value output) ∨
    (∃ failure rejected, lambdaExpression block input = .reject failure rejected) := by
  rcases keyword_ordinary .lamKw .expression input with
    ⟨marker, afterMarker, markerResult⟩ | ⟨failure, rejected, markerResult⟩
  · have markerBudget := keyword_remainingCount_lt_of_success .lamKw .expression markerResult adequate
    rcases lambdaParameters_ordinary_unrestricted afterMarker with
      ⟨parameters, afterParameters, parameterResult⟩ | ⟨failure, rejected, parameterResult⟩
    · have parameterFrame := lambdaParameters_success_context parameterResult
      have parameterCursor := delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
        lambdaParameter .parameter .expression afterMarker parameters afterParameters parameterResult
      have parameterBudget := remainingCount_lt_of_endIndex_eq
        (congrArg TokenWindow.endIndex parameterFrame.2) parameterCursor markerBudget
      rcases optionalLambdaReturnType_ordinary_unrestricted afterParameters with
        ⟨returnType, afterReturn, returnResult⟩ | ⟨failure, rejected, returnResult⟩
      · have returnFrame := optionalLambdaReturnType_concrete_success_context returnResult
        have returnCursor := optionalLambdaReturnType_cursorMonotoneOnSuccess
          afterParameters returnType afterReturn returnResult
        have returnBudget := remainingCount_lt_of_endIndex_eq
          (congrArg TokenWindow.endIndex returnFrame.2) returnCursor parameterBudget
        rcases bodyContract.ordinary afterReturn returnBudget with
          ⟨body, output, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
        · exact .inl ⟨{
            span := SourceSpan.cover marker.span body.span
            value := .lambda marker.span parameters returnType body
          }, output, by simp only [lambdaExpression, bind, markerResult, parameterResult, returnResult, bodyResult, pure]⟩
        · exact .inr ⟨failure, rejected, by
            simp only [lambdaExpression, bind, markerResult, parameterResult, returnResult, bodyResult]⟩
      · exact .inr ⟨failure, rejected, by simp only [lambdaExpression, bind, markerResult, parameterResult, returnResult]⟩
    · exact .inr ⟨failure, rejected, by simp only [lambdaExpression, bind, markerResult, parameterResult]⟩
  · exact .inr ⟨failure, rejected, by simp only [lambdaExpression, bind, markerResult]⟩

theorem lambdaExpression_ne_invariant_of_unrestrictedBodyFuel
    (block : Parser Block) (bodyFuel : Nat)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (input : State) (adequate : input.remainingCount < bodyFuel + 1) (error : ParserInvariantError) :
    lambdaExpression block input ≠ .invariant error := by
  intro failed
  rcases lambdaExpression_ordinary_of_unrestrictedBodyFuel block bodyFuel bodyContract input adequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;> rw [result] at failed <;> contradiction

/-- Outside the selected lambda branch the body parser is unused, so all
seven remaining branches reuse the established expression-child fuel proof. -/
theorem expressionAtomCore_ordinary_of_unrestrictedChildFuels
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) :
    (∃ value output, expressionAtomCore nested block input = .ok value output) ∨
    (∃ failure rejected, expressionAtomCore nested block input = .reject failure rejected) := by
  let unusedBody : Parser Block := fun state => rejectAt state { head := .expression, tail := [] } .expression
  have unusedOrdinary : Parser.Ordinary unusedBody := fun state => .inr ⟨_, state, rfl⟩
  have otherBranches := expressionAtomCore_ordinary_of_unrestrictedElementFuel nested unusedBody
    nestedFuel nestedContract unusedOrdinary input nestedAdequate
  rw [expressionAtomCore_eq_selected_raw] at otherBranches ⊢
  cases chosen : selectedBranch input with
  | lambda => exact lambdaExpression_ordinary_of_unrestrictedBodyFuel block bodyFuel bodyContract input bodyAdequate
  | literal | name | dotConstructor | proxy | parenthesized | array | final =>
      simpa only [chosen, rawParser] using otherBranches

theorem expressionAtomCore_ne_invariant_of_unrestrictedChildFuels
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) (error : ParserInvariantError) :
    expressionAtomCore nested block input ≠ .invariant error := by
  intro failed
  rcases expressionAtomCore_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
      nestedContract bodyContract input nestedAdequate bodyAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;> rw [result] at failed <;> contradiction

/-- Recovery is ordinary on every failed replacement carrier, independently
of both original budgets and without a rejection end-index frame. -/
theorem expressionAtom_ordinary_of_unrestrictedChildFuels
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) :
    (∃ value output, expressionAtom nested block input = .ok value output) ∨
    (∃ failure rejected, expressionAtom nested block input = .reject failure rejected) := by
  rcases expressionAtomCore_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
      nestedContract bodyContract input nestedAdequate bodyAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · exact .inl ⟨value, output, by simp only [expressionAtom, result]⟩
  · simp only [expressionAtom, result]
    split
    · exact .inr ⟨_, _, rfl⟩
    · exact recoverAtom_ordinary _

theorem expressionAtom_ne_invariant_of_unrestrictedChildFuels
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) (error : ParserInvariantError) :
    expressionAtom nested block input ≠ .invariant error := by
  intro failed
  rcases expressionAtom_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
      nestedContract bodyContract input nestedAdequate bodyAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomUnrestrictedChildContractProperties
/-! One actual recovering atom constructs a minimal fuel contract from its
two supplied children. Both rejected children must preserve endIndex because
their replacement carriers can become successful public recovery outcomes.
No source, token, byte-end, diagnostic, or validity frame is required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open ExpressionAtomInternals

/-- Success endIndex and progress hold on every State, independent of fuel.
Only the ordinary field uses the chosen atom budget and its two child bounds. -/
theorem expressionAtom_unrestrictedChildContract
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel atomFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (nestedBound : atomFuel ≤ nestedFuel + 1) (bodyBound : atomFuel ≤ bodyFuel + 1) :
    UnrestrictedFuelElementContract (expressionAtom nested block) atomFuel where
  endIndexOnSuccess := expressionAtom_endIndex_onSuccess nestedContract.endIndexOnSuccess nestedReject
    bodyContract.endIndexOnSuccess bodyReject
  cursorLtOnSuccess := expressionAtom_cursor_lt_onSuccess nested block
    (fun _ _ _ result => Nat.le_of_lt (nestedContract.cursorLtOnSuccess result))
    (fun _ _ _ result => Nat.le_of_lt (bodyContract.cursorLtOnSuccess result))
  ordinary input adequate := expressionAtom_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
    nestedContract bodyContract input (Nat.lt_of_lt_of_le adequate nestedBound) (Nat.lt_of_lt_of_le adequate bodyBound)

/-- Equal child budgets construct the next atom layer; this is a conditional
one-layer step, not a recursively closed expression or block contract. -/
theorem expressionAtom_unrestrictedChildContract_succ
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested fuel)
    (bodyContract : UnrestrictedFuelElementContract block fuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex) :
    UnrestrictedFuelElementContract (expressionAtom nested block) (fuel + 1) :=
  expressionAtom_unrestrictedChildContract nested block fuel fuel (fuel + 1)
    nestedContract bodyContract nestedReject bodyReject (Nat.le_refl _) (Nat.le_refl _)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ControlLeafDiagnosticTraceProperties
/-! Unconditional exact traces for the real Core break and continue leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem breakStatement_trace_success_sound :
    StatementTraceSuccessSound breakStatement DeclarativeGrammar.BreakStatementTraceParses :=
  ControlInternals.terminatedControl_trace_success_sound .breakKw .breakStmt

theorem breakStatement_trace_success_complete :
    StatementTraceSuccessComplete breakStatement DeclarativeGrammar.BreakStatementTraceParses :=
  ControlInternals.terminatedControl_trace_success_complete .breakKw .breakStmt

theorem breakStatement_success_context : StatementSuccessContext breakStatement :=
  ControlInternals.terminatedControl_success_context .breakKw .breakStmt

theorem breakStatement_trace_reject_sound :
    StatementTraceRejectSound breakStatement DeclarativeGrammar.BreakStatementTraceRejects :=
  ControlInternals.terminatedControl_trace_reject_sound .breakKw .breakStmt

theorem breakStatement_trace_reject_complete :
    StatementTraceRejectComplete breakStatement DeclarativeGrammar.BreakStatementTraceRejects :=
  ControlInternals.terminatedControl_trace_reject_complete .breakKw .breakStmt

theorem continueStatement_trace_success_sound :
    StatementTraceSuccessSound continueStatement DeclarativeGrammar.ContinueStatementTraceParses :=
  ControlInternals.terminatedControl_trace_success_sound .continueKw .continueStmt

theorem continueStatement_trace_success_complete :
    StatementTraceSuccessComplete continueStatement DeclarativeGrammar.ContinueStatementTraceParses :=
  ControlInternals.terminatedControl_trace_success_complete .continueKw .continueStmt

theorem continueStatement_success_context : StatementSuccessContext continueStatement :=
  ControlInternals.terminatedControl_success_context .continueKw .continueStmt

theorem continueStatement_trace_reject_sound :
    StatementTraceRejectSound continueStatement DeclarativeGrammar.ContinueStatementTraceRejects :=
  ControlInternals.terminatedControl_trace_reject_sound .continueKw .continueStmt

theorem continueStatement_trace_reject_complete :
    StatementTraceRejectComplete continueStatement DeclarativeGrammar.ContinueStatementTraceRejects :=
  ControlInternals.terminatedControl_trace_reject_complete .continueKw .continueStmt

/-- Actual `break;` success retains the exact covering AST and remainder,
and is equivalent to the silent independent trace on any incoming state. -/
theorem breakStatement_trace_success_iff
    {input : State} {statement : Statement} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BreakStatementTraceParses input.file.id input.window.endByte
      input.declarativeRemainder statement after trace ↔
    ∃ output, breakStatement input = .ok statement output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  ControlInternals.terminatedControl_trace_success_iff .breakKw .breakStmt

theorem continueStatement_trace_success_iff
    {input : State} {statement : Statement} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ContinueStatementTraceParses input.file.id input.window.endByte
      input.declarativeRemainder statement after trace ↔
    ∃ output, continueStatement input = .ok statement output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  ControlInternals.terminatedControl_trace_success_iff .continueKw .continueStmt

/-- The keyword or semicolon's complete first-failure report remains
uncommitted, preserving every incoming diagnostic event. -/
theorem breakStatement_trace_reject_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BreakStatementTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, breakStatement input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  ControlInternals.terminatedControl_trace_reject_iff .breakKw .breakStmt

theorem continueStatement_trace_reject_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ContinueStatementTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, continueStatement input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  ControlInternals.terminatedControl_trace_reject_iff .continueKw .continueStmt

theorem breakStatement_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BreakStatementTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, breakStatement input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  ControlInternals.terminatedControl_trace_reject_failure_iff .breakKw .breakStmt

theorem continueStatement_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ContinueStatementTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, continueStatement input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  ControlInternals.terminatedControl_trace_reject_failure_iff .continueKw .continueStmt

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionPostfixUnrestrictedChildContractProperties
/-! Actual atom-plus-postfix execution and its minimal contract are built from
nested-expression/body contracts. The intermediate atom contract is constructed,
not assumed. Rejected endIndex preservation is explicit because atom recovery
can turn a rejected carrier into success. No recursive closure is asserted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser Expr} {block : Parser Block}

/-- The minimum budget satisfies both child bounds and suffices to construct
the real atom contract internally. All remaining caller assumptions are on the
two supplied children; no atom contract or source/token frame is left abstract. -/
theorem expressionPostfix_ordinary_of_unrestrictedChildFuels
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) :
    (∃ value output, expressionPostfix nested block input = .ok value output) ∨
    (∃ failure rejected, expressionPostfix nested block input = .reject failure rejected) := by
  have atomContract := expressionAtom_unrestrictedChildContract nested block nestedFuel bodyFuel
    (min (nestedFuel + 1) (bodyFuel + 1)) nestedContract bodyContract nestedReject bodyReject
    (Nat.min_le_left _ _) (Nat.min_le_right _ _)
  exact expressionPostfix_ordinary_of_unrestrictedElementFuels nested block
    (min (nestedFuel + 1) (bodyFuel + 1)) nestedFuel atomContract nestedContract input
    (by omega) nestedAdequate

theorem expressionPostfix_ne_invariant_of_unrestrictedChildFuels
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) (error : ParserInvariantError) :
    expressionPostfix nested block input ≠ .invariant error := by
  intro failed
  rcases expressionPostfix_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
      nestedContract bodyContract nestedReject bodyReject input nestedAdequate bodyAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;> rw [result] at failed <;> contradiction

/-- Successful postfix replies preserve endIndex and advance strictly on all
States. Fuel bounds restrict only the ordinary field of the resulting contract. -/
theorem expressionPostfix_unrestrictedChildContract
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel postfixFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (nestedBound : postfixFuel ≤ nestedFuel + 1) (bodyBound : postfixFuel ≤ bodyFuel + 1) :
    UnrestrictedFuelElementContract (expressionPostfix nested block) postfixFuel := by
  have nestedFrame : Parser.PreservesEndIndex nested :=
    .of_success_reject nestedContract.endIndexOnSuccess nestedReject
  have bodyFrame : Parser.PreservesEndIndex block :=
    .of_success_reject bodyContract.endIndexOnSuccess bodyReject
  exact {
    endIndexOnSuccess := (expressionPostfix_preservesEndIndex nested block
      (expressionAtom_preservesEndIndex nested block nestedFrame bodyFrame) nestedFrame).endIndex_eq_of_ok
    cursorLtOnSuccess := ExpressionAtomInternals.expressionPostfix_cursor_lt_onSuccess nested block
      (fun _ _ _ result => Nat.le_of_lt (nestedContract.cursorLtOnSuccess result))
      (fun _ _ _ result => Nat.le_of_lt (bodyContract.cursorLtOnSuccess result))
    ordinary input adequate := expressionPostfix_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
      nestedContract bodyContract nestedReject bodyReject input
      (Nat.lt_of_lt_of_le adequate nestedBound) (Nat.lt_of_lt_of_le adequate bodyBound)
  }

/-- Equal child budgets close one actual postfix layer at the successor
budget, without promoting either supplied child to a recursive implementation. -/
theorem expressionPostfix_unrestrictedChildContract_succ
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested fuel)
    (bodyContract : UnrestrictedFuelElementContract block fuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex) :
    UnrestrictedFuelElementContract (expressionPostfix nested block) (fuel + 1) :=
  expressionPostfix_unrestrictedChildContract nested block fuel fuel (fuel + 1)
    nestedContract bodyContract nestedReject bodyReject (Nat.le_refl _) (Nat.le_refl _)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionUnaryUnrestrictedFuelContractProperties
/-! Actual unary layers inherit an unrestricted contract at the same budget
as their postfix parser. Prefix scanning cannot increase the remaining count,
but the empty prefix pays no extra fuel. Successful numeric frames and progress
hold on every State; only ordinary execution is restricted by the fuel bound.
No source, token-carrier, byte-end, or validity assumptions are needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

theorem expressionUnary_endIndex_onSuccess
    (nested : Parser Expr) (block : Parser Block)
    (postfixSuccess : ∀ {input output value},
      expressionPostfix nested block input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    {input output : State} {value : Expr}
    (result : expressionUnary nested block input = .ok value output) :
    output.window.endIndex = input.window.endIndex := by
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, middle, prefixResult⟩
  have prefixFrame := congrArg TokenWindow.endIndex
    (unaryOperators_success_context (input.remainingCount + 1) [] prefixResult).2
  simp only [expressionUnary, prefixResult] at result
  cases postfixResult : expressionPostfix nested block middle with
  | invariant error => simp [postfixResult] at result
  | reject failure rejected => simp [postfixResult] at result
  | ok base next =>
      simp only [postfixResult] at result
      cases result
      exact (postfixSuccess postfixResult).trans prefixFrame

/-- A rejected postfix carrier is passed through unchanged, so the all-reply
numeric frame requires its rejection frame as well as its success frame. -/
theorem expressionUnary_preservesEndIndex
    (nested : Parser Expr) (block : Parser Block)
    (postfixFrame : Parser.PreservesEndIndex (expressionPostfix nested block)) :
    Parser.PreservesEndIndex (expressionUnary nested block) := by
  intro input
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, middle, prefixResult⟩
  have prefixFrame := congrArg TokenWindow.endIndex
    (unaryOperators_success_context (input.remainingCount + 1) [] prefixResult).2
  simp only [expressionUnary, prefixResult]
  cases postfixResult : expressionPostfix nested block middle with
  | invariant error => trivial
  | reject failure rejected =>
      exact (postfixFrame.endIndex_eq_of_reject postfixResult).trans prefixFrame
  | ok base next =>
      exact (postfixFrame.endIndex_eq_of_ok postfixResult).trans prefixFrame

theorem expressionUnary_ordinary_of_unrestrictedPostfixFuel
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (postfixContract : UnrestrictedFuelElementContract (expressionPostfix nested block) fuel)
    (input : State) (adequate : input.remainingCount < fuel) :
    (∃ value output, expressionUnary nested block input = .ok value output) ∨
    (∃ failure rejected, expressionUnary nested block input = .reject failure rejected) := by
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, middle, prefixResult⟩
  have prefixFrame := congrArg TokenWindow.endIndex
    (unaryOperators_success_context (input.remainingCount + 1) [] prefixResult).2
  have prefixCursor := unaryOperators_cursorMonotoneOnSuccess
    (input.remainingCount + 1) [] input operators middle prefixResult
  have middleAdequate := remainingCount_lt_of_endIndex_eq prefixFrame prefixCursor adequate
  rcases postfixContract.ordinary middle middleAdequate with
    ⟨base, output, postfixResult⟩ | ⟨failure, rejected, postfixResult⟩
  · exact Or.inl ⟨applyUnaryOperators operators base, output, by
      simp only [expressionUnary, prefixResult, postfixResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [expressionUnary, prefixResult, postfixResult]⟩

theorem expressionUnary_ne_invariant_of_unrestrictedPostfixFuel
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (postfixContract : UnrestrictedFuelElementContract (expressionPostfix nested block) fuel)
    (input : State) (adequate : input.remainingCount < fuel) (error : ParserInvariantError) :
    expressionUnary nested block input ≠ .invariant error := by
  intro failed
  rcases expressionUnary_ordinary_of_unrestrictedPostfixFuel nested block fuel
      postfixContract input adequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- This is a same-fuel lift: the maximal unary prefix is allowed to be empty. -/
theorem expressionUnary_unrestrictedPostfixContract
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (postfixContract : UnrestrictedFuelElementContract (expressionPostfix nested block) fuel) :
    UnrestrictedFuelElementContract (expressionUnary nested block) fuel where
  endIndexOnSuccess := expressionUnary_endIndex_onSuccess nested block postfixContract.endIndexOnSuccess
  cursorLtOnSuccess := expressionUnary_cursor_lt_onSuccess nested block postfixContract.cursorLtOnSuccess
  ordinary := expressionUnary_ordinary_of_unrestrictedPostfixFuel nested block fuel postfixContract

/-- The actual postfix contract is constructed from the supplied children.
Neither that construction nor this unary lift asserts recursive closure. -/
theorem expressionUnary_unrestrictedChildContract
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel unaryFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (nestedBound : unaryFuel ≤ nestedFuel + 1) (bodyBound : unaryFuel ≤ bodyFuel + 1) :
    UnrestrictedFuelElementContract (expressionUnary nested block) unaryFuel :=
  expressionUnary_unrestrictedPostfixContract nested block unaryFuel
    (expressionPostfix_unrestrictedChildContract nested block nestedFuel bodyFuel unaryFuel
      nestedContract bodyContract nestedReject bodyReject nestedBound bodyBound)

theorem expressionUnary_unrestrictedChildContract_succ
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested fuel)
    (bodyContract : UnrestrictedFuelElementContract block fuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex) :
    UnrestrictedFuelElementContract (expressionUnary nested block) (fuel + 1) :=
  expressionUnary_unrestrictedChildContract nested block fuel fuel (fuel + 1)
    nestedContract bodyContract nestedReject bodyReject (Nat.le_refl _) (Nat.le_refl _)

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionUnaryTraceExistenceProperties
/-! Bounded unary trace existence is separate from unary joint exactness.
Successful silent prefix scanning and a bounded postfix contract supply actual
ordinary execution; corresponding soundness supplies its independent trace. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {postfixTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {postfixRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (successSound : ParserTraceSuccessSound (expressionPostfix nested block) postfixTrace)
  (rejectSound : ParserTraceRejectSound (expressionPostfix nested block) postfixRejects)
  (fuel : Nat) (contract : UnrestrictedFuelElementContract (expressionPostfix nested block) fuel)

include successSound rejectSound contract

theorem expressionUnary_exists_trace_outcome_of_unrestrictedPostfixFuel
    (input : State) (adequate : input.remainingCount < fuel) :
    (∃ value output trace,
      expressionUnary nested block input = .ok value output ∧
      ExpressionUnaryTraceParses postfixTrace input.file.id input.window.endByte
        input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      expressionUnary nested block input = .reject failure rejected ∧
      ExpressionUnaryTraceRejects postfixRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases expressionUnary_ordinary_of_unrestrictedPostfixFuel nested block fuel contract input adequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases expressionUnary_trace_success_sound successSound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases expressionUnary_reject_trace_sound rejectSound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem expressionUnaryTrace_outcome_exists_of_unrestrictedPostfixFuel
    (source : SourceId) (endByte : Nat) (input : Remainder)
    (adequate : input.endIndex - input.cursor < fuel) :
    (∃ value after trace, ExpressionUnaryTraceParses postfixTrace source endByte input value after trace) ∨
    (∃ rejected report trace, ExpressionUnaryTraceRejects postfixRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }, tokens := input.tokens, cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }, diagnosticsRev := []
  }
  rcases expressionUnary_exists_trace_outcome_of_unrestrictedPostfixFuel successSound rejectSound fuel contract state adequate with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, rejection⟩

end Solcore.Syntax.Parser.ExpressionInternals
end
