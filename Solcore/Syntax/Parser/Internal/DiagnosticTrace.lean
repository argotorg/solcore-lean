import Solcore.Syntax.DeclarativeIsolatedBlockTraceGrammar
import Solcore.Syntax.Parser.Block
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Internal.TraceBasics
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.TriviaProofs
import Solcore.Syntax.Parser.Primitive
import Solcore.Syntax.DeclarativeCoreBlockTraceGrammar
import Solcore.Syntax.DeclarativeCoreBlockRejectionTraceGrammar
import Solcore.Syntax.Parser.Internal.DelimitedTotality

/-!
Foundations of the parser's trace proofs: the contracts a traced child parser
satisfies, the diagnostic state they read, exact-token primitives, sequencing,
transactional choice, and cascade laws.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.BlockDiagnosticTraceContracts
/-! Explicit inner-parser contracts for diagnostic-trace lifting. These are
execution/grammar bridges, not independent syntax or concrete Core guarantees.
All states, including arbitrary existing diagnostics, are quantified. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every inner success has an independently described appended trace. -/
def BlockTraceSuccessSound (parser : Parser Block)
    (blockParses : SourceId → Nat → DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input output : State} {body : Block}, parser input = .ok body output →
    ∃ trace, blockParses input.file.id input.window.endByte
      input.declarativeRemainder body output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace

/-- Every inner ordinary rejection has an exact uncommitted report and a
preceding appended trace; no final report is implicitly added here. -/
def BlockTraceRejectSound (parser : Parser Block)
    (blockRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input rejected : State} {failure : Failure}, parser input = .reject failure rejected →
    ∃ trace, blockRejects input.file.id input.window.endByte
      input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace

/-- Independent inner success executes with the same AST and remainder and
appends its trace after any supplied prior diagnostics. -/
def BlockTraceSuccessComplete (parser : Parser Block)
    (blockParses : SourceId → Nat → DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {body : Block} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic},
    blockParses input.file.id input.window.endByte input.declarativeRemainder body after trace →
      ∃ output, parser input = .ok body output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace

/-- Independent inner rejection executes with the specified report, remainder,
and appended trace. Whole rejected-state or failure-record equality is not assumed. -/
def BlockTraceRejectComplete (parser : Parser Block)
    (blockRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic},
    blockRejects input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace →
      ∃ failure rejected, parser input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        rejected.diagnostics = input.diagnostics ++ trace

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DiagnosticTraceContracts
/-! Generic execution contracts for complete appended diagnostic traces.
All incoming states and prior diagnostics are quantified. Source/full-window
preservation is separate; token-carrier preservation is not assumed here. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

def ParserTraceSuccessSound {α : Type} (parser : Parser α)
    (traceParses : SourceId → Nat → DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input output : State} {value : α}, parser input = .ok value output →
    ∃ trace, traceParses input.file.id input.window.endByte input.declarativeRemainder
      value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace

def ParserTraceSuccessComplete {α : Type} (parser : Parser α)
    (traceParses : SourceId → Nat → DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {value : α} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic},
    traceParses input.file.id input.window.endByte input.declarativeRemainder value after trace →
      ∃ output, parser input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace

def ParserSuccessContext {α : Type} (parser : Parser α) : Prop :=
  ∀ {input output : State} {value : α}, parser input = .ok value output →
    output.file = input.file ∧ output.window = input.window

def ParserTraceRejectSound {α : Type} (parser : Parser α)
    (traceRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input rejected : State} {failure : Failure}, parser input = .reject failure rejected →
    ∃ trace, traceRejects input.file.id input.window.endByte input.declarativeRemainder
      rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace

def ParserTraceRejectComplete {α : Type} (parser : Parser α)
    (traceRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic},
    traceRejects input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace →
      ∃ failure rejected, parser input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        rejected.diagnostics = input.diagnostics ++ trace

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DiagnosticTraceCompletenessFromSoundnessProperties
/-! Exact trace functionality and ordinary execution turn both soundness
directions into completeness. The independent joint specification alone gives
no existence: the explicit no-invariant assumption excludes the third runtime
reply. No validity, source/window frame, or token-carrier law is imposed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {α : Type} {parser : Parser α}
  {traceParses : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {traceRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

/-- At one input, soundness and absence of invariant failure realize every
successful trace with the same AST, remainder, and appended event sequence. -/
theorem trace_success_exists_ok_of_sound
    (successSound : ParserTraceSuccessSound parser traceParses)
    (rejectSound : ParserTraceRejectSound parser traceRejects)
    {input : State}
    (outcomes : TraceExactOutcomeSpec traceParses traceRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, parser input ≠ .invariant error)
    {value : α} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : traceParses input.file.id input.window.endByte input.declarativeRemainder value after trace) :
    ∃ output, parser input = .ok value output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace := by
  cases result : parser input with
  | ok actual output =>
      rcases successSound result with ⟨actualTrace, actualParsed, events⟩
      rcases outcomes.successResultUnique actualParsed parsed with ⟨rfl, afterEq, rfl⟩
      exact ⟨output, rfl, afterEq, events⟩
  | reject failure output =>
      rcases rejectSound result with ⟨actualTrace, rejected, _⟩
      exact False.elim (outcomes.successRejectDisjoint rejected ⟨value, after, trace, parsed⟩)
  | invariant error => exact False.elim (invariantFree error result)

/-- At one input, rejection completeness retains its exact terminal report
separately from the preceding event suffix; no report is added to that suffix. -/
theorem trace_reject_exists_reject_of_sound
    (successSound : ParserTraceSuccessSound parser traceParses)
    (rejectSound : ParserTraceRejectSound parser traceRejects)
    {input : State}
    (outcomes : TraceExactOutcomeSpec traceParses traceRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, parser input ≠ .invariant error)
    {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : traceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace) :
    ∃ failure output, parser input = .reject failure output ∧ output.declarativeRemainder = after ∧
      failure.toDiagnostic = report ∧ output.diagnostics = input.diagnostics ++ trace := by
  cases result : parser input with
  | ok value output =>
      rcases successSound result with ⟨actualTrace, parsed, _⟩
      exact False.elim (outcomes.successRejectDisjoint rejection ⟨value, _, actualTrace, parsed⟩)
  | reject failure output =>
      rcases rejectSound result with ⟨actualTrace, actualRejected, events⟩
      rcases outcomes.rejectResultUnique actualRejected rejection with ⟨afterEq, reportEq, rfl⟩
      exact ⟨failure, output, rfl, afterEq, reportEq, events⟩
  | invariant error => exact False.elim (invariantFree error result)

/-- Global no-invariant execution supplies the unrestricted success contract,
including arbitrary incoming diagnostic accumulators. -/
theorem trace_success_complete_of_sound
    (successSound : ParserTraceSuccessSound parser traceParses)
    (rejectSound : ParserTraceRejectSound parser traceRejects)
    (outcomes : ∀ source endByte, TraceExactOutcomeSpec traceParses traceRejects source endByte)
    (invariantFree : ∀ input error, parser input ≠ .invariant error) :
    ParserTraceSuccessComplete parser traceParses := by
  intro input value after trace parsed
  exact trace_success_exists_ok_of_sound successSound rejectSound
    (outcomes input.file.id input.window.endByte) (invariantFree input) parsed

/-- Global no-invariant execution supplies the unrestricted rejection
contract, preserving the actual failure payload and exact ordered events. -/
theorem trace_reject_complete_of_sound
    (successSound : ParserTraceSuccessSound parser traceParses)
    (rejectSound : ParserTraceRejectSound parser traceRejects)
    (outcomes : ∀ source endByte, TraceExactOutcomeSpec traceParses traceRejects source endByte)
    (invariantFree : ∀ input error, parser input ≠ .invariant error) :
    ParserTraceRejectComplete parser traceRejects := by
  intro input after report trace rejection
  exact trace_reject_exists_reject_of_sound successSound rejectSound
    (outcomes input.file.id input.window.endByte) (invariantFree input) rejection

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DiagnosticTraceStateProperties
/-! Exact state reconstruction retains all remainder fields, including its
token carrier and end index. Replacing it by a cursor-only update requires
explicit carrier equalities. These are state equalities, not parser contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.State

open DeclarativeGrammar

theorem eq_of_file_endByte_remainder_diagnostics
    {left right : State} (fileEq : left.file = right.file)
    (endByteEq : left.window.endByte = right.window.endByte)
    (remainderEq : left.declarativeRemainder = right.declarativeRemainder)
    (diagnosticsEq : left.diagnostics = right.diagnostics) : left = right := by
  cases left with
  | mk leftFile leftTokens leftCursor leftWindow leftDiagnostics =>
      cases right with
      | mk rightFile rightTokens rightCursor rightWindow rightDiagnostics =>
          cases leftWindow
          cases rightWindow
          simp only [declarativeRemainder, Remainder.mk.injEq] at remainderEq
          rcases remainderEq with ⟨rfl, rfl, rfl⟩
          have reversed := congrArg List.reverse diagnosticsEq
          simp only [diagnostics, List.reverse_reverse] at reversed
          cases fileEq
          cases endByteEq
          cases reversed
          rfl

def traceResult (input : State) (after : Remainder) (trace : List ParseDiagnostic) : State := {
  file := input.file
  tokens := after.tokens
  cursor := after.cursor
  window := { endIndex := after.endIndex, endByte := input.window.endByte }
  diagnosticsRev := trace.reverse ++ input.diagnosticsRev
}

theorem traceResult_declarativeRemainder (input : State) (after : Remainder) (trace : List ParseDiagnostic) :
    (input.traceResult after trace).declarativeRemainder = after := rfl

theorem traceResult_diagnostics (input : State) (after : Remainder) (trace : List ParseDiagnostic) :
    (input.traceResult after trace).diagnostics = input.diagnostics ++ trace := by
  simp only [traceResult, diagnostics, List.reverse_append, List.reverse_reverse]

theorem eq_traceResult_of_fields {input output : State} {after : Remainder} {trace : List ParseDiagnostic}
    (fileEq : output.file = input.file) (endByteEq : output.window.endByte = input.window.endByte)
    (remainderEq : output.declarativeRemainder = after)
    (events : output.diagnostics = input.diagnostics ++ trace) :
    output = input.traceResult after trace :=
  eq_of_file_endByte_remainder_diagnostics fileEq endByteEq
    (remainderEq.trans (input.traceResult_declarativeRemainder after trace).symm)
    (events.trans (input.traceResult_diagnostics after trace).symm)

theorem traceResult_eq_cursor_update {input : State} {after : Remainder} (trace : List ParseDiagnostic)
    (tokensEq : after.tokens = input.tokens) (endIndexEq : after.endIndex = input.window.endIndex) :
    input.traceResult after trace =
      { input with cursor := after.cursor, diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases input
  rename_i file tokens cursor window diagnosticsRev
  cases window
  simp only [traceResult, tokensEq, endIndexEq]

end Solcore.Syntax.Parser.State
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties
/-! Exact token grammar determines primitive success without validity premises.
These consumers advance only the cursor and emit no raw diagnostic event. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- An accepted exact token changes only the cursor, not the diagnostic trace. -/
theorem acceptToken_eq_ok_of_exactTokenParses
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) {kind : TokenKind}
    (accepted : accepts kind = true) {input : State} {span : SourceSpan}
    {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses kind
      input.declarativeRemainder span after) :
    acceptToken expected context accepts input =
      .ok { span, value := kind } { input with cursor := input.cursor + 1 } := by
  have current := parsed.1
  change input.cursor < input.window.endIndex ∧
    input.tokens[input.cursor]? = some { span, value := kind } at current
  have found : input.peek? = some { span, value := kind } := by
    simp only [State.peek?, current.1, if_true, current.2]
  simp only [acceptToken, found, accepted, if_true]

/-- Every successful token consumer preserves the complete raw diagnostic list. -/
theorem acceptToken_success_diagnostics_eq
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) {input output : State} {token : Token}
    (result : acceptToken expected context accepts input = .ok token output) :
    output.diagnostics = input.diagnostics := by
  rw [(acceptToken_ok_state_shape expected context accepts result).2]
  rfl

/-- Fixed token, exact remainder, and silent diagnostics are complete in both
directions; the recognizer may accept other kinds without weakening this claim. -/
theorem acceptToken_exactToken_success_iff
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) {kind : TokenKind}
    (accepted : accepts kind = true) {input : State} {span : SourceSpan}
    {after : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ExactTokenParses kind input.declarativeRemainder span after ↔
      ∃ output, acceptToken expected context accepts input =
        .ok { span, value := kind } output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  constructor
  · intro parsed
    exact ⟨_, acceptToken_eq_ok_of_exactTokenParses expected context accepts accepted parsed,
      parsed.2.symm, rfl⟩
  · rintro ⟨output, result, remainderEq, _⟩
    rcases acceptToken_ok_state_shape expected context accepts result with ⟨found, shape⟩
    refine ⟨tokenAt_of_peek?_eq_some found, ?_⟩
    rw [← remainderEq, shape]
    rfl

private theorem keyword_accepts_self (value : HardKeyword) :
    ((.keyword value : TokenKind) == .keyword value) = true := by
  change instBEqHardKeyword.beq value value = true
  cases value <;> rfl

private theorem symbol_accepts_self (value : Symbol) :
    ((.symbol value : TokenKind) == .symbol value) = true := by
  change instBEqSymbol.beq value value = true
  cases value <;> rfl

private theorem contextual_accepts_self (value : ContextualKeyword) :
    (TokenKind.identifier value.spelling).isContextual value = true := by
  simp [TokenKind.isContextual]

/-- A hard-keyword grammar step returns the exact keyword token and state. -/
theorem keyword_eq_ok_of_exactTokenParses
    (value : HardKeyword) (context : ParseContext)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.keyword value)
      input.declarativeRemainder span after) :
    keyword value context input = .ok { span, value := .keyword value }
      { input with cursor := input.cursor + 1 } :=
  acceptToken_eq_ok_of_exactTokenParses (.keyword value) context
    (· == .keyword value) (keyword_accepts_self value) parsed

/-- A symbol grammar step returns the exact symbol token and state. -/
theorem symbol_eq_ok_of_exactTokenParses
    (value : Symbol) (context : ParseContext)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.symbol value)
      input.declarativeRemainder span after) :
    symbol value context input = .ok { span, value := .symbol value }
      { input with cursor := input.cursor + 1 } :=
  acceptToken_eq_ok_of_exactTokenParses (.symbol value) context
    (· == .symbol value) (symbol_accepts_self value) parsed

/-- A contextual word returns an identifier token, not a hard keyword. -/
theorem contextual_eq_ok_of_exactTokenParses
    (value : ContextualKeyword) (context : ParseContext)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.identifier value.spelling)
      input.declarativeRemainder span after) :
    contextual value context input = .ok { span, value := .identifier value.spelling }
      { input with cursor := input.cursor + 1 } :=
  acceptToken_eq_ok_of_exactTokenParses (.contextual value) context
    (·.isContextual value) (contextual_accepts_self value) parsed

/-- Hard-keyword exact grammar and executable success have identical silent traces. -/
theorem keyword_exactToken_success_iff
    (value : HardKeyword) (context : ParseContext)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ExactTokenParses (.keyword value)
      input.declarativeRemainder span after ↔
      ∃ output, keyword value context input = .ok { span, value := .keyword value } output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics :=
  acceptToken_exactToken_success_iff (.keyword value) context
    (· == .keyword value) (keyword_accepts_self value)

/-- Symbol exact grammar and executable success have identical silent traces. -/
theorem symbol_exactToken_success_iff
    (value : Symbol) (context : ParseContext)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ExactTokenParses (.symbol value)
      input.declarativeRemainder span after ↔
      ∃ output, symbol value context input = .ok { span, value := .symbol value } output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics :=
  acceptToken_exactToken_success_iff (.symbol value) context
    (· == .symbol value) (symbol_accepts_self value)

/-- Contextual-word exact grammar preserves its identifier spelling and silent trace. -/
theorem contextual_exactToken_success_iff
    (value : ContextualKeyword) (context : ParseContext)
    {input : State} {span : SourceSpan} {after : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.ExactTokenParses (.identifier value.spelling)
      input.declarativeRemainder span after ↔
      ∃ output, contextual value context input =
        .ok { span, value := .identifier value.spelling } output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics :=
  acceptToken_exactToken_success_iff (.contextual value) context
    (·.isContextual value) (contextual_accepts_self value)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties
/-! Independent token absence determines exact uncommitted primitive reports.
No source validity, diagnostic validity, or executable outcome is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem acceptToken_eq_rejectAt_of_absence
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) (kind : TokenKind) {input : State}
    (sound : ∀ {output : State} {token : Token},
      acceptToken expected context accepts input = .ok token output →
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor
        { span := token.span, value := kind })
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor kind) :
    acceptToken expected context accepts input =
      rejectAt input { head := expected, tail := [] } context := by
  unfold acceptToken
  cases found : input.peek? with
  | none => rfl
  | some token =>
      simp only
      split
      next accepted =>
        have result : acceptToken expected context accepts input =
            .ok token { input with cursor := input.cursor + 1 } := by
          simp only [acceptToken, found, accepted, if_true]
        exact False.elim (absent ⟨token.span, sound result⟩)
      next => rfl

/-- An absent hard keyword yields the exact retained-state failure. -/
theorem keyword_eq_rejectAt_of_tokenKindAbsent
    (value : HardKeyword) (context : ParseContext) {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.keyword value)) :
    keyword value context input =
      rejectAt input { head := .keyword value, tail := [] } context :=
  acceptToken_eq_rejectAt_of_absence (.keyword value) context
    (· == .keyword value) (.keyword value)
    (fun result => (keyword_ok_tokenAt value context result).1) absent

/-- An absent symbol yields the exact retained-state failure. -/
theorem symbol_eq_rejectAt_of_tokenKindAbsent
    (value : Symbol) (context : ParseContext) {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.symbol value)) :
    symbol value context input =
      rejectAt input { head := .symbol value, tail := [] } context :=
  acceptToken_eq_rejectAt_of_absence (.symbol value) context
    (· == .symbol value) (.symbol value)
    (fun result => (symbol_ok_tokenAt value context result).1) absent

/-- Contextual absence concerns its identifier spelling; the report retains
the contextual expectation rather than replacing it with identifier. -/
theorem contextual_eq_rejectAt_of_tokenKindAbsent
    (value : ContextualKeyword) (context : ParseContext) {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.identifier value.spelling)) :
    contextual value context input =
      rejectAt input { head := .contextual value, tail := [] } context :=
  acceptToken_eq_rejectAt_of_absence (.contextual value) context
    (·.isContextual value) (.identifier value.spelling)
    (fun result => (contextual_ok_tokenAt value context result).1) absent

private theorem exactToken_reject_reports_iff
    (parser : Parser Token) (kind : TokenKind)
    (expected : ParseExpectation) (context : ParseContext) {input : State}
    (complete : ∀ {span : SourceSpan} {after : DeclarativeGrammar.Remainder},
      DeclarativeGrammar.ExactTokenParses kind input.declarativeRemainder span after →
      parser input = .ok { span, value := kind } { input with cursor := input.cursor + 1 })
    (rejects : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor kind →
      parser input = rejectAt input { head := expected, tail := [] } context)
    {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor kind ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := expected, tail := [] } context input.declarativeRemainder diagnostic) ↔
      ∃ failure, parser input = .reject failure input ∧ failure.toDiagnostic = diagnostic := by
  constructor
  · rintro ⟨absent, reported⟩
    rcases (rejectAt_reports_iff (alpha := Token)).mp reported with
      ⟨failure, result, reportEq⟩
    exact ⟨failure, (rejects absent).trans result, reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    have absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
        input.window.endIndex input.cursor kind := by
      rintro ⟨span, present⟩
      have success := complete (after := { input.declarativeRemainder with
        cursor := input.cursor + 1 }) ⟨present, rfl⟩
      rw [success] at result
      contradiction
    refine ⟨absent, (rejectAt_reports_iff (alpha := Token)).mpr ?_⟩
    exact ⟨failure, (rejects absent).symm.trans result, reportEq⟩

/-- Hard-keyword absence and its independently reported payload exactly
characterize rejection, including the unchanged complete input state. -/
theorem keyword_reject_reports_iff
    (value : HardKeyword) (context : ParseContext)
    {input : State} {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.keyword value) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .keyword value, tail := [] } context input.declarativeRemainder diagnostic) ↔
      ∃ failure, keyword value context input = .reject failure input ∧
        failure.toDiagnostic = diagnostic :=
  exactToken_reject_reports_iff (keyword value context) (.keyword value) (.keyword value)
    context (keyword_eq_ok_of_exactTokenParses value context)
    (keyword_eq_rejectAt_of_tokenKindAbsent value context)

/-- Symbol absence and its independent report exactly characterize silent rejection. -/
theorem symbol_reject_reports_iff
    (value : Symbol) (context : ParseContext)
    {input : State} {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.symbol value) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .symbol value, tail := [] } context input.declarativeRemainder diagnostic) ↔
      ∃ failure, symbol value context input = .reject failure input ∧
        failure.toDiagnostic = diagnostic :=
  exactToken_reject_reports_iff (symbol value context) (.symbol value) (.symbol value)
    context (symbol_eq_ok_of_exactTokenParses value context)
    (symbol_eq_rejectAt_of_tokenKindAbsent value context)

/-- Contextual spelling absence yields the exact contextual report, not an
identifier expectation, while keeping the whole input and diagnostic sequence. -/
theorem contextual_reject_reports_iff
    (value : ContextualKeyword) (context : ParseContext)
    {input : State} {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.identifier value.spelling) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .contextual value, tail := [] } context input.declarativeRemainder diagnostic) ↔
      ∃ failure, contextual value context input = .reject failure input ∧
        failure.toDiagnostic = diagnostic :=
  exactToken_reject_reports_iff (contextual value context) (.identifier value.spelling)
    (.contextual value) context (contextual_eq_ok_of_exactTokenParses value context)
    (contextual_eq_rejectAt_of_tokenKindAbsent value context)

/-- Arbitrary primitive rejection realizes the independent report and emits
no event, even when the supplied state or earlier diagnostics are invalid. -/
theorem acceptToken_reject_reports
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) {input rejected : State} {failure : Failure}
    (result : acceptToken expected context accepts input = .reject failure rejected) :
    DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := expected, tail := [] } context input.declarativeRemainder failure.toDiagnostic ∧
      rejected.diagnostics = input.diagnostics := by
  unfold acceptToken at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_reports _ context result
  | some token =>
      simp only [found] at result
      split at result
      · contradiction
      · exact rejectAt_reject_reports _ context result

/-- A rejected keyword preserves the exact existing diagnostic order. -/
theorem keyword_reject_diagnostics_eq
    (value : HardKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics :=
  (acceptToken_reject_reports (.keyword value) context (· == .keyword value) result).2

/-- A rejected symbol preserves the exact existing diagnostic order. -/
theorem symbol_reject_diagnostics_eq
    (value : Symbol) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : symbol value context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics :=
  (acceptToken_reject_reports (.symbol value) context (· == .symbol value) result).2

/-- A rejected contextual spelling preserves the exact existing diagnostic order. -/
theorem contextual_reject_diagnostics_eq
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics :=
  (acceptToken_reject_reports (.contextual value) context (·.isContextual value) result).2

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionDiagnosticTraceContracts
/-! Explicit expression contracts for diagnostic-trace composition. They
quantify arbitrary incoming events and make no concrete Core-expression claim. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

def ExpressionTraceSuccessSound (parser : Parser Expr)
    (expressionTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input output : State} {value : Expr}, parser input = .ok value output →
    ∃ trace, expressionTrace input.file.id input.window.endByte input.declarativeRemainder
      value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace

def ExpressionTraceSuccessComplete (parser : Parser Expr)
    (expressionTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic},
    expressionTrace input.file.id input.window.endByte input.declarativeRemainder value after trace →
      ∃ output, parser input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace

/-- Successful expressions preserve the source and full active token/byte window. -/
def ExpressionSuccessContext (parser : Parser Expr) : Prop :=
  ∀ {input output : State} {value : Expr}, parser input = .ok value output →
    output.file = input.file ∧ output.window = input.window

def ExpressionTraceRejectSound (parser : Parser Expr)
    (expressionRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input rejected : State} {failure : Failure}, parser input = .reject failure rejected →
    ∃ trace, expressionRejects input.file.id input.window.endByte input.declarativeRemainder
      rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace

def ExpressionTraceRejectComplete (parser : Parser Expr)
    (expressionRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic},
    expressionRejects input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace →
      ∃ failure rejected, parser input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        rejected.diagnostics = input.diagnostics ++ trace

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties
/-! Exact independent normalization of arbitrary mixed parser diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Independent normalization determines each retained complete diagnostic. -/
theorem filterParseDiagnostics_eq_of_cascadeFilters
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    {raw kept : List ParseDiagnostic}
    (filtered : DeclarativeGrammar.ParseDiagnosticCascadeFilters
      file.content (lexical.map (·.span)) raw kept) :
    filterParseDiagnostics file lexical raw = kept := by
  induction filtered with
  | nil => exact filterParseDiagnostics_nil_parsed file lexical
  | keep retained tail ih =>
      rw [filterParseDiagnostics_cons_of_retained _ _ _ _ retained, ih]
  | drop suppressed tail ih =>
      rw [filterParseDiagnostics_cons_of_suppressed _ _ _ _ suppressed, ih]

/-- The filter is exactly the independent mixed-report relation, not merely a
span projection. Expectations, contexts, text, and constraint payloads remain exact. -/
theorem filterParseDiagnostics_eq_iff_cascadeFilters
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (raw kept : List ParseDiagnostic) :
    filterParseDiagnostics file lexical raw = kept ↔
      DeclarativeGrammar.ParseDiagnosticCascadeFilters
        file.content (lexical.map (·.span)) raw kept := by
  constructor
  · intro result
    rcases DeclarativeGrammar.parseDiagnosticCascadeFilters_total
        file.content (lexical.map (·.span)) raw with ⟨actual, filtered⟩
    have actualEq := (filterParseDiagnostics_eq_of_cascadeFilters file lexical filtered).symm.trans result
    simpa only [actualEq] using filtered
  · exact filterParseDiagnostics_eq_of_cascadeFilters file lexical

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties
/-! Executable normalization algebra derived from independent trace rules. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The same lexical context never changes an already normalized trace. -/
theorem filterParseDiagnostics_idempotent (file : SourceFile)
    (lexical : List LexicalDiagnostic) (parsed : List ParseDiagnostic) :
    filterParseDiagnostics file lexical (filterParseDiagnostics file lexical parsed) =
      filterParseDiagnostics file lexical parsed := by
  have filtered := (filterParseDiagnostics_eq_iff_cascadeFilters
    file lexical parsed (filterParseDiagnostics file lexical parsed)).mp rfl
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical filtered.stable

/-- Normalizing concatenated traces preserves their original partition and order. -/
theorem filterParseDiagnostics_append (file : SourceFile)
    (lexical : List LexicalDiagnostic) (left right : List ParseDiagnostic) :
    filterParseDiagnostics file lexical (left ++ right) =
      filterParseDiagnostics file lexical left ++ filterParseDiagnostics file lexical right := by
  have leftFiltered := (filterParseDiagnostics_eq_iff_cascadeFilters
    file lexical left (filterParseDiagnostics file lexical left)).mp rfl
  have rightFiltered := (filterParseDiagnostics_eq_iff_cascadeFilters
    file lexical right (filterParseDiagnostics file lexical right)).mp rfl
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical (leftFiltered.append rightFiltered)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SequencingDiagnosticTraceProperties
/-! Compositional laws from executable branch premises, not independent
grammar judgments. Sequencing retains each executed branch's diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- One explicit emission appends one event after all prior diagnostics. -/
theorem emitDiagnostic_success_trace (diagnostic : ParseDiagnostic) (input : State) :
    emitDiagnostic diagnostic input = .ok () (input.emit diagnostic) ∧
      (input.emit diagnostic).diagnostics = input.diagnostics ++ [diagnostic] := by
  refine ⟨rfl, ?_⟩
  simp only [State.emit, State.diagnostics, List.reverse_cons]

/-- Successful sequencing appends suffixes in execution order. -/
theorem bind_success_trace {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input middle output : State} {firstValue : alpha} {value : beta}
    {firstTrace nextTrace : List ParseDiagnostic}
    (firstResult : first input = .ok firstValue middle)
    (firstDiagnostics : middle.diagnostics = input.diagnostics ++ firstTrace)
    (nextResult : next firstValue middle = .ok value output)
    (nextDiagnostics : output.diagnostics = middle.diagnostics ++ nextTrace) :
    (first >>= next) input = .ok value output ∧
      output.diagnostics = input.diagnostics ++ (firstTrace ++ nextTrace) := by
  refine ⟨?_, ?_⟩
  · simp only [bind, firstResult, nextResult]
  · rw [nextDiagnostics, firstDiagnostics, List.append_assoc]

/-- Rejection in the continuation retains both executed suffixes in order;
ordinary bind is not a transactional rollback boundary. -/
theorem bind_reject_right_trace {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input middle rejected : State} {firstValue : alpha} {failure : Failure}
    {firstTrace nextTrace : List ParseDiagnostic}
    (firstResult : first input = .ok firstValue middle)
    (firstDiagnostics : middle.diagnostics = input.diagnostics ++ firstTrace)
    (nextResult : next firstValue middle = .reject failure rejected)
    (nextDiagnostics : rejected.diagnostics = middle.diagnostics ++ nextTrace) :
    (first >>= next) input = .reject failure rejected ∧
      rejected.diagnostics = input.diagnostics ++ (firstTrace ++ nextTrace) := by
  refine ⟨?_, ?_⟩
  · simp only [bind, firstResult, nextResult]
  · rw [nextDiagnostics, firstDiagnostics, List.append_assoc]

/-- A rejected first stage retains its exact failure/state/trace and never
executes the continuation. No premise about that continuation is required. -/
theorem bind_reject_left_trace {alpha beta : Type}
    {first : Parser alpha} (next : alpha → Parser beta)
    {input rejected : State} {failure : Failure} {trace : List ParseDiagnostic}
    (firstResult : first input = .reject failure rejected)
    (diagnostics : rejected.diagnostics = input.diagnostics ++ trace) :
    (first >>= next) input = .reject failure rejected ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  exact ⟨by simp only [bind, firstResult], diagnostics⟩

/-- Mapping changes only the successful value, preserving the exact state
and complete diagnostic suffix returned by its executable argument. -/
theorem map_success_trace {alpha beta : Type}
    (transform : alpha → beta) {parser : Parser alpha}
    {input output : State} {value : alpha} {trace : List ParseDiagnostic}
    (result : parser input = .ok value output)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    (transform <$> parser) input = .ok (transform value) output ∧
      output.diagnostics = input.diagnostics ++ trace := by
  refine ⟨?_, diagnostics⟩
  change ((parser >>= fun parsed => pure (transform parsed)) : Parser beta) input = _
  simp only [bind, result, pure]

/-- Mapping cannot replace a failure, rejected state, or emitted suffix. -/
theorem map_reject_trace {alpha beta : Type}
    (transform : alpha → beta) {parser : Parser alpha}
    {input rejected : State} {failure : Failure} {trace : List ParseDiagnostic}
    (result : parser input = .reject failure rejected)
    (diagnostics : rejected.diagnostics = input.diagnostics ++ trace) :
    (transform <$> parser) input = .reject failure rejected ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  refine ⟨?_, diagnostics⟩
  change ((parser >>= fun parsed => pure (transform parsed)) : Parser beta) input = _
  simp only [bind, result]

/-- Executor failure is propagated before sequencing can invoke a continuation. -/
theorem bind_invariant_left_exact {alpha beta : Type}
    {first : Parser alpha} (next : alpha → Parser beta)
    {input : State} {error : ParserInvariantError}
    (result : first input = .invariant error) :
    (first >>= next) input = .invariant error := by
  simp only [bind, result]

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.StatementDiagnosticTraceContracts
/-! Explicit abstract statement contracts for successful raw-block trace lifting.
They quantify arbitrary existing diagnostics and make no concrete Core claim. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful statement has an independent appended diagnostic suffix. -/
def StatementTraceSuccessSound (parser : Parser Statement)
    (statementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input output : State} {statement : Statement}, parser input = .ok statement output →
    ∃ trace, statementTrace input.file.id input.window.endByte input.declarativeRemainder
      statement output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace

/-- Each independent successful statement executes with the same AST, remainder,
and complete appended suffix, regardless of the incoming diagnostic sequence. -/
def StatementTraceSuccessComplete (parser : Parser Statement)
    (statementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {statement : Statement} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic},
    statementTrace input.file.id input.window.endByte input.declarativeRemainder statement after trace →
      ∃ output, parser input = .ok statement output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace

/-- Successful statements retain the source and full diagnostic window.
Strict cursor progress is checked separately by the independent block grammar. -/
def StatementSuccessContext (parser : Parser Statement) : Prop :=
  ∀ {input output : State} {statement : Statement}, parser input = .ok statement output →
    output.file = input.file ∧ output.window = input.window

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.StatementRejectionTraceContracts
/-! Explicit statement rejection contracts for raw-block trace composition.
The final failure report remains separate from events already emitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every rejected statement supplies its exact uncommitted diagnostic and
the complete suffix appended after arbitrary incoming diagnostics. -/
def StatementTraceRejectSound (parser : Parser Statement)
    (statementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input rejected : State} {failure : Failure}, parser input = .reject failure rejected →
    ∃ trace, statementRejects input.file.id input.window.endByte input.declarativeRemainder
      rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace

/-- Every independent statement rejection executes at its exact remainder,
with the specified failure report and preceding events, for any prior state. -/
def StatementTraceRejectComplete (parser : Parser Statement)
    (statementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic},
    statementRejects input.file.id input.window.endByte input.declarativeRemainder
      after diagnostic trace →
      ∃ failure rejected, parser input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        rejected.diagnostics = input.diagnostics ++ trace

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TransactionalChoiceDiagnosticTraceProperties
/-! Executable-premise laws for transactional ordered choice. Rejected left
states, including all their diagnostics, are discarded before the right branch.
These are compositional execution laws, not independent grammar judgments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Left rejection retries the right parser on exactly the original input.
No constraint on the discarded cursor, carrier, or diagnostic trace is needed. -/
theorem orElse_eq_right_of_reject {alpha : Type}
    {first : Parser alpha} (second : Parser alpha)
    {input discarded : State} {failure : Failure}
    (firstResult : first input = .reject failure discarded) :
    orElse first second input = second input := by
  simp only [orElse, firstResult]

/-- The first successful alternative returns its exact state and suffix;
the right alternative is irrelevant and no right outcome is assumed. -/
theorem orElse_success_left_trace {alpha : Type}
    {first : Parser alpha} (second : Parser alpha)
    {input output : State} {value : alpha} {trace : List ParseDiagnostic}
    (firstResult : first input = .ok value output)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    orElse first second input = .ok value output ∧
      output.diagnostics = input.diagnostics ++ trace := by
  exact ⟨by simp only [orElse, firstResult], diagnostics⟩

/-- Successful fallback retains only its suffix after the original prefix.
The left branch may have emitted any nonempty trace before rejecting. -/
theorem orElse_success_right_trace {alpha : Type}
    {first second : Parser alpha} {input discarded output : State}
    {failure : Failure} {value : alpha} {trace : List ParseDiagnostic}
    (firstResult : first input = .reject failure discarded)
    (secondResult : second input = .ok value output)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    orElse first second input = .ok value output ∧
      output.diagnostics = input.diagnostics ++ trace := by
  exact ⟨(orElse_eq_right_of_reject second firstResult).trans secondResult, diagnostics⟩

/-- Failed fallback also retains only the right failure/state/trace; neither
the left failure payload nor its emitted suffix survives the transaction. -/
theorem orElse_reject_right_trace {alpha : Type}
    {first second : Parser alpha} {input discarded rejected : State}
    {leftFailure rightFailure : Failure} {trace : List ParseDiagnostic}
    (firstResult : first input = .reject leftFailure discarded)
    (secondResult : second input = .reject rightFailure rejected)
    (diagnostics : rejected.diagnostics = input.diagnostics ++ trace) :
    orElse first second input = .reject rightFailure rejected ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  exact ⟨(orElse_eq_right_of_reject second firstResult).trans secondResult, diagnostics⟩

/-- Invariant failure is not ordinary rejection and never enables fallback. -/
theorem orElse_invariant_left_exact {alpha : Type}
    {first : Parser alpha} (second : Parser alpha)
    {input : State} {error : ParserInvariantError}
    (firstResult : first input = .invariant error) :
    orElse first second input = .invariant error := by
  simp only [orElse, firstResult]

/-- A fallback invariant is exactly the right reply at the original input;
there is no rejected-state trace to expose at an invariant-only boundary. -/
theorem orElse_invariant_right_exact {alpha : Type}
    {first second : Parser alpha} {input discarded : State}
    {failure : Failure} {error : ParserInvariantError}
    (firstResult : first input = .reject failure discarded)
    (secondResult : second input = .invariant error) :
    orElse first second input = .invariant error :=
  (orElse_eq_right_of_reject second firstResult).trans secondResult

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.UnexpectedDiagnosticCascadeProperties
/-! Exact lexical-cascade filtering of expectation failures with fixed found
token, expected alternatives, and grammar context. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Interpret ordered spans as failures carrying one fixed expectation report. -/
def unexpectedDiagnostics (found : Option TokenKind)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (spans : List SourceSpan) : List ParseDiagnostic :=
  spans.map fun span => { span, kind := .unexpected found expected context }

/-- Interpreting expectation-event spans does not lose their order or identity. -/
@[simp] theorem unexpectedDiagnostics_spans (found : Option TokenKind)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (spans : List SourceSpan) :
    (unexpectedDiagnostics found expected context spans).map ParseDiagnostic.span = spans := by
  simp [unexpectedDiagnostics, List.map_map, Function.comp_def]

/-- Independent keep/drop decisions fix the complete filtered expectation trace. -/
theorem filterParseDiagnostics_unexpected_of_filters
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) {raw kept : List SourceSpan}
    (filtered : DeclarativeGrammar.LexicalCascadeFilters
      file.content (lexical.map (·.span)) raw kept) :
    filterParseDiagnostics file lexical (unexpectedDiagnostics found expected context raw) =
      unexpectedDiagnostics found expected context kept := by
  induction filtered with
  | nil => simp [unexpectedDiagnostics]
  | keep retained tail ih =>
      simp only [unexpectedDiagnostics, List.map_cons] at ih ⊢
      rw [filterParseDiagnostics_cons_unexpected_of_retained _ _ _ _ _ _ _ retained, ih]
  | drop suppressed tail ih =>
      simp only [unexpectedDiagnostics, List.map_cons] at ih ⊢
      rw [filterParseDiagnostics_cons_unexpected_of_suppressed _ _ _ _ _ _ _ suppressed, ih]

/-- Normalization and independent filtering agree with all expectation metadata
shared explicitly; diagnostics are not identified solely by their spans. -/
theorem filterParseDiagnostics_unexpected_iff
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) (raw kept : List SourceSpan) :
    DeclarativeGrammar.LexicalCascadeFilters
      file.content (lexical.map (·.span)) raw kept ↔
      filterParseDiagnostics file lexical (unexpectedDiagnostics found expected context raw) =
        unexpectedDiagnostics found expected context kept := by
  constructor
  · exact filterParseDiagnostics_unexpected_of_filters file lexical found expected context
  · intro result
    rcases DeclarativeGrammar.lexicalCascadeFilters_total
        file.content (lexical.map (·.span)) raw with ⟨actual, filtered⟩
    have reportsEq :=
      (filterParseDiagnostics_unexpected_of_filters file lexical found expected context
        filtered).symm.trans result
    have spansEq := congrArg (List.map ParseDiagnostic.span) reportsEq
    simp only [unexpectedDiagnostics_spans] at spansEq
    simpa only [spansEq] using filtered

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.UnrestrictedFuelElementContract
/-! Fuel-aware ordinary execution on arbitrary states. Only successful child
end indices and strict cursor progress are constrained; no validity, token,
source, diagnostic, or rejected-state frame is required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

structure UnrestrictedFuelElementContract {α : Type}
    (element : Parser α) (fuel : Nat) : Prop where
  endIndexOnSuccess : ∀ {input next : State} {value : α},
    element input = .ok value next → next.window.endIndex = input.window.endIndex
  cursorLtOnSuccess : ∀ {input next : State} {value : α},
    element input = .ok value next → input.cursor < next.cursor
  ordinary : ∀ input, input.remainingCount < fuel →
    (∃ value next, element input = .ok value next) ∨
      (∃ failure next, element input = .reject failure next)

theorem remainingCount_le_of_endIndex_eq {input next : State}
    (endIndexEq : next.window.endIndex = input.window.endIndex)
    (cursorLe : input.cursor ≤ next.cursor) : next.remainingCount ≤ input.remainingCount := by
  simp only [State.remainingCount, endIndexEq]
  omega

theorem remainingCount_lt_of_endIndex_eq {input next : State} {fuel : Nat}
    (endIndexEq : next.window.endIndex = input.window.endIndex)
    (cursorLe : input.cursor ≤ next.cursor) (adequate : input.remainingCount < fuel) :
    next.remainingCount < fuel :=
  Nat.lt_of_le_of_lt (remainingCount_le_of_endIndex_eq endIndexEq cursorLe) adequate

/-- A real token, not a global state invariant, pays for one recursive unit. -/
theorem acceptToken_remainingCount_lt_of_success {input next : State} {token : Token} {fuel : Nat}
    (expected : ParseExpectation) (context : ParseContext) (accepts : TokenKind → Bool)
    (result : acceptToken expected context accepts input = .ok token next)
    (adequate : input.remainingCount < fuel + 1) : next.remainingCount < fuel := by
  rcases acceptToken_ok_state_shape expected context accepts result with ⟨found, rfl⟩
  have beforeEnd := State.cursor_lt_endIndex_of_peek?_eq_some found
  simp only [State.remainingCount] at adequate ⊢
  omega

theorem symbol_remainingCount_lt_of_success {input next : State} {token : Token} {fuel : Nat}
    (value : Symbol) (context : ParseContext)
    (result : symbol value context input = .ok token next)
    (adequate : input.remainingCount < fuel + 1) : next.remainingCount < fuel :=
  acceptToken_remainingCount_lt_of_success (.symbol value) context (· == .symbol value) result adequate

theorem keyword_remainingCount_lt_of_success {input next : State} {token : Token} {fuel : Nat}
    (value : HardKeyword) (context : ParseContext)
    (result : keyword value context input = .ok token next)
    (adequate : input.remainingCount < fuel + 1) : next.remainingCount < fuel :=
  acceptToken_remainingCount_lt_of_success (.keyword value) context (· == .keyword value) result adequate

theorem contextual_remainingCount_lt_of_success {input next : State} {token : Token} {fuel : Nat}
    (value : ContextualKeyword) (context : ParseContext)
    (result : contextual value context input = .ok token next)
    (adequate : input.remainingCount < fuel + 1) : next.remainingCount < fuel :=
  acceptToken_remainingCount_lt_of_success (.contextual value) context (·.isContextual value) result adequate

namespace UnrestrictedFuelElementContract

theorem weaken {α : Type} {element : Parser α} {smallFuel largeFuel : Nat}
    (contract : UnrestrictedFuelElementContract element largeFuel)
    (bound : smallFuel ≤ largeFuel) : UnrestrictedFuelElementContract element smallFuel where
  endIndexOnSuccess := contract.endIndexOnSuccess
  cursorLtOnSuccess := contract.cursorLtOnSuccess
  ordinary input adequate := contract.ordinary input (Nat.lt_of_lt_of_le adequate bound)

theorem ne_invariant {α : Type} {element : Parser α} {fuel : Nat}
    (contract : UnrestrictedFuelElementContract element fuel)
    (input : State) (adequate : input.remainingCount < fuel) (error : ParserInvariantError) :
    element input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem remainingCount_le_of_success {α : Type} {element : Parser α} {fuel : Nat}
    (contract : UnrestrictedFuelElementContract element fuel)
    {input next : State} {value : α} (result : element input = .ok value next) :
    next.remainingCount ≤ input.remainingCount :=
  remainingCount_le_of_endIndex_eq (contract.endIndexOnSuccess result)
    (Nat.le_of_lt (contract.cursorLtOnSuccess result))

theorem remainingCount_lt_of_success {α : Type} {element : Parser α} {fuel bound : Nat}
    (contract : UnrestrictedFuelElementContract element fuel)
    {input next : State} {value : α} (result : element input = .ok value next)
    (adequate : input.remainingCount < bound) : next.remainingCount < bound :=
  Nat.lt_of_le_of_lt (contract.remainingCount_le_of_success result) adequate

end UnrestrictedFuelElementContract

end Solcore.Syntax.Parser
end
