import Solcore.Syntax.Parser.IdentifierTraceProperties

/-! Exact identifier success traces and compatibility with rejection reports. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserIdentifierTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @identifierHyphenSpelling_iff_contains
example := @identifierDiagnosticTrace_total
example := @IdentifierDiagnosticTrace.trace_unique
example := @RawIdentifierTraceParses.result_unique
example := @IdentifierTraceParses.result_unique
example := @rawIdentifier_success_trace_sound
example := @identifier_success_diagnosticTrace
example := @identifier_success_trace_sound

example (span : SourceSpan) :
    IdentifierDiagnosticTrace { span, value := "a--b" }
      [{ span, kind := .invalidIdentifierHyphen "a--b" }] :=
  .hyphen (by change '-' ∈ "a--b".toList; decide)

example (span : SourceSpan) :
    IdentifierDiagnosticTrace { span, value := "a_b" } [] :=
  .clean (by change ¬ '-' ∈ "a_b".toList; decide)

example (context : ParseContext) {input output : State} {name : Identifier}
    (result : rawIdentifier context input = .ok name output) :
    output.diagnostics = input.diagnostics :=
  rawIdentifier_success_diagnostics_eq context result

example (context : ParseContext) {input output : State} {name : Identifier}
    (result : identifier context input = .ok name output)
    (hyphen : IdentifierHyphenSpelling name.value) :
    output.diagnostics = input.diagnostics ++
      [{ span := name.span, kind := .invalidIdentifierHyphen name.value }] :=
  identifier_success_diagnostics_eq_of_trace context result (.hyphen hyphen)

example (context : ParseContext) {input output : State} {name : Identifier}
    (result : identifier context input = .ok name output)
    (clean : ¬ IdentifierHyphenSpelling name.value) :
    output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using
    identifier_success_diagnostics_eq_of_trace context result (.clean clean)

example (context : ParseContext) {input : State} {name : Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (parsed : RawIdentifierTraceParses input.declarativeRemainder name remainder trace) :
    ∃ output, rawIdentifier context input = .ok name output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  (rawIdentifier_trace_success_iff context).mp parsed

example (context : ParseContext) {input output : State} {name : Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (result : rawIdentifier context input = .ok name output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    RawIdentifierTraceParses input.declarativeRemainder name remainder trace :=
  (rawIdentifier_trace_success_iff context).mpr ⟨output, result, after, diagnostics⟩

example (context : ParseContext) {input : State} {name : Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (parsed : IdentifierTraceParses input.declarativeRemainder name remainder trace) :
    ∃ output, identifier context input = .ok name output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  (identifier_trace_success_iff context).mp parsed

example (context : ParseContext) {input output : State} {name : Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (result : identifier context input = .ok name output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    IdentifierTraceParses input.declarativeRemainder name remainder trace :=
  (identifier_trace_success_iff context).mpr ⟨output, result, after, diagnostics⟩

example (context : ParseContext) {input output : State} {actual expected : Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (result : identifier context input = .ok actual output)
    (parsed : IdentifierTraceParses input.declarativeRemainder expected remainder trace) :
    actual = expected ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases identifier_success_trace_sound context result with
    ⟨actualTrace, actualParsed, actualDiagnostics⟩
  rcases actualParsed.result_unique parsed with ⟨rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, actualDiagnostics⟩

example (context : ParseContext) {input : State} {diagnostic : ParseDiagnostic}
    (absent : IdentifierAbsentAt input.declarativeRemainder)
    (reported : RejectAtReports input.file.id input.window.endByte
      { head := .identifier, tail := [] } context input.declarativeRemainder diagnostic) :
    ∃ failure, identifier context input = .reject failure input ∧
      failure.toDiagnostic = diagnostic :=
  (identifier_reject_reports_iff context).mp ⟨absent, reported⟩

end Solcore.Test.SyntaxParserIdentifierTraceProperties
