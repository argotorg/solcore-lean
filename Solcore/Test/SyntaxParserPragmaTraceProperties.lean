import Solcore.Syntax.Parser.PragmaDeclarationTraceProperties

/-! Consumers of ordered pragma success traces, including silent raw names. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PragmaInternals
open Solcore.Syntax.DeclarativeGrammar

example := @identifierListDiagnosticTrace_total
example := @IdentifierListDiagnosticTrace.trace_unique
example := @IdentifierListDiagnosticTrace.append
example := @PragmaItemsTailTraceParses.result_unique
example := @PragmaItemsTraceParses.result_unique
example := @PragmaDeclTraceParses.result_unique
example := @pragmaItemsTail_success_diagnosticTrace
example := @pragmaItemsTail_production_success_trace_sound
example := @pragmaItems_success_diagnosticTrace
example := @pragmaItems_success_diagnostics_eq_of_trace
example := @pragmaItems_success_trace_sound
example := @pragmaItemsTail_production_success_diagnostics_eq_of_trace
example := @pragmaDecl_success_diagnosticTrace
example := @pragmaDecl_success_diagnostics_eq_of_trace

example (first middle last : SourceSpan) :
    IdentifierListDiagnosticTrace
      [{ span := first, value := "a-b" }, { span := middle, value := "clean" },
        { span := last, value := "c--d" }]
      [{ span := first, kind := .invalidIdentifierHyphen "a-b" },
        { span := last, kind := .invalidIdentifierHyphen "c--d" }] :=
  .cons (.hyphen (by change '-' ∈ "a-b".toList; decide))
    (.cons (.clean (by change ¬ '-' ∈ "clean".toList; decide))
      (.cons (.hyphen (by change '-' ∈ "c--d".toList; decide)) .nil))

example (itemsRev : List Identifier) {input : State} {suffix : List Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (parsed : PragmaItemsTailTraceParses input.declarativeRemainder suffix remainder trace) :
    ∃ output, pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .ok (itemsRev.reverse ++ suffix) output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  (pragmaItemsTail_production_trace_success_iff itemsRev).mp parsed

example (itemsRev : List Identifier) {input output : State} {suffix : List Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (result : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .ok (itemsRev.reverse ++ suffix) output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaItemsTailTraceParses input.declarativeRemainder suffix remainder trace :=
  (pragmaItemsTail_production_trace_success_iff itemsRev).mpr
    ⟨output, result, after, diagnostics⟩

example {input : State} {items : List Identifier} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (parsed : PragmaItemsTraceParses input.declarativeRemainder items remainder trace) :
    ∃ output, pragmaItems input = .ok items output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaItems_trace_success_iff.mp parsed

example {input output : State} {items : List Identifier} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (result : pragmaItems input = .ok items output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaItemsTraceParses input.declarativeRemainder items remainder trace :=
  pragmaItems_trace_success_iff.mpr ⟨output, result, after, diagnostics⟩

example {input : State} {declaration : PragmaDecl} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (parsed : PragmaDeclTraceParses input.declarativeRemainder declaration remainder trace) :
    ∃ output, pragmaDecl input = .ok declaration output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  pragmaDecl_trace_success_iff.mp parsed

example {input output : State} {declaration : PragmaDecl} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .ok declaration output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    PragmaDeclTraceParses input.declarativeRemainder declaration remainder trace :=
  pragmaDecl_trace_success_iff.mpr ⟨output, result, after, diagnostics⟩

example {input : State} {declaration : PragmaDecl} {remainder : Remainder}
    (parsed : PragmaDeclOrdinaryParses input.declarativeRemainder declaration remainder)
    (noItems : declaration.value.items = []) :
    ∃ output, pragmaDecl input = .ok declaration output ∧
      output.declarativeRemainder = remainder ∧ output.diagnostics = input.diagnostics := by
  have diagnostics : IdentifierListDiagnosticTrace declaration.value.items [] := by
    rw [noItems]
    exact .nil
  simpa only [List.append_nil] using pragmaDecl_trace_success_iff.mp ⟨parsed, diagnostics⟩

example {input output : State} {actual expected : PragmaDecl} {remainder : Remainder}
    {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .ok actual output)
    (parsed : PragmaDeclTraceParses input.declarativeRemainder expected remainder trace) :
    actual = expected ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaDecl_success_trace_sound result with ⟨actualTrace, actualParsed, actualEq⟩
  rcases actualParsed.result_unique parsed with ⟨rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, actualEq⟩

end Solcore.Test.SyntaxParserPragmaTraceProperties
