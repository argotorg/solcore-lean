import Solcore.Syntax.Parser.TopItemRecoveryTraceCompletenessProperties

/-! Consumers of exact recovery traces, including nonempty prior diagnostics. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTopItemRecoveryTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example := @finishRecoveredTopItem_success_diagnosticsRev_eq
example := @recoverTopItemAux_success_diagnosticsRev_eq
example := @recoverTopItem_success_diagnosticsRev_eq
example := @finishRecoveredTopItem_success_diagnostics_eq
example := @recoverTopItemAux_success_diagnostics_eq
example := @recoverTopItem_reject_diagnosticsRev_eq
example := @recoverTopItem_ordinary_success_iff_with_trace
example := @recoverTopItem_ordinary_reject_iff_with_trace

example {input output : State} {item : TopItem}
    (result : recoverTopItem input = .ok item output) :
    output.diagnostics = input.diagnostics ++
      [{ span := item.span, kind := .recovered .topItem }] :=
  recoverTopItem_success_diagnostics_eq result

example {input output : State} {failure : Failure}
    (result : recoverTopItem input = .reject failure output) :
    output.diagnostics = input.diagnostics :=
  recoverTopItem_reject_diagnostics_eq result

example {input : State} {item : TopItem}
    {remainder : DeclarativeGrammar.Remainder} {trace : List SourceSpan}
    (parsed : DeclarativeGrammar.TopItemRecoveryTraceParses
      input.declarativeRemainder item remainder trace) :
    ∃ output, recoverTopItem input = .ok item output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ topItemRecoveryDiagnostics trace :=
  recoverTopItem_trace_success_iff.mp parsed

example {input output : State} {item : TopItem}
    {remainder : DeclarativeGrammar.Remainder} {trace : List SourceSpan}
    (result : recoverTopItem input = .ok item output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++
      topItemRecoveryDiagnostics trace) :
    DeclarativeGrammar.TopItemRecoveryTraceParses
      input.declarativeRemainder item remainder trace :=
  recoverTopItem_trace_success_iff.mpr ⟨output, result, after, diagnostics⟩

example {input : State} {remainder : DeclarativeGrammar.Remainder}
    {trace : List SourceSpan}
    (rejected : DeclarativeGrammar.TopItemRecoveryTraceRejects
      input.declarativeRemainder remainder trace) :
    ∃ failure output, recoverTopItem input = .reject failure output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ topItemRecoveryDiagnostics trace :=
  recoverTopItem_trace_reject_iff.mp rejected

example {input output : State} {failure : Failure}
    {remainder : DeclarativeGrammar.Remainder} {trace : List SourceSpan}
    (result : recoverTopItem input = .reject failure output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++
      topItemRecoveryDiagnostics trace) :
    DeclarativeGrammar.TopItemRecoveryTraceRejects
      input.declarativeRemainder remainder trace :=
  recoverTopItem_trace_reject_iff.mpr
    ⟨failure, output, result, after, diagnostics⟩

example {input output : State} {actual expected : TopItem}
    {remainder : DeclarativeGrammar.Remainder} {trace : List SourceSpan}
    (result : recoverTopItem input = .ok actual output)
    (parsed : DeclarativeGrammar.TopItemRecoveryTraceParses
      input.declarativeRemainder expected remainder trace) :
    actual = expected ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ topItemRecoveryDiagnostics trace := by
  rcases DeclarativeGrammar.topItemRecoveryTraceParses_iff.mp parsed with
    ⟨ordinary, rfl⟩
  rcases recoverTopItem_exactOutcomeSpec.successResultUnique
      (recoverTopItem_success_ordinaryOutcome_sound result) ordinary with
    ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, recoverTopItem_success_diagnostics_eq result⟩

example (trace : List SourceSpan) :
    (topItemRecoveryDiagnostics trace).map ParseDiagnostic.span = trace :=
  topItemRecoveryDiagnostics_spans trace

example {left right : List SourceSpan}
    (equal : topItemRecoveryDiagnostics left = topItemRecoveryDiagnostics right) :
    left = right :=
  topItemRecoveryDiagnostics_injective equal

end Solcore.Test.SyntaxParserTopItemRecoveryTraceProperties
