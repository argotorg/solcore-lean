import Solcore.Syntax.DeclarativeNamedTypeRejectionTraceGrammar
import Solcore.Syntax.Parser.QualifiedNameRejectionTraceStateProperties
import Solcore.Syntax.Parser.QualifiedNameTraceCorrespondenceProperties
import Solcore.Syntax.Parser.NamedTypeArgumentsRejectionTraceProperties
import Solcore.Syntax.Parser.NamedTypeFinishingTraceProperties

/-! Exact raw named-type rejection composes qualified-name and argument
failures. Finishing always succeeds, so no finishing event precedes rejection.
Only the recursive child contracts needed by optional arguments are required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseNamedType_reject_iff_components
    {input rejected : State} {failure : Failure} :
    parseNamedType nested input = .reject failure rejected ↔
      qualifiedName .typeExpr .typeExpr input = .reject failure rejected ∨
      ∃ name afterName, qualifiedName .typeExpr .typeExpr input = .ok name afterName ∧
        parseNamedTypeArguments nested afterName = .reject failure rejected := by
  cases nameResult : qualifiedName .typeExpr .typeExpr input with
  | invariant error => simp [parseNamedType, bind, nameResult]
  | reject nameFailure nameRejected => simp [parseNamedType, bind, nameResult]
  | ok name afterName =>
      cases argsResult : parseNamedTypeArguments nested afterName with
      | invariant error => simp [parseNamedType, bind, nameResult, argsResult]
      | reject argsFailure argsRejected =>
          simp [parseNamedType, bind, nameResult, argsResult]
          constructor
          · rintro ⟨rfl, rfl⟩
            exact ⟨name, afterName, ⟨rfl, rfl⟩, argsResult⟩
          · rintro ⟨otherName, otherState, ⟨rfl, rfl⟩, same⟩
            rw [argsResult] at same
            exact Reply.reject.inj same
      | ok arguments afterArguments =>
          simp only [parseNamedType, bind, nameResult, argsResult]
          constructor
          · intro impossible
            exact False.elim (finishNamedType_ne_reject name arguments afterArguments rejected failure impossible)
          · rintro (impossible | ⟨otherName, otherState, nameEq, argsEq⟩)
            · contradiction
            · cases nameEq
              rw [argsResult] at argsEq
              contradiction

theorem parseNamedType_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectSound (parseNamedType nested)
      (DeclarativeGrammar.NamedTypeTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  rcases parseNamedType_reject_iff_components.mp result with nameRejected | ⟨name, afterName, nameResult, argsResult⟩
  · rcases qualifiedName_reject_trace_sound .typeExpr .typeExpr nameRejected with ⟨trace, name, events⟩
    exact ⟨trace, .nameRejected name, events⟩
  · rcases qualifiedName_trace_success_sound .typeExpr .typeExpr nameResult with ⟨nameEvents, nameParsed, nameEq⟩
    have frame := qualifiedName_success_context .typeExpr .typeExpr nameResult
    rcases parseNamedTypeArguments_reject_trace_sound successSound rejectSound contextFrame argsResult with
      ⟨argumentEvents, arguments, argumentEq⟩
    refine ⟨nameEvents ++ argumentEvents, .argumentsRejected nameParsed ?_, ?_⟩
    · simpa only [frame.1, frame.2] using arguments
    · rw [argumentEq, nameEq]; exact List.append_assoc _ _ _

theorem parseNamedType_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectComplete (parseNamedType nested)
      (DeclarativeGrammar.NamedTypeTraceRejects elementTrace elementRejects) := by
  intro input after report trace rejection
  cases rejection with
  | nameRejected name =>
      rcases qualifiedName_trace_reject_complete .typeExpr .typeExpr name with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, parseNamedType_reject_iff_components.mpr (.inl result), afterEq, reportEq, events⟩
  | argumentsRejected name arguments =>
      rcases qualifiedName_trace_success_complete .typeExpr .typeExpr name with
        ⟨afterName, nameResult, afterEq, nameEvents⟩
      have frame := qualifiedName_success_context .typeExpr .typeExpr nameResult
      have argsAtNext := arguments
      rw [← afterEq, ← frame.1, ← frame.2] at argsAtNext
      rcases parseNamedTypeArguments_trace_reject_complete successComplete rejectComplete contextFrame argsAtNext with
        ⟨failure, rejected, result, finalEq, reportEq, events⟩
      refine ⟨failure, rejected, parseNamedType_reject_iff_components.mpr (.inr ⟨_, afterName, nameResult, result⟩),
        finalEq, reportEq, ?_⟩
      rw [events, nameEvents]; exact List.append_assoc _ _ _

theorem parseNamedType_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NamedTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parseNamedType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseNamedType_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parseNamedType_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parseNamedType_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NamedTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseNamedType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parseNamedType_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
