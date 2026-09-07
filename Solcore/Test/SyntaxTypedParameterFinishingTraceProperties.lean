import Solcore.Syntax.Parser.TypedParameterFinishingTraceProperties
import Solcore.Syntax.DeclarativeQualifiedNameTraceGrammar
import Solcore.Syntax.DeclarativeNamedTypeFinishingTraceGrammar

/-! Finishing-only consumers retain complete states and exact parameter ASTs.
An existing checked-type event is already in the input history: finishing adds
only its own suffix, including a repeated constraint when identical events are
already present. Only an outer comptime type triggers that suffix. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypedParameterFinishingTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.FunctionParameterInternals

private def source : SourceId := { origin := .main, path := "parameter-finishing.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def marker : Option SourceSpan := some (span 0 8)
private def name : Identifier := { span := span 9 12, value := "arg" }
private def typeName : Identifier := { span := span 22 25, value := "a-b" }
private def innerType : TypeExpr := namedTypeTraceValue (tracedQualifiedName typeName []) none
private def comptimeType : TypeExpr := {
  span := span 13 27, value := .comptime (span 13 21) (span 21 27) innerType
}
private def proxyType : TypeExpr := {
  span := span 12 27, value := .proxy (span 12 13) comptimeType
}
private def comptimeParameter : FunctionParameter := {
  span := span 0 27, value := .typed marker name comptimeType
}
private def proxyParameter : FunctionParameter := {
  span := span 0 27, value := .typed marker name proxyType
}
private def typeEvent : ParseDiagnostic := {
  span := typeName.span, kind := .invalidIdentifierHyphen typeName.value
}
private def finishingEvent : ParseDiagnostic := {
  span := comptimeType.span, kind := .constraintViolation .comptimeTypeInParameter
}
private def seed (base : State) (prior : List ParseDiagnostic) : State := {
  base with diagnosticsRev := prior.reverse
}
private def finished (base : State) (prior : List ParseDiagnostic) : State := {
  seed base (prior ++ [typeEvent]) with
  diagnosticsRev := [finishingEvent] ++ (prior ++ [typeEvent]).reverse
}

private theorem comptime_events : TypedParameterFinishingTrace comptimeType [finishingEvent] :=
  .comptime (by simp [ParameterTypeAllowed, comptimeType])

theorem outer_comptime_adds_only_finishing_suffix (base : State) (prior : List ParseDiagnostic) :
    TypedParameterFinishingTrace comptimeType [finishingEvent] ∧
      finishTypedParameter (span 0 8) marker name comptimeType (seed base (prior ++ [typeEvent])) =
        .ok comptimeParameter (finished base prior) ∧
      (finished base prior).diagnostics = prior ++ [typeEvent, finishingEvent] ∧
      (finished base prior).file = base.file ∧ (finished base prior).tokens = base.tokens ∧
      (finished base prior).cursor = base.cursor ∧ (finished base prior).window = base.window := by
  refine ⟨comptime_events, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact finishTypedParameter_eq_ok_of_trace (span 0 8) marker name comptimeType
      (seed base (prior ++ [typeEvent])) comptime_events
  · simp only [finished, State.diagnostics, List.reverse_append, List.reverse_reverse,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc, List.cons_append]

theorem duplicate_constraints_remain_ordered (base : State) (prior : List ParseDiagnostic) :
    finishTypedParameter (span 0 8) marker name comptimeType
        (seed base (prior ++ [finishingEvent, finishingEvent, typeEvent])) =
      .ok comptimeParameter (finished base (prior ++ [finishingEvent, finishingEvent])) ∧
      (finished base (prior ++ [finishingEvent, finishingEvent])).diagnostics =
        prior ++ [finishingEvent, finishingEvent, typeEvent, finishingEvent] := by
  have result := outer_comptime_adds_only_finishing_suffix base (prior ++ [finishingEvent, finishingEvent])
  exact ⟨by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1,
    by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.2.1⟩

theorem proxy_of_comptime_is_silent (base : State) (prior : List ParseDiagnostic) :
    TypedParameterFinishingTrace proxyType [] ∧
      finishTypedParameter (span 0 8) marker name proxyType (seed base (prior ++ [typeEvent])) =
        .ok proxyParameter (seed base (prior ++ [typeEvent])) ∧
      (seed base (prior ++ [typeEvent])).diagnostics = prior ++ [typeEvent] := by
  have events : TypedParameterFinishingTrace proxyType [] := .ordinary (by trivial)
  refine ⟨events, ?_, ?_⟩
  · exact finishTypedParameter_eq_ok_of_trace (span 0 8) marker name proxyType
      (seed base (prior ++ [typeEvent])) events
  · simp only [seed, State.diagnostics, List.reverse_reverse]

private theorem exact_error (base : State) (prior : List ParseDiagnostic)
    (errorSpan : SourceSpan) (constraint : ParseConstraint) :
    ∃ output, errorParameter errorSpan constraint (seed base prior) =
      .ok { span := errorSpan, value := .error } output ∧
      output = { seed base prior with diagnosticsRev :=
        [{ span := errorSpan, kind := .constraintViolation constraint }] ++ prior.reverse } ∧
      output.diagnostics = prior ++ [{ span := errorSpan, kind := .constraintViolation constraint }] := by
  refine ⟨_, errorParameter_eq_ok_of_trace errorSpan constraint (seed base prior) .emitted, rfl, ?_⟩
  simp only [seed, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem missing_named_type_keeps_error_span (base : State) (prior : List ParseDiagnostic) :
    ErrorParameterFinishingTrace name.span .namedParameterRequiresType [{
      span := name.span, kind := .constraintViolation .namedParameterRequiresType
    }] ∧
      ∃ output, errorParameter name.span .namedParameterRequiresType (seed base prior) =
        .ok { span := span 9 12, value := .error } output ∧
        output = { seed base prior with diagnosticsRev :=
          [{ span := span 9 12, kind := .constraintViolation .namedParameterRequiresType }] ++ prior.reverse } ∧
        output.diagnostics = prior ++ [{ span := span 9 12, kind := .constraintViolation .namedParameterRequiresType }] :=
  ⟨.emitted, exact_error base prior name.span .namedParameterRequiresType⟩

theorem missing_comptime_type_keeps_covering_span (base : State) (prior : List ParseDiagnostic) :
    ErrorParameterFinishingTrace (SourceSpan.cover (span 0 8) name.span) .comptimeParameterRequiresType [{
      span := span 0 12, kind := .constraintViolation .comptimeParameterRequiresType
    }] ∧
      ∃ output, errorParameter (SourceSpan.cover (span 0 8) name.span) .comptimeParameterRequiresType
          (seed base prior) = .ok { span := span 0 12, value := .error } output ∧
        output = { seed base prior with diagnosticsRev :=
          [{ span := span 0 12, kind := .constraintViolation .comptimeParameterRequiresType }] ++ prior.reverse } ∧
        output.diagnostics = prior ++ [{ span := span 0 12, kind := .constraintViolation .comptimeParameterRequiresType }] :=
  ⟨.emitted, exact_error base prior (SourceSpan.cover (span 0 8) name.span) .comptimeParameterRequiresType⟩

end Solcore.Test.SyntaxTypedParameterFinishingTraceProperties
