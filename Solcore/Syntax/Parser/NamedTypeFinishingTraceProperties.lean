import Solcore.Syntax.DeclarativeNamedTypeFinishingTraceProperties
import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.Parser.Type

/-! Finishing a named type always succeeds, retaining every State field except
the exact spelling-dependent appended events. Qualified `mapping` is not the
bare spelling, and optional generic arguments determine the report's span. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem mapping_guard_iff (name : QualifiedName) :
    (name.value.components.tail.isEmpty && name.value.components.head.value == "mapping") = true ↔
      DeclarativeGrammar.UnqualifiedMappingSpelling name := by
  simp [DeclarativeGrammar.UnqualifiedMappingSpelling]

theorem makeNamedType_eq_traceValue (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    makeNamedType name arguments = DeclarativeGrammar.namedTypeTraceValue name arguments := by
  cases arguments <;> rfl

theorem finishNamedType_eq_ok_of_trace (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) (input : State)
    {trace : List ParseDiagnostic}
    (events : DeclarativeGrammar.NamedTypeFinishingTrace name arguments trace) :
    finishNamedType name arguments input =
      .ok (DeclarativeGrammar.namedTypeTraceValue name arguments)
        { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases events with
  | canonicalRequired spelling =>
      have selected := (mapping_guard_iff name).mpr spelling
      simp only [finishNamedType, selected, if_true, emitDiagnostic, modifyState, bind,
        pure, State.emit, makeNamedType_eq_traceValue]
      rfl
  | ordinary spelling =>
      have absent : (name.value.components.tail.isEmpty && name.value.components.head.value == "mapping") = false := by
        apply Bool.eq_false_iff.mpr
        intro selected
        exact spelling ((mapping_guard_iff name).mp selected)
      simp only [finishNamedType, absent, Bool.false_eq_true, if_false, bind, pure,
        makeNamedType_eq_traceValue]
      rfl

theorem finishNamedType_success_trace_sound (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr))
    {input output : State} {value : TypeExpr}
    (result : finishNamedType name arguments input = .ok value output) :
    ∃ trace, DeclarativeGrammar.NamedTypeFinishingTrace name arguments trace ∧
      value = DeclarativeGrammar.namedTypeTraceValue name arguments ∧
      output = { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases DeclarativeGrammar.namedTypeFinishingTrace_exists name arguments with ⟨trace, events⟩
  have expected := finishNamedType_eq_ok_of_trace name arguments input events
  rw [result] at expected
  exact ⟨trace, events, (Reply.ok.inj expected).1, (Reply.ok.inj expected).2⟩

theorem finishNamedType_success_context (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    ParserSuccessContext (finishNamedType name arguments) := by
  intro input output value result
  rcases finishNamedType_success_trace_sound name arguments result with ⟨trace, _, _, same⟩
  rw [same]
  exact ⟨rfl, rfl⟩

theorem finishNamedType_trace_success_iff (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) {input : State}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NamedTypeFinishingTrace name arguments trace ↔
    ∃ output, finishNamedType name arguments input =
        .ok (DeclarativeGrammar.namedTypeTraceValue name arguments) output ∧
      output.declarativeRemainder = input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro events
    refine ⟨_, finishNamedType_eq_ok_of_trace name arguments input events, rfl, ?_⟩
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]
  · rintro ⟨output, result, _, diagnostics⟩
    rcases finishNamedType_success_trace_sound name arguments result with ⟨actual, events, _, same⟩
    rw [same] at diagnostics
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse] at diagnostics
    have traceEq := List.append_cancel_left diagnostics
    simpa only [traceEq] using events

theorem finishNamedType_ne_reject (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) (input rejected : State) (failure : Failure) :
    finishNamedType name arguments input ≠ .reject failure rejected := by
  rcases DeclarativeGrammar.namedTypeFinishingTrace_exists name arguments with ⟨trace, events⟩
  rw [finishNamedType_eq_ok_of_trace name arguments input events]
  intro impossible
  contradiction

end Solcore.Syntax.Parser
