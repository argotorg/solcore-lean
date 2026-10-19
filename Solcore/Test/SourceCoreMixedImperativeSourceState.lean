import Solcore.Test.SourceCoreSelectedInterleavedLocalTrace
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation

/-! The independent Source trace carries its own typing and lexical state.
Preservation is used only after constructing an actual Source step. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative
open Solcore Frontend SourceInference SourceSemantics

structure SourceState (program : SourceSemantics.Program) (source : TypedSource)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) : Prop where
  runtime : Dynamic.SourceRuntimeValid program context source
  covers : evidence.Covers context
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  heapTyped : Dynamic.HeapWellTyped context heap

theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

theorem SourceState.after_statement {program : SourceSemantics.Program} {source : TypedSource}
    {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment next : Dynamic.Environment} {before after : Dynamic.Heap}
    (state : SourceState program source context evidence environment before)
    (wellFormed : ProgramWellFormed program) {control : ControlContext} {id : StatementId} {facts : StatementFacts}
    (typed : StatementHasType source control context id final facts)
    (trace : Dynamic.StatementExecutes program context evidence source environment before id final (.fallthrough next) after) :
    SourceState program source final evidence next after := by
  have kept := wellFormed.wholeLanguagePreservation.statements _ _ _ _ _ _ _ _ _ _ _ _
    state.runtime state.covers state.locals state.heapTyped (StatementsHaveType.singleton typed)
    (Dynamic.StatementsExecute.cons trace .nil)
  have fields := Dynamic.StatementHasType.runtimeContextFields typed
  cases kept.outcome_typed with
  | fallthrough locals =>
    exact ⟨state.runtime.transport fields, fields.covers state.covers, locals,
      kept.heap_typed.transportClosed fields.signatures state.runtime.closed
        (fields.targetClosed state.runtime.closed) state.runtime.variables_closed
        (fields.targetResidualVariablesOpen state.runtime.residual_variables_open)⟩

theorem SourceState.after_expression {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    (state : SourceState program source context evidence environment before)
    (wellFormed : ProgramWellFormed program) {id : ExpressionId} {type : TypeSystem.Ty} {value : Dynamic.Value}
    (typed : ExpressionHasType source context id type)
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    SourceState program source context evidence environment after := by
  have kept := wellFormed.wholeLanguagePreservation.expression _ _ _ _ _ _ _ _ _
    state.runtime state.covers state.locals state.heapTyped typed trace
  exact ⟨state.runtime, state.covers, state.locals.mono kept.heap_extends, kept.heap_typed⟩

/-- Exact append-only Source heaps keep earlier initialized cells readable. -/
def HeapAppends (before after : Dynamic.Heap) : Prop := ∃ cells, after.cells = before.cells ++ cells

theorem HeapAppends.refl (heap : Dynamic.Heap) : HeapAppends heap heap := ⟨[], by simp⟩
theorem HeapAppends.trans {first middle last : Dynamic.Heap}
    (left : HeapAppends first middle) (right : HeapAppends middle last) : HeapAppends first last := by
  obtain ⟨a, ha⟩ := left
  obtain ⟨b, hb⟩ := right
  exact ⟨a ++ b, by rw [hb,ha,List.append_assoc]⟩

theorem HeapAppends.read {before after : Dynamic.Heap} (append : HeapAppends before after)
    {location : Dynamic.Location} {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads before location cell) :
    Dynamic.Heap.Reads after location cell := by
  obtain ⟨cells, same⟩ := append
  cases read with
  | intro selected =>
    apply Dynamic.Heap.Reads.intro
    rw [same]
    exact selected.append_left

end Tests.SourceCoreMixedImperative
