import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState

/-! Original ordinary declarations and terminal leaves lift without a native
store. Each successful prefix transports the actual Source heap typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
open Core Frontend SourceInference Staging.Recursive

variable {program : Program} {registry : Registry} {invocation : Scope}

theorem nil {context mode} : Lifts (program := program) (registry := registry) (invocation := invocation) context mode [] := by
  intro environment before state size finalContext outcome after trace
  obtain ⟨rfl,rfl,rfl⟩ := SelectedCompilationStageScopedTerminalInversion.nil trace
  exact ⟨.nil,state.heapTyped,.refl _⟩

theorem returnUnit {context mode id node rest}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode (id::rest) := by
  intro environment before state size finalContext outcome after trace
  obtain ⟨rfl,rfl,rfl⟩ := SelectedCompilationStageScopedTerminalInversion.return_unit state.runtime.graph.nodeOccurrencesUnique found form trace
  exact ⟨.returnUnit (lookupStatement?_sound found) form,state.heapTyped,.refl _⟩

theorem terminal (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    {checked : SourceCoreCompatibleCatalog.Checked} {reasonAt context scope id lowered node mode statements}
    (head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation id mode statements)
    (certificate : CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt context scope id lowered)
    (found : invocation.source.lookupExpression? id = some node) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode statements := by
  intro environment before state size finalContext outcome after trace
  obtain ⟨child,plain,_,rfl,rfl,childTrace⟩ := SelectedCompilationStageScopedTerminalInversion.child_of_body state.runtime.graph.nodeOccurrencesUnique head trace
  have lifted := expression (registry := registry) certificate state.runtime.graph.nodeOccurrencesUnique childTrace
  obtain ⟨_,measured⟩ := Size.Expression.of_trace lifted
  cases plain with
  | value value =>
    obtain ⟨_,reached,extension⟩ := expression_typed selectedBodies certificate found state childTrace
    exact ⟨(head.trace measured).sound,reached.heapTyped,extension⟩
  | fault reason => exact ⟨(head.trace measured).sound,trivial⟩

theorem State.allocate {context nextContext environment before binder value location after}
    (state : State (program := program) (invocation := invocation) context environment before)
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (typed : Dynamic.OptionalValueHasType context before value binder.scheme.body)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body value location after) :
    State (program := program) (invocation := invocation) nextContext ((binder.id,location)::environment) after := by
  refine ⟨state.runtime.transport (.ofBinderExtends extended),
    (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers state.covers,?_,
    (Dynamic.HeapWellTyped.iff_of_binderExtends extended).mp (state.heapTyped.allocate typed allocated)⟩
  cases extended
  exact .cons allocated.reads_new rfl (.ordinary mono rfl)
    (state.locals.mono (.of_allocation allocated))

theorem Post.restore {context nextContext before middle after owner binder outcome}
    (extended : BinderExtends owner context binder nextContext)
    (extension : Dynamic.HeapTypesExtend before middle)
    (post : Post nextContext middle after outcome) : Post context before after outcome := by
  cases outcome <;> try exact trivial
  all_goals exact ⟨(Dynamic.HeapWellTyped.iff_of_binderExtends extended).mpr post.1,extension.trans post.2⟩

theorem absent {context nextContext mode id node binder rest}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (mono : binder.scheme.quantified = []) (extended : BinderExtends invocation.source.owner context binder nextContext)
    (remaining : Lifts (program := program) (registry := registry) (invocation := invocation) nextContext mode rest) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode (id::rest) := by
  intro environment before state size finalContext outcome after trace
  obtain ⟨_,_,_,_,allocated,tail⟩ := SelectedCompilationStageLexicalInversion.absent state.runtime.graph.nodeOccurrencesUnique found form mono extended trace
  obtain ⟨lifted,post⟩ := remaining (state.allocate mono extended (.none _) allocated) tail
  exact ⟨.letUninitialized (lookupStatement?_sound found) form mono extended allocated lifted,
    post.restore extended (.of_allocation allocated)⟩

theorem initialized (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    {checked : SourceCoreCompatibleCatalog.Checked} {reasonAt context nextContext scope mode id node binder initializer initializerNode lowered rest}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = []) (extended : BinderExtends invocation.source.owner context binder nextContext)
    (initializerFound : invocation.source.lookupExpression? initializer = some initializerNode)
    (sourceType : initializerNode.type = binder.scheme.body)
    (certificate : CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt context scope initializer lowered)
    (remaining : Lifts (program := program) (registry := registry) (invocation := invocation) nextContext mode rest) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode (id::rest) := by
  intro environment before state size finalContext outcome after trace
  rcases SelectedCompilationStageLexicalInversion.initialized state.runtime.graph.nodeOccurrencesUnique found form mono extended trace with failed | done
  · obtain ⟨_,_,_,rfl,rfl,child⟩ := failed
    exact ⟨.letFault (lookupStatement?_sound found) form mono (expression certificate state.runtime.graph.nodeOccurrencesUnique child),trivial⟩
  · obtain ⟨_,_,_,_,_,_,_,_,child,allocated,tail⟩ := done
    have first := expression (registry := registry) certificate state.runtime.graph.nodeOccurrencesUnique child
    obtain ⟨typed,reached,extension⟩ := expression_typed selectedBodies certificate initializerFound state child
    obtain ⟨lifted,post⟩ := remaining (reached.allocate mono extended (.some (sourceType ▸ typed)) allocated) tail
    exact ⟨.letInitialized (lookupStatement?_sound found) form first mono extended allocated lifted,
      post.restore extended (extension.trans (.of_allocation allocated))⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
