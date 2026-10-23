import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationCapturedAllocation
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAcceptedInitializer

/-! The actual reached capture supplies its stored attachment even when its
native bundle has no candidate rows. The original binding source is supplied
by the real initialized statement compiler. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference TypeSystem
open CallableBodyMetadataViews CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {index : Index compiled ReachedView}

private theorem capture_roots {function : Dynamic.GeneralizedClosure}
    {roots : List NodeId}
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : Reaches function.source roots (.expression function.initializer)) :
    ∀ id ∈ lambdaRoots function.initializer function.body, Reaches function.source roots id := by
  obtain ⟨node, occurrence, form, _⟩ := captures.occurrence
  have found := lookupExpression?_complete unique occurrence
  intro id member
  rcases List.mem_cons.mp member with same | inBody
  · exact same ▸ reached
  · apply Reaches.expression reached found
    simpa only [form, ExpressionForm.references] using inBody

/-- This attachment uses the actual invocation and full native binding
origin. It does not require any candidate to exist in the bundle. -/
theorem Index.allocation_attachment (index : Index compiled ReachedView)
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    (source : binding.source = index.originalSource)
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer)) :
    GeneralizedLocalReachedAllocation.Attachment function binding index.active := by
  have view : BodyView function.source index.compilerSource (index.statements.map NodeId.statement) := by
    rw [sameSource]
    exact index.reached_view
  have actualReached : Reaches function.source (index.statements.map NodeId.statement)
      (.expression function.initializer) := view.symm.reaches reached
  refine ⟨GeneralizedLocalPreparedClosure.invocation_closed index, ?_⟩
  rw [source, ← index.compiler_original]
  exact view.restrict (capture_roots captures unique actualReached)

/-- A real statement site adds its lexical residual scope to the same
attachment, ready for storage and later contextual reads. -/
theorem Index.ResidualEntry.statement_attachment (entry : index.ResidualEntry)
    {id : StatementId} (site : index.Site (.statement id))
    {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {binder : TypedBinder} {binding : SourceCoreLocalPolymorphism.Binding}
    (form : statement.form = .letDecl binder (some binding.initializer))
    (source : binding.source = index.originalSource)
    (metadata : binding.binder.applySubstitution index.active = binder)
    {function : Dynamic.GeneralizedClosure}
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer)) :
    GeneralizedLocalCapturedScopes.Attachment function binding index.active := by
  refine ⟨index.allocation_attachment source sameSource captures unique reached, ?_⟩
  have captured := entry.capture_statement site found form
  have quantified : binding.binder.scheme.quantified = binder.scheme.quantified := by
    simpa only [TypedBinder.applySubstitution, Scheme.apply] using
      congrArg (fun actual : TypedBinder => actual.scheme.quantified) metadata
  simpa only [source, quantified] using captured

/-- A captured descriptor keeps this invocation's actual frame and its
reached lexical attachment. The native binding can have an empty bundle. -/
theorem Index.ResidualEntry.descriptor_at_statement (entry : index.ResidualEntry)
    (frame : Frame index)
    {id : StatementId} (site : index.Site (.statement id))
    {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {binder : TypedBinder} {initializer : ExpressionId}
    (form : statement.form = .letDecl binder (some initializer))
    {binding : SourceCoreLocalPolymorphism.Binding}
    (located : compiled.indexed.base.locals.binding index.owner binder.id = .ok binding)
    (metadata : binding.binder.applySubstitution index.active = binder)
    (initial : binding.initializer = initializer)
    (source : binding.source = index.originalSource)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {function : Dynamic.GeneralizedClosure}
    (captures : Dynamic.GeneralizedClosureCaptures context index.source environment
      binder initializer function)
    (unique : NodeOccurrencesUnique index.source) :
    ∃ origin : GeneralizedLocalDescriptorOrigin.Origin compiled.indexed function binding index.active,
      origin.native = frame.native ∧ origin.ghost = frame.ghost ∧ origin.metadata = frame.metadata ∧
      GeneralizedLocalCapturedScopes.Attachment function binding index.active ∧
      Nonempty (GeneralizedLocalLocatedRows.Attachment
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed GeneralizedLocalCapturedScopes.Attachment)
        function binding index.active) := by
  obtain ⟨owner, binderId⟩ := SourceCoreLocalPolymorphism.Catalog.binding_identity located
  have registered : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding := by
    simpa only [owner, binderId] using located
  have selfCapture : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function := by
    simpa only [captures.definitionContext_eq, captures.source_eq, captures.captured_eq,
      captures.binder_eq, captures.initializer_eq] using captures
  have reached : index.Reached (.expression function.initializer) := by
    rw [captures.initializer_eq]
    exact .statement site.reached found (by simp [form, StatementForm.references])
  let origin : GeneralizedLocalDescriptorOrigin.Origin compiled.indexed function binding index.active := {
    native := frame.native
    ghost := frame.ghost
    metadata := frame.metadata
    carried := frame.carried
    paired := captures.source_eq.symm ▸ frame.paired
    owner := frame.owner.trans owner.symm
    active := frame.active }
  have attached := entry.statement_attachment site found (initial.symm ▸ form)
    source metadata captures.source_eq selfCapture (captures.source_eq.symm ▸ unique) reached
  exact ⟨origin, rfl, rfl, rfl, attached,
    ⟨⟨registered, selfCapture, ⟨origin⟩,
      (congrArg TypedBinder.id captures.binder_eq).trans binderId.symm,
      captures.initializer_eq.trans initial.symm⟩⟩⟩

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
