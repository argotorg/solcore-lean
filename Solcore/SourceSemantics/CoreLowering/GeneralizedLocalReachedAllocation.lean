import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationInputIdentities
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationReachedReads
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualAllocation

/-! The actual reached initializer attaches body correspondence to the same
stored Snapshot. Unrelated table entries and input types are not compared. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAllocation
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open CallableBodyMetadataViews CallableLambdaBodyReachability
open CallableAncestryProfiles.SourceComposition
open GeneralizedLocalDescriptorOrigin (Origin)
open GeneralizedLocalInstanceValues (referenceIndex value)
open GeneralizedLocalAcceptedInstances (Snapshot)

/-- Evidence carried by the existing Snapshot, not another closure model. -/
structure Attachment (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (lexical : Substitution) : Prop where
  closed : RangesClosed lexical
  view : BodyView function.source (binding.source.applySubstitution lexical)
    (lambdaRoots function.initializer function.body)

private theorem source_at {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {owner : SourceCompilationPlan.Key} {active : Substitution} {source : TypedSource}
    (receipt : LambdaSourceAlignment.SourceReceipt program plan owner active source)
    {original : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok original) :
    source = original.function.typedBody.applySubstitution active := by
  cases receipt with
  | original found =>
    cases Except.ok.inj (found.symm.trans selected)
    exact (EmptySourceSubstitution.source _).symm
  | contextual accepted =>
    obtain ⟨row, found, _, _, same⟩ := LambdaSourceAlignment.prepared_source accepted
    cases Except.ok.inj (found.symm.trans selected)
    exact same

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

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The invocation supplies both the source-view relation and its original
compiler receipt. The lambda roots come from the actual reached capture. -/
theorem attachment_of_invocation
    (index : ActualBodyInvocation.Index compiled ActualBodyInvocation.ReachedView)
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext index.active)
    (owner : binding.caller = index.owner)
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer))
    (closed : RangesClosed index.active) : Attachment function binding index.active := by
  obtain ⟨candidateOwner, originalSource, _, _⟩ :=
    SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨row, selected, source, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan, candidateOwner, owner] at selected
  have current := source_at index.compiler_source_receipt selected
  rw [source, originalSource] at current
  have view : BodyView function.source index.compilerSource (index.statements.map NodeId.statement) := by
    rw [sameSource]
    exact index.reached_view
  have actualReached : Reaches function.source (index.statements.map NodeId.statement)
      (.expression function.initializer) := view.symm.reaches reached
  exact ⟨closed, current ▸ view.restrict (capture_roots captures unique actualReached)⟩

/-- The real creation evaluation stores the restricted proof alongside the
same candidate, captures, native value, and frame reference. -/
theorem formation_at_frame
    (index : ActualBodyInvocation.Index compiled ActualBodyInvocation.ReachedView)
    {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    {actual : Core.Environment}
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext index.active)
    (sameLexical : indexed.lexical = index.active)
    (owner : inputs.current.owner = binding.caller)
    (currentOwner : binding.caller = index.owner)
    (initializer : inputs.initializer = binding.initializer)
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer))
    (closed : RangesClosed index.active)
    (origin : Origin compiled.indexed function binding index.active)
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world
      inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type compiled.indexed.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (reference : captured.canonical[referenceIndex indexed]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (value indexed captured.embedding origin.native actual) store ∧
    Snapshot compiled.indexed mapping world function binding index.active location
      (Attachment function binding index.active) candidate
      (value indexed captured.embedding origin.native actual) := by
  have attached := attachment_of_invocation index indexed located member currentOwner sameSource
    captures unique reached closed
  obtain ⟨_, source, binder, _⟩ := SelectedCompilationLocalOrigins.at_context compiled located member
  exact GeneralizedLocalAcceptedInstances.formation_at_frame_with indexed sameLexical owner initializer
    source (congrArg TypedBinder.id binder) _ attached origin captured declarations ownership issuer
    typed stored reference read

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAllocation
