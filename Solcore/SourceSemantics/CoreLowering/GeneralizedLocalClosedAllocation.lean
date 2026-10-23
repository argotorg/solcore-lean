import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalPreparedClosure

/-! The authentic invocation factory supplies closed native ranges. Allocation
uses that fact for the same Snapshot and the same reached body attachment. -/
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
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The actual Packet validated its discovered local instance before creation.
No independent closedness premise is needed at the allocation boundary. -/
theorem attachment_of_actual_invocation
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
    (reached : index.Reached (.expression function.initializer)) : Attachment function binding index.active := by
  exact attachment_of_invocation index indexed located member owner sameSource captures unique reached
    (GeneralizedLocalPreparedClosure.invocation_closed index)

/-- The actual frame creation stores the same captured environment and native
value; authentic preparation supplies the attachment's closedness field. -/
theorem formation_at_actual_frame
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
  exact formation_at_frame index indexed located member sameLexical owner currentOwner initializer
    sameSource captures unique reached (GeneralizedLocalPreparedClosure.invocation_closed index)
    origin captured declarations ownership issuer typed stored reference read

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAllocation
