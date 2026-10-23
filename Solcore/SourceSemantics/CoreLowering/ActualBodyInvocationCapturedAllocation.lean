import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationCapturedScope
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBinderMetadata

/-! A successful binder compiler checks the actual binder metadata. Together
with the accepted candidate, this attaches captured scope to the same stored
Snapshot at an initialized statement or loop header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalAcceptedInstances (Snapshot)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {bodyRelation : BodyRelation} {index : Index compiled bodyRelation}

theorem Index.ResidualEntry.capture_binding_statement
    (entry : index.ResidualEntry) {id : StatementId}
    (site : index.Site (.statement id)) {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {binding : SourceCoreLocalPolymorphism.Binding} {binder : TypedBinder}
    (form : statement.form = .letDecl binder (some binding.initializer))
    {scope : SourceCoreLocalCell.Scope} {type : Core.Ty}
    (lowered : SourceCoreLocalPolymorphism.lowerBinder compiled.indexed.base.locals
      index.owner index.active index.compilerSource scope binder = .ok type)
    (located : compiled.indexed.base.locals.binding index.owner binder.id = .ok binding)
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (member : candidate ∈ binding.atContext index.active) :
    CapturedResidualScope binding.source binding.initializer
      binding.binder.scheme.quantified index.active.domain := by
  obtain ⟨owner, binderId⟩ := SourceCoreLocalPolymorphism.Catalog.binding_identity located
  have ownLocated : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding := by
    simpa only [owner, binderId] using located
  have source := index.binding_original indexed ownLocated member owner
  have captured := entry.capture_statement site found form
  rw [SourceCoreLocalPolymorphism.lowerBinder_quantified lowered located] at captured
  simpa only [source] using captured

theorem Index.ResidualEntry.capture_binding_header
    (entry : index.ResidualEntry) {id : StatementId}
    (site : index.Site (.statement id)) {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {initializers post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initializers condition post body)
    {binding : SourceCoreLocalPolymorphism.Binding} {binder : TypedBinder}
    (present : .letDecl binder (some binding.initializer) ∈ initializers ++ post)
    {scope : SourceCoreLocalCell.Scope} {type : Core.Ty}
    (lowered : SourceCoreLocalPolymorphism.lowerBinder compiled.indexed.base.locals
      index.owner index.active index.compilerSource scope binder = .ok type)
    (located : compiled.indexed.base.locals.binding index.owner binder.id = .ok binding)
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (member : candidate ∈ binding.atContext index.active) :
    CapturedResidualScope binding.source binding.initializer
      binding.binder.scheme.quantified index.active.domain := by
  obtain ⟨owner, binderId⟩ := SourceCoreLocalPolymorphism.Catalog.binding_identity located
  have ownLocated : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding := by
    simpa only [owner, binderId] using located
  have source := index.binding_original indexed ownLocated member owner
  have captured := entry.capture_header site found form present
  rw [SourceCoreLocalPolymorphism.lowerBinder_quantified lowered located] at captured
  simpa only [source] using captured

theorem Index.ResidualEntry.retain_statement
    (entry : index.ResidualEntry) {id : StatementId}
    (site : index.Site (.statement id)) {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {binding : SourceCoreLocalPolymorphism.Binding} {binder : TypedBinder}
    (form : statement.form = .letDecl binder (some binding.initializer))
    {scope : SourceCoreLocalCell.Scope} {type : Core.Ty}
    (lowered : SourceCoreLocalPolymorphism.lowerBinder compiled.indexed.base.locals
      index.owner index.active index.compilerSource scope binder = .ok type)
    (located : compiled.indexed.base.locals.binding index.owner binder.id = .ok binding)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {location : Core.Location}
    {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}
    (member : candidate ∈ binding.atContext index.active)
    (snapshot : Snapshot compiled.indexed mapping world function binding index.active location
      (GeneralizedLocalReachedAllocation.Attachment function binding index.active) candidate native) :
    Snapshot compiled.indexed mapping world function binding index.active location
      (GeneralizedLocalCapturedScopes.Attachment function binding index.active) candidate native := by
  apply GeneralizedLocalCapturedScopes.retain_scope snapshot
  cases snapshot with
  | retained packet indexed acceptedBody sameLexical owner initializer candidateSource candidateBinder
      attached origin frame declarations ownership issuer reference typed runtimeTyped =>
    exact entry.capture_binding_statement site found form lowered located indexed member

theorem Index.ResidualEntry.retain_header
    (entry : index.ResidualEntry) {id : StatementId}
    (site : index.Site (.statement id)) {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {initializers post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initializers condition post body)
    {binding : SourceCoreLocalPolymorphism.Binding} {binder : TypedBinder}
    (present : .letDecl binder (some binding.initializer) ∈ initializers ++ post)
    {scope : SourceCoreLocalCell.Scope} {type : Core.Ty}
    (lowered : SourceCoreLocalPolymorphism.lowerBinder compiled.indexed.base.locals
      index.owner index.active index.compilerSource scope binder = .ok type)
    (located : compiled.indexed.base.locals.binding index.owner binder.id = .ok binding)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {location : Core.Location}
    {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}
    (member : candidate ∈ binding.atContext index.active)
    (snapshot : Snapshot compiled.indexed mapping world function binding index.active location
      (GeneralizedLocalReachedAllocation.Attachment function binding index.active) candidate native) :
    Snapshot compiled.indexed mapping world function binding index.active location
      (GeneralizedLocalCapturedScopes.Attachment function binding index.active) candidate native := by
  apply GeneralizedLocalCapturedScopes.retain_scope snapshot
  cases snapshot with
  | retained packet indexed acceptedBody sameLexical owner initializer candidateSource candidateBinder
      attached origin frame declarations ownership issuer reference typed runtimeTyped =>
    exact entry.capture_binding_header site found form present lowered located indexed member

/-! The actual native frame creation consumes the scope above, retaining the
same evaluation and strengthening only the stored proof component. -/
theorem Index.ResidualEntry.form_statement_at_actual_frame
    (index : Index compiled ReachedView) (entry : index.ResidualEntry)
    {statementId : StatementId} (site : index.Site (.statement statementId))
    {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? statementId = some statement)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    {actual : Core.Environment}
    {allocatedBinder : TypedBinder} {type : Core.Ty}
    (form : statement.form = .letDecl allocatedBinder (some binding.initializer))
    (lowered : SourceCoreLocalPolymorphism.lowerBinder compiled.indexed.base.locals
      index.owner index.active index.compilerSource inputs.scope allocatedBinder = .ok type)
    (located : compiled.indexed.base.locals.binding index.owner allocatedBinder.id = .ok binding)
    (member : candidate ∈ binding.atContext index.active)
    (sameLexical : indexed.lexical = index.active)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer))
    (origin : GeneralizedLocalDescriptorOrigin.Origin compiled.indexed function binding index.active)
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world
      inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type compiled.indexed.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (reference : captured.canonical[GeneralizedLocalInstanceValues.referenceIndex indexed]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (GeneralizedLocalInstanceValues.value indexed captured.embedding origin.native actual) store ∧
    Snapshot compiled.indexed mapping world function binding index.active location
      (GeneralizedLocalCapturedScopes.Attachment function binding index.active) candidate
      (GeneralizedLocalInstanceValues.value indexed captured.embedding origin.native actual) := by
  obtain ⟨currentOwner, binderId⟩ := SourceCoreLocalPolymorphism.Catalog.binding_identity located
  have ownLocated : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding := by
    simpa only [currentOwner, binderId] using located
  obtain ⟨evaluation, snapshot⟩ := GeneralizedLocalReachedAllocation.formation_at_actual_frame index
    indexed ownLocated member sameLexical owner currentOwner initializer sameSource captures unique
    reached origin captured declarations ownership issuer typed stored reference read
  exact ⟨evaluation, entry.retain_statement site found form lowered located member snapshot⟩

theorem Index.ResidualEntry.form_header_at_actual_frame
    (index : Index compiled ReachedView) (entry : index.ResidualEntry)
    {statementId : StatementId} (site : index.Site (.statement statementId))
    {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? statementId = some statement)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    {actual : Core.Environment}
    {allocatedBinder : TypedBinder} {type : Core.Ty}
    {initializers post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initializers condition post body)
    (present : .letDecl allocatedBinder (some binding.initializer) ∈ initializers ++ post)
    (lowered : SourceCoreLocalPolymorphism.lowerBinder compiled.indexed.base.locals
      index.owner index.active index.compilerSource inputs.scope allocatedBinder = .ok type)
    (located : compiled.indexed.base.locals.binding index.owner allocatedBinder.id = .ok binding)
    (member : candidate ∈ binding.atContext index.active)
    (sameLexical : indexed.lexical = index.active)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer))
    (origin : GeneralizedLocalDescriptorOrigin.Origin compiled.indexed function binding index.active)
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world
      inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type compiled.indexed.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (reference : captured.canonical[GeneralizedLocalInstanceValues.referenceIndex indexed]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (GeneralizedLocalInstanceValues.value indexed captured.embedding origin.native actual) store ∧
    Snapshot compiled.indexed mapping world function binding index.active location
      (GeneralizedLocalCapturedScopes.Attachment function binding index.active) candidate
      (GeneralizedLocalInstanceValues.value indexed captured.embedding origin.native actual) := by
  obtain ⟨currentOwner, binderId⟩ := SourceCoreLocalPolymorphism.Catalog.binding_identity located
  have ownLocated : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding := by
    simpa only [currentOwner, binderId] using located
  obtain ⟨evaluation, snapshot⟩ := GeneralizedLocalReachedAllocation.formation_at_actual_frame index
    indexed ownLocated member sameLexical owner currentOwner initializer sameSource captures unique
    reached origin captured declarations ownership issuer typed stored reference read
  exact ⟨evaluation, entry.retain_header site found form present lowered located member snapshot⟩

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
