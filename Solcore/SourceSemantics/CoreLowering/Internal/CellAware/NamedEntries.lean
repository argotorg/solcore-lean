import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.LambdaCompilation
import Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedProjected
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.CellAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.OrdinaryBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MatchPrefixes
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyReads
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyEntries
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedParameters
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReceipts
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthorityReception
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls

/-!
# Cell-aware named bodies: entries and calls

The named entry and parameter entry, descriptors, declaration prefixes, call ports and authority, and the meaning of named expression trees with their Source lifting.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedDescriptor
/-! The actual named entry and the original lexical capture determine the
stored descriptor's source and binding. Neither projected function types nor
native closure headers are used to reconstruct Source identity. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedDescriptor
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (source state)
open CallableIndexedHistory

/-- The original catalog observation supplies the stored binding; the actual
named hook supplies its paired Source metadata and lexical frame. -/
theorem of_capture {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {binder : TypedBinder} {initializer : ExpressionId}
    (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
      (source named) binder initializer)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {function : Dynamic.GeneralizedClosure}
    (captures : Dynamic.GeneralizedClosureCaptures context (source named) environment binder initializer function)
    {id : Word} {native : NativeFrame}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some id)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (carried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      native (.named id) (some (state named))) :
    ∃ origin : GeneralizedLocalDescriptorOrigin.Origin prepared function site.binding [],
      origin.native = native ∧ origin.ghost = .named id ∧ origin.metadata = state named ∧
      origin.metadata = ⟨⟨site.binding.caller, [], site.binding.source⟩, []⟩ ∧
      Nonempty (GeneralizedLocalLocatedRows.Attachment
        (GeneralizedLocalInstanceValues.model prepared) function site.binding []) ∧
      function.source = site.binding.source ∧ function.binder = site.binding.binder ∧
      function.initializer = site.binding.initializer := by
  have binderEq : site.binding.binder = binder := by
    simpa only [EmptySourceSubstitution.binder] using site.bindingMetadata
  have sourceEq : site.binding.source = source named := by
    simpa only [EmptySourceSubstitution.source] using site.bindingSource
  have selfCapture : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function := by
    simpa only [captures.definitionContext_eq, captures.source_eq, captures.captured_eq,
      captures.binder_eq, captures.initializer_eq] using captures
  let origin : GeneralizedLocalDescriptorOrigin.Origin prepared function site.binding [] := {
    native
    ghost := .named id
    metadata := state named
    carried
    paired := by
      rw [captures.source_eq]
      exact .named (CallableIndexedNamedGeneration.seed prepared selected record)
    owner := site.bindingCaller.symm
    active := rfl }
  have registered : prepared.base.locals.binding site.binding.caller site.binding.binder.id = .ok site.binding := by
    rw [site.bindingCaller, binderEq]
    exact site.located
  have namedMetadata : origin.metadata = ⟨⟨site.binding.caller, [], site.binding.source⟩, []⟩ := by
    change state named = _
    rw [site.bindingCaller, sourceEq]
    rfl
  exact ⟨origin, rfl, rfl, rfl, namedMetadata, ⟨⟨registered, selfCapture, ⟨origin⟩,
      congrArg TypedBinder.id (captures.binder_eq.trans binderEq.symm),
      captures.initializer_eq.trans site.bindingInitializer.symm⟩⟩,
    captures.source_eq.trans sourceEq.symm, captures.binder_eq.trans binderEq.symm,
    captures.initializer_eq.trans site.bindingInitializer.symm⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedDescriptor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedPrefix
/-! A genuine named declaration constructs its descriptor origin from the
selected caller and extends the physical lexical authority at the actual
marked allocation. The declaration first copies its scope; the principal
captures the copies and the continuation keeps the original cells. No future
expression or body behavior is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (initializedRequest)
open CellAwareGeneralizedSnapshotCode (snapshotInner snapshotSequence)
open GeneralizedLocalDescriptorHeap GeneralizedLocalLocatedRows
open CallableIndexedNamedGeneration (source context)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)

include bridge in
/-- The caller witness reaches every administrative extension through the
owned pool and its returned wrapper. -/
theorem transitions : ProtectedStateTransition.AdministrativeTransitions protocol := by
  intro _ initial _ _ _ _ maps worlds frame metadata
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedFunctionState.protocol headers keys)
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys) (bridge.pool initial)
    maps worlds frame metadata
  obtain ⟨returned, _, callerRelated⟩ := bridge.restore initial reached maps worlds frame metadata related
  exact ⟨returned, callerRelated⟩

include record in
set_option maxHeartbeats 2000000 in
theorem complete {scope : SourceCoreLocalCell.Scope} {sourceContext nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {initializer : ExpressionId} {childFuel : Nat} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {administrative actualContext : Core.Context}
    (site : CellAwareSourceBodyAdmission.Site whole.indexed.base.locals named.signature.key []
      (source named) binder initializer)
    (receipt : GeneralizedLocalInitializerPackets.Receipt whole.indexed
      (GeneralizedLocalInitializerCompilation.namedInputs compiled childFuel (childFuel + 1)
        (context whole.indexed named) scope initializer reasonAt) site.binding [] lowered)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt)
    (declaration : (SourceCoreDataPlaces.declaredBinders (source named)).filter
      (fun actual => decide (actual.id = binder.id)) = [binder])
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends (source named).owner sourceContext binder nextContext)
    (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
      (initializedRequest (source named) scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest (source named) scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    {captured : Expr}
    (copied : SourceCoreSourceCells.copyScope (some (CallableIndexedNamedGeneration.allocator whole.indexed named))
      (source named) scope (fun index => index) (snapshotInner lowered.type lowered.expression annotation.expression) =
        .ok captured)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
    (bindings : ProtectedStateTransition.Bindings protocol)
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap} {store : Store}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before sourceContext.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge sourceContext initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical whole named sourceContext scope canonical mapping world before store environment)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {copies : Dynamic.Environment} {snapshotHeap : Dynamic.Heap}
    {function : Dynamic.GeneralizedClosure} {location : Dynamic.Location}
    (snapshot : Dynamic.EnvironmentCopies (source named) environment before copies snapshotHeap)
    (captures : Dynamic.GeneralizedClosureCaptures sourceContext (source named) copies binder initializer function)
    (functionTyped : Dynamic.GeneralizedClosureWellTyped sourceContext snapshotHeap function)
    (allocated : Dynamic.Heap.AllocatesGeneralized snapshotHeap function location after)
    (output : Ty) (body : Expr) :
    ∃ values marker, ∃ (copiedStore : Store) (copiedMap : LocationMap) (copiedWorld : StoreTyping),
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := copiedStore ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame
        physical.native, SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := copiedWorld ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := copiedMap ++ [copiedStore.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)
      ContinuationAgreement actual store ((snapshotSequence output captured body).rename embedding)
        (nextRef :: actual) nextStore (body.rename embedding.lift) ∧
      (∀ {size value finalStore}, EvaluationSize size actual store
          ((snapshotSequence output captured body).rename embedding) value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: actual) nextStore
          (body.rename embedding.lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, lowered.type) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree embedding.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType lowered.type :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
        named.signature.key [] nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, lowered.type) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareScopePhysical.Physical whole named nextContext ((binder.id, lowered.type) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  obtain ⟨_node, parameters, resultType, statements, _found, _form, _rawType, _type, _requirements, _coercions, rfl⟩ :=
    captures.canonical
  let function := Dynamic.GeneralizedClosure.ofDirectLambda sourceContext (source named) copies binder
    initializer parameters resultType statements
  obtain ⟨retainedOrigin, nativeEq, _ghostEq, _metadataEq, namedMetadata, ⟨attachment⟩,
      descriptorSource, binderEq, _initializerEq⟩ :=
    CellAwareNamedDescriptor.of_capture site captures physical.selected record physical.carried
  let origin : GeneralizedLocalDescriptorOrigin.Origin whole.indexed function site.binding [] :=
    { retainedOrigin with
      native := physical.native
      carried := by simpa only [nativeEq] using retainedOrigin.carried }
  let current : CallableIndexedLambdaValues.Captures whole.indexed mapping world scope environment actual :=
    ⟨administrative, canonical, actualContext, embedding, environments,
      agrees, TypedLexicalWhile.environment_respects environments.runtime_hasTypes actualTyped agrees, actualTyped⟩
  have originalExtended : BinderExtends function.source.owner function.definitionContext function.binder nextContext := extended
  have originalOrdinary : function.source.inputs.any (fun input => decide (input.id = function.binder.id)) = false := ordinary
  let originalAllocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
      (initializedRequest function.source scope function.binder lowered.type) := allocation
  let originalAnnotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest function.source scope function.binder lowered.type) := annotation
  have sameOriginal : originalAnnotation.original = originalAllocation.expression := by
    simpa only [originalAnnotation, originalAllocation] using same
  have originalDeclarations : CompatibleExpressionReads.ScopeDeclarations function.source scope function.definitionContext := physical.declarations
  have originalLocals : Dynamic.EnvironmentAgrees before function.definitionContext.locals environment := locals
  have originalSnapshot : Dynamic.EnvironmentCopies function.source environment before function.captured snapshotHeap :=
    snapshot
  have originalRead := physical.read
  have originalReady : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location origin.native := ready
  obtain ⟨values, marker, copiedStore, copiedMap, copiedWorld, agreement, smaller, nextEnvironments, nextHeaps,
      nextLocals, nextAgrees, nextTyped, _nextReference, _nextRead, preserved, maps, worlds, ⟨suffix, storeEq⟩,
      located, transition⟩ :=
    CellAwareGeneralizedSnapshotPrefix.complete receipt descriptorSource site.bindingCaller.symm
      site.bindingInitializer.symm origin rfl namedMetadata attachment originalExtended originalOrdinary
      originalAllocation originalAnnotation sameOriginal copied producer (transitions bridge) bindings registered
      current originalDeclarations physical.ownership
      (CellAwareNamedDiagnosticIssuer.Named.initializer compiled issuer childFuel (childFuel + 1) scope initializer)
      nativeTyped heaps originalLocals physical.reference (by rfl) originalRead originalSnapshot allocated initial
      originalReady output body
  obtain ⟨located, frames⟩ := located
  have metadata := snapshot.metadata_extends.trans (Dynamic.HeapMetadataExtend.of_generalized_allocation allocated)
  have effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
      mapping world before store (copiedMap ++ [copiedStore.length + 2])
      (copiedWorld ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]) after
      (copiedStore ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker,
        .inRight .unit (SourceCoreLocalPolymorphism.ProductBundle.value values)]) := by
    rw [storeEq]
    exact CellAwareScopeAuthority.Effect.append
      (instances := GeneralizedLocalInstanceValues.model whole.indexed) store suffix metadata maps worlds
  have bindingId : site.binding.binder.id = binder.id := by
    simpa only [EmptySourceSubstitution.binder] using congrArg TypedBinder.id site.bindingMetadata
  have lexical : GeneralizedLocalBundleContexts.ContextExtension [] [] := ⟨by simp, by simp⟩
  have nextAuthority := CellAwareScopeAuthority.At.cons
    (.generalized site.bindingCaller bindingId lexical ⟨located⟩) (authority.transport effect)
  obtain ⟨reached, related⟩ := transition
  have nextAdmitted : Admission bridge nextContext reached :=
    ⟨(Dynamic.HeapWellTyped.iff_of_binderExtends originalExtended).mp
        ((admitted.heap.copy snapshot).allocateGeneralized functionTyped allocated),
      CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
        (bridge.pool initial) (bridge.pool reached) admitted.rows preserved⟩
  have fields : Dynamic.RuntimeContextFields function.definitionContext nextContext :=
    Dynamic.RuntimeContextFields.ofBinderExtends extended
  have requirements : nextContext.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements := extended.local_scheme_requirements_self
  have head : CellAwareScopePhysical.Entry whole named nextContext physical.location binder.id location
      (copiedMap ++ [copiedStore.length + 2]) _ after _ :=
    .generalized located site.bindingCaller bindingId lexical frames fields requirements
  let nextPhysical := (physical.transport effect preserved).cons extended
    (CellAwareNativeBodyCollectors.scope_generalized lowered.type physical.declarations declaration polymorphic extended)
    ((List.mem_filter.mp (declaration ▸ List.mem_singleton_self binder)).1)
    (.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) head
  exact ⟨values, marker, copiedStore, copiedMap, copiedWorld, agreement, smaller, nextEnvironments, nextHeaps,
    nextLocals, nextAgrees, nextTyped, preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical,
    rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedOrdinaryPrefix
/-! An ordinary initialized declaration allocates from the successful child's
actual post. Every earlier generalized descriptor, frame and lexical authority
survives, and the real continuation receives the newly bound Source cell. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedOrdinaryPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (initializedRequest sequence)
open GeneralizedLocalDescriptorHeap
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}

theorem complete {scope : SourceCoreLocalCell.Scope} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {lowered : SourceCoreBasic.LoweredExpr} {administrative actualContext : Core.Context}
    (mono : binder.scheme.quantified = [])
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
    (extended : BinderExtends (source named).owner context binder nextContext)
    (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
      (initializedRequest (source named) scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest (source named) scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap}
    {startStore store : Store} {sourceValue : Dynamic.Value} {value : Value} {location : Dynamic.Location}
    (initialized : Evaluates actual startStore (lowered.expression.rename embedding) (.inRight .word value) store)
    (represented : model.Represents mapping world binder.scheme.body sourceValue value lowered.type)
    (valueTyped : Dynamic.ValueHasType context before sourceValue binder.scheme.body)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world before store environment)
    (ready : producer.Ready initial physical.location physical.native)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (output : Ty) (body : Expr) :
    ∃ marker,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit value]
      let nextWorld := world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual startStore
        ((sequence output lowered.expression annotation.expression body).rename embedding)
        (nextRef :: value :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) ∧
      (∀ {size result finalStore}, EvaluationSize size actual startStore
        ((sequence output lowered.expression annotation.expression body).rename embedding) result finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: value :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) result finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, lowered.type) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) embedding).lift
        (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
        named.signature.key [] nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, lowered.type) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareScopePhysical.Physical whole named nextContext ((binder.id, lowered.type) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  obtain ⟨marker, _captures, _markerTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, _nextReference, _nextRead, preserved, reached, related⟩ :=
    CellAwareOrdinaryAllocation.allocate_initialized (ordinary_cells (ordinary := model) (instances := GeneralizedLocalInstanceValues.model whole.indexed))
      producer rfl registered mono extended ordinary allocation annotation same represented environments heaps locals agrees actualTyped
      physical.reference physical.read allocated initial ready
  have metadata := Dynamic.HeapMetadataExtend.of_allocation allocated
  have effect := CellAwareScopeAuthority.Effect.append
    (instances := GeneralizedLocalInstanceValues.model whole.indexed) store
    [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
      SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit value] metadata
    (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
    (show WorldExtends world (world ++ [whole.indexed.ancestry.layout.frame.type,
      allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩)
  have nextAuthority := CellAwareScopeAuthority.At.cons (id := binder.id)
    (.ordinary allocated.reads_new rfl) (authority.transport effect)
  have nextAdmitted := CallableIndexedOwnedAdmittedLexicalAllocation.after_allocation bridge initial reached admitted
    extended (.some valueTyped) allocated preserved
  have head : CellAwareScopePhysical.Entry whole named nextContext physical.location binder.id location
      (mapping ++ [store.length + 2])
      (world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]) after
      (store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit value]) :=
    .ordinary allocated.reads_new rfl
  let nextPhysical := (physical.transport effect preserved).cons extended
    (CompatibleMatchArmScopes.scope_bind lowered.type physical.declarations member extended) member
    (.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) head
  exact ⟨marker, CellAwareOrdinaryContinuation.agreement initialized allocationEval,
    fun completed => CellAwareOrdinaryContinuation.smaller initialized allocationEval completed,
    nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, preserved, effect,
    nextAuthority, reached, related, nextAdmitted, nextPhysical, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedOrdinaryPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedAbsentPrefix
/-! The actual absent-cell allocation extends the mixed lexical state without
evaluating an initializer. Its continuation preserves all prior generalized
descriptors, source bindings and the original physical frame. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedAbsentPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalControl (absentRequest)
open GeneralizedLocalDescriptorHeap
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}

theorem complete {scope : SourceCoreLocalCell.Scope} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {payload : Ty} {administrative actualContext : Core.Context}
    (mono : binder.scheme.quantified = [])
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
    (extended : BinderExtends (source named).owner context binder nextContext)
    (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
      (absentRequest (source named) scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
      (absentRequest (source named) scope binder payload))
    (same : annotation.original = allocation.expression)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap}
    {store : Store} {location : Dynamic.Location}
    (projection : projects binder.scheme.body payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world before store environment)
    (ready : producer.Ready initial physical.location physical.native)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after)
    (body : Expr) :
    ∃ marker,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inLeft payload .unit]
      let nextWorld := world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      ContinuationAgreement actual store
        ((Expr.letE annotation.expression body).rename embedding)
        (nextRef :: actual) nextStore
        (body.rename embedding.lift) ∧
      (∀ {size result finalStore}, EvaluationSize size actual store
        ((Expr.letE annotation.expression body).rename embedding) result finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: actual) nextStore
          (body.rename embedding.lift) result finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree embedding.lift
        (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType payload :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
        named.signature.key [] nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareScopePhysical.Physical whole named nextContext ((binder.id, payload) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  obtain ⟨marker, _captures, _markerTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, _nextReference, _nextRead, preserved, reached, related⟩ :=
    CellAwareAbsentAllocation.allocate_absent (ordinary_cells (ordinary := model) (instances := GeneralizedLocalInstanceValues.model whole.indexed))
      producer rfl registered mono extended ordinary projection allocation annotation same environments heaps locals agrees actualTyped
      physical.reference physical.read allocated initial ready
  have metadata := Dynamic.HeapMetadataExtend.of_allocation allocated
  have effect := CellAwareScopeAuthority.Effect.append
    (instances := GeneralizedLocalInstanceValues.model whole.indexed) store
    [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
      SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inLeft payload .unit] metadata
    (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
    (show WorldExtends world (world ++ [whole.indexed.ancestry.layout.frame.type,
      allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩)
  have nextAuthority := CellAwareScopeAuthority.At.cons (id := binder.id)
    (.ordinary allocated.reads_new rfl) (authority.transport effect)
  have nextAdmitted := CallableIndexedOwnedAdmittedLexicalAllocation.after_allocation bridge initial reached admitted
    extended (.none _) allocated preserved
  have head : CellAwareScopePhysical.Entry whole named nextContext physical.location binder.id location
      (mapping ++ [store.length + 2])
      (world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType payload]) after
      (store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inLeft payload .unit]) :=
    .ordinary allocated.reads_new rfl
  let nextPhysical := (physical.transport effect preserved).cons extended
    (CompatibleMatchArmScopes.scope_bind payload physical.declarations member extended) member
    (.cellRef (OptionalCell.cellType payload) (store.length + 2)) head
  exact ⟨marker, (by simpa only [Expr.rename] using ContinuationAgreement.letE (body := body.rename embedding.lift) allocationEval),
    (fun completed => by simpa only [Expr.rename] using completed.let_body allocationEval),
    nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, preserved, effect,
    nextAuthority, reached, related, nextAdmitted, nextPhysical, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedAbsentPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallPorts
/-! Every indirect head obtains its callsite from the actual named compiler
policy and its sidecar from the actual named invocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallPorts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : Compilation compiled.indexed named diagnostics code)
  {rootFuel fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt (namedPolicy generation rootFuel)
    (namedLowerBody generation) fuel (context compiled.indexed named)
    source scope id callee ids metadata reasonAt lowered)

include compiler in
theorem read_policy :
    (namedPolicy generation rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id := by
  have viewed : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed named).plan compiled.indexed.base.locals named.signature.key none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, compiler.found, compiler.originalForm]
  simp only [namedPolicy, viewed, bind, Except.bind]
  rfl

theorem callable_policy :
    (namedPolicy generation rootFuel).callables = SourceCoreGeneralFunctions.callablePolicy
      (some compiled.indexed.ancestry.graph.inputs.callable) [] := by
  change SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [] = _
  rw [compiled.indexed.ancestry.graph.inputs.callableSelected]

theorem function_type : (namedPolicy generation rootFuel).callables.functionType = CallableContract.functionType := by
  rw [callable_policy generation]
  rfl

structure Authority (named : SourceCoreGeneralFunctions.Function) (invocation : Staging.Recursive.Scope) where
  sidecar : SourceCoreStageContracts.Sidecar
  caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan named.signature.key = .ok sidecar
  view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source invocation.source
  guardFrame : invocation.guards = CallableLedger.frame sidecar
  unique : NodeOccurrencesUnique sidecar.source

theorem port {invocation : Staging.Recursive.Scope}
    (authority : Authority (compiled := compiled) named invocation)
    (sourceEq : invocation.source = source)
    (parent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
    (calleeReceipt : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      source scope callee reasonAt compiler.calleeCode) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
      (compiled := compiled) (invocation := invocation) compiler) := by
  obtain ⟨prepared⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.prepared
    compiler (read_policy generation compiler) [] (callable_policy generation)
  refine ⟨{ prepared := prepared
            sidecar := authority.sidecar
            caller := ?_
            view := ?_
            guardFrame := authority.guardFrame
            originalUnique := authority.unique
            sourceParent := parent
            calleeNode := calleeReceipt.observations.original
            calleeFound := calleeReceipt.observations.originalFound }⟩
  · rw [prepared.caller]
    exact authority.caller
  · simpa only [sourceEq] using authority.view

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallPorts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionTreeBounds
/-! Structural recursion on the genuine named compiler tree fills every child
expression. Generalized reads and materialized application use their concrete
internal leaves; no whole-expression meaning is stored in a certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeExpressionBounds
open CallableIndexedNamedGeneration (Compilation)
open GeneralizedLocalInitializerCompilation (namedPolicy)
open CellAwareNamedExpressionCertificates (Tree)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : Compilation compiled.indexed named diagnostics code)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  (authority : CellAwareNamedCallPorts.Authority (compiled := compiled) named invocation)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) stages)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functionModel identities)
  (functionTypes : FunctionRuntimeViews functionModel)
  (indices : CellAwareNamedIndexDiagnostics.Ready compiled invocation.source reasonAt)
  {readFaults : FunctionCalls.FaultRep}
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead compiled.indexed.fuel (.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, readFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, readFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private def Three (scope : SourceCoreLocalCell.Scope) (test yes no : ExpressionId)
    (a b c : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = test ∧ code = a) ∨ (child = yes ∧ code = b) ∨ (child = no ∧ code = c))

omit positive in
private theorem product_values : CallableIndexedOwnedPreparedStagedPairBounds.ProductValues (model := valueModel) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include positive bridge profile receiver stagePrepared authority selectedBodies runtime covers unique
  extension sameLedger runtimeLedger faithful functionLeaves functionTypes indices uninitialized semantic in
theorem preserves_tree_selected
    (builtins : (CallableIndexedBuiltinValues.model compiled.indexed profile).Includes functionModel)
    (generalized : ∀ size, CellAwareScopeGeneralizedReadBounds.PreservesAt bridge context valueModel named stages invocation callFaults size)
    (applications : ∀ size, CellAwareScopeApplicationBounds.PreservesAt bridge context valueModel named stages invocation callFaults size)
    {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree generation rootFuel invocation.source context reasonAt scope id lowered)
    (size : Nat) :
    PreservesAt bridge context valueModel named stages invocation (Point scope id lowered) callFaults size := by
  induction tree generalizing size with
  | plain receipt =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeReadProductBounds.preserves bridge functionModel extension
      GeneralizedLocalDescriptorHeap.ordinary_cells sameLedger runtimeLedger callFaults uninitialized semantic unique size receipt
  | builtin receipt =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeBuiltinValueBounds.preserves bridge functionModel profile builtins callFaults unique size ⟨receipt⟩
  | generalized receipt recipe =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeGeneralizedReadProjection.preserves bridge context valueModel named stages invocation callFaults
      (generalized size) ⟨reasonAt, receipt, ⟨recipe⟩⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    have children : PreservesBelow bridge context valueModel named stages invocation (Point scope inner lowered) callFaults size :=
      fun childSize _smaller => ih childSize
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeGroupBounds.group_preserves bridge unique size children size (Nat.le_refl _)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    have children : PreservesBelow bridge context valueModel named stages invocation
        (Two scope left right first second) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopePairBounds.pair_preserves bridge unique (product_values profile) size children size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType
      firstTree secondTree firstIH secondIH =>
    have children : PreservesBelow bridge context valueModel named stages invocation
        (Two scope base key first second) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact firstIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact secondIH childSize ⟨rfl, rfl, rfl⟩
    obtain ⟨port⟩ := indices header
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeIndexBounds.preserves_selected bridge functionModel callFaults unique selectedBodies runtime covers
      header keyFound form sourceType faithful functionLeaves functionTypes
      ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩
      (port.missing receiver functionModel keyFound form) size children ⟨rfl, rfl, rfl⟩
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    have children : PreservesBelow bridge context valueModel named stages invocation
        (Point scope operand ⟨core.operandType, childCode⟩) callFaults size :=
      fun childSize _smaller => ih childSize
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeOperatorBounds.preserves_at_selected bridge functionModel size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.unary metadata form childFound inputType outputType operatorProfile ⟨rfl, rfl, rfl⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH rightIH =>
    have children : PreservesBelow bridge context valueModel named stages invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeOperatorBounds.preserves_at_selected bridge functionModel size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.binary metadata form leftFound rightFound leftType rightType outputType operatorProfile
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    have children : PreservesBelow bridge context valueModel named stages invocation
        (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; exact testIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; exact yesIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; exact noIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeOperatorBounds.preserves_at_selected bridge functionModel size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.conditional metadata form testFound yesFound noFound testType yesType noType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩)
  | @call id callee ids metadata fuel lowered types compiler calleeReceipt calleeRecipe parent sequence children ih =>
    have childMeaning : PreservesBelow bridge context valueModel named stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) callFaults size := by
      intro childSize _smaller current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member childSize ⟨rfl, rfl, rfl⟩
    obtain ⟨port⟩ := CellAwareNamedCallPorts.port generation compiler authority rfl parent calleeReceipt
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeIndirectHeadBounds.preserves_selected bridge receiver stagePrepared rfl profile
      selectedBodies runtime covers unique (CellAwareNamedCallPorts.function_type generation)
      compiler port calleeReceipt calleeRecipe sequence size
      (fun childSize _smaller => generalized childSize) childMeaning
      (fun childSize _smaller => applications childSize) ⟨rfl, rfl, rfl⟩

include positive bridge profile receiver stagePrepared authority selectedBodies runtime covers unique
  extension sameLedger runtimeLedger faithful functionLeaves functionTypes indices uninitialized semantic in
theorem reflects_tree_selected
    (builtins : (CallableIndexedBuiltinValues.model compiled.indexed profile).Includes functionModel)
    (generalized : ∀ size, CellAwareScopeGeneralizedReadBounds.ReflectsAt bridge context valueModel named stages invocation callFaults size)
    (applications : ∀ size, CellAwareScopeApplicationBounds.ReflectsAt bridge context valueModel named stages invocation callFaults size)
    {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree generation rootFuel invocation.source context reasonAt scope id lowered)
    (size : Nat) :
    ReflectsAt bridge context valueModel named stages invocation (Point scope id lowered) callFaults size := by
  induction tree generalizing size with
  | plain receipt =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeReadProductBounds.reflects bridge functionModel extension
      GeneralizedLocalDescriptorHeap.ordinary_cells sameLedger runtimeLedger callFaults uninitialized semantic unique size receipt
  | builtin receipt =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeBuiltinValueBounds.reflects bridge functionModel profile builtins callFaults size ⟨receipt⟩
  | generalized receipt recipe =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeGeneralizedReadProjection.reflects bridge context valueModel named stages invocation callFaults
      (generalized size) ⟨reasonAt, receipt, ⟨recipe⟩⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeGroupBounds.group_reflects bridge unique size (ih size)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    have children : ReflectsBelow bridge context valueModel named stages invocation
        (Two scope left right first second) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopePairBounds.pair_reflects bridge unique (product_values profile) size children size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType
      firstTree secondTree firstIH secondIH =>
    have children : ReflectsBelow bridge context valueModel named stages invocation
        (Two scope base key first second) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact firstIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact secondIH childSize ⟨rfl, rfl, rfl⟩
    obtain ⟨port⟩ := indices header
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeIndexBounds.reflects_selected bridge functionModel callFaults unique selectedBodies runtime covers
      header keyFound form sourceType faithful functionLeaves functionTypes
      ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩
      (port.missing receiver functionModel keyFound form) size children ⟨rfl, rfl, rfl⟩
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    have children : ReflectsBelow bridge context valueModel named stages invocation
        (Point scope operand ⟨core.operandType, childCode⟩) callFaults size :=
      fun childSize _smaller => ih childSize
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeOperatorBounds.reflects_at_selected bridge functionModel size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.unary metadata form childFound inputType outputType operatorProfile ⟨rfl, rfl, rfl⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH rightIH =>
    have children : ReflectsBelow bridge context valueModel named stages invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeOperatorBounds.reflects_at_selected bridge functionModel size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.binary metadata form leftFound rightFound leftType rightType outputType operatorProfile
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    have children : ReflectsBelow bridge context valueModel named stages invocation
        (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; exact testIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; exact yesIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; exact noIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeOperatorBounds.reflects_at_selected bridge functionModel size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.conditional metadata form testFound yesFound noFound testType yesType noType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩)
  | @call id callee ids metadata fuel lowered types compiler calleeReceipt calleeRecipe parent sequence children ih =>
    have childMeaning : ReflectsBelow bridge context valueModel named stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) callFaults size := by
      intro childSize _smaller current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member childSize ⟨rfl, rfl, rfl⟩
    obtain ⟨port⟩ := CellAwareNamedCallPorts.port generation compiler authority rfl parent calleeReceipt
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeIndirectHeadBounds.reflects_selected bridge receiver stagePrepared rfl profile
      selectedBodies runtime covers unique (CellAwareNamedCallPorts.function_type generation)
      compiler port calleeReceipt calleeRecipe sequence size
      (fun childSize _smaller => generalized childSize) childMeaning
      (fun childSize _smaller => applications childSize) ⟨rfl, rfl, rfl⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include positive bridge profile receiver stagePrepared authority wellFormed runtime covers unique
  extension sameLedger runtimeLedger faithful functionLeaves functionTypes indices uninitialized semantic in
theorem preserves_tree
    (builtins : (CallableIndexedBuiltinValues.model compiled.indexed profile).Includes functionModel)
    (generalized : ∀ size, CellAwareScopeGeneralizedReadBounds.PreservesAt bridge context valueModel named stages invocation callFaults size)
    (applications : ∀ size, CellAwareScopeApplicationBounds.PreservesAt bridge context valueModel named stages invocation callFaults size)
    {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree generation rootFuel invocation.source context reasonAt scope id lowered)
    (size : Nat) :
    PreservesAt bridge context valueModel named stages invocation (Point scope id lowered) callFaults size := by
  apply preserves_tree_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (positive := positive) (bridge := bridge) (profile := profile) (receiver := receiver) (stagePrepared := stagePrepared) (authority := authority) (runtime := runtime) (covers := covers) (unique := unique) (extension := extension) (sameLedger := sameLedger) (runtimeLedger := runtimeLedger) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes) (indices := indices) (uninitialized := uninitialized) (semantic := semantic) <;> assumption

include positive bridge profile receiver stagePrepared authority wellFormed runtime covers unique
  extension sameLedger runtimeLedger faithful functionLeaves functionTypes indices uninitialized semantic in
theorem reflects_tree
    (builtins : (CallableIndexedBuiltinValues.model compiled.indexed profile).Includes functionModel)
    (generalized : ∀ size, CellAwareScopeGeneralizedReadBounds.ReflectsAt bridge context valueModel named stages invocation callFaults size)
    (applications : ∀ size, CellAwareScopeApplicationBounds.ReflectsAt bridge context valueModel named stages invocation callFaults size)
    {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree generation rootFuel invocation.source context reasonAt scope id lowered)
    (size : Nat) :
    ReflectsAt bridge context valueModel named stages invocation (Point scope id lowered) callFaults size := by
  apply reflects_tree_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (positive := positive) (bridge := bridge) (profile := profile) (receiver := receiver) (stagePrepared := stagePrepared) (authority := authority) (runtime := runtime) (covers := covers) (unique := unique) (extension := extension) (sameLedger := sameLedger) (runtimeLedger := runtimeLedger) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes) (indices := indices) (uninitialized := uninitialized) (semantic := semantic) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedReadBounds
/-! Actual named generalized reads implement the scoped callee port. Both
execution directions use the original source dictionary and the actual stored
row. The same read-time frame and unchanged caller state remain available to
the subsequent ordered argument and application proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedReadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {named : SourceCoreGeneralFunctions.Function}
  {bodyRegistry rawRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions

private theorem represented_of_typed
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap}
    {function : Dynamic.Closure} {native : Core.Value} {bindings parameter result}
    (member : GeneralizedLocalMaterializedAssociation.Association compiled mapping world function native bindings parameter result)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (framed : member.AtFrame owner.key.frameLocation)
    {sourceType : TypeSystem.Ty} (typed : Dynamic.ValueHasType context heap (.closure function) sourceType) :
    ValueRep compiled.compatible.checked rawRegistry functions mapping world sourceType (.closure function) native
      (CallableContract.functionType parameter result) := by
  induction sourceType with
  | function parameter result _ _ =>
    cases typed
    exact .function (.generalized member owner framed)
  | comptime inner ih =>
    cases typed with
    | comptime innerTyped => exact .compatible (actual := inner) rfl (ih innerTyped)
  | _ => cases typed

include profile in
/-- The reached Source instantiation produces the actual indexed view while
retaining the physical frame required by indirect application. -/
theorem preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (requirementsUnique : RequirementIdsUnique context)
    (covers : invocation.evidence.Covers context)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (size : Nat) :
    CellAwareScopeGeneralizedReadBounds.PreservesAt bridge context model named registry invocation faults size := by
  intro scope id reasonAt lowered certificate recipe node found sourceTyped
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted _authority physical owner ownerLocation trace
  have nodeEq := Option.some.inj (certificate.observations.originalFound.symm.trans found)
  cases nodeEq
  obtain ⟨reached⟩ := GeneralizedLocalScopedReadFacts.resolve certificate recipe physical locals
  have originalEq := Option.some.inj (recipe.observations.originalFound.symm.trans certificate.observations.originalFound)
  have binderEq := GeneralizedLocalScopedReadFacts.binder certificate recipe
  have originalForm : certificate.observations.original.form =
      .reference recipe.observations.name (.local certificate.read.binder) := by
    simpa only [originalEq, binderEq] using recipe.observations.originalForm
  obtain ⟨owned, substitution, produced, instantiation, sameOutcome, sameHeap⟩ :=
    GeneralizedLocalSourceRead.invert unique certificate.observations.originalFound originalForm
      certificate.observations.originalCoercions reached.lookup reached.located.sourceRead reached.located.descriptor
      requirementsUnique covers trace
  cases sameHeap
  cases sameOutcome
  have descriptorTyped := ((admitted.heap _ reached.located.sourceRead.member).generalized_inv reached.located.descriptor).2
  have nodeType := GeneralizedLocalSourceRead.raw_type unique certificate.observations.originalFound
    certificate.observations.originalCoercions sourceTyped
  have sourceValueTyped := descriptorTyped.instantiateHasType
    (reached.fields.signatures ▸ catalog) reached.fields covers instantiation
  rw [nodeType] at sourceValueTyped
  have normalized := Option.some.inj (certificate.read.nodeFound.symm.trans certificate.observations.found)
  have rawType : certificate.observations.original.rawType = certificate.read.node.rawType := by
    rw [normalized, certificate.observations.rawType]
  obtain ⟨material, view, _materialFrame, viewFrame, nativeType, evaluated, member, atFrame⟩ :=
    GeneralizedLocalNamedReadFormation.preserves certificate recipe reached.located reached.frames
      reached.caller reached.binder reached.contextExtension environments reached.lookup agrees
      descriptorTyped.code.graph.nodeOccurrencesUnique instantiation reached.scheme rawType profile
      physical.carried rfl (agrees physical.reference) physical.read actualTyped
  refine ⟨.inRight .word view.native, store, mapping, world, evaluated, ?_, ?_, heaps,
    .refl _, .refl _, .refl _ _, Dynamic.HeapMetadataExtend.refl _,
    CellAwareScopeAuthority.Effect.refl _ _ _ _, initial, callerProtocol.refl initial, ?_⟩
  · rw [nativeType]
    exact .value (represented_of_typed profile member owner (by simpa only [ownerLocation] using atFrame) sourceValueTyped)
  · intro value same
    cases same
    exact ⟨_, _, _, _, _, rfl, rfl, member, by simpa only [ownerLocation] using atFrame⟩
  · exact ⟨admitted.rows, by intro value same; cases same; exact ⟨sourceValueTyped, admitted.heap⟩⟩

include profile in
/-- Native completion reconstructs the actual Source dictionary and retained
closure. Determinism compares only the two executions of this same emitted
read; it does not identify different creation or call histories. -/
theorem reflects
    (unique : NodeOccurrencesUnique invocation.source)
    (requirementsUnique : RequirementIdsUnique context)
    (covers : invocation.evidence.Covers context)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (size : Nat) :
    CellAwareScopeGeneralizedReadBounds.ReflectsAt bridge context model named registry invocation faults size := by
  intro scope id reasonAt lowered certificate recipe node found sourceTyped
    mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerLocation completed
  have nodeEq := Option.some.inj (certificate.observations.originalFound.symm.trans found)
  cases nodeEq
  obtain ⟨reached⟩ := GeneralizedLocalScopedReadFacts.resolve certificate recipe physical locals
  have originalEq := Option.some.inj (recipe.observations.originalFound.symm.trans certificate.observations.originalFound)
  have binderEq := GeneralizedLocalScopedReadFacts.binder certificate recipe
  have originalForm : certificate.observations.original.form =
      .reference recipe.observations.name (.local certificate.read.binder) := by
    simpa only [originalEq, binderEq] using recipe.observations.originalForm
  obtain ⟨owned, substitution, produced, sourceSize, _instantiation, trace⟩ :=
    GeneralizedLocalSourceRead.trace_of_typed (program := Program.ofChecked compiled.sourceProgram) (registry := registry)
      unique certificate.observations.originalFound originalForm certificate.observations.originalCoercions
      sourceTyped locals reached.lookup reached.located.sourceRead reached.located.descriptor reached.fields
      reached.requirements reached.matched covers
  obtain ⟨native, nativeStore, finalMap, finalWorld, evaluated, represented, strong, finalHeaps,
      maps, worlds, frame, metadata, effect, final, related, post⟩ :=
    preserves bridge profile unique requirementsUnique covers catalog sourceSize certificate recipe
      certificate.observations.originalFound sourceTyped environments heaps locals agrees actualTyped
      initial admitted authority physical owner ownerLocation trace
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed.sound
  exact ⟨sourceSize, _, before, finalMap, finalWorld, trace, represented, strong, finalHeaps,
    maps, worlds, frame, metadata, effect, final, related, post⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedReadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedApplicationBounds
/-! The scoped call port is discharged from the actual materialized compiler,
Source closure frame and issued public diagnostics. No body execution law is
supplied by its consumer. The reached caller retains the restored owned pool. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open GeneralizedLocalMaterializedAssociation
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {named : SourceCoreGeneralFunctions.Function}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  {invocation : Staging.Recursive.Scope}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "receivedFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "base" => CallableIndexedOwnedBodyRestorationAdmission.bridge

private theorem post_at {index : ProtectedStateTransition.Index} {type : TypeSystem.Ty}
    {outcome : Staging.Recursive.Outcome} (returned : callerProtocol.State index)
    (pool : State headers keys index) (same : bridge.pool returned = pool)
    (post : PostAdmission base context type outcome pool) :
    PostAdmission bridge context type outcome returned := by
  cases outcome with
  | value value => exact ⟨same ▸ post.rows, post.successful⟩
  | fault failure => cases failure with
    | semantic reason => exact ⟨same ▸ post.rows, post.successful⟩
    | stage _ _ _ =>
      change CallableIndexedOwnedIndirectExpressionHeads.StableRows (bridge.pool returned)
      rw [same]
      exact post

include receiver extension runtime selectedBodies in
/-- The original graded Source call determines both actual execution and its
public result, with no new runtime or body assumptions. -/
theorem preserves_selected (size : Nat) :
    CellAwareScopeApplicationBounds.PreservesAt bridge context model named stages invocation receivedFaults size := by
  intro scope mapping world environment canonical before store function native bindings parameter result sources values
    association raw frame arguments heaps initial admitted _authority _physical owner _ownerFrame atFrame outcome after trace
  cases association with
  | viewed material view _typed =>
    obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
    obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, represented, finalHeaps, maps, worlds,
        preserved, metadata, effect, pool, related, post⟩ :=
      GeneralizedLocalApplicationMeaning.preserves (faults := receivedFaults) material view inputs functions extension owner (bridge.pool initial)
        atFrame frame raw admitted.rows runtime (selectedBodies) (material.body_uninitialized receiver)
        (fun _ _ proof => proof) arguments heaps trace
    obtain ⟨returned, samePool, returnedRelated⟩ := bridge.restore initial pool maps worlds preserved metadata related
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
      preserved, metadata, effect, returned, returnedRelated, post_at bridge returned pool samePool post⟩

include receiver extension runtime selectedBodies in
/-- Native completion selects the real child scope and reconstructs its
original Source call, retaining exactly the same returned caller. -/
theorem reflects_selected (size : Nat) :
    CellAwareScopeApplicationBounds.ReflectsAt bridge context model named stages invocation receivedFaults size := by
  intro scope mapping world environment canonical before store function native bindings parameter result sources values
    association raw frame arguments heaps initial admitted _authority _physical owner _ownerFrame atFrame value finalStore completed
  cases association with
  | viewed material view _typed =>
    obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
    obtain ⟨sidecar, _accepted, selected⟩ := material.scope_at
    obtain ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, represented, finalHeaps, maps, worlds,
        preserved, metadata, effect, pool, related, post⟩ :=
      GeneralizedLocalApplicationMeaning.reflects (faults := receivedFaults) (registry := stages) material view inputs functions extension owner (bridge.pool initial)
        atFrame frame raw admitted.rows runtime (selectedBodies) (material.body_uninitialized receiver)
        (fun _ _ proof => proof) arguments heaps (.anonymous selected) completed.sound
    obtain ⟨returned, samePool, returnedRelated⟩ := bridge.restore initial pool maps worlds preserved metadata related
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
      preserved, metadata, effect, returned, returnedRelated, post_at bridge returned pool samePool post⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension runtime wellFormed in
theorem preserves (size : Nat) :
    CellAwareScopeApplicationBounds.PreservesAt bridge context model named stages invocation receivedFaults size := by
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed)  <;> assumption

include receiver extension runtime wellFormed in
theorem reflects (size : Nat) :
    CellAwareScopeApplicationBounds.ReflectsAt bridge context model named stages invocation receivedFaults size := by
  apply reflects_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed)  <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionMeaning
/-! The actual finite named compiler certificate supplies complete expression
meaning. Ordinary reads, generalized instantiation and real application are
all discharged here; the body consumer receives no expression or call law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  (authority : CellAwareNamedCallPorts.Authority (compiled := compiled) named invocation)
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (issuer : CellAwareNamedDiagnosticIssuer.Named compiled.indexed named (diagnostics.reasonAt named.signature.key))
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (covers : invocation.evidence.Covers context)

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver extension authority sourceEq issuer record sameLedger runtime selectedBodies covers in
/-- Every accepted expression in the bounded compiler profile preserves its
original Source execution, including reached mixed cells and public failures. -/
theorem preserves_selected (size : Nat) :
    CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation
      (CellAwareNamedBodyProducer.Certificate generation context) callFaults size := by
  intro scope id lowered certificate node
  obtain ⟨rootFuel, tree⟩ := certificate
  rw [← sourceEq] at tree
  have catalog : SignatureCatalogWellFormed context.signatures := runtime.signatures.symm ▸ selectedBodies.signatures
  exact CellAwareNamedExpressionTreeBounds.preserves_tree_selected (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) generation bridge profile receiver
    (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled) authority selectedBodies runtime covers
    runtime.graph.nodeOccurrencesUnique extension sameLedger runtime.requirements
    (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
    (CellAwarePhysicalFunctionOrigins.observations profile) (CellAwarePhysicalFunctionOrigins.runtime_views profile)
    (CellAwareNamedIndexDiagnostics.ready issuer record sourceEq runtime.graph.nodeOccurrencesUnique)
    (fun _ _ _ read location => CellAwareNamedReadDiagnostics.uninitialized issuer record receiver sourceEq
      runtime.graph.nodeOccurrencesUnique read location)
    (fun _ _ proof => proof)
    (CellAwareBuiltinValueOrigins.included profile)
    (CellAwareNamedGeneralizedReadBounds.preserves bridge profile runtime.graph.nodeOccurrencesUnique
      runtime.requirements.idsUnique covers catalog)
    (CellAwareNamedGeneralizedApplicationBounds.preserves_selected bridge functions receiver extension runtime selectedBodies)
    tree size ⟨rfl, rfl, rfl⟩

include receiver extension authority sourceEq issuer record sameLedger runtime selectedBodies covers in
/-- Finite Core completion reconstructs the independent Source grade and the
same returned state through the actual accepted compiler tree. -/
theorem reflects_selected (size : Nat) :
    CellAwareScopeExpressionBounds.ReflectsAt bridge context model named stages invocation
      (CellAwareNamedBodyProducer.Certificate generation context) callFaults size := by
  intro scope id lowered certificate node
  obtain ⟨rootFuel, tree⟩ := certificate
  rw [← sourceEq] at tree
  have catalog : SignatureCatalogWellFormed context.signatures := runtime.signatures.symm ▸ selectedBodies.signatures
  exact CellAwareNamedExpressionTreeBounds.reflects_tree_selected (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) generation bridge profile receiver
    (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled) authority selectedBodies runtime covers
    runtime.graph.nodeOccurrencesUnique extension sameLedger runtime.requirements
    (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
    (CellAwarePhysicalFunctionOrigins.observations profile) (CellAwarePhysicalFunctionOrigins.runtime_views profile)
    (CellAwareNamedIndexDiagnostics.ready issuer record sourceEq runtime.graph.nodeOccurrencesUnique)
    (fun _ _ _ read location => CellAwareNamedReadDiagnostics.uninitialized issuer record receiver sourceEq
      runtime.graph.nodeOccurrencesUnique read location)
    (fun _ _ proof => proof)
    (CellAwareBuiltinValueOrigins.included profile)
    (CellAwareNamedGeneralizedReadBounds.reflects bridge profile runtime.graph.nodeOccurrencesUnique
      runtime.requirements.idsUnique covers catalog)
    (CellAwareNamedGeneralizedApplicationBounds.reflects_selected bridge functions receiver extension runtime selectedBodies)
    tree size ⟨rfl, rfl, rfl⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension authority sourceEq issuer record sameLedger runtime wellFormed covers in
theorem preserves (size : Nat) :
    CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation
      (CellAwareNamedBodyProducer.Certificate generation context) callFaults size := by
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed)  <;> assumption

include receiver extension authority sourceEq issuer record sameLedger runtime wellFormed covers in
theorem reflects (size : Nat) :
    CellAwareScopeExpressionBounds.ReflectsAt bridge context model named stages invocation
      (CellAwareNamedBodyProducer.Certificate generation context) callFaults size := by
  apply reflects_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed)  <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedParameterEntry
/-! Real named parameter allocation initializes the mixed lexical authority.
The named seed is retained explicitly from the compiler hook, and every Source
binder and marked native cell comes from the actual parameter prefix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedParameterEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion CallableIndexedParameterMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedAdmittedBodyEntries

private theorem monomorphic_context {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner context parameters types final)
    (initial : ∀ id scheme, (id, scheme) ∈ context.locals → scheme.quantified = []) :
    ∀ id scheme, (id, scheme) ∈ final.locals → scheme.quantified = [] := by
  induction extended with
  | nil => exact initial
  | @cons context binder next rest types final payload mono head tail ih =>
    apply ih
    cases head
    intro id scheme member
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp only [mono, TypeSystem.Scheme.mono]
    · exact initial id scheme member

private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type definitions) :
    DataHeap.EnvRepresents catalog mapping world (type :: administrative) scope environment
      (Environment.insertAt canonical scope.length value) definitions := by
  induction related with
  | nil suffixTyped => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed suffixTyped)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions}

/-- This is the actual prefix result, before any body execution or completion. -/
theorem parameters_selected
    (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (sameGlobals : header.globals = compiled.indexed.base.globals.length)
    (sourceTyping : SelectedCompilationNamedSourceTyping.Certified header)
    (empty : header.function.context.locals = [])
    (ownership : LocalIdentityOwnership header.function.source)
    (native : NativeFrame) (id : Word)
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some id)
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      native (.named id) (some (CallableIndexedNamedGeneration.state header.named)))
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {administrative actualContext : Core.Context} {canonical actual : Environment} {embedding : Renaming}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative [] [] canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
      mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (agrees : EnvironmentsAgree embedding (DataPatternValues.packValues payloads :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (location : Core.Location)
    (reference : canonical[compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : location ∉ mapping)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      (protocol headers keys) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
    (initial : State headers keys ⟨[], mapping, world, heap, store, canonical⟩)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer location native) :
    ∃ environment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] heap header.function.parameters arguments environment finalHeap ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        environment finalCanonical compiled.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld finalHeap finalStore ∧
      SourceReceipt program header.function header.context environment finalHeap ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (CellAwareParameterTyped.prefixContext header.bindings actualContext)
        compiled.indexed.layouts.definitions ∧
      ContinuationAgreement actual store (header.parameterCode.rename embedding)
        finalActual finalStore (header.body.rename finalEmbedding) ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world heap store finalMap finalWorld finalHeap finalStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) header.named.signature.key []
        finalMap finalWorld finalHeap finalStore environment ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        Relates initial reached ∧
      ∃ physical : CellAwareScopePhysical.Physical compiled header.named header.context
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          finalCanonical finalMap finalWorld finalHeap finalStore environment,
        physical.location = location ∧ physical.native = native := by
  have accepted := header.acceptedPrefix
  rw [sameLayouts, sameGlobals] at accepted
  have tree := CallableIndexedParameterCertificates.of_accepted header.onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical
      (DataPatternValues.packValues payloads :: canonical) := by intro index value found; exact found
  have length : (header.bindings.map Prod.snd).length = payloads.length := by simpa using represented.length.2
  obtain ⟨environment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, finalEmbedding,
      allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, storeExtension,
      _lookups, actualLayout, spine, finalTyped, agreement, reached, related⟩ :=
    CellAwareParameterTyped.Stateful.prefix_typed tree GeneralizedLocalDescriptorHeap.ordinary_cells
      (protocol headers keys) producer rfl header.registered represented environments heaps
      sourceLayout agrees actualTyped (allTypes := header.bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds header.inputs)
      (by simpa using reference) read unmapped initial ready
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := insert_administrative finalEnvironments bundleTyped
  have scopeLength : (header.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = header.bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical header.bindings.length
      (DataPatternValues.packValues payloads) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  rw [← header.parameters] at allocated
  have sourceReceipt := SelectedCompilationNamedAdmission.parameter_source sourceTyping allocated heapTyped argumentsTyped
  have metadata := GenericLexicalContext.binders_metadata allocated
  have monomorphic := monomorphic_context header.extended (by intro id scheme member; rw [empty] at member; cases member)
  have authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      header.named.signature.key [] finalMap finalWorld finalHeap finalStore environment :=
    CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  have finalReference : finalLogical[header.bindings.length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location) := by
    rw [logicalEq]
    have index : header.bindings.length + 1 + compiled.indexed.base.globals.length =
        added.length + (compiled.indexed.base.globals.length + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  obtain ⟨stillUnmapped, stillRead⟩ := preservation location unmapped (List.getElem?_eq_some_iff.mp read).1
  have sourceEq : header.function.source = CallableIndexedNamedGeneration.source header.named := header.agreement.source
  let physical : CellAwareScopePhysical.Physical compiled header.named header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      finalLogical finalMap finalWorld finalHeap finalStore environment := CellAwareScopePhysical.Physical.of_monomorphic native id selected carried
    (by simpa only [← sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using (RecursiveNamedHeaderScopeDeclarations.header_scope (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header))
    (sourceEq ▸ ownership)
    (by simpa only [← sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using (CellAwareScopeDeclarations.header_scope (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header))
    location (by simpa using finalReference) (stillRead.trans read) stillUnmapped
    sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  obtain ⟨suffix, storeEq⟩ := storeExtension
  have effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world heap store finalMap finalWorld finalHeap finalStore := by
    rw [storeEq]
    exact .append store suffix metadata maps worlds
  refine ⟨environment, finalHeap, finalLogical, finalActual, finalStore, finalMap, finalWorld, finalEmbedding,
    allocated, (by simpa only [List.append_nil] using finalWithBundle), finalHeaps, sourceReceipt, actualLayout, finalTyped, agreement, preservation,
    effect, authority, reached, related, physical, rfl, rfl⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
theorem parameters
    (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (sameGlobals : header.globals = compiled.indexed.base.globals.length)
    (wellFormed : ProgramWellFormed program)
    (empty : header.function.context.locals = [])
    (ownership : LocalIdentityOwnership header.function.source)
    (native : NativeFrame) (id : Word)
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some id)
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      native (.named id) (some (CallableIndexedNamedGeneration.state header.named)))
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {administrative actualContext : Core.Context} {canonical actual : Environment} {embedding : Renaming}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative [] [] canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
      mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (agrees : EnvironmentsAgree embedding (DataPatternValues.packValues payloads :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (location : Core.Location)
    (reference : canonical[compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : location ∉ mapping)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      (protocol headers keys) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
    (initial : State headers keys ⟨[], mapping, world, heap, store, canonical⟩)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer location native) :
    ∃ environment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] heap header.function.parameters arguments environment finalHeap ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        environment finalCanonical compiled.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld finalHeap finalStore ∧
      SourceReceipt program header.function header.context environment finalHeap ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (CellAwareParameterTyped.prefixContext header.bindings actualContext)
        compiled.indexed.layouts.definitions ∧
      ContinuationAgreement actual store (header.parameterCode.rename embedding)
        finalActual finalStore (header.body.rename finalEmbedding) ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world heap store finalMap finalWorld finalHeap finalStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) header.named.signature.key []
        finalMap finalWorld finalHeap finalStore environment ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        Relates initial reached ∧
      ∃ physical : CellAwareScopePhysical.Physical compiled header.named header.context
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          finalCanonical finalMap finalWorld finalHeap finalStore environment,
        physical.location = location ∧ physical.native = native := by
  apply parameters_selected (sourceTyping := RecursiveNamedHeaderSourceTyping.certificate header wellFormed)  <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedParameterEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedEntry
/-! The actual named hook installs its authenticated seed and allocates the real
parameters in the mixed heap. Its continuation restores the saved physical
caller, while retaining every body write and marked allocation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedOwnedAdmittedBodyEntries
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : CallableIndexedOwnedFunctionValues.Header compiled program)
  (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}

/-- Source facts, actual compiler fields and the reached authority suffice.
There is no premise concerning this named body's execution. -/
theorem prepare_selected
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (sameGlobals : header.globals = compiled.indexed.base.globals.length)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      header.named.signature.key = .ok header.named.specialized)
    (sourceTyping : SelectedCompilationNamedSourceTyping.Certified header)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (stable : StableRows caller) :
    ∃ environment finalHeap finalCanonical finalActual finalContext finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment finalHeap ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        environment finalCanonical compiled.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld finalHeap finalStore ∧
      SourceReceipt program header.function header.context environment finalHeap ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext compiled.indexed.layouts.definitions ∧
      AdministrativePreserved mapping
        (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame compiled.indexed.ancestry.graph.table
            ((compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key)).getD Word.zero))))
        finalMap finalStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld finalHeap finalStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) header.named.signature.key []
        finalMap finalWorld finalHeap finalStore environment ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        Relates caller reached ∧ StableRows reached ∧
      ∃ physical : CellAwareScopePhysical.Physical compiled header.named header.context
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          finalCanonical finalMap finalWorld finalHeap finalStore environment,
        physical.location = owner.key.frameLocation ∧
      (∀ {value bodyStore}, Evaluates finalActual finalStore (header.body.rename finalEmbedding) value bodyStore →
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value
          (bodyStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current))) ∧
      (∀ {value bodyStore}, Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value bodyStore →
        ∃ reachedStore, Evaluates finalActual finalStore (header.body.rename finalEmbedding) value reachedStore ∧
          bodyStore = reachedStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current)) := by
  have originalTyping := sourceTyping
  obtain ⟨_facts, certified⟩ := originalTyping
  have empty : header.function.context.locals = [] := by
    rw [header.frame.context]
    exact certified.locals_empty
  have ownership : LocalIdentityOwnership header.function.source := by
    rw [header.frame.source]
    exact certified.local_identity_ownership
  let row := caller.rows owner.position
  have rowLocation : row.authority.frameLocation = owner.key.frameLocation := row.frame_eq
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [rowLocation] using row.authority.unmapped
  have current : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame row.authority.current) := by
    simpa only [rowLocation] using row.authority.frame.read
  obtain ⟨origin, index, selected, frame, emitted⟩ := CallableIndexedFormation.namedBody_receipt compiled.indexed.ancestry header.hook
  have history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named origin) (some (CallableIndexedNamedGeneration.state header.named)) := by
    rw [← frame]
    exact named_complete compiled.indexed.ancestry.graph (CallableIndexedNamedGeneration.seed compiled.indexed selected record)
  let installed := install caller owner.position (.stable history)
  have written : store.write? owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)) =
      some (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp current).1, rfl⟩
  have referenceTyped : world[owner.key.frameLocation]? = some compiled.indexed.ancestry.layout.frame.type := by
    simpa only [rowLocation] using row.authority.typed
  have installedHeaps := heaps.write_administrative
    (fun found => unmapped (List.mem_of_getElem? found)) referenceTyped
    (encode_runtime_typed world header.registered (.state index)) written
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) headers keys
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
  let initial : State headers keys ⟨[], mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), capture.canonical⟩ := installed
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer owner.key.frameLocation (.state index) := by
    intro index reached read
    exact CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position read history
  let actual := .unit :: encode compiled.indexed.ancestry.layout.frame row.authority.current ::
    DataPatternValues.packValues payloads :: capture.captured
  let embedding := Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift)
  have layout : EnvironmentsAgree embedding (DataPatternValues.packValues payloads :: capture.canonical) actual :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift capture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame row.authority.current)) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := compiled.indexed.layouts.definitions))
    (.cons (encode_runtime_typed world header.registered row.authority.current)
      (.cons (CallableIndexedParameters.Arguments.pack_typed represented) capture.typed))
  obtain ⟨environment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld, finalEmbedding,
      allocated, environments, finalHeaps, sourceReceipt, agrees, finalTyped, agreement, preserved,
      effect, lexical, reached, related, physical, locationEq, nativeEq⟩ :=
    CellAwareNamedParameterEntry.parameters_selected header sameLayouts sameGlobals sourceTyping empty ownership (.state index) origin selected history
      represented capture.environments installedHeaps heapTyped argumentsTyped layout actualTyped owner.key.frameLocation
      (by simpa only [sameGlobals] using capture.reference) (Store.write?_reads_written written) unmapped producer initial ready
  have finalStable := GeneralizedLocalParameterAdmission.after_parameters caller reached owner.position
    (fun i _ => stable i) history preserved
  have fullEffect := (CellAwareScopeAuthority.Effect.set_unmapped store
    (encode compiled.indexed.ancestry.layout.frame (.state index)) unmapped).trans effect
  have reference : (DataPatternValues.packValues payloads :: capture.captured)[capture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  have renamed : header.code.rename capture.embedding.lift = withFrame
      (.var (capture.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (header.parameterCode.rename capture.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have next : Evaluates (encode compiled.indexed.ancestry.layout.frame row.authority.current ::
      DataPatternValues.packValues payloads :: capture.captured) store
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) store := by
    rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
    exact CallableIndexedContextFrames.literal_evaluates _ _ _ _
  refine ⟨environment, finalHeap, finalCanonical, finalActual, _, finalStore, finalMap, finalWorld, finalEmbedding,
    allocated, environments, finalHeaps, sourceReceipt, agrees, finalTyped, ?_, fullEffect, lexical,
    reached, (install_related caller owner.position (.stable history)).trans related, finalStable,
    physical, locationEq, ?_, ?_⟩
  · simpa only [selected, Option.getD_some, frame] using preserved
  · intro value bodyStore evaluated
    have parameterRun := agreement.wrap evaluated
    simp only [embedding, GenericExpressionMeaning.rename_prefix] at parameterRun
    rw [renamed]
    exact CallableContextFrames.withFrame_evaluates (.var reference) current next parameterRun
  · intro value bodyStore evaluated
    rw [renamed] at evaluated
    obtain ⟨installedValue, nextStore, reachedStore, actualNext, parameterRun, restored⟩ :=
      CallableContextFrames.withFrame_reflects (.var reference) current evaluated
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic actualNext next
    refine ⟨reachedStore, agreement.unwrap ?_, restored⟩
    simpa only [embedding, GenericExpressionMeaning.rename_prefix] using parameterRun

/- Compatibility adapters for callers with a whole-program receipt. -/
theorem prepare
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (sameGlobals : header.globals = compiled.indexed.base.globals.length)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      header.named.signature.key = .ok header.named.specialized)
    (wellFormed : ProgramWellFormed program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (stable : StableRows caller) :
    ∃ environment finalHeap finalCanonical finalActual finalContext finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment finalHeap ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        environment finalCanonical compiled.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld finalHeap finalStore ∧
      SourceReceipt program header.function header.context environment finalHeap ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext compiled.indexed.layouts.definitions ∧
      AdministrativePreserved mapping
        (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame compiled.indexed.ancestry.graph.table
            ((compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key)).getD Word.zero))))
        finalMap finalStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld finalHeap finalStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) header.named.signature.key []
        finalMap finalWorld finalHeap finalStore environment ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        Relates caller reached ∧ StableRows reached ∧
      ∃ physical : CellAwareScopePhysical.Physical compiled header.named header.context
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          finalCanonical finalMap finalWorld finalHeap finalStore environment,
        physical.location = owner.key.frameLocation ∧
      (∀ {value bodyStore}, Evaluates finalActual finalStore (header.body.rename finalEmbedding) value bodyStore →
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value
          (bodyStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current))) ∧
      (∀ {value bodyStore}, Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value bodyStore →
        ∃ reachedStore, Evaluates finalActual finalStore (header.body.rename finalEmbedding) value reachedStore ∧
          bodyStore = reachedStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current)) := by
  apply prepare_selected (sourceTyping := RecursiveNamedHeaderSourceTyping.certificate header wellFormed)  <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSourceLifting
/-! The accepted finite expression tree lifts independent Source executions
through the actual mixed state and the selected call gates. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSourceLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareNamedExpressionCertificates (Tree)
open CellAwareScopeSourceLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  (authority : CellAwareNamedCallPorts.Authority (compiled := compiled) named invocation)
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (issuer : CellAwareNamedDiagnosticIssuer.Named compiled.indexed named (diagnostics.reasonAt named.signature.key))
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (covers : invocation.evidence.Covers context)

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics


private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private def Three (scope : SourceCoreLocalCell.Scope) (test yes no : ExpressionId)
    (a b c : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = test ∧ code = a) ∨ (child = yes ∧ code = b) ∨ (child = no ∧ code = c))

include receiver extension authority sourceEq issuer record sameLedger runtime selectedBodies covers in
private theorem preserve_tree {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree generation rootFuel invocation.source context (diagnostics.reasonAt named.signature.key) scope id lowered)
    (size : Nat) : CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation
      (Point scope id lowered) callFaults size := by
  intro current expression code point
  obtain ⟨rfl, rfl, rfl⟩ := point
  exact CellAwareNamedExpressionMeaning.preserves_selected generation bridge profile receiver extension authority sourceEq issuer
    record sameLedger runtime selectedBodies covers size ⟨rootFuel, by simpa only [sourceEq] using tree⟩

include receiver extension authority sourceEq issuer record sameLedger runtime selectedBodies covers in
theorem tree_selected {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : Tree generation rootFuel invocation.source context (diagnostics.reasonAt named.signature.key) scope id lowered)
    (size : Nat) : LiftsAt bridge context model named stages invocation (Point scope id lowered) size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  induction certificate generalizing size with
  | plain receipt =>
    intro current expression code point node found typed mapping world administrative environment canonical actual actualContext
      before store embedding outcome after environments heaps locals agrees actualTyped initial admitted scopeAuthority physical owner ownerFrame trace
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact .completed (CellAwareSourceReadProductLifting.exact_trace receipt unique trace.sound)
  | builtin receipt =>
    intro current expression code point node found typed mapping world administrative environment canonical actual actualContext
      before store embedding outcome after environments heaps locals agrees actualTyped initial admitted scopeAuthority physical owner ownerFrame trace
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact .completed (Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound receipt.found)
      (receipt.form.symm ▸ .reference _ _) receipt.coercions
      (by intro name binder impossible; rw [receipt.form] at impossible; cases impossible) trace.sound)
  | generalized receipt recipe =>
    intro current expression code point node found typed mapping world administrative environment canonical actual actualContext
      before store embedding outcome after environments heaps locals agrees actualTyped initial admitted scopeAuthority physical owner ownerFrame trace
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact .completed (CellAwareSourceReadLifting.read unique receipt.observations.originalFound
      receipt.observations.originalForm receipt.observations.originalCoercions trace.sound)
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeSourceProductLifting.group bridge model unique ih size
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    have children : ∀ size, LiftsAt bridge context model named stages invocation
        (Two scope left right first second) size := by
      intro childSize current expression code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    have preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation
        (Two scope left right first second) callFaults size := by
      intro childSize current expression code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left =>
        obtain ⟨rfl, rfl⟩ := left
        exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
          runtime selectedBodies covers leftTree childSize ⟨rfl, rfl, rfl⟩
      | inr right =>
        obtain ⟨rfl, rfl⟩ := right
        exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
          runtime selectedBodies covers rightTree childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeSourceProductLifting.pair bridge model unique children preservation size
      (.actual metadata form leftFound rightFound sourceType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType
      firstTree secondTree firstIH secondIH =>
    have children : ∀ childSize, childSize < size → LiftsAt bridge context model named stages invocation
        (Two scope base key first second) childSize := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact firstIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact secondIH childSize ⟨rfl, rfl, rfl⟩
    have preservation : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation
        (Two scope base key first second) callFaults childSize := by
      intro childSize current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first =>
        obtain ⟨rfl, rfl⟩ := first
        exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
          runtime selectedBodies covers firstTree childSize ⟨rfl, rfl, rfl⟩
      | inr second =>
        obtain ⟨rfl, rfl⟩ := second
        exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
          runtime selectedBodies covers secondTree childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeSourceIndexLifting.index bridge (reason := diagnostics.reasonAt named.signature.key expression) header keyFound form unique
      ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩ size children preservation ⟨rfl, rfl, rfl⟩
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeSourceOperatorLifting.unary bridge size
      (lowered := ⟨core.resultType, LocalPrimitiveResults.unary core childCode⟩)
      (childCode := ⟨core.operandType, childCode⟩)
      metadata form unique childFound (children := Point _ operand ⟨core.operandType, childCode⟩)
      ⟨rfl, rfl, rfl⟩ (fun childSize _smaller => ih childSize) ⟨rfl, rfl, rfl⟩
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH rightIH =>
    have children : ∀ childSize, childSize < size → LiftsAt bridge context model named stages invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩) childSize := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    have preservation : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩) callFaults childSize := by
      intro childSize current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first =>
        obtain ⟨rfl, rfl⟩ := first
        exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
          runtime selectedBodies covers leftTree childSize ⟨rfl, rfl, rfl⟩
      | inr second =>
        obtain ⟨rfl, rfl⟩ := second
        exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
          runtime selectedBodies covers rightTree childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeSourceOperatorLifting.binary bridge size
      (lowered := ⟨mode.resultType operator, mode.binary operator leftCode rightCode⟩)
      (leftCode := ⟨mode.operandType operator, leftCode⟩) (rightCode := ⟨mode.operandType operator, rightCode⟩)
      metadata form unique leftFound rightFound
      ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩ children preservation ⟨rfl, rfl, rfl⟩
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    have children : ∀ childSize, childSize < size → LiftsAt bridge context model named stages invocation
        (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) childSize := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; exact testIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; exact yesIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; exact noIH childSize ⟨rfl, rfl, rfl⟩
    have preservation : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation
        (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) callFaults childSize := by
      intro childSize current child code point
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test
        exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
          runtime selectedBodies covers testTree childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes
        exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
          runtime selectedBodies covers yesTree childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no
        exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
          runtime selectedBodies covers noTree childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeSourceConditionalLifting.conditional bridge functions size
      (lowered := ⟨type, LocalControl.choose type testCode yesCode noCode⟩)
      (conditionCode := ⟨.bool, testCode⟩) (thenCode := ⟨type, yesCode⟩) (elseCode := ⟨type, noCode⟩)
      metadata form unique rfl
      ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩
      children preservation ⟨rfl, rfl, rfl⟩
  | @call id callee ids metadata fuel lowered types compiler calleeReceipt calleeRecipe parent sequence children ih =>
    have childLift : ∀ childSize, childSize < size → LiftsAt bridge context model named stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) childSize := by
      intro childSize _smaller current expression code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih expression code member childSize ⟨rfl, rfl, rfl⟩
    have preservation : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) callFaults childSize := by
      intro childSize current expression code entry
      obtain ⟨rfl, member⟩ := entry
      exact preserve_tree generation bridge profile receiver extension authority sourceEq issuer record sameLedger
        runtime selectedBodies covers (children expression code member) childSize ⟨rfl, rfl, rfl⟩
    obtain ⟨port⟩ := CellAwareNamedCallPorts.port generation compiler authority rfl parent calleeReceipt
    have catalog : SignatureCatalogWellFormed context.signatures := runtime.signatures.symm ▸ selectedBodies.signatures
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeSourceIndirectLifting.indirect_selected (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) bridge profile compiler port runtime unique selectedBodies covers size
      calleeReceipt calleeRecipe sequence childLift preservation
      (CellAwareNamedGeneralizedReadBounds.preserves bridge profile unique runtime.requirements.idsUnique covers catalog) ⟨rfl, rfl, rfl⟩

include receiver extension authority sourceEq issuer record sameLedger runtime selectedBodies covers in
theorem lifts_selected (size : Nat) : LiftsAt bridge context model named stages invocation
    (CellAwareNamedBodyProducer.Certificate generation context) size := by
  intro scope id lowered certificate
  obtain ⟨rootFuel, actual⟩ := certificate
  rw [← sourceEq] at actual
  exact tree_selected generation bridge profile receiver extension authority sourceEq issuer record sameLedger runtime
    selectedBodies covers actual size ⟨rfl, rfl, rfl⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension authority sourceEq issuer record sameLedger runtime wellFormed covers in
theorem tree {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : Tree generation rootFuel invocation.source context (diagnostics.reasonAt named.signature.key) scope id lowered)
    (size : Nat) : LiftsAt bridge context model named stages invocation (Point scope id lowered) size := by
  apply tree_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (receiver := receiver) (extension := extension) (authority := authority) (sourceEq := sourceEq) (issuer := issuer) (record := record) (sameLedger := sameLedger) (runtime := runtime) (covers := covers) <;> assumption

include receiver extension authority sourceEq issuer record sameLedger runtime wellFormed covers in
theorem lifts (size : Nat) : LiftsAt bridge context model named stages invocation
    (CellAwareNamedBodyProducer.Certificate generation context) size := by
  apply lifts_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (receiver := receiver) (extension := extension) (authority := authority) (sourceEq := sourceEq) (issuer := issuer) (record := record) (sameLedger := sameLedger) (runtime := runtime) (covers := covers) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSourceLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedAssignmentDiagnostics
/-! The actual named specialization and its issued place table provide reached
assignment diagnostics in the receiving public registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedAssignmentDiagnostics
open Core Frontend SourceInference CompatiblePayload
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}

/-- Source identity and diagnostic token identity come from the original
specialization and actual compiler issuance. -/
theorem source_port
    (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
    (unique : NodeOccurrencesUnique (source named))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics) :
    Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort whole (source named)
      (fun site root => diagnostics.placeReason named.signature.key site root none)
      (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))) := by
  obtain ⟨issuer, present, _sameBase, samePlaces⟩ := issued
  refine ⟨⟨named.signature.key, named.specialized, record, rfl, unique, issuer, present, ?_, ?_⟩⟩
  · intro site root
    simp only [SourceCoreDataPlaceFaultSites.Program.placeReason, samePlaces]
  · intro site root raw
    simp only [SourceCoreDataPlaceFaultSites.Program.placeReason, samePlaces]

universe u v

theorem ready
    (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
    (unique : NodeOccurrencesUnique (source named))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
      completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {ambient : AmbientDefinitions whole.compatible.checked.catalog.definitions}
    (functions : FunctionModel whole.compatible.checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u,v} Records) :
    PreparedAssignmentReachedDiagnostics.Ready (values := .initial whole.compatible.checked)
      functions protocol (source named)
      (fun site root => diagnostics.placeReason named.signature.key site root none)
      (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))
      completion.result.context.registry
      (fun reason token => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token) := by
  obtain ⟨port⟩ := source_port record unique issued
  exact port.ready receiver functions protocol

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedAssignmentDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallAuthority
/-! An actual named header and its selected sidecar supply the static call
authority for the corresponding invocation scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallAuthority
open Core Frontend SourceInference

def of_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment}
    {program : Program}
    (header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values definitions program)
    {sidecar : SourceCoreStageContracts.Sidecar}
    (issued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      header.named.signature.key = .ok sidecar) :
    CellAwareNamedCallPorts.Authority (compiled := compiled) header.named
      (RecursiveStageRegistry.scope sidecar [] header.function) := by
  have receipt := (CallableIndexedActualNamedSourceReceipts.header_source compiled header).1
  have sourceEq : header.function.source = sidecar.source := by
    simpa only [EmptySourceSubstitution.source] using receipt.source issued
  exact { sidecar := sidecar
          caller := issued
          view := .inl sourceEq
          guardFrame := rfl
          unique := sourceEq ▸ header.unique }

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallAuthority
end
