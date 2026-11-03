import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedSnapshotPrefix
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAllocationAttachment
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysicalExtension
import Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCollectors
import Solcore.SourceSemantics.CoreLowering.CellAllocationReadiness

/-! An actual initialized statement constructs its ordered bundle from the
compiler receipt, then retains its same frame and lexical scope through the
marked allocation and continuation in either invocation kind. The declaration
first copies its scope; the principal captures the copies and the continuation
keeps the original cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (initializedRequest)
open CellAwareGeneralizedSnapshotCode (snapshotInner snapshotSequence)
open SourceSemantics.CaptureBinders (copiedBinder?)
open GeneralizedLocalDescriptorHeap GeneralizedLocalLocatedRows
open ActualBodyInvocation

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView}

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

set_option maxHeartbeats 2000000 in
theorem complete_at_source {allocationSource : TypedSource} {scope : SourceCoreLocalCell.Scope} {sourceContext nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {initializer : ExpressionId} {childFuel : Nat} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {administrative actualContext : Core.Context}
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    (entry : index.ResidualEntry) (unique : NodeOccurrencesUnique index.source)
    {statementId : StatementId}
    (site : index.Site (.statement statementId)) {statement : StatementNode} {stored : Ty}
    (readStatement : index.policy.readStatement index.compilerSource statementId = .ok (statement, stored))
    (form : statement.form = .letDecl binder (some initializer))
    {payload : Ty}
    (projected : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
    (generated : index.policy.lowerExpression childFuel index.compilerSource scope initializer reasonAt = .ok lowered)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
      (index.initializerInputs childFuel scope initializer reasonAt))
    (declaration : (SourceCoreDataPlaces.declaredBinders index.source).filter
      (fun actual => decide (actual.id = binder.id)) = [binder])
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends index.source.owner sourceContext binder nextContext)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
      (initializedRequest allocationSource scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest allocationSource scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    {captured : Expr}
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))))
      allocationSource scope (fun index => index) (snapshotInner lowered.type lowered.expression annotation.expression) =
        .ok captured)
    (copiedIds : ∀ id, (copiedBinder? allocationSource id).isSome = (copiedBinder? index.source id).isSome)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)))
    (bindings : ProtectedStateTransition.Bindings protocol)
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap} {store : Store}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before sourceContext.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge sourceContext initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
      index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := GeneralizedLocalCapturedScopes.Attachment) whole index sourceContext scope canonical mapping world before store environment)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {copies : Dynamic.Environment} {snapshotHeap : Dynamic.Heap}
    {function : Dynamic.GeneralizedClosure} {location : Dynamic.Location}
    (snapshot : Dynamic.EnvironmentCopies index.source environment before copies snapshotHeap)
    (captures : Dynamic.GeneralizedClosureCaptures sourceContext index.source copies binder initializer function)
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
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree embedding.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType lowered.type :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
        index.owner index.active nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, lowered.type) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareInvocationPhysical.Physical (attachment := GeneralizedLocalCapturedScopes.Attachment) whole index nextContext ((binder.id, lowered.type) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  obtain ⟨binding, located, metadata, initializerEq, originalSource, _payload, ⟨receipt⟩⟩ :=
    index.initialized_accepted_receipt artifact checked site.reached readStatement form
      polymorphic projected generated
  obtain ⟨_representation, _program, _catalog, _native, _plan, inputOwner, globals,
      administrativePrefix, inputInitializer, inputScope, _reason⟩ :=
    index.initializerInputs_fields childFuel scope initializer reasonAt
  have found : index.compilerSource.lookupStatement? statementId = some statement :=
    (index.reached_view.statement (.inr site.reached)).symm.trans
      (index.statement_read_reached site.reached readStatement)
  obtain ⟨_node, parameters, resultType, statements, _found, _form, _rawType, _type, _requirements, _coercions, rfl⟩ :=
    captures.canonical
  let function := Dynamic.GeneralizedClosure.ofDirectLambda sourceContext index.source copies binder
    initializer parameters resultType statements
  obtain ⟨retainedOrigin, nativeEq, _ghostEq, _metadataEq, attached, ⟨attachment⟩⟩ :=
    entry.descriptor_at_statement physical.frame site found form located metadata initializerEq originalSource
      captures unique
  generalize inputsEq : index.initializerInputs childFuel scope initializer reasonAt = originalInputs at receipt issuer inputOwner globals administrativePrefix inputInitializer inputScope
  let inputs : GeneralizedLocalInstanceCompilation.Inputs :=
    { originalInputs with
      scope := scope
      initializer := initializer
      current := { originalInputs.current with
        owner := index.owner
        globals := whole.indexed.base.globals
        administrativePrefix := 1 } }
  have sameInputs : inputs = originalInputs := by
    dsimp only [inputs]
    rw [← inputScope, ← inputInitializer, ← inputOwner, ← globals, ← administrativePrefix]
  rw [← sameInputs] at receipt issuer
  let origin : GeneralizedLocalDescriptorOrigin.Origin whole.indexed function binding index.active :=
    { retainedOrigin with
      native := physical.native
      carried := by simpa only [nativeEq] using retainedOrigin.carried }
  let current : CallableIndexedLambdaValues.Captures whole.indexed mapping world inputs.scope environment actual :=
    ⟨administrative, canonical, actualContext, embedding, environments,
      agrees, TypedLexicalWhile.environment_respects environments.runtime_hasTypes actualTyped agrees,
      actualTyped⟩
  obtain ⟨bindingOwner, bindingId⟩ := SourceCoreLocalPolymorphism.Catalog.binding_identity located
  have originalExtended : BinderExtends function.source.owner function.definitionContext function.binder nextContext := extended
  have originalOrdinary : allocationSource.inputs.any (fun input => decide (input.id = function.binder.id)) = false := ordinary
  let originalAllocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts inputs.current.owner index.active
      (initializedRequest allocationSource inputs.scope function.binder lowered.type) := allocation
  let originalAnnotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt inputs.current.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest allocationSource inputs.scope function.binder lowered.type) := annotation
  have sameOriginal : originalAnnotation.original = originalAllocation.expression := by
    simpa only [originalAnnotation, originalAllocation] using same
  have originalCopied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt inputs.current.owner index.active
          (fun error => .sourceAllocation (reprStr error)))))
      allocationSource inputs.scope (fun index => index)
      (snapshotInner lowered.type lowered.expression originalAnnotation.expression) = .ok captured := copied
  have originalCopiedIds :
      ∀ id, (copiedBinder? allocationSource id).isSome = (copiedBinder? function.source id).isSome := copiedIds
  have originalDeclarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext := physical.declarations
  have originalLocals : Dynamic.EnvironmentAgrees before function.definitionContext.locals environment := locals
  have originalSnapshot : Dynamic.EnvironmentCopies function.source environment before function.captured snapshotHeap :=
    snapshot
  have originalTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ current.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions := nativeTyped
  have originalReference : current.canonical[inputs.scope.length + 1 + whole.indexed.base.globals.length]? =
      some (.cellRef whole.indexed.ancestry.layout.frame.type physical.location) := physical.reference
  have referenceIndex : SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope =
      inputs.scope.length + 1 + whole.indexed.base.globals.length := rfl
  let originalInitial : protocol.State ⟨inputs.scope, mapping, world, before, store, current.canonical⟩ := initial
  have originalReady : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location origin.native := ready
  obtain ⟨values, marker, copiedStore, copiedMap, copiedWorld, agreement, smaller, nextEnvironments, nextHeaps,
      nextLocals, nextAgrees, nextTyped, _nextReference, _nextRead, preserved, maps, worlds, ⟨suffix, storeEq⟩,
      locatedRows, transition⟩ :=
    GeneralizedLocalAcceptedSnapshotPrefix.complete_with_at_source receipt GeneralizedLocalCapturedScopes.Attachment
      attached bindingOwner.symm initializerEq.symm origin attachment originalExtended originalOrdinary
      originalAllocation originalAnnotation sameOriginal originalCopied originalCopiedIds producer
      (transitions bridge) bindings registered current originalDeclarations physical.ownership issuer originalTyped
      heaps originalLocals originalReference referenceIndex physical.read originalSnapshot allocated originalInitial
      originalReady output body
  obtain ⟨locatedRows, frames⟩ := locatedRows
  have heapMetadata := snapshot.metadata_extends.trans (Dynamic.HeapMetadataExtend.of_generalized_allocation allocated)
  have effect : CellAwareScopeAuthority.Effect
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
      mapping world before store (copiedMap ++ [copiedStore.length + 2])
      (copiedWorld ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]) after
      (copiedStore ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker,
        .inRight .unit (SourceCoreLocalPolymorphism.ProductBundle.value values)]) := by
    rw [storeEq]
    exact CellAwareScopeAuthority.Effect.append
      (instances := GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
      store suffix heapMetadata maps worlds
  have lexical : GeneralizedLocalBundleContexts.ContextExtension index.active index.active :=
    ⟨fun _ member => member, fun _ _ => rfl⟩
  have nextAuthority := CellAwareScopeAuthority.At.cons
    (.generalized bindingOwner bindingId lexical ⟨locatedRows⟩) (authority.transport effect)
  obtain ⟨reached, related⟩ := transition
  have nextAdmitted : Admission bridge nextContext reached :=
    ⟨(Dynamic.HeapWellTyped.iff_of_binderExtends originalExtended).mp
        ((admitted.heap.copy snapshot).allocateGeneralized functionTyped allocated),
      CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
        (bridge.pool initial) (bridge.pool reached) admitted.rows preserved⟩
  have fields : Dynamic.RuntimeContextFields function.definitionContext nextContext :=
    Dynamic.RuntimeContextFields.ofBinderExtends extended
  have requirements : nextContext.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements := extended.local_scheme_requirements_self
  have head : CellAwareInvocationPhysical.Entry (attachment := GeneralizedLocalCapturedScopes.Attachment)
      whole index nextContext physical.location binder.id location (copiedMap ++ [copiedStore.length + 2]) _ after _ :=
    .generalized locatedRows bindingOwner bindingId lexical frames fields requirements
  let nextPhysical := (physical.transport effect preserved).cons extended
    (CellAwareNativeBodyCollectors.scope_generalized lowered.type physical.declarations declaration polymorphic extended)
    ((List.mem_filter.mp (declaration ▸ List.mem_singleton_self binder)).1)
    (.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) head
  exact ⟨values, marker, copiedStore, copiedMap, copiedWorld, agreement, smaller, nextEnvironments, nextHeaps,
    nextLocals, nextAgrees, nextTyped, preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical,
    rfl, rfl⟩

theorem complete {scope : SourceCoreLocalCell.Scope} {sourceContext nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {initializer : ExpressionId} {childFuel : Nat} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {administrative actualContext : Core.Context}
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    (entry : index.ResidualEntry) (unique : NodeOccurrencesUnique index.source)
    {statementId : StatementId}
    (site : index.Site (.statement statementId)) {statement : StatementNode} {stored : Ty}
    (readStatement : index.policy.readStatement index.compilerSource statementId = .ok (statement, stored))
    (form : statement.form = .letDecl binder (some initializer))
    {payload : Ty}
    (projected : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
    (generated : index.policy.lowerExpression childFuel index.compilerSource scope initializer reasonAt = .ok lowered)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
      (index.initializerInputs childFuel scope initializer reasonAt))
    (declaration : (SourceCoreDataPlaces.declaredBinders index.source).filter
      (fun actual => decide (actual.id = binder.id)) = [binder])
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends index.source.owner sourceContext binder nextContext)
    (ordinary : index.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
      (initializedRequest index.source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest index.source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    {captured : Expr}
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))))
      index.source scope (fun index => index) (snapshotInner lowered.type lowered.expression annotation.expression) =
        .ok captured)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)))
    (bindings : ProtectedStateTransition.Bindings protocol)
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap} {store : Store}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before sourceContext.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge sourceContext initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
      index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := GeneralizedLocalCapturedScopes.Attachment) whole index sourceContext scope canonical mapping world before store environment)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {copies : Dynamic.Environment} {snapshotHeap : Dynamic.Heap}
    {function : Dynamic.GeneralizedClosure} {location : Dynamic.Location}
    (snapshot : Dynamic.EnvironmentCopies index.source environment before copies snapshotHeap)
    (captures : Dynamic.GeneralizedClosureCaptures sourceContext index.source copies binder initializer function)
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
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree embedding.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType lowered.type :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
        index.owner index.active nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, lowered.type) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareInvocationPhysical.Physical (attachment := GeneralizedLocalCapturedScopes.Attachment) whole index nextContext ((binder.id, lowered.type) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  exact complete_at_source bridge artifact checked entry unique site readStatement form projected generated issuer
    declaration polymorphic extended ordinary nativeTyped allocation annotation same copied (fun _ => rfl) producer
    bindings registered environments heaps locals agrees actualTyped initial admitted authority physical ready snapshot
    captures functionTyped allocated output body

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedPrefix
