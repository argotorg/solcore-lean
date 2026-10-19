import Solcore.SourceSemantics.CoreLowering.CellAwareNamedDiagnosticIssuer
import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedPrefix
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedDescriptor
import Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysicalExtension
import Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCollectors
import Solcore.SourceSemantics.CoreLowering.CellAllocationReadiness

/-! A genuine named declaration constructs its descriptor origin from the
selected caller and extends the physical lexical authority at the actual
marked allocation. No future expression or body behavior is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (initializedRequest sequence)
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
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
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
    (ready : producer.Ready initial physical.location physical.native)
    {function : Dynamic.GeneralizedClosure} {location : Dynamic.Location}
    (captures : Dynamic.GeneralizedClosureCaptures sourceContext (source named) environment binder initializer function)
    (functionTyped : Dynamic.GeneralizedClosureWellTyped sourceContext before function)
    (allocated : Dynamic.Heap.AllocatesGeneralized before function location after)
    (output : Ty) (body : Expr) :
    ∃ values marker,
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual store
        ((sequence output lowered.expression annotation.expression body).rename embedding)
        (nextRef :: bundle :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) ∧
      (∀ {size value finalStore}, EvaluationSize size actual store
          ((sequence output lowered.expression annotation.expression body).rename embedding) value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: bundle :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, lowered.type) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) embedding).lift
        (nextRef :: canonical) (nextRef :: bundle :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: bundle :: actual)
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
  obtain ⟨_node, parameters, resultType, statements, _found, _form, _rawType, _type, _requirements, _coercions, rfl⟩ :=
    captures.canonical
  let function := Dynamic.GeneralizedClosure.ofDirectLambda sourceContext (source named) environment binder
    initializer parameters resultType statements
  obtain ⟨retainedOrigin, nativeEq, _ghostEq, _metadataEq, namedMetadata, ⟨attachment⟩,
      descriptorSource, binderEq, _initializerEq⟩ :=
    CellAwareNamedDescriptor.of_capture site captures physical.selected record physical.carried
  let origin : GeneralizedLocalDescriptorOrigin.Origin whole.indexed function site.binding [] :=
    { retainedOrigin with
      native := physical.native
      carried := by simpa only [nativeEq] using retainedOrigin.carried }
  let captured : CallableIndexedLambdaValues.Captures whole.indexed mapping world scope function.captured actual :=
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
  have originalLocals : Dynamic.EnvironmentAgrees before function.definitionContext.locals function.captured := locals
  have originalRead := physical.read
  have originalReady : producer.Ready initial physical.location origin.native := ready
  obtain ⟨values, marker, agreement, smaller, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, _nextReference, _nextRead, preserved, located, transition⟩ :=
    CellAwareGeneralizedPrefix.complete receipt descriptorSource site.bindingCaller.symm site.bindingInitializer.symm
      origin rfl namedMetadata attachment originalExtended originalOrdinary originalAllocation originalAnnotation sameOriginal
      producer registered captured originalDeclarations physical.ownership
      (CellAwareNamedDiagnosticIssuer.Named.initializer compiled issuer childFuel (childFuel + 1) scope initializer) nativeTyped heaps originalLocals physical.reference
      (by rfl) originalRead allocated initial originalReady output body
  obtain ⟨located, frames⟩ := located
  have metadata := Dynamic.HeapMetadataExtend.of_generalized_allocation allocated
  have effect := CellAwareScopeAuthority.Effect.append
    (instances := GeneralizedLocalInstanceValues.model whole.indexed) store
    [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame origin.native,
      SourceCoreHeapMarkers.markerValue allocation.entry.layout marker,
      .inRight .unit (SourceCoreLocalPolymorphism.ProductBundle.value values)] metadata
    (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
    (show WorldExtends world (world ++ [whole.indexed.ancestry.layout.frame.type,
      allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩)
  have bindingId : site.binding.binder.id = binder.id := by
    simpa only [EmptySourceSubstitution.binder] using congrArg TypedBinder.id site.bindingMetadata
  have lexical : GeneralizedLocalBundleContexts.ContextExtension [] [] := ⟨by simp, by simp⟩
  have nextAuthority := CellAwareScopeAuthority.At.cons
    (.generalized site.bindingCaller bindingId lexical ⟨located⟩) (authority.transport effect)
  obtain ⟨reached, related⟩ := transition
  have nextAdmitted := CellAwareGeneralizedDeclaration.admitted_after_allocation bridge initial reached admitted
    originalExtended functionTyped allocated preserved
  have fields : Dynamic.RuntimeContextFields function.definitionContext nextContext :=
    Dynamic.RuntimeContextFields.ofBinderExtends extended
  have requirements : nextContext.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements := extended.local_scheme_requirements_self
  have head : CellAwareScopePhysical.Entry whole named nextContext physical.location binder.id location
      (mapping ++ [store.length + 2]) _ after _ :=
    .generalized located site.bindingCaller bindingId lexical frames fields requirements
  let nextPhysical := (physical.transport effect preserved).cons extended
    (CellAwareNativeBodyCollectors.scope_generalized lowered.type physical.declarations declaration polymorphic extended)
    ((List.mem_filter.mp (declaration ▸ List.mem_singleton_self binder)).1)
    (.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) head
  exact ⟨values, marker, agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
    preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedPrefix
