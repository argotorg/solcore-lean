import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeBody
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNamedRuntimeBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogEntries

/-! Independent source closure calls complete the actual indexed application.
The legacy builtin entry uses the shared finite body kernel with True entry.
NamedModel uses the same kernel and actual catalog/source prefix, with named
callee meaning closed by static profiles and the existing mutual induction.
Both restore the full caller catalog. Indirect apply, nested lambda formation
and general method body closure remain separate grammar boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimePreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

private abbrev builtinEntry : ProtectedExpressionMeaning.Entry := fun _ _ _ _ _ _ => True
private theorem builtinTransport : ProtectedExpressionMeaning.Transport builtinEntry := ⟨fun _ _ _ _ _ => True.intro⟩
private theorem builtinBindings : ProtectedExpressionMeaning.Binds builtinEntry :=
  ⟨fun _ => True.intro, fun _ => True.intro⟩

section GeneralModel

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
  (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions (Identity prepared))
  (functionTypes : FunctionRuntimeViews functions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}

theorem wrap_body_at_for (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap} {result : Value} {bodyStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping}
    (evaluated : Evaluates entry.entry.actualBody entry.entry.store
      (code.receipt.body.rename entry.entry.embedding) result bodyStore)
    (related : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result)
    (finalHeaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after bodyStore)
    (maps : LocationMap.Extends entry.entry.mapping finalMap) (worlds : WorldExtends entry.entry.world finalWorld)
    (frame : AdministrativePreserved entry.entry.mapping entry.entry.store finalMap bodyStore)
    (metadata : Dynamic.HeapMetadataExtend entry.entry.heap after) :
    Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    Dynamic.HeapMetadataExtend before after ∧
    CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) := by
  have applied : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result (bodyStore.set location (encode prepared.ancestry.layout.frame current)) :=
    .apply (.second (.first (.var rfl))) (.var rfl) (entry.wrap evaluated)
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ := CallableIndexedBodyFrames.restore
    (CallableIndexedAmbient.frame_registered prepared) entry.unmapped entry.referenceTyped
    (show CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
      location current currentGhost store from ⟨entry.currentRead, entry.currentHistory⟩)
    finalHeaps (entry.entry.worlds.trans worlds) (entry.entry.frame.trans frame)
  exact ⟨applied, related, restoredHeaps, entry.entry.maps.trans maps, entry.entry.worlds.trans worlds,
    restoredFrame, entry.entry.metadata.trans metadata, restoredCaller⟩

private theorem wrap_body_for (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap} {result : Value} {bodyStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping}
    (evaluated : Evaluates entry.entry.actualBody entry.entry.store
      (code.receipt.body.rename entry.entry.embedding) result bodyStore)
    (related : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result)
    (finalHeaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after bodyStore)
    (maps : LocationMap.Extends entry.entry.mapping finalMap) (worlds : WorldExtends entry.entry.world finalWorld)
    (frame : AdministrativePreserved entry.entry.mapping entry.entry.store finalMap bodyStore)
    (metadata : Dynamic.HeapMetadataExtend entry.entry.heap after) :
    Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    Dynamic.HeapMetadataExtend before after ∧
    CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) :=
  wrap_body_at_for captured code history functions inputs entry evaluated related finalHeaps maps worlds frame metadata


include extension uninitialized missing escaped functionLeaves functionTypes in
/-- The independent source allocation is identified with this actual prefix.
The shared finite statement proof closes the body once; the real wrap then
completes the application and restores every unmapped caller cell. -/
theorem entry_preserves_for
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history body.toContext functions registry arguments nativeArguments before store location current currentGhost)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  obtain ⟨size, sized⟩ := RecursiveNamedCallBounds.BodyTrace.has_size trace
  obtain ⟨result, bodyStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    (CallableIndexedLambdaNamedRuntimeBodyMeaning.builtin_kernel code body).preserves_sized functions rfl
      (CallableIndexedAmbient.frame_registered prepared) extension program (identity_faithful prepared) functionLeaves escaped
      builtinTransport builtinBindings (fun valid extended => valid.extend extended) (fun valid => valid)
      size size (Nat.le_refl size)
      (fun context valid child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded
        (ProtectedExpressionMeaning.preserves_of_typed builtinEntry
          (CompatibleExpressionBuiltinRuntime.preserves functions extension
            (identity_faithful prepared) functionLeaves functionTypes
            program function.evidence valid.ledger valid.runtime body.unique uninitialized missing)) child)
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups
      entry.entry.actualTyped entry.entry.reference entry.entry.read entry.entry.unmapped True.intro sized
  exact ⟨result, _, finalMap, finalWorld,
    wrap_body_for captured code history functions body.toContext entry evaluated related finalHeaps maps worlds frame metadata⟩

variable {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body extension uninitialized missing escaped functionLeaves functionTypes initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The source call supplies its own context, ordered allocation and body trace.
Only those static contexts and allocations are identified with the actual
prefix. The full original caller catalog is transported after restoration. -/
theorem preserves_for {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have arity : function.parameters.length = arguments.length := by
    rw [CallableIndexedLambdaEntryPrefix.parameters code]
    simpa using represented.length.1
  obtain ⟨types, context, environment, bound, extended, allocated, trace⟩ := FunctionCallBody.Outcome.trace arity executed
  have sameTypes : types = body.types := extended.bodyTypes_eq.symm.trans body.extended.bodyTypes_eq
  subst types
  have sameContext := extended.functional body.extended
  subst context
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  obtain ⟨entry⟩ := CallableIndexedLambdaEntryPrefix.entry_exists_for captured code history body.toContext functions
    represented heaps locals reference read currentCarried unmapped allowed
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, caller⟩ :=
    entry_preserves_for captured code history body functions functionLeaves functionTypes extension uninitialized missing escaped entry allocated trace
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata,
    ⟨initial.extend maps worlds frame metadata⟩, caller⟩

end GeneralModel

section NamedModel
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix : Nat}
  (body : CallableIndexedLambdaNamedRuntimeBodyMeaning.Body headers code program registry faults)
  (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions (Identity prepared))
  (functionTypes : FunctionRuntimeViews functions)
  (family : CallableIndexedLambdaNamedRuntimeBodyMeaning.CatalogFamily headers locations capturePrefix functions registry faults)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}

  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix code.compilation.administrativePrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

include body family owners extension uninitialized missing escaped functionLeaves functionTypes initial sameFrame in
/-- The actual ordered prefix retains its catalog source entry. The original
source child grade feeds the shared kernel, then the sole wrap/restore adapter
returns the complete caller store. -/
theorem entry_preserves_named_sized_for (budget size : Nat) (within : size ≤ budget)
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history body.toContext functions registry arguments nativeArguments before store location current currentGhost)
    {added : Environment} (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  let installed := CallableIndexedLambdaCatalogEntries.source_entry entry initial sameFrame length spine
  obtain ⟨result, bodyStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    CallableIndexedLambdaNamedRuntimeBodyMeaning.Body.preserves_sized code history body functions extension functionLeaves
      functionTypes owners family uninitialized missing escaped budget size within
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
      entry.entry.reference entry.entry.read entry.entry.unmapped ⟨installed⟩ trace
  exact ⟨result, _, finalMap, finalWorld,
    wrap_body_for captured code history functions body.toContext entry evaluated related finalHeaps maps worlds frame metadata⟩

variable
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body family owners extension uninitialized missing escaped functionLeaves functionTypes initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The original source body child supplies its grade independently of the
native application. Its actual prefix spine closes catalog installation and
full caller restoration without any unsized-to-sized conversion. -/
theorem preserves_named_sized_for (budget size : Nat) (within : size ≤ budget)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {environment : Dynamic.Environment} {bound : Dynamic.Heap}
    (allocated : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix code.compilation.administrativePrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  obtain ⟨entry, added, length, spine⟩ := CallableIndexedLambdaEntryPrefix.entry_exists_for_with_spine
    captured code history body.toContext functions represented heaps locals reference read currentCarried unmapped allowed
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, caller⟩ :=
    entry_preserves_named_sized_for captured code history body functions functionLeaves functionTypes family owners extension
      uninitialized missing escaped initial sameFrame budget size within entry length spine allocated trace
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata,
    ⟨initial.extend maps worlds frame metadata⟩, caller⟩

end NamedModel

section NestedModel
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {rank : Nat} {caller : RecursiveNamedCatalog.Header prepared.ancestry values prepared.layouts.definitions program}
  (body : CallableIndexedLambdaNestedRuntimeBodyMeaning.Body headers caller registry faults rank code)
  (profile : values.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions prepared) headers)
  (globals : caller.globals = prepared.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < prepared.base.globals.length)
  (metadataSource : history.metadata = CallableIndexedNamedGeneration.state caller.named)
  (family : CallableIndexedLambdaNamedRuntimeBodyMeaning.CatalogFamily headers locations 0 (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) registry faults)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}

  (initial : RecursiveNamedCatalog.Entry headers locations 0 code.compilation.administrativePrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

include body complete globals slots metadataSource family owners extension uninitialized missing escaped initial sameFrame in
/-- The actual ordered prefix retains its catalog source entry. The original
source child grade feeds the shared kernel, then the sole wrap/restore adapter
returns the complete caller store. -/
theorem entry_preserves_nested_sized_for (budget size : Nat) (within : size ≤ budget)
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history body.body.toContext (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) registry arguments nativeArguments before store location current currentGhost)
    {added : Environment} (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  let original := CallableIndexedLambdaCatalogEntries.source_entry entry initial sameFrame length spine
  let installed := CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.entry_of_source body original metadataSource globals entry.entry.environments
  obtain ⟨result, bodyStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.preserves_sized code body profile complete globals slots extension family owners
      uninitialized missing escaped budget size within
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
      entry.entry.reference entry.entry.read entry.entry.unmapped ⟨installed⟩ trace
  exact ⟨result, _, finalMap, finalWorld,
    wrap_body_at_for captured code history (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) body.body.toContext entry evaluated related finalHeaps maps worlds frame metadata⟩

variable
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body complete globals slots metadataSource family owners extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The original source body child supplies its grade independently of the
native application. Its actual prefix spine closes catalog installation and
full caller restoration without any unsized-to-sized conversion. -/
theorem preserves_nested_sized_for (budget size : Nat) (within : size ≤ budget)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {environment : Dynamic.Environment} {bound : Dynamic.Heap}
    (allocated : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations 0 code.compilation.administrativePrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  obtain ⟨entry, added, length, spine⟩ := CallableIndexedLambdaEntryPrefix.entry_exists_for_with_spine
    captured code history body.body.toContext (CallableIndexedLambdaNestedRuntimeCertificates.model headers locations registry faults profile) represented heaps locals reference read currentCarried unmapped allowed
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, caller⟩ :=
    entry_preserves_nested_sized_for captured code history body profile complete globals slots metadataSource family owners extension
      uninitialized missing escaped initial sameFrame budget size within entry length spine allocated trace
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata,
    ⟨initial.extend maps worlds frame metadata⟩, caller⟩

end NestedModel

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
  (profile : values.checked.catalog.callableContracts = true)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}

include extension uninitialized missing escaped in
/-- The independent source allocation is identified with this actual prefix.
The shared finite statement proof closes the body once; the real wrap then
completes the application and restores every unmapped caller cell. -/
theorem entry_preserves
    (entry : CallableIndexedLambdaRuntimeBody.Entry captured code history body profile arguments nativeArguments before store location current currentGhost)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact entry_preserves_for captured code history body (model prepared profile)
    (observations prepared profile) (runtime_views prepared profile)
    extension uninitialized missing escaped entry.toFor allocated trace

variable {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The source call supplies its own context, ordered allocation and body trace.
Only those static contexts and allocations are identified with the actual
prefix. The full original caller catalog is transported after restoration. -/
theorem preserves {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact preserves_for captured code history body (model prepared profile)
    (observations prepared profile) (runtime_views prepared profile)
    extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed executed



end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimePreservation
