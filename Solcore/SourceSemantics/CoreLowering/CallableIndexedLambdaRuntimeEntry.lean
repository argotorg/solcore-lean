import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCatalogEntries
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeBody
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForReflection

/-! The reached lambda prefix keeps the actual installed catalog. Its source
allocation and native canonical spine transport the original global slots;
its protected store effects transport the original catalog authority after the
actual frame installation. No older lambda Entry or unused native environment
identity is needed, and no body execution law is stored in this adapter. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

section CatalogFor
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  {captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual}
  {code : Code prepared function scope captured.administrative} {history : History code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context code} {functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared)}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame}
  (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history inputs functions registry arguments before store location current)
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

/-- The input is an actual catalog observation at the original capture.
Only the original frame cell is installed, then the reached prefix's certified
effects and ordered canonical additions transport that observation. -/
def catalog_entry_for : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    reached.mapping reached.world reached.heap reached.store reached.canonical :=
  CallableIndexedLambdaCatalogEntries.catalog_entry_sized reached initial sameFrame

/-- This is the same physical frame cell as the one in the supplied original
catalog authority; it is not recovered from a native frame type. -/
theorem catalog_frame_for : (catalog_entry_for reached initial sameFrame).authority.frameLocation = location :=
  sameFrame

theorem catalog_current_for : (catalog_entry_for reached initial sameFrame).authority.current = reached.next := rfl

theorem catalog_ghost_for : (catalog_entry_for reached initial sameFrame).authority.ghost =
    .lambda code.descriptor.id history.ghost := rfl

include initial sameFrame in
/-- The actual reflected body's store effects compose with the original
prefix effects. Restoring the observed caller frame then transports the
original catalog Entry at its unchanged canonical capture. -/
theorem restore_catalog_for
    {finalMap : LocationMap} {finalWorld : StoreTyping} {after : Dynamic.Heap} {bodyStore : Store}
    {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
    (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
    (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions
      finalMap finalWorld after bodyStore)
    (maps : LocationMap.Extends reached.mapping finalMap)
    (worlds : WorldExtends reached.world finalWorld)
    (frame : AdministrativePreserved reached.mapping reached.store finalMap bodyStore)
    (metadata : Dynamic.HeapMetadataExtend reached.heap after) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) captured.canonical) ∧
    AdministrativePreserved mapping store finalMap
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) := by
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  have typed : world[location]? = some prepared.ancestry.layout.frame.type := sameFrame ▸ initial.authority.typed
  obtain ⟨finalHeaps, restoredFrame, caller⟩ := CallableIndexedBodyFrames.restore
    (CallableIndexedAmbient.frame_registered prepared) unmapped typed
    (show CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
      location current currentGhost store from ⟨read, .stable currentCarried⟩)
    heaps (reached.worlds.trans worlds) (reached.frame.trans frame)
  exact ⟨finalHeaps, ⟨initial.extend (reached.maps.trans maps) (reached.worlds.trans worlds)
    restoredFrame (reached.metadata.trans metadata)⟩, restoredFrame, caller⟩

end CatalogFor

section ReflectionFor
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
  (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  (functionObservations : CompatibleEquality.FunctionObservations values.checked.catalog functions (Identity prepared))
  (functionViews : FunctionRuntimeViews functions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

include body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame in
/-- The actual reached state consumes the canonical static receipt. Its builtin
children are closed by the runtime literal certificate at each reached site.
The original native body size is used directly; the source size is independent. -/
theorem reached_reflects_for
    (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.toContext functions registry arguments before store location current)
    {size : Nat} {result : Value} {bodyStore : Store}
    (evaluated : EvaluationSize size reached.actual reached.store
      (code.receipt.body.rename reached.embedding) result bodyStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.context reached.environment reached.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after bodyStore ∧
      LocationMap.Extends reached.mapping finalMap ∧ WorldExtends reached.world finalWorld ∧
      AdministrativePreserved reached.mapping reached.store finalMap bodyStore ∧ Dynamic.HeapMetadataExtend reached.heap after := by
  let entry := RecursiveNamedCatalog.protectedEntry headers locations capturePrefix callerPrefix
  have expressionMeaning : ∀ context,
      CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedBoundedContracts.Below size (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence
        function.source (CompatibleExpressionBuiltinRuntime.Certificate body.readFuel values function.source context
          code.compilation.solvedRequirements code.reasonAt) faults entry) := by
    intro context valid
    exact RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (CompatibleExpressionBuiltinRuntime.reflects functions extension
          (identity_faithful prepared) functionObservations functionViews
          program function.evidence valid.ledger valid.runtime uninitialized missing)) size
  have flow := RecursiveNamedImperativeFor.reflectsAt_match_with
    (validity := fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence)
    (extend := fun valid extended => valid.extend extended) (runtimeOf := fun _ valid => valid)
    functions rfl (CallableIndexedAmbient.frame_registered prepared) extension program function.evidence
    (RecursiveNamedCatalog.entry_transport (headers := headers) (locations := locations))
    (RecursiveNamedCatalog.entry_binds (headers := headers) (locations := locations))
    size expressionMeaning (identity_faithful prepared) functionObservations .reachable
    functionViews body.unique body.tree body.sites
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, _, _⟩ :=
    RecursiveNamedFunctionFinishBounds.reflects_at_emitted functions program body.tree body.projection body.unique
      escaped (RecursiveNamedCatalog.entry_transport (headers := headers) (locations := locations)) body.emitted
      (fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence)
      size size (Nat.le_refl size) flow body.valid reached.environments reached.heaps reached.locals reached.lookups
      reached.actualTyped reached.reference reached.read reached.unmapped ⟨catalog_entry_for reached initial sameFrame⟩ evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata⟩


variable {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The original application selects its actual reached prefix and strict
native body child. The independent source closure call uses that prefix's real
allocation and the same source frame; its source grade is separately retained.
Full store restoration then transports the original caller catalog Entry. -/
theorem reflects_original_for {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.toContext functions registry arguments before store location current,
      ∃ child bodyStore sourceSize outcome after finalMap finalWorld,
      child < size ∧ EvaluationSize child reached.actual reached.store
        (code.receipt.body.rename reached.embedding) result bodyStore ∧
      finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.context reached.environment reached.heap outcome after ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    CallableIndexedLambdaEntryBounds.application_prefix_for captured code history body.toContext functions
      represented heaps locals reference read currentCarried unmapped allowed completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata⟩ :=
    reached_reflects_for captured code history body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame reached evaluated
  obtain ⟨restoredHeaps, restoredEntry, restoredFrame, caller⟩ :=
    restore_catalog_for reached initial sameFrame read currentCarried finalHeaps maps worlds frame metadata
  have source := trace.sound.call (context := callerContext) (caller := callerEvidence) body.frame body.extended reached.allocation
  subst finalStore
  exact ⟨reached, child, bodyStore, sourceSize, outcome, after, finalMap, finalWorld,
    smaller, evaluated, rfl, trace, source, related, restoredHeaps, reached.maps.trans maps, reached.worlds.trans worlds,
    restoredFrame, reached.metadata.trans metadata, restoredEntry, caller⟩

include body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- The public independent call outcome is a projection of the original sized
completion theorem. No older Entry agreement or preservation theorem is used. -/
theorem reflects_for {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨_, _, _, _, outcome, after, finalMap, finalWorld, _, _, _, _, source, rest⟩ :=
    reflects_original_for captured code history body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame
      represented heaps locals reference read currentCarried allowed completed
  exact ⟨outcome, after, finalMap, finalWorld, source, rest⟩

end ReflectionFor
section Catalog
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  {captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual}
  {code : Code prepared function scope captured.administrative} {history : History code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context code} {profile : values.checked.catalog.callableContracts = true}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame}
  (reached : CallableIndexedLambdaEntryBounds.Prefix captured code history inputs profile registry arguments before store location current)
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

def catalog_entry : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    reached.mapping reached.world reached.heap reached.store reached.canonical := by
  exact catalog_entry_for reached.toFor initial sameFrame

theorem catalog_frame : (catalog_entry reached initial sameFrame).authority.frameLocation = location := by
  exact sameFrame

theorem catalog_current : (catalog_entry reached initial sameFrame).authority.current = reached.next := by
  rfl

theorem catalog_ghost : (catalog_entry reached initial sameFrame).authority.ghost =
    .lambda code.descriptor.id history.ghost := by
  rfl

include initial sameFrame in

theorem restore_catalog
    {finalMap : LocationMap} {finalWorld : StoreTyping} {after : Dynamic.Heap} {bodyStore : Store}
    {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
    (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
    (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile)
      finalMap finalWorld after bodyStore)
    (maps : LocationMap.Extends reached.mapping finalMap)
    (worlds : WorldExtends reached.world finalWorld)
    (frame : AdministrativePreserved reached.mapping reached.store finalMap bodyStore)
    (metadata : Dynamic.HeapMetadataExtend reached.heap after) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) captured.canonical) ∧
    AdministrativePreserved mapping store finalMap
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) ∧
    CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost
      (bodyStore.set location (encode prepared.ancestry.layout.frame current)) := by
  exact restore_catalog_for reached.toFor initial sameFrame read currentCarried heaps maps worlds frame metadata

end Catalog

section Reflection
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
  (profile : values.checked.catalog.callableContracts = true)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

include body profile extension uninitialized missing escaped initial sameFrame in

theorem reached_reflects
    (reached : CallableIndexedLambdaEntryBounds.Prefix captured code history body.toContext profile registry arguments before store location current)
    {size : Nat} {result : Value} {bodyStore : Store}
    (evaluated : EvaluationSize size reached.actual reached.store
      (code.receipt.body.rename reached.embedding) result bodyStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.context reached.environment reached.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after bodyStore ∧
      LocationMap.Extends reached.mapping finalMap ∧ WorldExtends reached.world finalWorld ∧
      AdministrativePreserved reached.mapping reached.store finalMap bodyStore ∧ Dynamic.HeapMetadataExtend reached.heap after := by
  exact reached_reflects_for captured code history body (model prepared profile)
    (observations prepared profile) (runtime_views prepared profile) extension uninitialized missing escaped
    initial sameFrame reached.toFor evaluated

variable {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)


include body profile extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in

theorem reflects_original {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.Prefix captured code history body.toContext profile registry arguments before store location current,
      ∃ child bodyStore sourceSize outcome after finalMap finalWorld,
      child < size ∧ EvaluationSize child reached.actual reached.store
        (code.receipt.body.rename reached.embedding) result bodyStore ∧
      finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.context reached.environment reached.heap outcome after ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨reached, rest⟩ := reflects_original_for captured code history body (model prepared profile)
    (observations prepared profile) (runtime_views prepared profile) extension uninitialized missing escaped
    initial sameFrame represented heaps locals reference read currentCarried allowed completed
  exact ⟨reached.toLegacy (profile := profile), rest⟩

include body profile extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in

theorem reflects {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  exact reflects_for captured code history body (model prepared profile)
    (observations prepared profile) (runtime_views prepared profile) extension uninitialized missing escaped
    initial sameFrame represented heaps locals reference read currentCarried allowed completed

end Reflection

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeEntry
