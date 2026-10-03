import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeBody
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogEntries

/-! Independent source closure calls complete the actual indexed application.
The concrete builtin body uses the existing finite imperative proof and the
same emitted finish. Its real prefix and caller-frame restoration preserve the
full original catalog. The body does not use named observations; no global
suffix of an arbitrary older prefix receipt is inferred here. Named, indirect
and method child closure remain separate obligations. -/
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
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  obtain ⟨size, sized⟩ := RecursiveNamedCallBounds.BodyTrace.has_size trace
  have flow := RecursiveNamedImperativeFor.preservesAt_match_with
    (validity := fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence)
    (extend := fun valid extended => valid.extend extended) (runtimeOf := fun _ valid => valid)
    (functions := model prepared profile) (definitions := rfl)
    (registered := CallableIndexedAmbient.frame_registered prepared) (extension := extension)
    (program := program) (evidence := function.evidence) (transport := builtinTransport) (bindings := builtinBindings)
    (budget := size) (faithful := identity_faithful prepared) (observations := observations prepared profile)
    (meaningMost := fun context valid child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed builtinEntry
        (CompatibleExpressionBuiltinRuntime.preserves (model prepared profile) extension
          (identity_faithful prepared) (observations prepared profile) (runtime_views prepared profile)
          program function.evidence valid.ledger valid.runtime body.unique uninitialized missing)) child)
    .reachable body.unique body.tree body.sites size (Nat.le_refl size)
  obtain ⟨result, bodyStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    RecursiveNamedFunctionFinishBounds.preserves_at_emitted (model prepared profile) program body.tree body.projection body.unique
      escaped builtinTransport body.emitted
      (fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence)
      size flow body.valid entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups
      entry.entry.actualTyped entry.entry.reference entry.entry.read entry.entry.unmapped True.intro sized
  have applied : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result (bodyStore.set location (encode prepared.ancestry.layout.frame current)) :=
    .apply (.second (.first (.var rfl))) (.var rfl) (entry.wrap evaluated)
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ := CallableIndexedBodyFrames.restore
    (CallableIndexedAmbient.frame_registered prepared) entry.unmapped entry.referenceTyped
    (show CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
      location current currentGhost store from ⟨entry.currentRead, entry.currentHistory⟩)
    finalHeaps (entry.entry.worlds.trans worlds) (entry.entry.frame.trans frame)
  exact ⟨result, _, finalMap, finalWorld, applied, related, restoredHeaps,
    entry.entry.maps.trans maps, entry.entry.worlds.trans worlds, restoredFrame,
    entry.entry.metadata.trans metadata, restoredCaller⟩

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
  have arity : function.parameters.length = arguments.length := by
    rw [CallableIndexedLambdaEntryPrefix.parameters code]
    simpa using represented.length.1
  obtain ⟨types, context, environment, bound, extended, allocated, trace⟩ := FunctionCallBody.Outcome.trace arity executed
  have sameTypes : types = body.types := extended.bodyTypes_eq.symm.trans body.extended.bodyTypes_eq
  subst types
  have sameContext := extended.functional body.extended
  subst context
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  obtain ⟨entry⟩ := CallableIndexedLambdaRuntimeBody.entry_exists captured code history body profile
    represented heaps locals reference read currentCarried unmapped allowed
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, caller⟩ :=
    entry_preserves captured code history body profile extension uninitialized missing escaped entry allocated trace
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata,
    ⟨initial.extend maps worlds frame metadata⟩, caller⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimePreservation
