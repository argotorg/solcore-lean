import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls

/-! Ordinary closure calls combine concrete lexical builtin bodies with the
actual indexed frame and marked parameter prefix. The lambda's generation
receipt and caller history remain semantic inputs. Completed native execution
constructs the independent source call; no body execution is an input. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaViewInvocation
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

abbrev represented_closure := @CallableIndexedLambdaCalls.represented_closure
abbrev applyPayload := CallableIndexedLambdaCalls.applyPayload

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))

include extension uninitialized missing in
theorem Entry.preserves
    (entry : Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  have registered := CallableIndexedAmbient.frame_registered prepared
  obtain ⟨result, bodyStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    body.certificate.preserves (model prepared profile) extension rfl registered program body.valid body.unique uninitialized missing
      (identity_faithful prepared) (observations prepared profile) (runtime_views prepared profile)
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
      entry.entry.reference entry.entry.read entry.entry.unmapped trace
  have maps := entry.entry.maps.trans maps
  have worlds := entry.entry.worlds.trans worlds
  have frame := entry.entry.frame.trans frame
  have metadata := entry.entry.metadata.trans metadata
  have bodyEval := entry.wrap evaluated
  have callEval : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result (bodyStore.set location (encode prepared.ancestry.layout.frame current)) :=
    .apply (.second (.first (.var rfl))) (.var rfl) bodyEval
  obtain ⟨restoredHeap, restoredFrame, restoredCaller⟩ := CallableIndexedBodyFrames.restore registered entry.unmapped entry.referenceTyped
    (show CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost store from
      ⟨entry.currentRead, entry.currentHistory⟩) finalHeaps worlds frame
  exact ⟨result, _, finalMap, finalWorld, callEval, related, restoredHeap, maps, worlds, restoredFrame, metadata, restoredCaller⟩

include extension uninitialized missing in
theorem Entry.reflects
    (entry : Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost)
    {result : Value} {finalStore : Store}
    (evaluated : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result finalStore) :
    ∃ environment bound outcome after finalMap finalWorld,
      Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function body.context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  cases evaluated with
  | apply callee argument applied =>
    have expected : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store (.second (.first (.var 0)))
        (.closure code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore)
          (code.body.rename captured.embedding.lift.lift) (encode prepared.ancestry.layout.frame history.native :: capturedActual)) store :=
      .second (.first (.var rfl))
    obtain ⟨sameClosure, sameStore⟩ := evaluation_deterministic callee expected
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj sameClosure
    rw [sameStore] at argument
    obtain ⟨sameArgument, sameAfter⟩ := evaluation_deterministic argument
      (show Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store (.var 1) (DataPatternValues.packValues nativeArguments) store from .var rfl)
    rw [sameArgument, sameAfter] at applied
    obtain ⟨bodyStore, bodyEval, finalEq⟩ := entry.unwrap applied
    have registered := CallableIndexedAmbient.frame_registered prepared
    obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
      body.certificate.reflects (model prepared profile) extension rfl registered program body.valid body.unique uninitialized missing
        (identity_faithful prepared) (observations prepared profile) (runtime_views prepared profile)
        entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
        entry.entry.reference entry.entry.read entry.entry.unmapped bodyEval
    have maps := entry.entry.maps.trans maps
    have worlds := entry.entry.worlds.trans worlds
    have frame := entry.entry.frame.trans frame
    have metadata := entry.entry.metadata.trans metadata
    obtain ⟨restoredHeap, restoredFrame, restoredCaller⟩ := CallableIndexedBodyFrames.restore registered entry.unmapped entry.referenceTyped
      (show CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost store from
        ⟨entry.currentRead, entry.currentHistory⟩) finalHeaps worlds frame
    subst finalStore
    exact ⟨entry.entry.environment, entry.entry.heap, outcome, after, finalMap, finalWorld, entry.entry.allocation, trace,
      related, restoredHeap, maps, worlds, restoredFrame, metadata, restoredCaller⟩

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem reflects {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {result : Value} {finalStore : Store}
    (evaluated : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨entry⟩ := entry_exists captured code history body profile represented heaps locals reference read currentCarried unmapped allowed
  obtain ⟨environment, bound, outcome, after, finalMap, finalWorld, allocated, trace, rest⟩ :=
    Entry.reflects captured code history body profile extension uninitialized missing entry evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace.call body.frame body.extended allocated, rest⟩

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem preserves {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have arity : function.parameters.length = arguments.length := by rw [parameters code]; simpa using represented.length.1
  obtain ⟨types, context, environment, bound, extended, allocated, trace⟩ := FunctionCallBody.Outcome.trace arity executed
  have sameTypes : types = body.types := extended.bodyTypes_eq.symm.trans body.extended.bodyTypes_eq
  subst types
  have sameContext := extended.functional body.extended
  subst context
  obtain ⟨entry⟩ := entry_exists captured code history body profile represented heaps locals reference read currentCarried unmapped allowed
  exact Entry.preserves captured code history body profile extension uninitialized missing entry allocated trace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewCalls
