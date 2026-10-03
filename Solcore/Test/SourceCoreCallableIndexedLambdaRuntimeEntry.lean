import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeEntry
import Solcore.Test.SourceCoreCallableIndexedLambdaViewCalls
import Solcore.Test.SourceCoreCallableIndexedLambdaValues

/-! The actual canonical body receipt closes reflection from the supplied
original application. The consumers retain its strict native body child,
independent source body grade, ordered globals and the restored caller Entry.
Runtime regression delegates to existing capture/call suites; it does not
assert identity with an arbitrary unsized older lambda Entry or closure of
named/indirect recursive body syntax. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaRuntimeEntry
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames

abbrev actual_reached_body := @CallableIndexedLambdaRuntimeEntry.reached_reflects
abbrev original_strict_state := @CallableIndexedLambdaRuntimeEntry.reflects_original
abbrev original_source_outcome := @CallableIndexedLambdaRuntimeEntry.reflects
abbrev finish_without_recompilation := @RecursiveNamedFunctionFinishBounds.reflects_at_emitted

section Actual
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
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


include initial sameFrame in
/-- Global row order comes from the original Entry and the actual native
parameter spine. The same physical slots are retained at the reached state. -/
theorem ordered_globals
    (reached : CallableIndexedLambdaEntryBounds.Prefix captured code history body.toContext profile registry arguments before store location current)
    (header : RecursiveNamedCatalog.Header prepared.ancestry values prepared.layouts.definitions program)
    (member : header ∈ headers) :
    reached.canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length +
      callerPrefix + header.slot]? = some
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) :=
  (CallableIndexedLambdaRuntimeEntry.catalog_entry reached initial sameFrame).globals header member

include initial sameFrame in
theorem actual_frame
    (reached : CallableIndexedLambdaEntryBounds.Prefix captured code history body.toContext profile registry arguments before store location current) :
    (CallableIndexedLambdaRuntimeEntry.catalog_entry reached initial sameFrame).authority.frameLocation = location ∧
    (CallableIndexedLambdaRuntimeEntry.catalog_entry reached initial sameFrame).authority.current = reached.next ∧
    (CallableIndexedLambdaRuntimeEntry.catalog_entry reached initial sameFrame).authority.ghost =
      .lambda code.descriptor.id history.ghost :=
  ⟨CallableIndexedLambdaRuntimeEntry.catalog_frame reached initial sameFrame,
    CallableIndexedLambdaRuntimeEntry.catalog_current reached initial sameFrame,
    CallableIndexedLambdaRuntimeEntry.catalog_ghost reached initial sameFrame⟩

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
/-- Empty arity keeps the original strict native witness. The same source
allocation and caller restoration follow from the concrete runtime body. -/
theorem empty_arguments {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store} (empty : nativeArguments = [])
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.Prefix captured code history body.toContext profile registry arguments before store location current,
      ∃ child bodyStore outcome after finalMap finalWorld,
      child < size ∧ EvaluationSize child reached.actual reached.store
        (code.receipt.body.rename reached.embedding) result bodyStore ∧
      reached.canonical = captured.canonical ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨reached, child, bodyStore, _, outcome, after, finalMap, finalWorld, smaller, evaluated, _, _, source, _, heaps,
    _, _, _, _, callerEntry, caller⟩ :=
    CallableIndexedLambdaRuntimeEntry.reflects_original captured code history body profile extension uninitialized missing escaped initial sameFrame
      represented heaps locals reference read currentCarried allowed completed
  obtain ⟨added, length, spine⟩ := reached.spine
  have zero : code.receipt.loweredParameters.length = 0 := by simpa [empty] using represented.length.2
  have nil : added = [] := List.eq_nil_of_length_eq_zero (length.trans zero)
  exact ⟨reached, child, bodyStore, outcome, after, finalMap, finalWorld, smaller, evaluated,
    by simpa only [nil, List.nil_append] using spine, source, heaps, callerEntry, caller⟩

end Actual

/-- Existing whole capture and callable regressions are reused once. New
reflection itself is checked above through its original sized completion. -/
def run : IO Unit := do
  Tests.SourceCoreCallableIndexedLambdaViewCalls.run
  Tests.SourceCoreCallableIndexedLambdaValues.run

end Tests.SourceCoreCallableIndexedLambdaRuntimeEntry
