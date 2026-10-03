import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeEntry
import Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody
import Solcore.Test.SourceCoreCallableIndexedLambdaEntryBounds

/-! The supplied function relation stays unchanged from the original application
through its strict body child and full restored store. Static observations and
runtime views concern represented function values; they are separate from body
execution. No unsized entry agreement supplies a size or an arbitrary stronger
model. The runtime runner reuses the existing actual indexed lambda suite. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaModelEntryBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedLambdaEntryBounds

abbrev actual_reached_reflection := @CallableIndexedLambdaRuntimeEntry.reached_reflects_for
abbrev original_reflection := @CallableIndexedLambdaRuntimeEntry.reflects_original_for
abbrev independent_source_outcome := @CallableIndexedLambdaRuntimeEntry.reflects_for

section Entry
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context code) (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
/-- The consumer keeps the body subderivation of the supplied application,
and reads the ordered lexical prefix from its reached state. -/
theorem original_application {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : PrefixFor captured code history inputs functions registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
        ∃ added : Environment, added.length = code.receipt.loweredParameters.length ∧
          reached.canonical = added ++ captured.canonical ∧
            CompatibleAmbientHeap.HeapRepresents values.checked registry functions reached.mapping reached.world reached.heap reached.store := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    application_prefix_for captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed completed
  refine ⟨reached, child, bodyStore, smaller, evaluated, restored, ?_⟩
  obtain ⟨added, length, spine⟩ := reached.spine
  exact ⟨added, length, spine, reached.heaps⟩

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
/-- Zero arguments retain the original strict body edge; the canonical
lexical spine has no added parameter values. Administrative values remain. -/
theorem empty_arguments_strict {size : Nat} {result : Value} {finalStore : Store}
    (empty : nativeArguments = [])
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : PrefixFor captured code history inputs functions registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
        reached.canonical = captured.canonical := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    application_prefix_for captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed completed
  obtain ⟨added, length, spine⟩ := reached.spine
  have parameters : code.receipt.loweredParameters.length = 0 := by
    simpa [empty] using represented.length.2
  have noValues : added = [] := List.eq_nil_of_length_eq_zero (length.trans parameters)
  rw [noValues] at spine
  exact ⟨reached, child, bodyStore, smaller, evaluated, restored, by simpa using spine⟩

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
/-- This consumer erases only the extracted child witness. It never chooses a
new grade for the original completion. -/
theorem original_body {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore) :
    ∃ reached : PrefixFor captured code history inputs functions registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        Evaluates reached.actual reached.store (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    body_prefix_for captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed completed
  exact ⟨reached, child, bodyStore, smaller, evaluated, evaluated.sound, restored⟩
end Entry

section Actual
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
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


include initial sameFrame in
/-- Global row order comes from the original Entry and the actual native
parameter spine. The same physical slots are retained at the reached state. -/
theorem ordered_globals
    (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.toContext functions registry arguments before store location current)
    (header : RecursiveNamedCatalog.Header prepared.ancestry values prepared.layouts.definitions program)
    (member : header ∈ headers) :
    reached.canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length +
      callerPrefix + header.slot]? = some
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) :=
  (CallableIndexedLambdaRuntimeEntry.catalog_entry_for reached initial sameFrame).globals header member

include initial sameFrame in
theorem actual_frame
    (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.toContext functions registry arguments before store location current) :
    (CallableIndexedLambdaRuntimeEntry.catalog_entry_for reached initial sameFrame).authority.frameLocation = location ∧
    (CallableIndexedLambdaRuntimeEntry.catalog_entry_for reached initial sameFrame).authority.current = reached.next ∧
    (CallableIndexedLambdaRuntimeEntry.catalog_entry_for reached initial sameFrame).authority.ghost =
      .lambda code.descriptor.id history.ghost :=
  ⟨CallableIndexedLambdaRuntimeEntry.catalog_frame_for reached initial sameFrame,
    CallableIndexedLambdaRuntimeEntry.catalog_current_for reached initial sameFrame,
    CallableIndexedLambdaRuntimeEntry.catalog_ghost_for reached initial sameFrame⟩

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
/-- Empty arity keeps the original strict native witness. The same source
allocation and caller restoration follow from the concrete runtime body. -/
theorem empty_arguments {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store} (empty : nativeArguments = [])
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.toContext functions registry arguments before store location current,
      ∃ child bodyStore outcome after finalMap finalWorld,
      child < size ∧ EvaluationSize child reached.actual reached.store
        (code.receipt.body.rename reached.embedding) result bodyStore ∧
      reached.canonical = captured.canonical ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨reached, child, bodyStore, _, outcome, after, finalMap, finalWorld, smaller, evaluated, _, _, source, _, heaps,
    _, _, _, _, callerEntry, caller⟩ :=
    CallableIndexedLambdaRuntimeEntry.reflects_original_for captured code history body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame
      represented heaps locals reference read currentCarried allowed completed
  obtain ⟨added, length, spine⟩ := reached.spine
  have zero : code.receipt.loweredParameters.length = 0 := by simpa [empty] using represented.length.2
  have nil : added = [] := List.eq_nil_of_length_eq_zero (length.trans zero)
  exact ⟨reached, child, bodyStore, outcome, after, finalMap, finalWorld, smaller, evaluated,
    by simpa only [nil, List.nil_append] using spine, source, heaps, callerEntry, caller⟩

end Actual

section StrongerModel
private def SourceFrame (program : SourceSemantics.Program) (source : Dynamic.Value) : Prop :=
  match source with
  | .closure function => Dynamic.ClosureFrame program function
  | _ => True

private def framed {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (base : FunctionModel checked.catalog ambient) (program : SourceSemantics.Program) :
    FunctionModel checked.catalog ambient where
  Represents := fun registry mapping world type source native nativeType =>
    base.Represents registry mapping world type source native nativeType ∧ SourceFrame program source
  projection := fun related => base.projection related.1
  runtime_hasType := fun related => base.runtime_hasType related.1
  source_function := fun related => base.source_function related.1
  extend := fun related registries maps worlds =>
    ⟨base.extend related.1 registries maps worlds, related.2⟩

/-- The independent closure frame is carried in the model itself. -/
theorem frame_from_stronger_relation {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {type : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {nativeType : Core.Ty}
    (related : (framed base program).Represents registry mapping world type (.closure function) native nativeType) :
    Dynamic.ClosureFrame program function := related.2

/-- Observations of represented values survive strengthening. This supplies no
body semantics or missing closure frame to an older value representation. -/
theorem framed_observations {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {identities : Dynamic.Value → Word → Prop}
    (observed : CompatibleEquality.FunctionObservations checked.catalog base identities) :
    CompatibleEquality.FunctionObservations checked.catalog (framed base program) identities :=
  fun related => observed related.1

theorem framed_runtime_views {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    (views : FunctionRuntimeViews base) : FunctionRuntimeViews (framed base program) :=
  fun related => views related.1

/-- The weak relation cannot supply the missing independent source frame. -/
theorem missing_frame_blocks_reverse_inclusion {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {type : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {nativeType : Core.Ty}
    (related : base.Represents registry mapping world type (.closure function) native nativeType)
    (missing : ¬ Dynamic.ClosureFrame program function) :
    ¬ base.Includes (framed base program) := by
  intro includes
  exact missing (frame_from_stronger_relation (includes related))
end StrongerModel

abbrev unsized_agreement_boundary := Tests.SourceCoreCallableIndexedLambdaEntryBounds.agreement_does_not_force_strict
abbrev actual_empty_manifest := Tests.SourceCoreCallableIndexedLambdaEntryBounds.empty_manifest_actual

/-- Actual lambda, capture, fault and resume regressions are reused once.
Generic model preservation and reflection are formal consumers above. -/
def run : IO Unit := do
  Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
  IO.println "lambda model entry bounds: same function relation, original strict children, full heap and caller restore GREEN"
end Tests.SourceCoreCallableIndexedLambdaModelEntryBounds
