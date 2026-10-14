import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodInvocationEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
import Solcore.SourceSemantics.CoreLowering.RecursiveStageMeaning
import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! Staged method invocation enters the actual marked parameter prefix and
restores the caller from the body's reached pool. Both callbacks receive the
real complete cache and slot layout, and preserve semantic and stage faults. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodInvocationLifting
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodInvocationBounds (ParameterEntry)
open CallableIndexedOwnedPreparedStagedMethodInvocationEntries
open SelectedCompilationStageBodyLiftBounds
open Staging.Recursive.Lifting (Adapted)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Expr} (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry}
  (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt generation
    (.initial compiled.compatible.checked) sourceBody dictionary)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed generation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world named.inputs arguments payloads)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (sameFrame : installed.frameLocation = owner.key.frameLocation)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)


variable {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] installed.canonical)

def LiftBodyAt (budget : Nat)
    {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body)
    (_reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) : Prop :=
  ∀ {size finalContext bodyOutcome after},
    RecursiveNamedCallBounds.FunctionOutcome program size sourceAt.context child.evidence child.source entry.environment
      entry.heap generation.statements finalContext bodyOutcome after →
    size < budget →
    BodyLift program stages true child sourceAt.context entry.environment entry.heap
      generation.statements finalContext bodyOutcome after

def LiftContinuation (budget : Nat) : Prop :=
  ∀ (originId : Word) (index : Int) (metadata : MetadataState)
    (_selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named named.signature.key) = some originId)
    (_history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named originId) (some metadata))
    (_emitted : generation.output = withFrame (.var (compiled.indexed.base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) generation.parameterCode)
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) sourceAt.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body)
    (added : Environment), added.length = named.inputs.length →
    entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical →
  ∀ (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
    Relates caller reached →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled entry.mapping entry.store →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) entry.canonical →
    LiftBodyAt (stages := stages) (child := child)
      generation sourceAt functions budget entry reached

/-- The result retains the actual allocated Source frame and the complete
body derivation. An earlier stage rejection carries its own reached heap. -/
def MethodLift (arguments : List Dynamic.Value) (before : Dynamic.Heap)
    (plain : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ environment bound finalContext staged result reached,
    Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound ∧
    Staging.Recursive.StatementsIn program stages true child sourceAt.context environment bound
      generation.statements finalContext staged reached ∧
    Staging.Recursive.BodyResult sourceBody.resultType staged result ∧
    Adapted plain after result reached

include sourceAt installed represented sameFrame heaps physical slots in
/-- The original body trace enters the exact installed parameter state before
using the internally supplied selected-body lift. -/
theorem lifts_invocation (budget : Nat)
    (selected : stages.Closure (methodFunction generation sourceBody dictionary) child)
    (bodyMeaning : LiftContinuation (registry := registry) (program := program) (headers := headers) (keys := keys)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) generation sourceAt functions installed budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size sourceBody dictionary before arguments outcome after)
    (within : size ≤ budget) :
    MethodLift (program := program) (stages := stages) (child := child) generation sourceAt arguments before outcome after := by
  have parameters : MonoBindersExtend (methodFunction generation sourceBody dictionary).source.owner
      (methodFunction generation sourceBody dictionary).context (methodFunction generation sourceBody dictionary).parameters
      sourceAt.types sourceAt.context := by
    simpa only [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] using sourceAt.extended
  have arity : (methodFunction generation sourceBody dictionary).parameters.length = arguments.length := by
    rw [sourceAt.frame.parameters, sourceAt.parameters, List.length_map]
    exact represented.length.1
  obtain ⟨bodySize, environment, bound, allocated, sourceTrace, strict⟩ :=
    RecursiveNamedCallBounds.body_trace_of_fields sourceAt.frame.source sourceAt.frame.context
      sourceAt.frame.parameters sourceAt.frame.result sourceAt.frame.roots parameters arity trace
  obtain ⟨finalContext, control, plainBody, exit⟩ := SelectedCompilationStageNamedInvocationLifting.body_control sourceTrace
  obtain ⟨originId, index, metadata, owned, history, emitted, entry, added, length, spine, parameterState, parameterRelated⟩ :=
    parameters_with_state generation sourceAt functions installed represented owner caller sameFrame heaps
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at plainBody
  let physicalEntry := CallableIndexedOwnedPhysicalCanonicalState.of_parameter_spine physical
    (by
      have same : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
        (caller.rows owner.position).frame_eq
      simpa only [same] using (caller.rows owner.position).authority.frame.read)
    (.state index) entry.frame parameterState slots (DataPatternValues.packValues payloads)
    (by simpa only [List.length_map, List.length_reverse] using length) spine
  obtain ⟨lastContext, staged, reached, bodyTrace, adapted⟩ :=
    bodyMeaning originId index metadata owned history emitted entry added length spine parameterState parameterRelated
      physicalEntry.physical physicalEntry.base.property
      (by simpa only [stages.source selected, stages.evidence selected, methodFunction, CallableCoercionMethodFrame.view] using plainBody)
      (Nat.lt_of_lt_of_le strict within)
  obtain ⟨result, converted, resultAdapted⟩ := adapted.exit (sourceAt.frame.result ▸ exit)
  exact ⟨entry.environment, entry.heap, lastContext, staged, result, reached,
    sourceAt.frame.parameters ▸ entry.allocation, bodyTrace, converted, resultAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodInvocationLifting
