import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicRootStart
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission

/-! The actual ready Session supplies one strong initial invocation pair.
The public root call keeps that pair's causal body exit and caller admission,
with independent Source and native child grades. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof RecursiveNamedCatalog
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
open SourceCoreChosenOrdinaryAcceptedPublicSessionEntry

variable (actual : PublicSessionFixture) {caller : ActualHeader actual.fixture}
  {compilation : Compilation actual.fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics actual.fixture.packet.compiled actual.fixture.packet.diagnostics) actual.fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root actual.fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory actual.fixture)
  {faults : FunctionCalls.FaultRep} {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory (registry actual) faults)
    (registry actual) world store)
  {boundaryFuel : Nat} (checkpoint : Checkpoint actual.artifact)

/-- The actual startup, native machine and strong invocation share one initial
store and capture. The legacy root is only a projection of this same pair. -/
structure RootAtInitialWithExit : Prop where
  accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryFuel = .ok checkpoint
  machine : CheckpointInitial checkpoint
    (SourceCoreCalls.call caller.named.signature caller.slot (LanguageResult.success .unit) Word.zero)
    (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
  invocation : SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.InvocationAtInitialWithExit
    actual.fixture root inventory initial

theorem RootAtInitialWithExit.forget
    (meaning : RootAtInitialWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint) :
    SourceCoreChosenOrdinaryAcceptedPublicRootStart.RootAtInitial
      (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint := by
  exact ⟨meaning.accepted, meaning.machine,
    SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.InvocationAtInitialWithExit.forget
      actual.fixture root inventory initial meaning.invocation⟩

/-- Source completion invokes the strong body pair once, then closes the
original public call. The resulting native fuel is independent of Source size. -/
theorem preserves_root
    (atRoot : RootAtInitialWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      size caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
        actual.fixture root inventory initial size none
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, body, result⟩ :=
    atRoot.invocation.preserves size trace (Nat.le_refl size)
  have argument : Evaluates (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
      (LanguageResult.success .unit) (.inRight .word .unit) store := .inRight .unit
  have whole := SourceCoreCalls.call_success argument
    (SourceCoreChosenOrdinaryAcceptedPublicRootStart.read_at_initial actual root inventory initial) body
  obtain ⟨required, completes⟩ := evaluation_runStateful_complete_with_sufficient_fuel whole
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel enough => atRoot.machine.native_done_iff.mpr (completes fuel enough), result⟩

/-- The real completed root exposes its strict native invocation child. That
child and its independent Source grade remain explicit in the causal receipt. -/
theorem reflects_root
    (atRoot : RootAtInitialWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {fuel : Nat} {value : Core.Value} {finalStore : Store}
    (done : checkpoint.NativeDone fuel value finalStore) :
    ∃ sourceSize nativeChildSize outcome after finalMap finalWorld,
      EvaluationSize nativeChildSize (DataPatternValues.packValues ([] : List Core.Value) :: initial.capture.captured)
        store (caller.code.rename initial.capture.embedding.lift) value finalStore ∧
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
        actual.fixture root inventory initial sourceSize (some nativeChildSize)
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨size, evaluated⟩ :=
    evaluation_has_size (runStateful_evaluation_sound (atRoot.machine.native_done_iff.mp done))
  have argument : Evaluates (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
      (LanguageResult.success .unit) (.inRight .word .unit) store := .inRight .unit
  have reference : (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled)[caller.slot]? =
      some (.cellRef (OptionalCell.cellType caller.named.signature.functionType)
        ((SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.key actual.fixture).locations caller)) := by
    simpa only [List.length_nil, Nat.zero_add] using initial.catalog.globals caller (List.mem_singleton_self caller)
  obtain ⟨child, strict, body⟩ :=
    RecursiveNamedCallBounds.call_body argument reference initial.capture.read evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    atRoot.invocation.reflects size body (Nat.le_of_lt strict)
  exact ⟨sourceSize, child, outcome, after, finalMap, finalWorld, body, trace, result⟩

/-- One proof inversion of the actual ready bootstrap feeds one original
initial-state factory. The strong pair belongs to that exact ready Session. -/
theorem invocation_at_session
    (bootstrap : BootstrapEvidence actual.fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape actual.fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata actual.fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata actual.fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt actual.fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt actual.fixture) :
    ∃ completed : CompletedBootstrap actual.prepared bootstrapFuel,
    ∃ nextWorld,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory (registry actual) faults)
      (registry actual) nextWorld completed.store,
      actual.session.NativeAt nextWorld completed.store ∧ actual.session.RegistryAt (registry actual) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.InvocationAtInitialWithExit
        actual.fixture root inventory first := by
  obtain ⟨completed, booted⟩ := completed_at_ready actual
  have extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial actual.fixture.packet.compiled.compatible.checked).registry
      (registry actual) := SourceCoreRawMetadata.Extends.refl _
  obtain ⟨nextWorld, first, invocation⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.at_completed actual.fixture root inventory
      actual.prepared bootstrap shape typing checked chosen outer extension completed
  have sameWorld : nextWorld = completed.store.map Core.Value.type := first.heaps.runtime_hasTypes.world_eq
  have atNative : actual.session.NativeAt nextWorld completed.store := by
    rw [sameWorld]
    exact booted.native_at
  have atRegistry : actual.session.RegistryAt (registry actual) := by
    have observed := booted.registry_at actual.initial
    simpa only [registry, compiled_eq actual.prepared] using observed
  exact ⟨completed, nextWorld, first, atNative, atRegistry, invocation⟩
/-- The actual accepted startup and one strong ready-state factory construct
the original root machine together, without replaying startup or invocation. -/
theorem at_session
    (bootstrap : BootstrapEvidence actual.fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape actual.fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata actual.fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata actual.fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt actual.fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt actual.fixture)
    (accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryFuel = .ok checkpoint) :
    ∃ completed : CompletedBootstrap actual.prepared bootstrapFuel,
    ∃ nextWorld,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory (registry actual) faults)
      (registry actual) nextWorld completed.store,
      actual.session.NativeAt nextWorld completed.store ∧
      RootAtInitialWithExit (boundaryFuel := boundaryFuel) actual root inventory first checkpoint := by
  obtain ⟨completed, nextWorld, first, atNative, _atRegistry, invocation⟩ :=
    invocation_at_session actual root inventory bootstrap shape typing checked chosen outer
  have complete := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete
    actual.fixture actual.prepared bootstrap.toHeaderAt
  have inputs : caller.named.inputs = [] := by
    rw [bootstrap.toHeaderAt.named]
    exact checked.named_inputs
  have machine := SourceCoreChosenOrdinaryAcceptedPublicRootStart.at_header_start
    (compiled := actual.fixture.packet.compiled)
    (values := .initial actual.fixture.packet.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions actual.fixture.packet.compiled.indexed)
    (program := Program.ofChecked actual.fixture.packet.compiled.sourceProgram) caller complete inputs
    actual.prepared.accepted actual.session actual.recipeAt atNative accepted
  refine ⟨completed, nextWorld, first, atNative, accepted, ?_, invocation⟩
  simpa only [RecursiveNamedPublicBootstrapGlobals.environment_eq] using machine

end Tests.SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission
