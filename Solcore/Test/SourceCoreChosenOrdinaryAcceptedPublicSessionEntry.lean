import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicInvocation
import Solcore.Frontend.SourceCoreIndexedSession

/-! The actual public artifact and fresh bootstrap produce one ready Session.
Its retained completion supplies the same initial store for the proved body.
The native machine is executed only by the original public resume action. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicSessionEntry
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt

/-- The opaque public objects and erased receipts all belong to this one run. -/
structure PublicSessionFixture where
  fixture : AcceptedFixture
  prepared : PublicRecipeReceipt fixture
  artifact : SourceCoreIndexedSession.Artifact
  recipeAt : artifact.RecipeAt prepared.recipe
  checkpoint : SourceCoreIndexedSession.Bootstrap artifact
  initial : checkpoint.InitialAt prepared.recipe {}
  session : SourceCoreIndexedSession.Session artifact
  ready : checkpoint.resume bootstrapFuel = .ready session

/-- The original fixture and Recipe preparation run once. The receipt-bearing
public actions mint one artifact and checkpoint, then resume that checkpoint
once. Original validation errors and fuel exhaustion remain observable. -/
def accepted_public_session_fixture : IO (Except String PublicSessionFixture) := do
  match SourceCoreChosenOrdinaryAcceptedFixture.acceptedFixture with
  | .error error => pure (.error error)
  | .ok fixture =>
    match prepare_public fixture with
    | .error error => pure (.error error)
    | .ok prepared =>
      let opened ← prepared.recipe.openWithReceipt
      let started ← opened.val.bootstrapFreshWithReceipt prepared.recipe opened.property
      match ready : started.val.resume bootstrapFuel with
      | .ready session =>
        pure (.ok ⟨fixture, prepared, opened.val, opened.property,
          started.val, started.property, session, ready⟩)
      | .error error => pure (.error s!"public bootstrap validation: {reprStr error}")
      | .outOfFuel _ => pure (.error s!"public bootstrap exhausted fuel {bootstrapFuel}")

/-- Invert the retained ready equation only in a proof. The original completion
becomes the existing CompletedBootstrap; no store accessor or second run is used. -/
theorem completed_at_ready (actual : PublicSessionFixture) :
    ∃ completed : CompletedBootstrap actual.prepared bootstrapFuel,
      actual.session.BootstrappedFrom actual.checkpoint completed.store := by
  obtain ⟨value, store, done, _success, booted⟩ :=
    SourceCoreIndexedSession.Bootstrap.resume_ready_receipt actual.checkpoint bootstrapFuel actual.ready
  exact ⟨⟨value, store, actual.initial.native_done done⟩, booted⟩

def registry (actual : PublicSessionFixture) : SourceCoreRawMetadata.Registry :=
  actual.fixture.packet.compiled.compatible.checked.staticRegistry

theorem registry_at (actual : PublicSessionFixture) : actual.session.RegistryAt (registry actual) := by
  obtain ⟨completed, booted⟩ := completed_at_ready actual
  have atRegistry := booted.registry_at actual.initial
  simpa only [registry, compiled_eq actual.prepared] using atRegistry

theorem inert_prefix (actual : PublicSessionFixture) : actual.session.inertPrefix = {} := by
  obtain ⟨completed, booted⟩ := completed_at_ready actual
  exact booted.inert_prefix actual.initial

theorem function_count (actual : PublicSessionFixture) : actual.session.functionCount = 0 := by
  obtain ⟨completed, booted⟩ := completed_at_ready actual
  exact booted.function_count

variable (actual : PublicSessionFixture) {caller : ActualHeader actual.fixture}
  {compilation : Compilation actual.fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics actual.fixture.packet.compiled actual.fixture.packet.diagnostics)
    actual.fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root actual.fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory actual.fixture)
  {faults : FunctionCalls.FaultRep}

/-- The real ready Session and full body meaning share the original initialized
store and its unique native world. All Source/compiler facts remain genuine;
the Source body law and parameter receipt are conclusions. -/
theorem body_at_session
    (bootstrap : BootstrapEvidence actual.fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape actual.fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata actual.fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata actual.fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt actual.fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt actual.fixture) :
    ∃ completed : CompletedBootstrap actual.prepared bootstrapFuel,
    ∃ world,
    ∃ initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
        (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions actual.fixture root inventory
          (registry actual) faults) (registry actual) world completed.store,
    ∃ receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry actual)
        (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions actual.fixture root inventory
          (registry actual) faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner actual.fixture) initial.state caller [],
      actual.session.NativeAt world completed.store ∧ actual.session.RegistryAt (registry actual) ∧
      SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.BodyAtReceipt
        actual.fixture root inventory initial receipt := by
  obtain ⟨completed, booted⟩ := completed_at_ready actual
  have extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial actual.fixture.packet.compiled.compatible.checked).registry
      (registry actual) := SourceCoreRawMetadata.Extends.refl _
  obtain ⟨world, initial, receipt, body⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.at_completed actual.fixture root inventory
      actual.prepared completed bootstrap shape typing checked chosen outer extension
  have sameWorld : world = completed.store.map Core.Value.type := initial.heaps.runtime_hasTypes.world_eq
  have atNative : actual.session.NativeAt world completed.store := by
    rw [sameWorld]
    exact booted.native_at
  exact ⟨completed, world, initial, receipt, atNative, registry_at actual, body⟩

/-- The original named invocation and caller restoration use the same actual
ready Session's initialized store. The low invocation result keeps its full
returned pool and cumulative effects; stronger post admission is separate. -/
theorem invocation_at_session
    (bootstrap : BootstrapEvidence actual.fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape actual.fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata actual.fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata actual.fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt actual.fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt actual.fixture) :
    ∃ completed : CompletedBootstrap actual.prepared bootstrapFuel,
    ∃ world,
    ∃ initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory
          (registry actual) faults) (registry actual) world completed.store,
      actual.session.NativeAt world completed.store ∧ actual.session.RegistryAt (registry actual) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.InvocationAtInitial
        actual.fixture root inventory initial := by
  obtain ⟨completed, booted⟩ := completed_at_ready actual
  have extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial actual.fixture.packet.compiled.compatible.checked).registry
      (registry actual) := SourceCoreRawMetadata.Extends.refl _
  obtain ⟨world, initial, invocation⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicInvocation.at_completed actual.fixture root inventory
      actual.prepared bootstrap shape typing checked chosen outer extension completed
  have sameWorld : world = completed.store.map Core.Value.type := initial.heaps.runtime_hasTypes.world_eq
  have atNative : actual.session.NativeAt world completed.store := by
    rw [sameWorld]
    exact booted.native_at
  exact ⟨completed, world, initial, atNative, registry_at actual, invocation⟩

/-- Exercises actual public readiness and its installed native globals. -/
def run : IO Unit := do
  match ← accepted_public_session_fixture with
  | .error error => throw (IO.userError error)
  | .ok actual =>
    unless actual.session.heapSize == 2 && actual.session.functionCount == 0 &&
        actual.session.installedGlobalsPresent do
      throw (IO.userError "the actual ready Session has invalid initial cells or globals")
    IO.println s!"accepted public Session: one artifact, one fresh checkpoint, one resume at fuel {bootstrapFuel}; ready with {actual.session.heapSize} native cells"

end Tests.SourceCoreChosenOrdinaryAcceptedPublicSessionEntry
