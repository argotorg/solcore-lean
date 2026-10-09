import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicSessionEntry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature

/-! Actual successful public startup selects the original singleton Header.
Its retained capture supplies the original call read. The named invocation
ports prove finite root completion, without replaying public startup or
bootstrap and without asserting successful public export. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicRootStart
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof RecursiveNamedCatalog
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
open SourceCoreChosenOrdinaryAcceptedPublicSessionEntry

theorem recipe_at {artifact : Artifact} {recipe : Recipe} (atRecipe : artifact.RecipeAt recipe) :
    ArtifactRecipe artifact recipe := by
  cases artifact
  exact atRecipe

theorem session_state {artifact : Artifact} {session : Session artifact}
    {world : StoreTyping} {store : Store} (atNative : session.NativeAt world store) :
    SessionState session world store := by
  cases session
  exact atNative

private theorem recipe_unique {artifact : Artifact} {left right : Recipe}
    (a : ArtifactRecipe artifact left) (b : ArtifactRecipe artifact right) : left = right := by
  cases artifact
  exact a.symm.trans b

private theorem state_unique {artifact : Artifact} {session : Session artifact}
    {leftWorld rightWorld : StoreTyping} {leftStore rightStore : Store}
    (a : SessionState session leftWorld leftStore) (b : SessionState session rightWorld rightStore) :
    leftWorld = rightWorld ∧ leftStore = rightStore := by
  cases session
  exact ⟨a.1.symm.trans b.1, a.2.symm.trans b.2⟩

/-- Singleton completeness supplies the full selected Header. Empty native
inputs follow from the actual encoder typing, not a guessed source context. -/
theorem at_header_start {compiled : SourceCoreUnifiedCompilation.Compiled}
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : SourceSemantics.Program} (header : Header compiled.indexed.ancestry values ambient.definitions program)
    (complete : RecursiveNamedCatalogNativeContexts.Complete [header])
    (inputs : header.named.inputs = [])
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {artifact : Artifact} (session : Session artifact) (atRecipe : artifact.RecipeAt recipe)
    {world : StoreTyping} {store : Store} (atNative : session.NativeAt world store)
    {key : SourceCoreCalls.Key} {boundaryFuel : Nat} {checkpoint : Checkpoint artifact}
    (accepted : session.start key [] boundaryFuel = .ok checkpoint) :
    CheckpointInitial checkpoint
      (SourceCoreCalls.call header.named.signature header.slot (LanguageResult.success .unit) Word.zero)
      (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store := by
  have compiledEq := Recipe.prepare_compiled prepared
  subst compiled
  obtain ⟨actualRecipe, root, actualWorld, actualStore, native, encodedValues, started⟩ := actual_start session accepted
  have sameRecipe : actualRecipe = recipe := recipe_unique started.recipe_eq (recipe_at atRecipe)
  subst actualRecipe
  obtain ⟨rfl, rfl⟩ := state_unique started.state (session_state atNative)
  obtain ⟨selected, selection⟩ := started.selection prepared complete
  have sameHeader : selected = header := List.mem_singleton.mp selection.member
  subst selected
  have types : root.types = [] := by
    rw [selection.shape.1, inputs]
    rfl
  have typed := started.typed
  rw [types] at typed
  have empty : native = [] := by cases typed; rfl
  have body := selection.shape.2
  rw [types] at body
  change root.body = SourceCoreCalls.call header.named.signature header.slot (LanguageResult.success .unit) Word.zero at body
  simpa only [empty, List.reverse_nil, List.nil_append, body] using started.initial

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

/-- This checkpoint and invocation use the same actual ready Session store.
The result remains the original low invocation result, including restoration. -/
structure RootAtInitial : Prop where
  accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryFuel = .ok checkpoint
  machine : CheckpointInitial checkpoint
    (SourceCoreCalls.call caller.named.signature caller.slot (LanguageResult.success .unit) Word.zero)
    (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
  invocation : SourceCoreChosenOrdinaryAcceptedPublicInvocation.InvocationAtInitial actual.fixture root inventory initial

/-- The actual catalog and prescribed capture fix the original initialized
cell and its full closure. No arbitrary value representation is inverted. -/
theorem read_at_initial :
    Evaluates (.unit :: RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
      (OptionalCell.read caller.named.signature.functionType (.var (caller.slot + 1)) Word.zero)
      (.inRight .word (.closure caller.named.signature.parameterType
        (LanguageResult.resultType caller.named.signature.resultType)
        (caller.code.rename initial.capture.embedding.lift) initial.capture.captured)) store := by
  have reference : (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled)[caller.slot]? =
      some (.cellRef (OptionalCell.cellType caller.named.signature.functionType)
        ((SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.key actual.fixture).locations caller)) := by
    simpa only [List.length_nil, Nat.zero_add] using initial.catalog.globals caller (List.mem_singleton_self caller)
  exact OptionalCell.read_success Word.zero (.var reference) initial.capture.read

/-- The independent Source body yields a budget for this actual public root
call. The original invocation and caller restoration are executed once. -/
theorem preserves_root (atRoot : RootAtInitial (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      size caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt actual.fixture root inventory initial
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, body, result⟩ :=
    atRoot.invocation.preserves size trace (Nat.le_refl size)
  have argument : Evaluates (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
      (LanguageResult.success .unit) (.inRight .word .unit) store := .inRight .unit
  have whole := SourceCoreCalls.call_success argument (read_at_initial actual root inventory initial) body
  obtain ⟨required, completes⟩ := evaluation_runStateful_complete_with_sufficient_fuel whole
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel enough => atRoot.machine.native_done_iff.mpr (completes fuel enough), result⟩

/-- Actual finite public native completion yields its strict invocation child.
Reflection retains an independent Source size and the same restored pool. -/
theorem reflects_root (atRoot : RootAtInitial (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {fuel : Nat} {value : Core.Value} {finalStore : Store}
    (done : checkpoint.NativeDone fuel value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt actual.fixture root inventory initial
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨size, evaluated⟩ := evaluation_has_size (runStateful_evaluation_sound (atRoot.machine.native_done_iff.mp done))
  have argument : Evaluates (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled) store
      (LanguageResult.success .unit) (.inRight .word .unit) store := .inRight .unit
  have reference : (RecursiveNamedCatalogPreparedInitialization.environment actual.fixture.packet.compiled)[caller.slot]? =
      some (.cellRef (OptionalCell.cellType caller.named.signature.functionType)
        ((SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.key actual.fixture).locations caller)) := by
    simpa only [List.length_nil, Nat.zero_add] using initial.catalog.globals caller (List.mem_singleton_self caller)
  obtain ⟨child, strict, body⟩ := RecursiveNamedCallBounds.call_body argument reference initial.capture.read evaluated
  exact atRoot.invocation.reflects size body (Nat.le_of_lt strict)

/-- Tie original successful startup to the genuine invocation at the same
ready Session. Selection uses both original preparation and first-find. -/
theorem at_session
    (bootstrap : BootstrapEvidence actual.fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape actual.fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata actual.fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata actual.fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt actual.fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt actual.fixture)
    (accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryFuel = .ok checkpoint) :
    ∃ completed : CompletedBootstrap actual.prepared bootstrapFuel,
    ∃ world,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture caller
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture root inventory (registry actual) faults)
      (registry actual) world completed.store,
      actual.session.NativeAt world completed.store ∧
      RootAtInitial (boundaryFuel := boundaryFuel) actual root inventory first checkpoint := by
  obtain ⟨completed, nextWorld, first, atNative, _atRegistry, invocation⟩ :=
    invocation_at_session actual root inventory bootstrap shape typing checked chosen outer
  have complete := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete actual.fixture actual.prepared bootstrap.toHeaderAt
  have inputs : caller.named.inputs = [] := by
    rw [bootstrap.toHeaderAt.named]
    exact checked.named_inputs
  have machine := at_header_start (compiled := actual.fixture.packet.compiled)
    (values := .initial actual.fixture.packet.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions actual.fixture.packet.compiled.indexed)
    (program := Program.ofChecked actual.fixture.packet.compiled.sourceProgram) caller complete inputs actual.prepared.accepted actual.session actual.recipeAt atNative accepted
  refine ⟨completed, nextWorld, first, atNative, accepted, ?_, invocation⟩
  simpa only [RecursiveNamedPublicBootstrapGlobals.environment_eq] using machine

end Tests.SourceCoreChosenOrdinaryAcceptedPublicRootStart
