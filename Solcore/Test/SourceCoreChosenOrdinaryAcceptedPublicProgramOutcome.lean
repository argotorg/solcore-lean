import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicRootStart
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicResultObservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramOutcomeMeaning

/-! The actual public run and the original admitted Source program share one
accepted fixture. Static checks retain equations on that fixture; startup and
resume run once. Completed results preserve the full invocation correspondence,
and a successful public export returns the same Word as the Source program. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedNamedGeneration
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
open SourceCoreChosenOrdinaryAcceptedPublicSessionEntry

/-- Every receipt concerns the same unchanged original checked program. -/
structure StaticReceipt (fixture : AcceptedFixture) where
  selected : OriginalSelection fixture.packet
  checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet
  shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture
  typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture
  body : SourceCoreChosenOrdinaryAcceptedBodyMetadata.Receipt fixture.packet fixture.graph
  inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture
  catalog : SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission.OriginalCatalog fixture.packet

def staticReceipt (fixture : AcceptedFixture) : Except String (StaticReceipt fixture) := do
  let selected ← originalSelection fixture.packet
  let checked ← SourceCoreChosenOrdinaryAcceptedHeader.metadata fixture.packet
  let shape ← SourceCoreChosenOrdinaryAcceptedTyping.shape fixture
  let typing ← SourceCoreChosenOrdinaryAcceptedOuterTyping.metadata fixture
  let body ← SourceCoreChosenOrdinaryAcceptedBodyMetadata.receipt fixture.packet fixture.graph
  let inventory ← SourceCoreChosenOrdinaryAcceptedStaticInventory.inventory fixture
  let catalog ← SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission.originalCatalog fixture.packet
  pure ⟨selected, checked.down, shape, typing.down, body.down, inventory.down, catalog.down⟩

theorem StaticReceipt.stages {fixture : AcceptedFixture} (given : StaticReceipt fixture) :
    Staging.ProgramHasStages (Program.ofChecked fixture.packet.compiled.sourceProgram) :=
  SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission.program_has_stages
    given.catalog given.selected given.checked given.shape given.typing

private theorem recipe_unique {artifact : Artifact} {left right : Recipe}
    (a : ArtifactRecipe artifact left) (b : ArtifactRecipe artifact right) : left = right := by
  cases artifact
  exact a.symm.trans b

/-- The selected raw Source result determines the original checkpoint request. -/
theorem requested_result {compiled : SourceCoreUnifiedCompilation.Compiled}
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : SourceSemantics.Program} (header : Header compiled.indexed.ancestry values ambient.definitions program)
    (complete : RecursiveNamedCatalogNativeContexts.Complete [header])
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {artifact : Artifact} (session : Session artifact) (atRecipe : artifact.RecipeAt recipe)
    {key : SourceCoreCalls.Key} {boundaryFuel : Nat} {checkpoint : Checkpoint artifact}
    (accepted : session.start key [] boundaryFuel = .ok checkpoint) :
    checkpoint.ResultTypeAt header.function.resultType := by
  have compiledEq := Recipe.prepare_compiled prepared
  subst compiled
  obtain ⟨actualRecipe, root, world, store, native, encoded, started⟩ := actual_start session accepted
  have sameRecipe : actualRecipe = recipe :=
    recipe_unique started.recipe_eq (SourceCoreChosenOrdinaryAcceptedPublicRootStart.recipe_at atRecipe)
  subst actualRecipe
  obtain ⟨selected, selection⟩ := started.selection prepared complete
  have sameHeader : selected = header := List.mem_singleton.mp selection.member
  subst selected
  have result := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selection).2
  simpa only [result] using started.original.result_type_at atRecipe started.selected

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

/-- Source admission, actual startup and the full invocation use one run. -/
structure ProgramAt : Prop where
  bootstrap : BootstrapEvidence actual.fixture caller
  stages : Staging.ProgramHasStages (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
  root : SourceCoreChosenOrdinaryAcceptedPublicRootStart.RootAtInitial
    (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint
  requested : checkpoint.ResultTypeAt .word

/-- The original static receipts construct admission and body meaning as
conclusions at the actual accepted checkpoint, without evaluating Source. -/
theorem at_started (given : StaticReceipt actual.fixture)
    (accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryFuel = .ok checkpoint) :
    ∃ header : ActualHeader actual.fixture,
    ∃ selectedCompilation : Compilation actual.fixture.packet.compiled.indexed header.named
      (effectiveDiagnostics actual.fixture.packet.compiled actual.fixture.packet.diagnostics) actual.fixture.packet.namedCode,
    ∃ selectedRoot : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root actual.fixture header selectedCompilation,
    ∃ nextWorld nextStore,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt actual.fixture header
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions actual.fixture selectedRoot given.inventory (registry actual) faults)
      (registry actual) nextWorld nextStore,
      actual.session.NativeAt nextWorld nextStore ∧
      ProgramAt (boundaryFuel := boundaryFuel) actual selectedRoot given.inventory first checkpoint := by
  obtain ⟨header, bootstrap⟩ := header_exists_with_bootstrap actual.fixture given.selected given.checked
  obtain ⟨selectedCompilation, selectedRoot, ⟨chosen⟩⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.at_original_root
      actual.fixture bootstrap.toHeaderAt given.shape given.body given.inventory
  obtain ⟨outer⟩ := SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.of_body actual.fixture
  obtain ⟨completed, nextWorld, first, atNative, atRoot⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicRootStart.at_session actual selectedRoot given.inventory checkpoint
      bootstrap given.shape given.typing given.checked chosen outer accepted
  have requested := requested_result (compiled := actual.fixture.packet.compiled) header
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete actual.fixture actual.prepared bootstrap.toHeaderAt)
    actual.prepared.accepted actual.session actual.recipeAt accepted
  rw [given.typing.header_result bootstrap.toHeaderAt] at requested
  exact ⟨header, selectedCompilation, selectedRoot, nextWorld, completed.store, first, atNative,
    bootstrap, given.stages, atRoot, requested⟩

/-- Reflection retains the original admitted whole-program outcome, final
heap, restored owned pool and cumulative effects of this finite execution. -/
theorem native_completed_reflects_program
    (atProgram : ProgramAt (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {fuel : Nat} {value : Core.Value} {finalStore : Store}
    (done : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt actual.fixture root inventory initial
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨size, outcome, after, finalMap, finalWorld, body, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicRootStart.reflects_root actual root inventory initial checkpoint atProgram.root done
  have heapTyped : Dynamic.HeapWellTyped caller.function.context ⟨[]⟩ := by intro cell member; cases member
  have argumentsTyped : Dynamic.ValuesHaveTypes caller.function.context ⟨[]⟩ [] caller.types := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.types_empty actual.fixture atProgram.bootstrap.toHeaderAt]
    exact .nil
  exact ⟨outcome, after, finalMap, finalWorld,
    RecursiveNamedProgramOutcomeMeaning.program_from_body caller atProgram.stages heapTyped argumentsTyped body.sound, result⟩

/-- Independent Source completion yields sufficient native fuel for the same
checkpoint. The Source and Core budgets need not be equal. -/
theorem program_has_sufficient_native_fuel
    (atProgram : ProgramAt (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt actual.fixture root inventory initial
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨size, body⟩ := RecursiveNamedCallBounds.BodyOutcome.has_size
    (RecursiveNamedProgramOutcomeMeaning.body_from_program caller executed)
  exact SourceCoreChosenOrdinaryAcceptedPublicRootStart.preserves_root
    actual root inventory initial checkpoint atProgram.root body

/-- Actual successful public export reflects to the identical Source Word.
Export acceptance is read from the retained completion, not inferred from
native typing. The same final store and full invocation relation remain. -/
theorem public_succeeded_reflects_program
    (atProgram : ProgramAt (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {fuel : Nat} {completion : Completion actual.artifact}
    (resumed : checkpoint.ResumeAt fuel boundaryFuel (.succeeded completion)) :
    ∃ word after finalStore finalMap finalWorld,
      completion.value = .word word ∧ completion.sourceType = .word ∧
      completion.session.NativeAt (finalStore.map Core.Value.type) finalStore ∧
      Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ (.value (.word word)) after ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt actual.fixture root inventory initial
        (.value (.word word)) after (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨generation, native, finalStore, done, succeeded⟩ := resumed.succeeded
  obtain ⟨outcome, after, finalMap, finalWorld, executed, result⟩ :=
    native_completed_reflects_program actual root inventory initial checkpoint atProgram done
  have observed := SourceCoreChosenOrdinaryAcceptedPublicResultObservation.observe
    actual.fixture root inventory initial atProgram.bootstrap result
  have decoded : ∃ payload, LanguageResult.decode? native = some (.succeeded payload) := by
    obtain ⟨_, payload, _, _, _, decoded, _⟩ := succeeded
    exact ⟨payload, decoded⟩
  obtain ⟨word, sourceEq, nativeEq⟩ :
      ∃ word, outcome = .value (.word word) ∧ native = .inRight .word (.word word) := by
    cases observed with
    | word word => exact ⟨word, rfl, rfl⟩
    | fault related => obtain ⟨payload, impossible⟩ := decoded; simp [LanguageResult.decode?] at impossible
  subst outcome
  subst native
  exact ⟨word, after, finalStore, finalMap, finalWorld,
    succeeded.word_value atProgram.requested, succeeded.source_type atProgram.requested,
    succeeded.native_at.2, executed, result⟩

/-- A Source Word result successfully crosses the same public boundary at
sufficient native fuel and a positive export budget. Resume is not replayed. -/
theorem program_word_preserved
    (atProgram : ProgramAt (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    (positive : 0 < boundaryFuel) {word : Word} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ (.value (.word word)) after) :
    ∃ finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → ∀ outcome, checkpoint.ResumeAt fuel boundaryFuel outcome →
        ∃ completion, outcome = .succeeded completion ∧ completion.value = .word word) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt actual.fixture root inventory initial
        (.value (.word word)) after (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨native, finalStore, finalMap, finalWorld, required, completes, result⟩ :=
    program_has_sufficient_native_fuel actual root inventory initial checkpoint atProgram executed
  have observed := SourceCoreChosenOrdinaryAcceptedPublicResultObservation.observe
    actual.fixture root inventory initial atProgram.bootstrap result
  have nativeEq := (observed.word_iff word).mp rfl
  subst native
  exact ⟨finalStore, finalMap, finalWorld, required,
    fun fuel enough outcome resumed => resumed.word_succeeded (completes fuel enough) atProgram.requested positive, result⟩

def nativeFuel : Nat := 10000
def boundaryBudget : Nat := 1024

/-- These values and erased receipts belong to one actual public action chain. -/
structure PublicRun where
  actual : PublicSessionFixture
  static : StaticReceipt actual.fixture
  checkpoint : Checkpoint actual.artifact
  accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryBudget = .ok checkpoint
  outcome : Outcome actual.artifact
  resumed : checkpoint.ResumeAt nativeFuel boundaryBudget outcome

def accepted_public_program_run : IO (Except String PublicRun) := do
  match ← accepted_public_session_fixture with
  | .error error => pure (.error error)
  | .ok actual =>
    match staticReceipt actual.fixture with
    | .error error => pure (.error error)
    | .ok static =>
      match accepted : actual.session.start actual.fixture.packet.named.signature.key [] boundaryBudget with
      | .error error => pure (.error s!"public root validation: {reprStr error}")
      | .ok checkpoint =>
        let resumed ← checkpoint.resumeWithReceipt nativeFuel boundaryBudget
        pure (.ok ⟨actual, static, checkpoint, accepted, resumed.val, resumed.property⟩)

/-- A success retained by the actual public collector has genuine original
Source admission and the same full returned invocation correspondence. -/
theorem PublicRun.succeeded_reflects_program (given : PublicRun)
    (faults : FunctionCalls.FaultRep) {completion : Completion given.actual.artifact}
    (succeeded : given.outcome = .succeeded completion) :
    ∃ header : ActualHeader given.actual.fixture,
    ∃ selectedCompilation : Compilation given.actual.fixture.packet.compiled.indexed header.named
      (effectiveDiagnostics given.actual.fixture.packet.compiled given.actual.fixture.packet.diagnostics)
      given.actual.fixture.packet.namedCode,
    ∃ selectedRoot : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root
      given.actual.fixture header selectedCompilation,
    ∃ firstWorld firstStore,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt given.actual.fixture header
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions given.actual.fixture selectedRoot
        given.static.inventory (registry given.actual) faults)
      (registry given.actual) firstWorld firstStore,
      ProgramAt (boundaryFuel := boundaryBudget) given.actual selectedRoot given.static.inventory first given.checkpoint ∧
      given.actual.session.NativeAt firstWorld firstStore ∧
      ∃ word after finalStore finalMap finalWorld,
        completion.value = .word word ∧ completion.sourceType = .word ∧
        completion.session.NativeAt (finalStore.map Core.Value.type) finalStore ∧
        Dynamic.ProgramOutcome (Program.ofChecked given.actual.fixture.packet.compiled.sourceProgram)
          (RecursiveNamedProgramEntrySource.entry header []) ⟨[]⟩ (.value (.word word)) after ∧
        SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt given.actual.fixture selectedRoot
          given.static.inventory first (.value (.word word)) after (.inRight .word (.word word))
          finalStore finalMap finalWorld := by
  obtain ⟨header, selectedCompilation, selectedRoot, firstWorld, firstStore, first, native, atProgram⟩ :=
    at_started (faults := faults) given.actual given.checkpoint given.static given.accepted
  have resumed : given.checkpoint.ResumeAt nativeFuel boundaryBudget (.succeeded completion) := by
    rw [← succeeded]
    exact given.resumed
  exact ⟨header, selectedCompilation, selectedRoot, firstWorld, firstStore, first, atProgram, native,
    public_succeeded_reflects_program given.actual selectedRoot given.static.inventory first
      given.checkpoint atProgram resumed⟩

/-- Measure original catalog acceptance and the actual public Word result. -/
def run : IO Unit := do
  match ← accepted_public_program_run with
  | .error error => throw (IO.userError error)
  | .ok actual =>
    match actual.outcome with
    | .succeeded completion =>
      match completion.value with
      | .word word =>
        unless word == Word.ofNatModulo 7 && completion.sourceType == TypeSystem.Ty.word &&
            completion.session.functionCount == 0 && completion.session.installedGlobalsPresent do
          throw (IO.userError "the actual public program returned a different Word, type or session")
        IO.println s!"accepted original Source program: public Word 7 at native fuel {nativeFuel}; original catalog accepted, one root start and one resume"
      | _ => throw (IO.userError "the actual public program returned a non-Word value")
    | .failed reason _ => throw (IO.userError s!"public program language failure: {reason.toNat}")
    | .exportError error _ => throw (IO.userError s!"public program export validation: {reprStr error}")
    | .outOfFuel _ => throw (IO.userError s!"public program exhausted native fuel {nativeFuel}")

end Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome
