import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome

/-! The same accepted public run retains genuine body exit and caller
admission inside its original root invocation. The existing static collector
and public action receipts remain inputs; this companion performs no IO. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramOutcomeWithExit
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableIndexedNamedGeneration
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
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

/-- The authentic static admission, requested result and strong root pair
belong to this same checkpoint and initial caller state. -/
structure ProgramAtWithExit : Prop where
  bootstrap : BootstrapEvidence actual.fixture caller
  stages : Staging.ProgramHasStages (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
  root : SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission.RootAtInitialWithExit
    (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint
  requested : checkpoint.ResultTypeAt .word

/-- The original program contract is a pure projection of the same root. -/
theorem ProgramAtWithExit.forget
    (meaning : ProgramAtWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint) :
    SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.ProgramAt
      (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint := by
  exact ⟨meaning.bootstrap, meaning.stages,
    SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission.RootAtInitialWithExit.forget
      actual root inventory initial checkpoint meaning.root,
    meaning.requested⟩

/-- The existing collector supplies one authentic Header and compiler root.
The strong ready-state factory is used once at the actual startup receipt. -/
theorem at_started
    (given : SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.StaticReceipt actual.fixture)
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
      ProgramAtWithExit (boundaryFuel := boundaryFuel) actual selectedRoot given.inventory first checkpoint := by
  obtain ⟨header, bootstrap⟩ := header_exists_with_bootstrap actual.fixture given.selected given.checked
  obtain ⟨selectedCompilation, selectedRoot, ⟨chosen⟩⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.at_original_root
      actual.fixture bootstrap.toHeaderAt given.shape given.body given.inventory
  obtain ⟨outer⟩ := SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.of_body actual.fixture
  obtain ⟨completed, nextWorld, first, atNative, atRoot⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission.at_session
      actual selectedRoot given.inventory checkpoint bootstrap given.shape given.typing given.checked chosen outer accepted
  have requested := SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.requested_result
    (compiled := actual.fixture.packet.compiled) header
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete actual.fixture actual.prepared bootstrap.toHeaderAt)
    actual.prepared.accepted actual.session actual.recipeAt accepted
  rw [given.typing.header_result bootstrap.toHeaderAt] at requested
  exact ⟨header, selectedCompilation, selectedRoot, nextWorld, completed.store, first, atNative,
    bootstrap, given.stages, atRoot, requested⟩

/-- Native completion retains its actual invocation child grade and the
independent Source grade while admitting the same whole-program outcome. -/
theorem native_completed_reflects_program_with_exit
    (atProgram : ProgramAtWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {fuel : Nat} {value : Core.Value} {finalStore : Store}
    (done : checkpoint.NativeDone fuel value finalStore) :
    ∃ sourceSize nativeChildSize outcome after finalMap finalWorld,
      EvaluationSize nativeChildSize (DataPatternValues.packValues ([] : List Core.Value) :: initial.capture.captured)
        store (caller.code.rename initial.capture.embedding.lift) value finalStore ∧
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
        actual.fixture root inventory initial sourceSize (some nativeChildSize)
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, nativeChildSize, outcome, after, finalMap, finalWorld, child, body, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission.reflects_root
      actual root inventory initial checkpoint atProgram.root done
  have heapTyped : Dynamic.HeapWellTyped caller.function.context ⟨[]⟩ := by
    intro cell member
    cases member
  have argumentsTyped : Dynamic.ValuesHaveTypes caller.function.context ⟨[]⟩ [] caller.types := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.types_empty actual.fixture atProgram.bootstrap.toHeaderAt]
    exact .nil
  exact ⟨sourceSize, nativeChildSize, outcome, after, finalMap, finalWorld, child, body,
    RecursiveNamedProgramOutcomeMeaning.program_from_body caller atProgram.stages heapTyped argumentsTyped body.sound,
    result⟩

/-- Independent Source completion supplies a genuine body grade and native
fuel. The original strong root producer keeps the same causal result. -/
theorem program_has_sufficient_native_fuel_with_exit
    (atProgram : ProgramAtWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after) :
    ∃ sourceSize value finalStore finalMap finalWorld required,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
        actual.fixture root inventory initial sourceSize none
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨size, body⟩ := RecursiveNamedCallBounds.BodyOutcome.has_size
    (RecursiveNamedProgramOutcomeMeaning.body_from_program caller executed)
  obtain ⟨value, finalStore, finalMap, finalWorld, required, completes, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission.preserves_root
      actual root inventory initial checkpoint atProgram.root body
  exact ⟨size, value, finalStore, finalMap, finalWorld, required, body, completes, result⟩

/-- The actual successful export identifies the same Source Word. The low
observation is only a projection; the returned result still retains its exit. -/
theorem public_succeeded_reflects_program_with_exit
    (atProgram : ProgramAtWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    {fuel : Nat} {completion : Completion actual.artifact}
    (resumed : checkpoint.ResumeAt fuel boundaryFuel (.succeeded completion)) :
    ∃ sourceSize nativeChildSize word after finalStore finalMap finalWorld,
      completion.value = .word word ∧ completion.sourceType = .word ∧
      completion.session.NativeAt (finalStore.map Core.Value.type) finalStore ∧
      EvaluationSize nativeChildSize (DataPatternValues.packValues ([] : List Core.Value) :: initial.capture.captured)
        store (caller.code.rename initial.capture.embedding.lift) (.inRight .word (.word word)) finalStore ∧
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] (.value (.word word)) after ∧
      Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ (.value (.word word)) after ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
        actual.fixture root inventory initial sourceSize (some nativeChildSize)
        (.value (.word word)) after (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨generation, native, finalStore, done, succeeded⟩ := resumed.succeeded
  obtain ⟨sourceSize, nativeChildSize, outcome, after, finalMap, finalWorld, child, body, executed, result⟩ :=
    native_completed_reflects_program_with_exit actual root inventory initial checkpoint atProgram done
  have observed := SourceCoreChosenOrdinaryAcceptedPublicResultObservation.observe
    actual.fixture root inventory initial atProgram.bootstrap
    (SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit.forget
      actual.fixture root inventory initial result)
  have decoded : ∃ payload, LanguageResult.decode? native = some (.succeeded payload) := by
    obtain ⟨_, payload, _, _, _, decoded, _⟩ := succeeded
    exact ⟨payload, decoded⟩
  obtain ⟨word, sourceEq, nativeEq⟩ :
      ∃ word, outcome = .value (.word word) ∧ native = .inRight .word (.word word) := by
    cases observed with
    | word word => exact ⟨word, rfl, rfl⟩
    | fault related =>
      obtain ⟨payload, impossible⟩ := decoded
      simp [LanguageResult.decode?] at impossible
  subst outcome
  subst native
  exact ⟨sourceSize, nativeChildSize, word, after, finalStore, finalMap, finalWorld,
    succeeded.word_value atProgram.requested, succeeded.source_type atProgram.requested,
    succeeded.native_at.2, child, body, executed, result⟩

/-- A Source Word crosses the same positive export boundary at sufficient
native fuel. The genuine Source grade and full strong result are retained. -/
theorem program_word_preserved_with_exit
    (atProgram : ProgramAtWithExit (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)
    (positive : 0 < boundaryFuel) {word : Word} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ (.value (.word word)) after) :
    ∃ sourceSize finalStore finalMap finalWorld required,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] (.value (.word word)) after ∧
      (∀ fuel, required ≤ fuel → ∀ outcome, checkpoint.ResumeAt fuel boundaryFuel outcome →
        ∃ completion, outcome = .succeeded completion ∧ completion.value = .word word) ∧
      SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
        actual.fixture root inventory initial sourceSize none
        (.value (.word word)) after (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, native, finalStore, finalMap, finalWorld, required, body, completes, result⟩ :=
    program_has_sufficient_native_fuel_with_exit actual root inventory initial checkpoint atProgram executed
  have observed := SourceCoreChosenOrdinaryAcceptedPublicResultObservation.observe
    actual.fixture root inventory initial atProgram.bootstrap
    (SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit.forget
      actual.fixture root inventory initial result)
  have nativeEq := (observed.word_iff word).mp rfl
  subst native
  exact ⟨sourceSize, finalStore, finalMap, finalWorld, required, body,
    fun fuel enough outcome resumed => resumed.word_succeeded
      (completes fuel enough) atProgram.requested positive, result⟩

/-- The existing public run's erased receipts supply one strong factory and
one reflection. No new collector, start or resume action is introduced. -/
theorem public_run_succeeded_reflects_program_with_exit
    (given : SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.PublicRun)
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
      ProgramAtWithExit (boundaryFuel := SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.boundaryBudget)
        given.actual selectedRoot given.static.inventory first given.checkpoint ∧
      given.actual.session.NativeAt firstWorld firstStore ∧
      ∃ sourceSize nativeChildSize word after finalStore finalMap finalWorld,
        completion.value = .word word ∧ completion.sourceType = .word ∧
        completion.session.NativeAt (finalStore.map Core.Value.type) finalStore ∧
        EvaluationSize nativeChildSize (DataPatternValues.packValues ([] : List Core.Value) :: first.capture.captured)
          firstStore (header.code.rename first.capture.embedding.lift) (.inRight .word (.word word)) finalStore ∧
        RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked given.actual.fixture.packet.compiled.sourceProgram)
          sourceSize header.sourceBody header.function.evidence ⟨[]⟩ [] (.value (.word word)) after ∧
        Dynamic.ProgramOutcome (Program.ofChecked given.actual.fixture.packet.compiled.sourceProgram)
          (RecursiveNamedProgramEntrySource.entry header []) ⟨[]⟩ (.value (.word word)) after ∧
        SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission.ResultAtWithExit
          given.actual.fixture selectedRoot given.static.inventory first sourceSize (some nativeChildSize)
          (.value (.word word)) after (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨header, selectedCompilation, selectedRoot, firstWorld, firstStore, first, native, atProgram⟩ :=
    at_started (faults := faults) given.actual given.checkpoint given.static given.accepted
  have resumed : given.checkpoint.ResumeAt
      SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.nativeFuel
      SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.boundaryBudget (.succeeded completion) := by
    rw [← succeeded]
    exact given.resumed
  exact ⟨header, selectedCompilation, selectedRoot, firstWorld, firstStore, first, atProgram, native,
    public_succeeded_reflects_program_with_exit
      given.actual selectedRoot given.static.inventory first given.checkpoint atProgram resumed⟩

end Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramOutcomeWithExit
