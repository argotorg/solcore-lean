import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedProgramAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestorationAdmission

/-! The original public program result retains its actual returned caller
state. Genuine Source execution supplies successful value and deep heap
typing; the saved stable rows follow the actual administrative effects.
Preservation and reflection consume the existing producers once. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt
open SourceCoreChosenOrdinaryAcceptedPublicSessionEntry

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
    registry world store)

local notation "bridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (headers := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
  (keys := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.keys fixture)

/-- The final six semantic effects and this same returned pool remain joined.
Faults retain stable rows without claiming successful value or heap typing. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Core.Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults))
    finalMap finalWorld caller.function.resultType caller.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
    finalMap finalWorld after finalStore ∧
  LocationMap.Extends [] finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved [] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
  ∃ returned : State
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.keys fixture)
      ⟨[], finalMap, finalWorld, after, finalStore,
        RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled⟩,
    Relates initial.state returned ∧
    PostAdmission bridge caller.function.context caller.function.resultType outcome returned

/-- Forgetting admission reconstructs the original transition with the same
returned witness; no separate pool is introduced. -/
theorem ResultAt.forget {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Core.Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ResultAt fixture root inventory initial outcome after value finalStore finalMap finalWorld) :
    SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt fixture root inventory initial
      outcome after value finalStore finalMap finalWorld := by
  obtain ⟨represented, heaps, maps, worlds, frame, metadata, returned, related, _post⟩ := result
  exact ⟨represented, heaps, maps, worlds, frame, metadata, returned, related⟩

/-- The actual admitted Source program and final administrative frame supply
successful typing and every stable row at the original transition witness. -/
theorem post_at_initial {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Core.Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after)
    (result : SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt fixture root inventory initial
      outcome after value finalStore finalMap finalWorld) :
    ResultAt fixture root inventory initial outcome after value finalStore finalMap finalWorld := by
  obtain ⟨represented, heaps, maps, worlds, frame, metadata, transition⟩ := result
  obtain ⟨returned, related, post⟩ :=
    CallableIndexedOwnedNamedProgramAdmission.after_program_transition bridge caller initial.state
      initial.stable executed frame transition
  exact ⟨represented, heaps, maps, worlds, frame, metadata, returned, related, post⟩

/-- A successful result is reusable Source admission at that same returned
state, with raw Source typing in the actual final heap. -/
theorem ResultAt.at_value {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    {value : Core.Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ResultAt fixture root inventory initial (.value sourceValue) after value finalStore finalMap finalWorld) :
    ∃ returned : State
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.keys fixture)
      ⟨[], finalMap, finalWorld, after, finalStore,
        RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled⟩,
      Relates initial.state returned ∧
      Dynamic.ValueHasType caller.function.context after sourceValue caller.function.resultType ∧
      Admission bridge caller.function.context returned := by
  obtain ⟨_, _, _, _, _, _, returned, related, post⟩ := result
  have admitted := post.at_value
  exact ⟨returned, related, admitted.1, admitted.2⟩

end Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission

namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedNamedGeneration
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
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
  (atProgram : SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.ProgramAt
    (boundaryFuel := boundaryFuel) actual root inventory initial checkpoint)

include atProgram

/-- Actual native completion reflects to the original program and its same
returned state, including successful Source admission and all stable rows. -/
theorem native_completed_reflects_program {fuel : Nat} {value : Core.Value} {finalStore : Store}
    (done : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after ∧
      ResultAt actual.fixture root inventory initial outcome after value finalStore finalMap finalWorld := by
  obtain ⟨outcome, after, finalMap, finalWorld, executed, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.native_completed_reflects_program
      actual root inventory initial checkpoint atProgram done
  exact ⟨outcome, after, finalMap, finalWorld, executed,
    post_at_initial actual.fixture root inventory initial executed result⟩

/-- Independent Source completion gives sufficient native fuel and admission
at the same restored caller; the two execution budgets stay independent. -/
theorem program_has_sufficient_native_fuel {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      ResultAt actual.fixture root inventory initial outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, required, completes, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.program_has_sufficient_native_fuel
      actual root inventory initial checkpoint atProgram executed
  exact ⟨value, finalStore, finalMap, finalWorld, required, completes,
    post_at_initial actual.fixture root inventory initial executed result⟩

/-- A real successful public export retains its identical Source Word, final
native store and admitted original returned caller state. -/
theorem public_succeeded_reflects_program {fuel : Nat} {completion : Completion actual.artifact}
    (resumed : checkpoint.ResumeAt fuel boundaryFuel (.succeeded completion)) :
    ∃ word after finalStore finalMap finalWorld,
      completion.value = .word word ∧ completion.sourceType = .word ∧
      completion.session.NativeAt (finalStore.map Core.Value.type) finalStore ∧
      Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ (.value (.word word)) after ∧
      ResultAt actual.fixture root inventory initial (.value (.word word)) after
        (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨word, after, finalStore, finalMap, finalWorld, exported, typed, native, executed, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.public_succeeded_reflects_program
      actual root inventory initial checkpoint atProgram resumed
  exact ⟨word, after, finalStore, finalMap, finalWorld, exported, typed, native, executed,
    post_at_initial actual.fixture root inventory initial executed result⟩

/-- Source Word preservation keeps the same actual resume receipt, positive
export budget and final returned-state admission. -/
theorem program_word_preserved (positive : 0 < boundaryFuel) {word : Word} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (Program.ofChecked actual.fixture.packet.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry caller []) ⟨[]⟩ (.value (.word word)) after) :
    ∃ finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → ∀ outcome, checkpoint.ResumeAt fuel boundaryFuel outcome →
        ∃ completion, outcome = .succeeded completion ∧ completion.value = .word word) ∧
      ResultAt actual.fixture root inventory initial (.value (.word word)) after
        (.inRight .word (.word word)) finalStore finalMap finalWorld := by
  obtain ⟨finalStore, finalMap, finalWorld, required, exports, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.program_word_preserved
      actual root inventory initial checkpoint atProgram positive executed
  exact ⟨finalStore, finalMap, finalWorld, required, exports,
    post_at_initial actual.fixture root inventory initial executed result⟩

omit atProgram

/-- The actual accepted public collector retains the same original program
result and admitted returned state without replaying startup or resume. -/
theorem public_run_succeeded_reflects_program
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
      SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.ProgramAt (boundaryFuel := SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.boundaryBudget) given.actual selectedRoot given.static.inventory first given.checkpoint ∧
      given.actual.session.NativeAt firstWorld firstStore ∧
      ∃ word after finalStore finalMap finalWorld,
        completion.value = .word word ∧ completion.sourceType = .word ∧
        completion.session.NativeAt (finalStore.map Core.Value.type) finalStore ∧
        Dynamic.ProgramOutcome (Program.ofChecked given.actual.fixture.packet.compiled.sourceProgram)
          (RecursiveNamedProgramEntrySource.entry header []) ⟨[]⟩ (.value (.word word)) after ∧
        ResultAt given.actual.fixture selectedRoot
          given.static.inventory first (.value (.word word)) after (.inRight .word (.word word))
          finalStore finalMap finalWorld := by
  obtain ⟨header, selectedCompilation, selectedRoot, firstWorld, firstStore, first, atProgram, native,
    word, after, finalStore, finalMap, finalWorld, exported, typed, finalNative, executed, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome.PublicRun.succeeded_reflects_program
      given faults succeeded
  exact ⟨header, selectedCompilation, selectedRoot, firstWorld, firstStore, first, atProgram, native,
    word, after, finalStore, finalMap, finalWorld, exported, typed, finalNative, executed,
    post_at_initial given.actual.fixture selectedRoot given.static.inventory first executed result⟩

end Tests.SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission
