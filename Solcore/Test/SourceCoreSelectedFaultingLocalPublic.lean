import Solcore.Test.SourceCoreSelectedFaultingLocalSelectedSource
import Solcore.Test.SourceCoreSelectedFaultingLocalPublicStart
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialStart
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureForward

/-! A genuine absent read follows generalized materialization and ordinary
allocation. Independent Source failure is connected before public resume;
the returned failed session retains the reached descriptor heap and history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.invocation (selected : SelectedInventory fixture row) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar fixture.original.recipe.compiled.indexed.base.plan
        selected.packet.header.named.signature.key = .ok sidecar ∧
      (SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).Closure
        selected.packet.header.function (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) := by
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts selected.rows).receipts
      selected.packet.header (by exact List.mem_cons_self)
  obtain ⟨descriptor⟩ := SelectedCompilationCertifiedPublicSession.header_descriptor selected.packet.header
  obtain ⟨sidecar, issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected)
      selected.packet.aligned (SelectedCompilationPhysicalProgramSupport.stagePrepared fixture.original.recipe.compiled)
      descriptor
  refine ⟨sidecar, ?_, ?_⟩
  · simpa only [selected.packet.aligned.named, CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued,
      RecursiveNamedPreparedCallEvidence.Prepared.signature_key selected.input.prepared] using issued
  · rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected

namespace FailureBridge

structure InitialForward (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) where
  start : SelectedCompilationPublicSessionInitial.Started selected.rows fixture.ready selected.packet.header started.call
  origin : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.original.recipe.compiled.indexed
  initial : CellAwarePublicInitialStart.Ready callableProfile origin.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics) start [.bool flag]
  forward : CellAwarePublicFaultingFailureForward.FailureForward callableProfile
    (completion := initial.receiving) (header := selected.packet.header)
    (bodyRegistry := origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) initial.caller.base.val
    (payloads := start.native) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := started.call.checkpoint)
    (.semantic ((selected.shape shape).failure selected.packet.header.context
      (flagEnvironment (selected.shape shape).flag ⟨[]⟩) (flagHeap ⟨[]⟩ flag)))
    ((selected.shape shape).finalHeap selected.packet.header.context
      (flagEnvironment (selected.shape shape).flag ⟨[]⟩) (flagHeap ⟨[]⟩ flag)) ∨
    ∃ originId call reason reached, CellAwarePublicFaultingFailureForward.FailureForward callableProfile
    (completion := initial.receiving) (header := selected.packet.header)
    (bodyRegistry := origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) initial.caller.base.val
    (payloads := start.native) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := started.call.checkpoint)
    (.stage originId call reason) reached

/-- Every premise is an original checked/static observation or an actual public
start. Source execution is constructed inside, before the target is resumed. -/
theorem initial_from_source (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨start⟩ := CellAwarePublicInitialStart.from_call
    (rows := selected.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member => selected.root_selection member)
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started selected.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.fault sourceTrace)
  have forward := CellAwarePublicFaultingFailureForward.first_fault callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, forward⟩⟩

/-- The complete original inventory is produced from its actual declarative
proof before the public call is resumed. -/
theorem complete_from_source (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    ∃ selected : SelectedInventory fixture row, Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨selected⟩ := fixture.inventory row typing.wellFormed
  exact ⟨selected, initial_from_source selected shape flag typing started callableProfile⟩

def publicProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "local"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  let ⟨profile⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.observe
    (fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "interleaved actual callable profile"
  for flag in [true, false] do
    let started ← observeStarted fixture.original row.original.key [.bool flag]
    let _proof := complete_from_source fixture row shape flag typing started profile
    match ← started.call.checkpoint.resume runOptions.executionFuel runOptions.outputValidationFuel with
    | .failed token returned =>
      unless returned.heapSize > started.session.heapSize do
        throw (IO.userError "faulting Source-first heap effects missing")
      IO.println s!"FAULTING_LOCAL_PUBLIC_FAILURE: flag={flag}, token={token.toNat}, heap={returned.heapSize}"
    | _ => throw (IO.userError "faulting Source-first call did not fail")
  IO.println "FAULTING_LOCAL_COMPLETE_OUTCOME: originals1/cache1/typing1/profile1"
  IO.println "FAULTING_LOCAL_COMPLETE_OUTCOME_PASS"

end FailureBridge
end Tests.SourceCoreSelectedFaultingLocal
