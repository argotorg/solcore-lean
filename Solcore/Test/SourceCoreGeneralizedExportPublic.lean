import Solcore.Test.SourceCoreGeneralizedExportPublicStart
import Solcore.Test.SourceCoreGeneralizedExportSelectedSource
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialSelectedStart
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionInitial

/-! The complete original cache supplies the real initial public receiver.
Independent Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}

theorem SelectedInventory.invocation (selected : SelectedInventory whole row) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar fixture.original.recipe.compiled.indexed.base.plan
        selected.packet.header.named.signature.key = .ok sidecar ∧
      (SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).Closure
        selected.packet.header.function (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) := by
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts whole.rows).receipts
      selected.packet.header (CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory.header_member selected.retained)
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

structure InitialForward (selected : SelectedInventory whole row)
    (shape : MakeShape row.original.function.typedBody) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) where
  start : SelectedCompilationPublicSessionInitial.Started whole.rows fixture.ready selected.packet.header started.call
  origin : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.original.recipe.compiled.indexed
  initial : CellAwarePublicInitialStart.Ready callableProfile origin.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics) start [.bool flag]
  forward : CellAwarePublicNamedForward.ValueForward callableProfile
    (completion := initial.receiving) (header := selected.packet.header)
    (bodyRegistry := origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) initial.caller.base.val
    (payloads := start.native) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := started.call.checkpoint)
    ((selected.make_shape shape).value selected.packet.header.context
      (inputEnvironment (selected.make_shape shape).principal.input ⟨[]⟩) selected.packet.header.function.evidence)
    ((selected.make_shape shape).principal.allocatedHeap selected.packet.header.context
      (inputEnvironment (selected.make_shape shape).principal.input ⟨[]⟩) (inputHeap ⟨[]⟩ .bool (.bool flag)))

/-- Every premise is an original checked/static observation or an actual public
start. Source execution is constructed inside, before the target is resumed. -/
theorem initial_from_source (selected : SelectedInventory whole row)
    (shape : MakeShape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨start⟩ := CellAwarePublicInitialSelectedStart.from_selected_call
    (rows := whole.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member key => selected.root_selection member key)
  let actualShape := selected.make_shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.make_input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started whole.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.make_source_body actualShape typing.wellFormed ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicNamedForward.first_value callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, forward⟩⟩

end Tests.SourceCoreGeneralizedExport
