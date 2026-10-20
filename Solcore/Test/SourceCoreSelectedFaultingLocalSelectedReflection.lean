import Solcore.Test.SourceCoreSelectedFaultingLocalSelectedPublic
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureReflection

/-! Actual failed public outcomes recover the ordinary Source failure and its
reached heap, and establish a reusable history from selected original rows. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreSelectedFaultingLocal.FailureBridge
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row}
  {shape : Shape row.original.function.typedBody} {flag : Bool}
  {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

def ReflectedMeaning (first : InitialForward selected shape flag started callableProfile)
    (executionFuel : Nat) (token : Word) (returned : SourceCoreExecution.Session started.artifact) : Prop :=
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
    ∃ observed : CellAwarePublicFaultingFailureReflection.Reflected
      (completion := first.initial.receiving) (header := selected.packet.header)
      (bodyRegistry := first.origin.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults first.origin.result.diagnostics)
      (payloads := first.start.native) (arguments := [.bool flag])
      (nativeCheckpoint := first.start.checkpoint) (sidecar := sidecar)
      callableProfile (owner fixture.original.recipe.compiled) first.initial.caller.base.val
      executionFuel token returned,
    ∃ reached : CellAwarePublicFunctionHistory.Caller (headers selected.rows)
      (keys fixture.original.recipe.compiled) observed.finalMap observed.finalWorld observed.after observed.finalStore,
      CallableIndexedOwnedFunctionState.Relates first.initial.caller.base.val reached ∧
      CellAwarePublicPhysicalHistory.History
        (functions := CellAwarePhysicalFunctionOrigins.functions (headers selected.rows)
          (keys fixture.original.recipe.compiled) first.origin.result.context.registry
          (CallableIndexedOwnedPublicDecodedCallFaults.faults first.origin.result.diagnostics) callableProfile)
        (cells := GeneralizedLocalDescriptorHeap.cellModel
          (CompatibleAmbientHeap.payloadModel fixture.original.recipe.compiled.compatible.checked
            first.initial.receiving.result.context.registry
            (CellAwarePhysicalFunctionOrigins.functions (headers selected.rows)
              (keys fixture.original.recipe.compiled) first.origin.result.context.registry
              (CallableIndexedOwnedPublicDecodedCallFaults.faults first.origin.result.diagnostics) callableProfile))
          (GeneralizedLocalInstanceValues.model fixture.original.recipe.compiled.indexed))
        (receiving := first.initial.receiving.result.context.registry) (anchor := selected.packet.header)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached []

theorem InitialForward.reflected_selected
    (first : InitialForward selected shape flag started callableProfile)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {token : Word}
    {returned : SourceCoreExecution.Session started.artifact}
    (resumed : started.call.checkpoint.ResumeAt executionFuel outputFuel (.failed token returned)) :
    ReflectedMeaning first executionFuel token returned := by
  unfold ReflectedMeaning
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  let support := (typing.checked_registry selected).namedSupport
  obtain ⟨observed⟩ := CellAwarePublicFaultingFailureReflection.reflect_selected callableProfile
    first.initial.issued first.initial.extension prepared selected.packet.aligned fixture.ready diagnostic support
    (profile.for_compilation prepared.compilation) first.start.selected
    (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference
    first.initial.keyPhysical first.initial.caller.physical first.initial.stable
    first.initial.heapTyped first.initial.argumentsTyped issued bodySelected first.initial.represented
    first.initial.heaps rfl first.start.started first.start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry first.initial.contextAt)
    first.initial.exportsReady resumed
  obtain ⟨reached, related, history⟩ :=
    CellAwarePublicFaultingFailureReflection.Reflected.first_history_selected
      callableProfile support first.start.selected (owner fixture.original.recipe.compiled)
      first.initial.caller.base.val first.initial.caller.physical rfl first.start.started observed
  exact ⟨sidecar, observed, reached, related, history⟩

theorem reflect_complete
    (typing : OriginalTyping fixture.original)
    (plan : ∃ selected : SelectedInventory fixture row,
      Nonempty (InitialForward selected shape flag started callableProfile))
    {executionFuel outputFuel : Nat} {token : Word}
    {returned : SourceCoreExecution.Session started.artifact}
    (resumed : started.call.checkpoint.ResumeAt executionFuel outputFuel (.failed token returned)) :
    ∃ selected : SelectedInventory fixture row,
    ∃ first : InitialForward selected shape flag started callableProfile,
      ReflectedMeaning first executionFuel token returned := by
  obtain ⟨selected, ⟨first⟩⟩ := plan
  exact ⟨selected, first, first.reflected_selected typing resumed⟩

end Tests.SourceCoreSelectedFaultingLocal.FailureBridge
