import Solcore.Test.SourceCoreMixedBuiltinValueRetained
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedCollection

/-! Actual completed public calls retain the Source-derived continuation without
requiring the observer to guess a sufficient execution or export budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicOutputSelections (Selection Selected)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

theorem SelectedInventory.result_eq (selected : SelectedInventory fixture row) :
    selected.packet.header.function.resultType = row.original.function.inferredBodyType :=
  selected.packet.header.agreement.result.trans
    (congrArg (fun named => named.function.inferredBodyType) selected.header_original)

def builtinSelection {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {flag : Bool} {handle : SourceCorePublicValues.Handle}
    (types : type = .product .bool (.function .word .integer))
    (values : value = .product (.bool flag) (.function handle)) : Selection type value := by
  cases types
  cases values
  exact .product .skip .function

theorem builtin_selected {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {flag : Bool} {handle : SourceCorePublicValues.Handle}
    (types : type = .product .bool (.function .word .integer))
    (values : value = .product (.bool flag) (.function handle))
    {sourceFlag : Bool} {native : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected (builtinSelection types values)
      (.product (.bool sourceFlag) (.builtin ⟨.wordToInteger⟩)) native nativeType fuel entries) :
    ∃ native nativeType remaining,
      entries = [⟨.function .word .integer,.builtin ⟨.wordToInteger⟩,handle,native,nativeType,remaining⟩] := by
  cases types
  cases values
  cases selected with
  | product left right =>
    cases left
    cases right
    exact ⟨_,_,_,rfl⟩

private theorem selected_original {sourceType : TypeSystem.Ty}
    {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : Selection sourceType first}
    {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected (same ▸ selection) source native type fuel entries) :
    Selected selection source native type fuel entries := by
  cases same
  exact selected

/-- The initial independent body and actual observed export retain the same
heap, decoder and original complete compiler inventory. -/
theorem InitialForward.observed_collected
    (first : InitialForward selected shape firstFlag firstStart callableProfile)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion firstStart.artifact}
    (resumed : firstStart.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (selection : Selection selected.packet.header.function.resultType returned.value) :
    ∃ (entries : List Entry) (_retained : first.Retained returned.session entries) (payload : Core.Value),
      Selected selection (.product (.bool firstFlag) (.builtin ⟨.wordToInteger⟩))
        payload selected.packet.header.output outputFuel entries := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control first.source.trace)
  obtain ⟨stagedContext, stagedOutcome, heap, capture, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) first.start.selected
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference first.initial.keyPhysical
      first.initial.caller.physical first.initial.stable first.initial.heapTyped first.initial.argumentsTyped issued bodySelected
      first.initial.represented first.initial.heaps rfl first.start.started first.source.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual,generation,_exported,atReturned,registry,exportsReady,collect⟩ :=
      CellAwarePublicNamedObservedCollection.first_collected _ _ first.start.selected first.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry first.initial.contextAt)
        first.initial.exportsReady first.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        first.initial.caller.physical
    let actualSelection : Selection selected.packet.header.function.resultType actual.value :=
      atReturned.1 ▸ selection
    obtain ⟨caller,payload,entries,_native,selectedLeaves,_handles,_related,history⟩ := collect actualSelection
    exact ⟨entries, ⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := mapping, world := world, heap := first.source.after,
      store := store, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩, payload, selected_original atReturned.1 selectedLeaves⟩
  | rejected origin call reason stagedContext reached =>
    obtain ⟨actual, generation, exported, _atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result first.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload, _extension, _slots, _encoded, decoded, _rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Tests.SourceCoreMixedBuiltinValue
