import Solcore.Test.SourceCoreGeneralizedExportContinuation
import Solcore.Test.SourceCoreGeneralizedExportMaterializedProfile
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedSourceRoot

/-! Actual factory output carries positive generalized materialization through
Source lifting, public encoding and exact selected exported leaves. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}
  {selected : SelectedInventory whole row} {shape : MakeShape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

/-- A successful observed factory result is linked to its Source-produced
closures without a numeric sufficient-fuel premise. -/
theorem InitialForward.observed_materialized
    (first : InitialForward selected shape flag started callableProfile)
    (typing : OriginalTyping fixture.original)
    (materialized : MaterializedRow fixture.original row)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion started.artifact}
    (resumed : started.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (selection : RecursiveNamedPublicOutputSelections.Selection selected.packet.header.function.resultType returned.value) :
    ∃ (entries : List Entry) (retained : first.Retained returned.session entries) (payload : Core.Value),
      entries.map Entry.handle = selection.handles ∧
      RecursiveNamedPublicOutputSelections.Selected selection
        ((selected.make_shape shape).value selected.packet.header.context
          (inputEnvironment (selected.make_shape shape).principal.input ⟨[]⟩) selected.packet.header.function.evidence)
        payload selected.packet.header.output outputFuel entries ∧
      retained.state.heap = (selected.make_shape shape).principal.allocatedHeap selected.packet.header.context
        (inputEnvironment (selected.make_shape shape).principal.input ⟨[]⟩) (inputHeap ⟨[]⟩ .bool (.bool flag)) ∧
      CellAwareMaterializedOutput.EntriesAt fixture.original.recipe.compiled retained.state.mapping retained.state.world
        (owner fixture.original.recipe.compiled).key.frameLocation entries := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  let profile := materialized.for_selected selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.make_source_body (selected.make_shape shape) typing.wellFormed ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  obtain ⟨capture, stagedContext, stagedOutcome, heap, native, store, mapping, world, required, adapted, run, result,output⟩ :=
    CellAwarePublicMaterializedSourceRoot.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) first.start.selected
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference first.initial.keyPhysical
      first.initial.caller.physical first.initial.stable first.initial.heapTyped first.initial.argumentsTyped issued bodySelected
      first.initial.represented first.initial.heaps rfl first.start.started allocated measured
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
    let actualSelection : RecursiveNamedPublicOutputSelections.Selection selected.packet.header.function.resultType actual.value :=
      atReturned.1 ▸ selection
    obtain ⟨reached,payload,entries,nativeEq,selectedLeaves,handles,_related,history⟩ := collect actualSelection
    have selectedPublic : RecursiveNamedPublicOutputSelections.Selected selection
        ((selected.make_shape shape).value selected.packet.header.context
          (inputEnvironment (selected.make_shape shape).principal.input ⟨[]⟩) selected.packet.header.function.evidence)
        payload selected.packet.header.output outputFuel entries := selected_original atReturned.1 selectedLeaves
    obtain ⟨strongPayload,strongEq,strongValue⟩ := output _ rfl
    have payloadEq : strongPayload = payload := (Core.Value.inRight.inj (strongEq.symm.trans nativeEq)).2
    have leaves := CellAwareMaterializedOutput.selected selectedPublic (payloadEq ▸ strongValue)
    refine ⟨entries, ⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := (selected.make_shape shape).principal.allocatedHeap selected.packet.header.context
        (inputEnvironment (selected.make_shape shape).principal.input ⟨[]⟩) (inputHeap ⟨[]⟩ .bool (.bool flag)),
      store := store, caller := reached, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩,payload,?_,selectedPublic,rfl,leaves⟩
    exact handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast atReturned.1 selection)
  | rejected origin call reason stagedContext reached =>
    obtain ⟨actual,generation,exported,_atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result first.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload,_extension,_slots,_encoded,decoded,_rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

section Continuation
open SelectedCompilationPublicSessionState (StartedCall)
variable {firstRow : Row fixture.original}
  {firstSelected : SelectedInventory whole firstRow} {firstShape : MakeShape firstRow.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original firstRow.original.key [.bool firstFlag]}
  (first : InitialForward firstSelected firstShape firstFlag firstStart callableProfile)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} (retained : first.Retained session entries)
  (next : SelectedInventory whole row)

/-- The actual later observed export preserves every earlier handle and keeps
its selected leaves tied to the independent Source body stored in the plan. -/
theorem NextSourcePlan.observed_materialized
    {publicArguments : List SourceCorePublicValues.Value} {arguments : List Dynamic.Value}
    {call : StartedCall session row.original.key publicArguments runOptions}
    {value : Dynamic.Value} {after : Dynamic.Heap}
    (plan : NextSourcePlan first retained next publicArguments arguments call value after)
    (typing : OriginalTyping fixture.original)
    (materialized : MaterializedRow fixture.original row)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (selection : RecursiveNamedPublicOutputSelections.Selection next.packet.header.function.resultType returned.value) :
    ∃ (added : List Entry) (continued : first.Retained returned.session (entries ++ added)) (payload : Core.Value),
      added.map Entry.handle = selection.handles ∧
      RecursiveNamedPublicOutputSelections.Selected selection value payload next.packet.header.output outputFuel added ∧
      continued.state.heap = after ∧
      GeneralHeap.LocationMap.Extends retained.state.mapping continued.state.mapping ∧
      Core.WorldExtends retained.state.world continued.state.world ∧
      CellAwareMaterializedOutput.EntriesAt fixture.original.recipe.compiled continued.state.mapping continued.state.world
        (owner fixture.original.recipe.compiled).key.frameLocation added := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued next.input.prepared next.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨next.packet.selected.diagnostics,next.packet.selected.found,rfl⟩
  let profile := materialized.for_selected next
  obtain ⟨sidecar,issued,bodySelected⟩ := next.invocation
  obtain ⟨sourceSize,measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control plan.sourceTrace)
  obtain ⟨capture,stagedContext,stagedOutcome,heap,native,store,mapping,world,required,adapted,run,result,output⟩ :=
    CellAwarePublicMaterializedSourceRoot.checkpoint_has_sufficient_fuel callableProfile plan.ready.issued plan.ready.receiving.result.extension
      prepared next.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) plan.start.selected
      (owner fixture.original.recipe.compiled) retained.state.caller plan.ready.globalReference
      (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      plan.ready.history.physical plan.ready.stable plan.ready.heapTyped plan.ready.argumentsTyped issued bodySelected
      plan.ready.represented plan.ready.history.semantic.current.2.1 rfl plan.start.started plan.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports next.packet.header firstSelected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual,generation,_exported,atReturned,registry,exportsReady,collect⟩ :=
      CellAwarePublicNamedObservedCollection.after_collected _ _ plan.start.selected plan.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry plan.ready.contextAt)
        retained.exportsReady plan.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        plan.ready.history
    let actualSelection : RecursiveNamedPublicOutputSelections.Selection next.packet.header.function.resultType actual.value :=
      atReturned.1 ▸ selection
    obtain ⟨reached,payload,added,nativeEq,selectedLeaves,handles,_related,history⟩ := collect actualSelection
    have selectedPublic : RecursiveNamedPublicOutputSelections.Selected selection value payload
        next.packet.header.output outputFuel added := selected_original atReturned.1 selectedLeaves
    obtain ⟨strongPayload,strongEq,strongValue⟩ := output _ rfl
    have payloadEq : strongPayload = payload := (Core.Value.inRight.inj (strongEq.symm.trans nativeEq)).2
    have leaves := CellAwareMaterializedOutput.selected selectedPublic (payloadEq ▸ strongValue)
    refine ⟨added,⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := mapping, world := world, heap := after, store := store, caller := reached,
      atSession := atReturned.2.2.2, atRecipe := retained.state.atRecipe,
      receiving := plan.ready.receiving, issued := plan.ready.issued, extension := plan.ready.extension,
      registry := registry, history := history
      },exportsReady⟩,payload,?_,selectedPublic,rfl,result.2.2.2.1,result.2.2.2.2.1,leaves⟩
    exact handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast atReturned.1 selection)
  | rejected origin stageCall reason stagedContext reached =>
    obtain ⟨actual,generation,exported,_atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result plan.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload,_extension,_slots,_encoded,decoded,_rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Continuation

end Tests.SourceCoreGeneralizedExport
