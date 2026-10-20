import Solcore.Test.SourceCoreGeneralizedExportContinuation
import Solcore.Test.SourceCoreGeneralizedNamedSelectedPublic
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {firstRow : Row fixture.original}
  {selected : SelectedInventory whole firstRow} {firstShape : MakeShape firstRow.original.function.typedBody}
  {firstFlag : Bool} {started : Started fixture.original firstRow.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  (first : InitialForward selected firstShape firstFlag started callableProfile)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} (retained : first.Retained session entries)
  {row : Row fixture.original} (next : SelectedInventory whole row)

private theorem selected_start
    {publicArguments : List SourceCorePublicValues.Value}
    (call : StartedCall session row.original.key publicArguments runOptions) :
    Nonempty (CellAwarePublicNextStart.Started (header := next.packet.header) retained.state call) := by
  apply CellAwarePublicNextStart.from_call (prepared := fixture.ready) retained.state call
  intro root found
  apply next.root_selection (List.mem_of_find?_eq_some found)
  exact of_decide_eq_true (List.find?_some
    (p := fun candidate : SourceCoreIndexedSession.Root fixture.original.recipe.compiled =>
      decide (candidate.key = row.original.key)) found)

/-- Capture retains the earlier history and constructs its own authentic
parameter allocation and generalized closure return at that exact heap. -/
theorem capture_plan_selected
    (shape : CaptureShape row.original.function.typedBody) (seed : Word)
    (support : SelectedCompilationNamedSupport.Support fixture.original.recipe.compiled)
    (call : StartedCall session row.original.key [.word seed] runOptions) :
    Nonempty (NextSourcePlan first retained next [.word seed] [.word seed] call
      ((next.capture_shape shape).value next.packet.header.context
        (inputEnvironment (next.capture_shape shape).principal.input retained.state.heap)
        next.packet.header.function.evidence)
      ((next.capture_shape shape).principal.allocatedHeap next.packet.header.context
        (inputEnvironment (next.capture_shape shape).principal.input retained.state.heap)
        (inputHeap retained.state.heap .word (.word seed)))) := by
  obtain ⟨start⟩ := selected_start first retained next call
  let actualShape := next.capture_shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      next.packet.header.function.context [.word seed] next.packet.header.types := by
    rw [next.capture_input_types actualShape]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  obtain ⟨ready⟩ := CellAwarePublicNextStart.of_started retained.state call
    (CellAwarePublicCells.generalized_extends_registry _ _)
    support.bodyTyping start inputTypes inputMeanings
  obtain ⟨allocated,final,trace⟩ := next.capture_source_body_selected actualShape support.bodyTyping retained.state.heap seed
  exact ⟨⟨start,ready,_,_,final,allocated,trace⟩⟩

/-- An unrelated ordinary row uses the same complete inventory and returned
state, with a genuine Source parameter allocation and read. -/

theorem tick_plan_selected
    (shape : TickShape row.original.function.typedBody) (flag : Bool)
    (support : SelectedCompilationNamedSupport.Support fixture.original.recipe.compiled)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Nonempty (NextSourcePlan first retained next [.bool flag] [.bool flag] call
      (.bool flag) (inputHeap retained.state.heap .bool (.bool flag))) := by
  obtain ⟨start⟩ := selected_start first retained next call
  let actualShape := next.tick_shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      next.packet.header.function.context [.bool flag] next.packet.header.types := by
    rw [next.tick_input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨ready⟩ := CellAwarePublicNextStart.of_started retained.state call
    (CellAwarePublicCells.generalized_extends_registry _ _)
    support.bodyTyping start inputTypes inputMeanings
  obtain ⟨allocated,trace⟩ := next.tick_source_body actualShape retained.state.heap flag
  exact ⟨⟨start,ready,_,_,_,allocated,trace⟩⟩

/-- The actual later observed export preserves every earlier handle and keeps
its selected leaves tied to the independent Source body stored in the plan. -/

theorem NextSourcePlan.observed_collected_selected
    {publicArguments : List SourceCorePublicValues.Value} {arguments : List Dynamic.Value}
    {call : StartedCall session row.original.key publicArguments runOptions}
    {value : Dynamic.Value} {after : Dynamic.Heap}
    (plan : NextSourcePlan first retained next publicArguments arguments call value after)
    (support : SelectedCompilationNamedSupport.Support fixture.original.recipe.compiled)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (selection : RecursiveNamedPublicOutputSelections.Selection next.packet.header.function.resultType returned.value) :
    ∃ (added : List Entry) (continued : first.Retained returned.session (entries ++ added)) (payload : Core.Value),
      added.map Entry.handle = selection.handles ∧
      RecursiveNamedPublicOutputSelections.Selected selection value payload next.packet.header.output outputFuel added ∧
      continued.state.heap = after ∧
      GeneralHeap.LocationMap.Extends retained.state.mapping continued.state.mapping ∧
      Core.WorldExtends retained.state.world continued.state.world := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued next.input.prepared next.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨next.packet.selected.diagnostics,next.packet.selected.found,rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar,issued,bodySelected⟩ := next.invocation
  obtain ⟨sourceSize,measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control plan.sourceTrace)
  obtain ⟨stagedContext,stagedOutcome,heap,capture,native,store,mapping,world,required,adapted,run,result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel_selected callableProfile plan.ready.issued plan.ready.receiving.result.extension
      prepared next.packet.aligned fixture.ready diagnostic support
      (profile.for_compilation prepared.compilation) plan.start.selected
      (owner fixture.original.recipe.compiled) retained.state.caller plan.ready.globalReference
      (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      plan.ready.history.physical plan.ready.stable plan.ready.heapTyped plan.ready.argumentsTyped issued bodySelected
      plan.ready.represented plan.ready.history.semantic.current.2.1 rfl plan.start.started plan.allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports next.packet.header selected.packet.header
        support.bodyTyping).2
    obtain ⟨actual,generation,_exported,atReturned,registry,exportsReady,collect⟩ :=
      CellAwarePublicNamedObservedCollection.after_collected _ _ plan.start.selected plan.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry plan.ready.contextAt)
        retained.exportsReady plan.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        plan.ready.history
    let actualSelection : RecursiveNamedPublicOutputSelections.Selection next.packet.header.function.resultType actual.value :=
      atReturned.1 ▸ selection
    obtain ⟨reached,payload,added,_native,selectedLeaves,handles,_related,history⟩ := collect actualSelection
    have selectedPublic : RecursiveNamedPublicOutputSelections.Selected selection value payload
        next.packet.header.output outputFuel added := selected_original atReturned.1 selectedLeaves
    refine ⟨added,⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := mapping, world := world, heap := after, store := store, caller := reached,
      atSession := atReturned.2.2.2, atRecipe := retained.state.atRecipe,
      receiving := plan.ready.receiving, issued := plan.ready.issued, extension := plan.ready.extension,
      registry := registry, history := history
      },exportsReady⟩,payload,?_,selectedPublic,rfl,result.2.2.2.1,result.2.2.2.2.1⟩
    exact handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast atReturned.1 selection)
  | rejected origin stageCall reason stagedContext reached =>
    obtain ⟨actual,generation,exported,_atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result plan.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload,_extension,_slots,_encoded,decoded,_rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded
end Tests.SourceCoreGeneralizedExport
