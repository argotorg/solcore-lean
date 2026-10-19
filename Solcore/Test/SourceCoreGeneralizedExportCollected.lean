import Solcore.Test.SourceCoreGeneralizedExportPublic
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedCollection
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicSessionState
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNextStart

/-! Actual observed factory output retains every selected leaf together with
its independent Source value and exact returned physical session. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem selected_original {sourceType : TypeSystem.Ty}
    {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : RecursiveNamedPublicOutputSelections.Selection sourceType first}
    {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : RecursiveNamedPublicOutputSelections.Selected (same ▸ selection) source native type fuel entries) :
    RecursiveNamedPublicOutputSelections.Selected selection source native type fuel entries := by
  cases same
  exact selected

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}
  {selected : SelectedInventory whole row} {shape : MakeShape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

def InitialForward.functions (first : InitialForward selected shape flag started callableProfile) :=
  CellAwareSelectedPublicSessionState.functions whole.rows first.origin callableProfile

def InitialForward.cells (first : InitialForward selected shape flag started callableProfile) :=
  CellAwareSelectedPublicSessionState.cells whole.rows first.origin callableProfile

structure InitialForward.Retained (first : InitialForward selected shape flag started callableProfile)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List Entry) where
  state : CellAwarePublicSessionState.State whole.rows first.functions first.cells selected.packet.header
    first.initial.receiving fixture.original.recipe session entries
  exportsReady : state.session.ExportsReady

/-- A successful observed factory result is linked to its Source-produced
closures without a numeric sufficient-fuel premise. -/
theorem InitialForward.observed_collected
    (first : InitialForward selected shape flag started callableProfile)
    (typing : OriginalTyping fixture.original)
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
        (inputEnvironment (selected.make_shape shape).principal.input ⟨[]⟩) (inputHeap ⟨[]⟩ .bool (.bool flag)) := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.make_source_body (selected.make_shape shape) typing.wellFormed ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  obtain ⟨stagedContext, stagedOutcome, heap, capture, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
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
    obtain ⟨reached,payload,entries,_native,selectedLeaves,handles,_related,history⟩ := collect actualSelection
    have selectedPublic : RecursiveNamedPublicOutputSelections.Selected selection
        ((selected.make_shape shape).value selected.packet.header.context
          (inputEnvironment (selected.make_shape shape).principal.input ⟨[]⟩) selected.packet.header.function.evidence)
        payload selected.packet.header.output outputFuel entries := selected_original atReturned.1 selectedLeaves
    refine ⟨entries, ⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := (selected.make_shape shape).principal.allocatedHeap selected.packet.header.context
        (inputEnvironment (selected.make_shape shape).principal.input ⟨[]⟩) (inputHeap ⟨[]⟩ .bool (.bool flag)),
      store := store, caller := reached, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩,payload,?_,selectedPublic,rfl⟩
    exact handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast atReturned.1 selection)
  | rejected origin call reason stagedContext reached =>
    obtain ⟨actual,generation,exported,_atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result first.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload,_extension,_slots,_encoded,decoded,_rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Tests.SourceCoreGeneralizedExport
