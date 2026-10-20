import Solcore.Test.SourceCoreGeneralizedSelectedRegistry
import Solcore.Test.SourceCoreGeneralizedExportSelection
import Solcore.Test.SourceCoreGeneralizedExportCalls
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicHandleStart
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedHandle

/-! A retained exact Source closure supplies its ordinary application before
resuming its actual packed public handle call. -/
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
  (first : InitialForward selected shape flag started callableProfile)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} (retained : first.Retained session entries)
  (entry : Entry) {parameter result : TypeSystem.Ty}
  {argument : SourceCorePublicValues.Value} {sourceArgument : Dynamic.Value}
  (call : CellAwarePublicHandleStart.StartedCall session entry.handle argument runOptions.inputValidationFuel)

structure HandleSourcePlan (parameter result : TypeSystem.Ty) (sourceArgument value : Dynamic.Value) (after : Dynamic.Heap) where
  member : entry ∈ entries
  entryType : entry.sourceType = .function parameter result
  start : CellAwarePublicHandleStart.Started retained.state entry call parameter result
  ready : CellAwarePublicHandleStart.Ready retained.state entry call start sourceArgument
  function : Dynamic.Closure
  sourceEq : entry.source = .closure function
  materialized : CellAwareMaterializedRetainedEntries.EntryAt (keys fixture.original.recipe.compiled)
    retained.state.mapping retained.state.world entry
  input : RecursiveNamedPublicFunctionHistoryInputs.Input entries selected.packet.header.function.context parameter argument sourceArgument
  callerEvidence : Dynamic.EvidenceEnvironment
  invocationEvidence : Dynamic.EvidenceEnvironment
  arity : [sourceArgument].length = function.parameters.length
  trace : Dynamic.CallableApplies (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
    selected.packet.header.function.context callerEvidence invocationEvidence retained.state.heap
    entry.source [sourceArgument] value after

/-- A genuine identity instance returns the actual input and appends exactly
its parameter cell. Its Source frame comes from the retained typed history. -/
theorem identity_plan (member : entry ∈ entries) (entryType : entry.sourceType = .function parameter result)
    (materialized : CellAwareMaterializedRetainedEntries.EntryAt (keys fixture.original.recipe.compiled)
      retained.state.mapping retained.state.world entry)
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries selected.packet.header.function.context parameter argument sourceArgument)
    {source : TypedSource} (identity : MakeShape source)
    (definitionContext : SourceSemantics.Context) (captured : Dynamic.Environment)
    (substitution : TypeSystem.Substitution) (evidence : Dynamic.EvidenceEnvironment)
    (sourceEq : entry.source = .closure ((identity.principal.descriptor definitionContext captured).instantiate substitution evidence))
    (typing : OriginalTyping fixture.original) :
    Nonempty (HandleSourcePlan first retained entry call parameter result sourceArgument sourceArgument
      ⟨retained.state.heap.cells ++ [{type := (identity.principal.parameter.applySubstitution substitution).scheme.body, value := some sourceArgument}]⟩) := by
  obtain ⟨start⟩ := CellAwarePublicHandleStart.from_call retained.state entry call member entryType
  obtain ⟨ready⟩ := CellAwarePublicHandleStart.of_started retained.state entry call
    (CellAwarePublicCells.generalized_extends_registry _ _) member entryType input start
  have frame := CellAwarePublicRetainedMaterializedHandle.source_frame first.functions
    typing.selected_bodies ready.history.semantic entry member entryType sourceEq
  have trace := identity.identity_applies (context := selected.packet.header.function.context)
    captured substitution evidence [] retained.state.heap sourceArgument frame
  exact ⟨⟨member,entryType,start,ready,_,sourceEq,materialized,input,[],evidence,rfl,sourceEq.symm ▸ trace⟩⟩

/-- The captured instance reads the original saved cell, preserved in the
current Source heap, before returning its unchanged value. -/
theorem captured_plan (member : entry ∈ entries) (entryType : entry.sourceType = .function parameter result)
    (materialized : CellAwareMaterializedRetainedEntries.EntryAt (keys fixture.original.recipe.compiled)
      retained.state.mapping retained.state.world entry)
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries selected.packet.header.function.context parameter argument sourceArgument)
    {source : TypedSource} (capture : CaptureShape source)
    (definitionContext : SourceSemantics.Context) (captured : Dynamic.Environment)
    (substitution : TypeSystem.Substitution) (evidence : Dynamic.EvidenceEnvironment)
    (sourceEq : entry.source = .closure ((capture.principal.descriptor definitionContext captured).instantiate substitution evidence))
    {location : Dynamic.Location} {cell : Dynamic.Cell} {saved : Dynamic.Value}
    (capturedLookup : Dynamic.Environment.LooksUp captured capture.principal.input.id location)
    (capturedRead : Dynamic.Heap.Reads retained.state.heap location cell)
    (ordinary : cell.generalized = none) (capturedValue : cell.value = some saved)
    (typing : OriginalTyping fixture.original) :
    Nonempty (HandleSourcePlan first retained entry call parameter result sourceArgument saved
      ⟨retained.state.heap.cells ++ [{type := (capture.principal.parameter.applySubstitution substitution).scheme.body, value := some sourceArgument}]⟩) := by
  obtain ⟨start⟩ := CellAwarePublicHandleStart.from_call retained.state entry call member entryType
  obtain ⟨ready⟩ := CellAwarePublicHandleStart.of_started retained.state entry call
    (CellAwarePublicCells.generalized_extends_registry _ _) member entryType input start
  have frame := CellAwarePublicRetainedMaterializedHandle.source_frame first.functions
    typing.selected_bodies ready.history.semantic entry member entryType sourceEq
  have trace := capture.captured_applies (context := selected.packet.header.function.context)
    captured substitution evidence [] retained.state.heap sourceArgument saved capturedLookup capturedRead ordinary capturedValue frame
  exact ⟨⟨member,entryType,start,ready,_,sourceEq,materialized,input,[],evidence,rfl,sourceEq.symm ▸ trace⟩⟩

end Tests.SourceCoreGeneralizedExport
