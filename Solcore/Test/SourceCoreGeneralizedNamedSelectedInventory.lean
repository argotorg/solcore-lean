import Solcore.Test.SourceCoreGeneralizedExportSelectedSource
import Solcore.Test.SourceCoreGeneralizedSelectedRegistry
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedNamedSupport
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories
theorem ProfiledFixture.inventory_selected (fixture : ProfiledFixture)
    (cache : ObservedCache fixture.original fixture.original.recipe.compiled.indexed.base.functions)
    (bodies : SelectedCompilationBodyTyping.Bodies fixture.original.recipe.compiled) :
    Nonempty (WholeInventory fixture) := by
  classical
  let functions := fixture.original.recipe.compiled.indexed.base.functions
  have available : ∀ position : Fin functions.length, ∃ input : Input fixture.original.recipe.compiled,
      input.prepared.index = position.val ∧ input.prepared.named = functions[position.val] := by
    intro position
    have selected : functions[position.val]? = some functions[position.val] := List.getElem?_eq_getElem position.isLt
    obtain ⟨observation⟩ := cache.at_slot selected
    have origin := SelectedCompilationCatalog.ordinary_origin fixture.original.recipe.compiled
      bodies.signatures (RecursiveNamedPreparedFinalPlanOrigins.final_member _ selected rfl)
      observation.member observation.declaration
    have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
        (Context.ofSignatures fixture.original.recipe.compiled.sourceProgram.signatures)
        functions[position.val].specialized.parameterSubstitution := by
      rw [observation.substitution]
      intro name value found
      cases found
    obtain ⟨input, _row, slot, named⟩ := SelectedCompilationCatalog.of_cached fixture.original.recipe.compiled
      bodies.signatures selected origin range observation.ordinary observation.parameters
    exact ⟨input, slot, named⟩
  let choose := fun position => Classical.choose (available position)
  have chosen := fun position => Classical.choose_spec (available position)
  let inputs := (List.finRange functions.length).map choose
  obtain ⟨rows⟩ := SelectedCompilationCatalog.inventory bodies inputs
  refine ⟨⟨inputs, rows, ?_⟩⟩
  simp only [inputs, List.map_map]
  exact List.map_congr_left (fun position _ => (chosen position).1)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}

theorem SelectedInventory.make_source_body_selected (selected : SelectedInventory whole row)
    (shape : MakeShape selected.packet.header.function.source)
    (bodies : SelectedCompilationBodyTyping.Bodies fixture.original.recipe.compiled)
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (inputEnvironment shape.principal.input before) (inputHeap before .bool (.bool flag)) ∧
    ∃ final, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (inputEnvironment shape.principal.input before)
      (inputHeap before .bool (.bool flag)) selected.packet.header.function.body final
      (.returned (shape.value selected.packet.header.context
        (inputEnvironment shape.principal.input before) selected.packet.header.function.evidence))
      (shape.principal.allocatedHeap selected.packet.header.context
        (inputEnvironment shape.principal.input before) (inputHeap before .bool (.bool flag))) := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (inputHeap before .bool (.bool flag)) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      (inputEnvironment shape.principal.input before) (inputHeap before .bool (.bool flag)) := by
    rw [selected.factory_parameters shape.principal]
    exact .cons (by simpa only [shape.principal.inputScheme, TypeSystem.Scheme.mono,
      shape.inputType] using allocation) (.nil _ _)
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    SelectedCompilationHeaderCertificates.certified bodies header
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.make_statements shape] at typed
  obtain ⟨next, body⟩ := shape.body_from_source header.function.evidence
    (inputEnvironment shape.principal.input before) (inputHeap before .bool (.bool flag))
    certified.runtime.graph.nodeOccurrencesUnique typed
  exact ⟨bound, next, selected.make_statements shape ▸ body⟩

theorem SelectedInventory.capture_source_body_selected (selected : SelectedInventory whole row)
    (shape : CaptureShape selected.packet.header.function.source)
    (bodies : SelectedCompilationBodyTyping.Bodies fixture.original.recipe.compiled)
    (before : Dynamic.Heap) (seed : Word) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.word seed]
      (inputEnvironment shape.principal.input before) (inputHeap before .word (.word seed)) ∧
    ∃ final, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (inputEnvironment shape.principal.input before)
      (inputHeap before .word (.word seed)) selected.packet.header.function.body final
      (.returned (shape.value selected.packet.header.context
        (inputEnvironment shape.principal.input before) selected.packet.header.function.evidence))
      (shape.principal.allocatedHeap selected.packet.header.context
        (inputEnvironment shape.principal.input before) (inputHeap before .word (.word seed))) := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .word (some (.word seed))
      ⟨before.cells.length⟩ (inputHeap before .word (.word seed)) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.word seed]
      (inputEnvironment shape.principal.input before) (inputHeap before .word (.word seed)) := by
    rw [selected.factory_parameters shape.principal]
    exact .cons (by simpa only [shape.principal.inputScheme, TypeSystem.Scheme.mono,
      shape.inputType] using allocation) (.nil _ _)
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    SelectedCompilationHeaderCertificates.certified bodies header
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.capture_statements shape] at typed
  obtain ⟨next, body⟩ := shape.body_from_source header.function.evidence
    (inputEnvironment shape.principal.input before) (inputHeap before .word (.word seed))
    certified.runtime.graph.nodeOccurrencesUnique typed
  exact ⟨bound, next, selected.capture_statements shape ▸ body⟩

end Tests.SourceCoreGeneralizedExport
