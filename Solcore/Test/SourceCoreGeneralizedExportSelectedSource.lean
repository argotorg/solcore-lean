import Solcore.Test.SourceCoreGeneralizedExportInventory
import Solcore.Test.SourceCoreGeneralizedExportSourceFirst
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping

/-! Actual selected headers allocate their original inputs before independent
Source factory execution. Every selection retains the complete cache inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}

theorem SelectedInventory.result_eq (selected : SelectedInventory whole row) :
    selected.packet.header.function.resultType = row.original.function.inferredBodyType :=
  selected.packet.header.agreement.result.trans
    (congrArg (fun named => named.function.inferredBodyType) selected.header_original)

def SelectedInventory.make_shape (selected : SelectedInventory whole row)
    (original : MakeShape row.original.function.typedBody) :
    MakeShape selected.packet.header.function.source := selected.source_eq.symm ▸ original

def SelectedInventory.capture_shape (selected : SelectedInventory whole row)
    (original : CaptureShape row.original.function.typedBody) :
    CaptureShape selected.packet.header.function.source := selected.source_eq.symm ▸ original

def SelectedInventory.tick_shape (selected : SelectedInventory whole row)
    (original : TickShape row.original.function.typedBody) :
    TickShape selected.packet.header.function.source := selected.source_eq.symm ▸ original

theorem SelectedInventory.factory_parameters (selected : SelectedInventory whole row)
    (shape : LambdaShape selected.packet.header.function.source) :
    selected.packet.header.function.parameters = [shape.input] :=
  selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans shape.inputs)

theorem SelectedInventory.factory_input_types (selected : SelectedInventory whole row)
    (shape : LambdaShape selected.packet.header.function.source) :
    selected.packet.header.types = [shape.inputType] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [selected.factory_parameters shape, List.map_cons, List.map_nil,
    shape.inputScheme, TypeSystem.Scheme.mono] using types.symm

theorem SelectedInventory.make_input_types (selected : SelectedInventory whole row)
    (shape : MakeShape selected.packet.header.function.source) :
    selected.packet.header.types = [.bool] := by
  rw [selected.factory_input_types shape.principal, shape.inputType]

theorem SelectedInventory.capture_input_types (selected : SelectedInventory whole row)
    (shape : CaptureShape selected.packet.header.function.source) :
    selected.packet.header.types = [.word] := by
  rw [selected.factory_input_types shape.principal, shape.inputType]

theorem SelectedInventory.tick_parameters (selected : SelectedInventory whole row)
    (shape : TickShape selected.packet.header.function.source) :
    selected.packet.header.function.parameters = [shape.input] :=
  selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans shape.inputs)

theorem SelectedInventory.tick_input_types (selected : SelectedInventory whole row)
    (shape : TickShape selected.packet.header.function.source) :
    selected.packet.header.types = [.bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [selected.tick_parameters shape, List.map_cons, List.map_nil,
    shape.inputScheme, TypeSystem.Scheme.mono] using types.symm

theorem SelectedInventory.make_statements (selected : SelectedInventory whole row)
    (shape : MakeShape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.principal.initialized.id, shape.returned.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

theorem SelectedInventory.capture_statements (selected : SelectedInventory whole row)
    (shape : CaptureShape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.principal.initialized.id, shape.returned.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

theorem SelectedInventory.tick_statements (selected : SelectedInventory whole row)
    (shape : TickShape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.returned.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

def inputHeap (before : Dynamic.Heap) (type : TypeSystem.Ty) (value : Dynamic.Value) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := type, value := some value}]⟩

def inputEnvironment (binder : TypedBinder) (before : Dynamic.Heap) : Dynamic.Environment :=
  [(binder.id, ⟨before.cells.length⟩)]

theorem SelectedInventory.make_source_body (selected : SelectedInventory whole row)
    (shape : MakeShape selected.packet.header.function.source)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
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
    RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.make_statements shape] at typed
  obtain ⟨next, body⟩ := shape.body_from_source header.function.evidence
    (inputEnvironment shape.principal.input before) (inputHeap before .bool (.bool flag))
    certified.runtime.graph.nodeOccurrencesUnique typed
  exact ⟨bound, next, selected.make_statements shape ▸ body⟩

theorem SelectedInventory.capture_source_body (selected : SelectedInventory whole row)
    (shape : CaptureShape selected.packet.header.function.source)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
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
    RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.capture_statements shape] at typed
  obtain ⟨next, body⟩ := shape.body_from_source header.function.evidence
    (inputEnvironment shape.principal.input before) (inputHeap before .word (.word seed))
    certified.runtime.graph.nodeOccurrencesUnique typed
  exact ⟨bound, next, selected.capture_statements shape ▸ body⟩

theorem SelectedInventory.tick_source_body (selected : SelectedInventory whole row)
    (shape : TickShape selected.packet.header.function.source)
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (inputEnvironment shape.input before) (inputHeap before .bool (.bool flag)) ∧
    Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (inputEnvironment shape.input before)
      (inputHeap before .bool (.bool flag)) selected.packet.header.function.body selected.packet.header.context
      (.returned (.bool flag)) (inputHeap before .bool (.bool flag)) := by
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (inputHeap before .bool (.bool flag)) := .append
  have bound : Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (inputEnvironment shape.input before) (inputHeap before .bool (.bool flag)) := by
    rw [selected.tick_parameters shape]
    exact .cons (by simpa only [shape.inputScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have body := shape.body_trace
    (program := Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
    (context := selected.packet.header.context) selected.packet.header.function.evidence
    (inputEnvironment shape.input before) (inputHeap before .bool (.bool flag)) flag
    Dynamic.Environment.LooksUp.head allocation.reads_new rfl rfl
  exact ⟨bound, selected.tick_statements shape ▸ body⟩

end Tests.SourceCoreGeneralizedExport
