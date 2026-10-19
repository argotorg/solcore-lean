import Solcore.Test.SourceCoreMixedOperatorsInventory
import Solcore.Test.SourceCoreMixedOperatorsSourceFirst
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping

/-! The selected actual header receives the original Bool argument by Source
allocation. Original program typing then constructs the complete Source body
execution, before any target execution is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreMixedImperative (SourceState StoredValue)

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

variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.source_eq (selected : SelectedInventory fixture row) :
    selected.packet.header.function.source = row.original.function.typedBody :=
  selected.packet.header.agreement.source.trans
    (congrArg (fun named => named.function.typedBody) selected.header_original)

def SelectedInventory.shape (selected : SelectedInventory fixture row)
    (original : Shape row.original.function.typedBody) :
    Shape selected.packet.header.function.source :=
  selected.source_eq.symm ▸ original

theorem SelectedInventory.parameters (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.parameters = [shape.flag] :=
  selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans shape.inputs)

theorem SelectedInventory.input_types (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.types = [.bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [selected.parameters shape, List.map_cons, List.map_nil,
    shape.flagScheme, TypeSystem.Scheme.mono] using types.symm

theorem SelectedInventory.statements (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.initialized.node.id, shape.returned.node.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

def flagHeap (before : Dynamic.Heap) (flag : Bool) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .bool, value := some (.bool flag)}]⟩

def flagEnvironment (binder : TypedBinder) (before : Dynamic.Heap) : Dynamic.Environment :=
  [(binder.id, ⟨before.cells.length⟩)]

/-- Source parameters and the complete independent body are obtained from the
actual selected Header and the original program typing certificate. -/
theorem SelectedInventory.source_body (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    (before : Dynamic.Heap) (flag : Bool)
    (heapTyped : Dynamic.HeapWellTyped selected.packet.header.function.context before) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) ∧
    ∃ final after, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (flagEnvironment shape.flag before) (flagHeap before flag)
      selected.packet.header.function.body final
      (.returned (.product (.bool flag) (.builtin ⟨.wordToInteger⟩)))
      after := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (flagHeap before flag) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) := by
    rw [selected.parameters shape]
    exact .cons (by simpa only [shape.flagScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have initialLocals : header.function.context.locals = [] := by
    rw [header.frame.context]
    cases header.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq => rw [contextEq]; rfl
  have locals : Dynamic.EnvironmentAgrees (flagHeap before flag) header.context.locals
      (flagEnvironment shape.flag before) := by
    rw [header.extended.locals_eq, selected.parameters shape, initialLocals]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
      List.append_nil]
    exact .cons allocation.reads_new (by rw [shape.flagScheme]; rfl)
      (.ordinary (by rw [shape.flagScheme]; rfl) rfl) .nil
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields header.extended
  have runtime := certified.runtime.transport fields
  have covers : header.function.evidence.Covers header.context :=
    fields.covers (header.frame.context.symm ▸ header.frame.covers)
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.statements shape] at typed
  have allocatedTyped := heapTyped.allocate (.some (.bool flag)) allocation
  have boundTyped : Dynamic.HeapWellTyped header.context (flagHeap before flag) :=
    allocatedTyped.transportClosed fields.signatures certified.runtime.closed runtime.closed
      certified.runtime.variables_closed runtime.residual_variables_open
  have state : SourceState (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      header.function.source header.context header.function.evidence
      (flagEnvironment shape.flag before) (flagHeap before flag) :=
    ⟨runtime, covers, locals, boundTyped⟩
  have stored : StoredValue shape.flag (flagEnvironment shape.flag before) (flagHeap before flag) (.bool flag) :=
    ⟨_, _, .head, allocation.reads_new, rfl, rfl⟩
  obtain ⟨next, after, body, _append⟩ := shape.body_from_source state wellFormed typed flag stored
  exact ⟨bound, next, after, selected.statements shape ▸ body⟩

end Tests.SourceCoreMixedOperators
