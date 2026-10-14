import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedBodyControl
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

structure Shape (source : TypedSource) where
  binder : TypedBinder
  first : ExpressionNode
  discard : StatementNode
  second : ExpressionNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  binderType : binder.scheme = .mono .word
  roots : source.roots = [.statement discard.id, .statement returned.id]
  firstFound : source.lookupExpression? first.id = some first
  firstForm : first.form = .reference binder.name (.local binder.id)
  firstRequirements : first.requirements = []
  firstCoercions : first.coercions = []
  discardFound : source.lookupStatement? discard.id = some discard
  discardForm : discard.form = .expression first.id true
  secondFound : source.lookupExpression? second.id = some second
  secondForm : second.form = .reference binder.name (.local binder.id)
  secondRequirements : second.requirements = []
  secondCoercions : second.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some second.id)

def sourceHeap (word : Word) : Dynamic.Heap := ⟨[{type := .word, value := some (.word word)}]⟩

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

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (shape : Shape header.function.source)

include shape in
theorem input_types : header.types = [.word] := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.binderType, TypeSystem.Scheme.mono] using types.symm

include shape in
/-- Allocate the parameter, evaluate the discarded read, then evaluate the return.
The proof uses original Source occurrences before the public checkpoint runs. -/
theorem ordinary_call {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) (word : Word) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩ [.word word]
      (.word word) (sourceHeap word) := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have allocated : Dynamic.Heap.Allocates ⟨[]⟩ shape.binder.scheme.body
      (some (.word word)) ⟨0⟩ (sourceHeap word) := by
    rw [shape.binderType]
    exact .append
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.word word]
      [(shape.binder.id, ⟨0⟩)] (sourceHeap word) := by
    rw [params]
    exact .cons allocated (.nil _ _)
  have roots : header.function.body = [shape.discard.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have read (node : ExpressionNode) (found : header.function.source.lookupExpression? node.id = some node)
      (form : node.form = .reference shape.binder.name (.local shape.binder.id))
      (requirements : node.requirements = []) (coercions : node.coercions = []) :
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)]
        (sourceHeap word) node.id (.word word) (sourceHeap word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found)
    · rw [form]
      exact .local (by rw [requirements, coercions]; rfl) .head
        (Dynamic.Heap.Allocates.reads_new (Dynamic.Heap.Allocates.append (heap := ⟨[]⟩)
          (type := .word) (value := some (.word word)))) rfl rfl
    · rw [coercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)] (sourceHeap word)
      header.function.body header.context (.returned (.word word)) (sourceHeap word) := by
    rw [roots]
    exact .cons (.expression (lookupStatement?_sound shape.discardFound) shape.discardForm
      (read shape.first shape.firstFound shape.firstForm shape.firstRequirements shape.firstCoercions))
      (.singleton (lookupStatement?_sound shape.returnedFound)
        (by rw [shape.returnedForm]; intro id impossible; cases impossible)
        (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm
          (read shape.second shape.secondFound shape.secondForm shape.secondRequirements shape.secondCoercions)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedBodyControl
