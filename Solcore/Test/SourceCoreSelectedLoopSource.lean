import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLoop
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

structure Shape (source : TypedSource) where
  binder : TypedBinder
  copy : TypedBinder
  first : ExpressionNode
  condition : ExpressionNode
  breaking : StatementNode
  loop : StatementNode
  second : ExpressionNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  binderType : binder.scheme = .mono .word
  copyType : copy.scheme = .mono .word
  roots : source.roots = [.statement loop.id, .statement returned.id]
  firstFound : source.lookupExpression? first.id = some first
  firstForm : first.form = .reference binder.name (.local binder.id)
  firstRequirements : first.requirements = []
  firstCoercions : first.coercions = []
  conditionFound : source.lookupExpression? condition.id = some condition
  conditionForm : condition.form = .reference "true" (.builtinBoolean true)
  conditionRequirements : condition.requirements = []
  conditionCoercions : condition.coercions = []
  breakingFound : source.lookupStatement? breaking.id = some breaking
  breakingForm : breaking.form = .breakStmt
  loopFound : source.lookupStatement? loop.id = some loop
  loopForm : loop.form = .forLoop [.letDecl copy (some first.id)] condition.id [] [breaking.id]
  secondFound : source.lookupExpression? second.id = some second
  secondForm : second.form = .reference binder.name (.local binder.id)
  secondRequirements : second.requirements = []
  secondCoercions : second.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some second.id)

def inputHeap (word : Word) : Dynamic.Heap := ⟨[{type := .word, value := some (.word word)}]⟩
def sourceHeap (word : Word) : Dynamic.Heap := ⟨[{type := .word, value := some (.word word)}, {type := .word, value := some (.word word)}]⟩

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

/-- The loop's original Source typing supplies its genuine lexical extension. -/
private theorem header_extension (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ∃ loopContext, BinderExtends header.function.source.owner header.context shape.copy loopContext := by
  obtain ⟨final, facts, typed, completes⟩ := certified.statements
  have roots : header.function.body = [shape.loop.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  rw [roots] at typed
  cases typed with
  | cons head tail =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj ((lookupStatement?_complete header.unique contains).symm.trans shape.loopFound)
    rw [shape.loopForm] at formTyped
    cases formTyped with
    | forLoop init condition body post =>
      cases init with
      | cons head tail =>
        cases head with
        | letInitialized _ _ _ extension => exact ⟨_, extension⟩
        | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly (by rw [shape.copyType]; rfl))

include shape in
/-- Evaluate the initializer, enter a true for-loop, break, restore the outer
scope and return its original parameter. No public execution is a premise. -/
theorem ordinary_call (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) (word : Word) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩ [.word word]
      (.word word) (sourceHeap word) := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have allocated : Dynamic.Heap.Allocates ⟨[]⟩ shape.binder.scheme.body
      (some (.word word)) ⟨0⟩ (inputHeap word) := by
    rw [shape.binderType]
    exact .append
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.word word]
      [(shape.binder.id, ⟨0⟩)] (inputHeap word) := by
    rw [params]
    exact .cons allocated (.nil _ _)
  have roots : header.function.body = [shape.loop.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have read (node : ExpressionNode) (found : header.function.source.lookupExpression? node.id = some node)
      (form : node.form = .reference shape.binder.name (.local shape.binder.id))
      (requirements : node.requirements = []) (coercions : node.coercions = [])
      (heap : Dynamic.Heap) (reads : Dynamic.Heap.Reads heap ⟨0⟩ ⟨.word, some (.word word), none⟩) :
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)]
        heap node.id (.word word) heap := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found)
    · rw [form]
      exact .local (by rw [requirements, coercions]; rfl) .head reads rfl rfl
    · rw [coercions]; exact .nil
  obtain ⟨loopContext, extension⟩ := header_extension header shape certified
  have initial : Dynamic.ForItemsExecute (Program.ofChecked compiled.sourceProgram) header.context
      header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)] (inputHeap word)
      [.letDecl shape.copy (some shape.first.id)] loopContext
      [(shape.copy.id, ⟨1⟩), (shape.binder.id, ⟨0⟩)] (sourceHeap word) := by
    exact .cons (.letInitialized
      (read shape.first shape.firstFound shape.firstForm shape.firstRequirements shape.firstCoercions
        (inputHeap word) (by exact .intro .head))
      (by rw [shape.copyType]; rfl) extension (by rw [shape.copyType]; exact .append)) .nil
  have condition : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      loopContext header.function.evidence header.function.source
      [(shape.copy.id, ⟨1⟩), (shape.binder.id, ⟨0⟩)] (sourceHeap word) shape.condition.id (.bool true) (sourceHeap word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.conditionFound)
    · rw [shape.conditionForm]
      exact .builtinBoolean (by rw [shape.conditionRequirements, shape.conditionCoercions]; rfl)
    · rw [shape.conditionCoercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)] (inputHeap word)
      header.function.body header.context (.returned (.word word)) (sourceHeap word) := by
    rw [roots]
    apply Dynamic.FunctionStatementsExecute.cons
    · exact .forLoop (lookupStatement?_sound shape.loopFound) shape.loopForm initial
        (.breaks condition (.terminal (.breakStmt (lookupStatement?_sound shape.breakingFound) shape.breakingForm) (.breaking _)))
    · exact .singleton (lookupStatement?_sound shape.returnedFound)
        (by rw [shape.returnedForm]; intro id impossible; cases impossible)
        (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm
          (read shape.second shape.secondFound shape.secondForm shape.secondRequirements shape.secondCoercions
            (sourceHeap word) (by exact .intro .head)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedLoop
