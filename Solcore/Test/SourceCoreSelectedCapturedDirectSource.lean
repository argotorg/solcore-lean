import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedDirectForward

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCapturedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

structure Shape (source : TypedSource) where
  binder : TypedBinder
  read : ExpressionNode
  inner : StatementNode
  lambda : ExpressionNode
  outer : StatementNode
  inputs : source.inputs = [binder]
  binderType : binder.scheme = .mono .word
  roots : source.roots = [.statement outer.id]
  readFound : source.lookupExpression? read.id = some read
  readForm : read.form = .reference binder.name (.local binder.id)
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  innerFound : source.lookupStatement? inner.id = some inner
  innerForm : inner.form = .returnStmt (some read.id)
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [] .word [inner.id]
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  outerFound : source.lookupStatement? outer.id = some outer
  outerForm : outer.form = .returnStmt (some lambda.id)

def capturedHeap (word : Word) : Dynamic.Heap := ⟨[{type := .word, value := some (.word word)}]⟩

def capturedFunction {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (shape : Shape header.function.source) : Dynamic.Closure := {
  parameters := [], resultType := .word, body := [shape.inner.id]
  source := header.function.source, captured := [(shape.binder.id, ⟨0⟩)]
  context := header.context, evidence := header.function.evidence }

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

/-- Build the factory execution directly from its original allocation and lambda. -/
theorem factory_plain {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) (word : Word) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩ [.word word]
      (.closure (capturedFunction header shape)) (capturedHeap word) := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have allocated : Dynamic.Heap.Allocates ⟨[]⟩ shape.binder.scheme.body
      (some (.word word)) ⟨0⟩ (capturedHeap word) := by
    rw [shape.binderType]
    exact .append
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.word word]
      [(shape.binder.id, ⟨0⟩)] (capturedHeap word) := by
    rw [params]
    exact .cons allocated (.nil _ _)
  have roots : header.function.body = [shape.outer.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have expression : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)]
      (capturedHeap word) shape.lambda.id (.closure (capturedFunction header shape)) (capturedHeap word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.lambdaFound)
    · rw [shape.lambdaForm]
      exact .lambda (by rw [shape.lambdaRequirements, shape.lambdaCoercions]; rfl)
    · rw [shape.lambdaCoercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)] (capturedHeap word)
      header.function.body header.context (.returned (.closure (capturedFunction header shape))) (capturedHeap word) := by
    rw [roots]
    exact .singleton (lookupStatement?_sound shape.outerFound)
      (by rw [shape.outerForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.outerFound) shape.outerForm expression)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

/-- Read the literal retained capture without observing a completed direct call. -/
theorem closure_plain (word : Word) {context : SourceSemantics.Context} (invocation : Staging.Recursive.Scope)
    (signatures : context.signatures = (Program.ofChecked compiled.sourceProgram).signatures)
    (typed : Dynamic.ValueHasType context (capturedHeap word)
      (.closure (capturedFunction header shape)) (.function .unit .word)) :
    Dynamic.CallableApplies (Program.ofChecked compiled.sourceProgram) context invocation.evidence
      (capturedFunction header shape).evidence (capturedHeap word)
      (.closure (capturedFunction header shape)) [] (.word word) (capturedHeap word) := by
  obtain ⟨_parameters, _result, sameSignatures, code, covers, _captures⟩ := typed.closure_function_inv
  have frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) (capturedFunction header shape) :=
    ⟨sameSignatures.trans signatures, code.owner, code, code.requirement_ledger.idsUnique, covers⟩
  have read : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)]
      (capturedHeap word) shape.read.id (.word word) (capturedHeap word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.readFound)
    · rw [shape.readForm]
      exact .local (by rw [shape.readRequirements, shape.readCoercions]; rfl) .head
        (Dynamic.Heap.Allocates.reads_new (Dynamic.Heap.Allocates.append (heap := ⟨[]⟩)
          (type := .word) (value := some (.word word)))) rfl rfl
    · rw [shape.readCoercions]; exact .nil
  exact .closure rfl frame (.nil _) (.nil _ _)
    (.singleton (lookupStatement?_sound shape.innerFound)
      (by rw [shape.innerForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.innerFound) shape.innerForm read)) rfl

end Tests.SourceCoreSelectedCapturedDirect
