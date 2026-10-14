import Solcore.Test.SourceCoreCoercionPublicFixture
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedDirectForward

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCoercedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

structure Shape (source : TypedSource) where
  binder : TypedBinder
  read : ExpressionNode
  call : ExpressionNode
  inner : StatementNode
  lambda : ExpressionNode
  outer : StatementNode
  inputs : source.inputs = [binder]
  binderType : binder.scheme = .mono .bool
  roots : source.roots = [.statement outer.id]
  readFound : source.lookupExpression? read.id = some read
  readForm : read.form = .reference binder.name (.local binder.id)
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  innerFound : source.lookupStatement? inner.id = some inner
  innerForm : inner.form = .returnStmt (some call.id)
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [] .word [inner.id]
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  outerFound : source.lookupStatement? outer.id = some outer
  outerForm : outer.form = .returnStmt (some lambda.id)

def capturedHeap (flag : Bool) : Dynamic.Heap := ⟨[{type := .bool, value := some (.bool flag)}]⟩

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
theorem input_types : header.types = [.bool] := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.binderType, TypeSystem.Scheme.mono] using types.symm

/-- Build the factory execution directly from its original allocation and lambda. -/
theorem factory_plain {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) (flag : Bool) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩ [.bool flag]
      (.closure (capturedFunction header shape)) (capturedHeap flag) := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have allocated : Dynamic.Heap.Allocates ⟨[]⟩ shape.binder.scheme.body
      (some (.bool flag)) ⟨0⟩ (capturedHeap flag) := by
    rw [shape.binderType]
    exact .append
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.bool flag]
      [(shape.binder.id, ⟨0⟩)] (capturedHeap flag) := by
    rw [params]
    exact .cons allocated (.nil _ _)
  have roots : header.function.body = [shape.outer.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have expression : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)]
      (capturedHeap flag) shape.lambda.id (.closure (capturedFunction header shape)) (capturedHeap flag) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.lambdaFound)
    · rw [shape.lambdaForm]
      exact .lambda (by rw [shape.lambdaRequirements, shape.lambdaCoercions]; rfl)
    · rw [shape.lambdaCoercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)] (capturedHeap flag)
      header.function.body header.context (.returned (.closure (capturedFunction header shape))) (capturedHeap flag) := by
    rw [roots]
    exact .singleton (lookupStatement?_sound shape.outerFound)
      (by rw [shape.outerForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.outerFound) shape.outerForm expression)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

def appendBool (before : Dynamic.Heap) (flag : Bool) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .bool, value := some (.bool flag)}]⟩

/-- The numeric literal uses its original requirement and complete solved ledger. -/
theorem word_plain {program : SourceSemantics.Program} {function : CheckedFunction}
    (literal : Tests.SourceCoreCoercionPublic.WordLiteral function)
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context) :
    Dynamic.ExpressionEvaluates program context evidence function.typedBody environment heap
      literal.node.id (.word literal.validated.value) heap := by
  have metadata := SourceCoreElaboration.validateWordIntegerLiteral_sound literal.accepted
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound literal.found)
  · rw [literal.form]
    exact .integerLiteral (by rw [metadata.requirements, metadata.coercions]; rfl)
      (NumericLiteralEvidenceReceipts.word_constructs literal.accepted ledger runtime)
  · rw [metadata.coercions]; exact .nil

/-- Construct the selected method's ordinary allocation, read and chosen branch.
Its static extension and numeric ledger come from the exact selected body. -/
theorem method_plain {program : SourceSemantics.Program} {body : Dynamic.BodyInstance}
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (method : Tests.SourceCoreCoercionPublic.MethodShape function signature)
    (source : body.source = function.typedBody)
    {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    (extended : MonoBindersExtend body.source.owner body.context body.source.inputs types context)
    (scheme : method.binder.scheme = .mono .bool)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context)
    {evidence : Dynamic.EvidenceEnvironment} (covers : evidence.Covers body.context)
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.BodyInvokes program body evidence before [.bool flag]
      (.word (if flag then method.first.validated.value else method.second.validated.value))
      (appendBool before flag) := by
  let environment : Dynamic.Environment := [(method.binder.id, ⟨before.cells.length⟩)]
  have allocated : Dynamic.Heap.Allocates before method.binder.scheme.body
      (some (.bool flag)) ⟨before.cells.length⟩ (appendBool before flag) := by
    rw [scheme]; exact .append
  have bound : Dynamic.BindersAllocate [] before body.source.inputs [.bool flag]
      environment (appendBool before flag) := by
    rw [source, method.inputs]
    exact .cons allocated (.nil _ _)
  have read : Dynamic.ExpressionEvaluates program context evidence function.typedBody environment
      (appendBool before flag) method.read.node.id (.bool flag) (appendBool before flag) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound method.read.found)
    · rw [method.read.form]
      exact .local (by rw [method.read.requirements, method.read.coercions]; rfl)
        .head allocated.reads_new rfl rfl
    · rw [method.read.coercions]; exact .nil
  have expression : Dynamic.ExpressionEvaluates program context evidence function.typedBody environment
      (appendBool before flag) method.value.node.id
      (.word (if flag then method.first.validated.value else method.second.validated.value))
      (appendBool before flag) := by
    cases flag with
    | false =>
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound method.value.found)
      · rw [method.conditional]
        exact .conditionalFalse (by rw [method.value.requirements, method.value.coercions]; rfl)
          read (word_plain method.second ledger runtime)
      · rw [method.value.coercions]; exact .nil
    | true =>
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound method.value.found)
      · rw [method.conditional]
        exact .conditionalTrue (by rw [method.value.requirements, method.value.coercions]; rfl)
          read (word_plain method.first ledger runtime)
      · rw [method.value.coercions]; exact .nil
  have roots : Dynamic.StatementRoots body.source.roots [method.statement.id] := by
    rw [source, method.roots]; exact .cons .nil
  have executed : Dynamic.FunctionStatementsExecute program context evidence body.source environment
      (appendBool before flag) [method.statement.id] context
      (.returned (.word (if flag then method.first.validated.value else method.second.validated.value)))
      (appendBool before flag) := by
    rw [source]
    exact .singleton (lookupStatement?_sound method.statementFound)
      (by rw [method.statementForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound method.statementFound) method.statementForm expression)
  exact .returned covers roots extended bound executed rfl

/-- The generic target keeps its full retained instantiation and dictionary. -/
theorem identity_plain {function : CheckedFunction}
    (identity : Tests.SourceCoreCoercionPublic.SelectedIdentityShape function .bool)
    (source : header.function.source = function.typedBody)
    (scheme : identity.binder.scheme = .mono .bool)
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.CallableApplies (Program.ofChecked compiled.sourceProgram) context evidence header.function.evidence
      before (.global ⟨header.instantiation, header.function.evidence⟩) [.bool flag]
      (.bool flag) (appendBool before flag) := by
  have parameters : header.function.parameters = [identity.binder] := by
    rw [header.parameters, ← header.inputs, source, identity.inputs]
  have allocated : Dynamic.Heap.Allocates before identity.binder.scheme.body
      (some (.bool flag)) ⟨before.cells.length⟩ (appendBool before flag) := by
    rw [scheme]; exact .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      [(identity.binder.id, ⟨before.cells.length⟩)] (appendBool before flag) := by
    rw [parameters]; exact .cons allocated (.nil _ _)
  have roots : header.function.body = [identity.statement.id] :=
    roots_injective (header.agreement.roots.symm.trans (by rw [source, identity.roots]; rfl))
  have read : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(identity.binder.id, ⟨before.cells.length⟩)] (appendBool before flag)
      identity.read.node.id (.bool flag) (appendBool before flag) := by
    rw [source]
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound identity.read.found)
    · rw [identity.read.form]
      exact .local (by rw [identity.read.requirements, identity.read.coercions]; rfl)
        .head allocated.reads_new rfl rfl
    · rw [identity.read.coercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(identity.binder.id, ⟨before.cells.length⟩)] (appendBool before flag)
      header.function.body header.context (.returned (.bool flag)) (appendBool before flag) := by
    rw [source] at read
    rw [roots, source]
    exact .singleton (lookupStatement?_sound identity.statementFound)
      (by rw [identity.statementForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound identity.statementFound) identity.statementForm read)
  have invoked := header.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact .global header.frame.instantiated rfl header.frame.covers invoked

end Tests.SourceCoreSelectedCoercedDirect
