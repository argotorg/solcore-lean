import Solcore.Test.SourceCoreGeneralizedBodyExpressionCalls

/-! Allocate the original generalized closure, evaluate both distinct instances
from Source typing, and retain the actual captured flag across the first call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

 def StoredLambda {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap) (flag : Bool) : Prop :=
  ∃ definitionContext captured location cell,
    Dynamic.Environment.LooksUp environment shape.binder.id location ∧ Dynamic.Heap.Reads heap location cell ∧
    cell.generalized = some (shape.descriptor definitionContext captured) ∧
    Dynamic.RuntimeContextFields definitionContext context ∧ StoredValue shape.flag captured heap (.bool flag)

theorem StoredLambda.mono {source : TypedSource} {shape : LambdaShape source}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {flag : Bool}
    (stored : StoredLambda shape context environment before flag) (append : HeapAppends before after) :
    StoredLambda shape context environment after flag := by
  obtain ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields,capture⟩ := stored
  exact ⟨definitionContext,captured,location,cell,lookup,append.read read,descriptor,fields,capture.mono append⟩

theorem CallShape.typed {source : TypedSource} {binder : TypedBinder} {argument : ExpressionId} {type result : TypeSystem.Ty}
    (call : CallShape source binder argument type) {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context call.node.id result) :
    ∃ calleeType argumentType, ExpressionHasType source context call.callee.node.id calleeType ∧
      ExpressionHasType source context argument argumentType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans call.found)
    rw [call.form] at raw
    cases raw with
    | indirectCall callee arguments _ =>
      cases arguments with | cons argument _ => exact ⟨_,_,callee,argument⟩

theorem StoredLambda.invoke {program : SourceSemantics.Program} {source : TypedSource}
    {shape : LambdaShape source} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {flag : Bool}
    (stored : StoredLambda shape context environment before flag)
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    {argument : ExpressionId} {type result : TypeSystem.Ty} (call : CallShape source shape.binder argument type)
    (builtin : type = .word ∨ type = .bool)
    (typed : ExpressionHasType source context call.node.id result) {value : Dynamic.Value}
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment before argument value before) :
    ∃ after, Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      (resultValue value flag) after ∧ HeapAppends before after := by
  obtain ⟨_,_,callee,_⟩ := call.typed state.runtime.graph.nodeOccurrencesUnique typed
  obtain ⟨node,contains,sameType⟩ := callee.stored_type
  have sameNode := Option.some.inj ((lookupExpression?_complete state.runtime.graph.nodeOccurrencesUnique contains).symm.trans call.callee.found)
  subst node
  have ground : TypeWellFormed context type := by
    rcases builtin with same | same
    · rw [same]; exact ⟨callee.type_admissible.binders,.builtin .word⟩
    · rw [same]; exact ⟨callee.type_admissible.binders,.builtin .bool⟩
  obtain ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields,capture⟩ := stored
  have trace := shape.invoke_from_typed call captured environment evidence flag state.runtime
    (by simpa only [state.runtime.signatures] using wellFormed.signatures)
    state.covers state.locals state.heapTyped (sameType.symm ▸ callee) ground capture lookup read descriptor fields argumentTrace
  exact ⟨_,trace,⟨_,rfl⟩⟩

def closureHeap {source : TypedSource} (shape : LambdaShape source) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := shape.binder.scheme.body, value := none, generalized := some (shape.descriptor context environment)}]⟩

theorem generalized_step {program : SourceSemantics.Program} {source : TypedSource}
    (shape : LambdaShape source) (site : StatementAt source (.letDecl shape.binder (some shape.lambda.id)))
    {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {flag : Bool}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (captured : StoredValue shape.flag environment before (.bool flag))
    {control : ControlContext} {facts : StatementFacts}
    (typed : StatementHasType source control context site.node.id final facts) :
    Dynamic.StatementExecutes program context evidence source environment before site.node.id final
      (.fallthrough ((shape.binder.id,⟨before.cells.length⟩) :: environment)) (closureHeap shape context environment before) ∧
    SourceState program source final evidence ((shape.binder.id,⟨before.cells.length⟩) :: environment)
      (closureHeap shape context environment before) ∧
    StoredLambda shape final ((shape.binder.id,⟨before.cells.length⟩) :: environment) (closureHeap shape context environment before) flag := by
  have form := form_at state.runtime.graph.nodeOccurrencesUnique site.found typed
  rw [site.formEq] at form
  cases form with
  | letInitialized _ mono _ => rw [shape.scheme] at mono; cases mono
  | letInitializedGeneralized polymorphic _ _ _ extended =>
    have allocation : Dynamic.Heap.AllocatesGeneralized before (shape.descriptor context environment)
        ⟨before.cells.length⟩ (closureHeap shape context environment before) := .append
    have trace := Dynamic.StatementExecutes.letInitializedGeneralized (program := program)
      (evidence := evidence) (lookupStatement?_sound site.found) site.formEq (shape.captures context environment)
      polymorphic extended allocation
    exact ⟨trace,state.after_statement wellFormed typed trace,
      ⟨context,environment,_,_,.head,allocation.reads_new,rfl,.ofBinderExtends extended,captured.mono ⟨_,rfl⟩⟩⟩

theorem Shape.body_from_source {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {control : ControlContext} {facts : BodyFacts}
    (state : SourceState program source context evidence environment before)
    (wellFormed : ProgramWellFormed program)
    (typed : StatementsHaveType source control context
      [shape.initialized.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ next after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.initialized.node.id,shape.returned.node.id] next (.returned (outputValue flag)) after ∧ HeapAppends before after := by
  obtain ⟨middle,_,_,firstTyped,tailTyped⟩ := head_tail typed
  obtain ⟨declaration,stateNext,stored⟩ := generalized_step shape.f shape.initialized state wellFormed flagStored firstTyped
  obtain ⟨next,_,_,returnedTyped,_⟩ := head_tail tailTyped
  have original := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnedTyped
  rw [shape.returned.formEq] at original
  cases original with
  | returnValue tupleTyped =>
    obtain ⟨_,_,wordTyped,boolTyped⟩ := shape.tuple.children state.runtime.graph.nodeOccurrencesUnique tupleTyped
    obtain ⟨_,_,_,literalTyped⟩ := shape.wordCall.typed state.runtime.graph.nodeOccurrencesUnique wordTyped
    have literalTrace := shape.literal.evaluates (program := program) evidence ((shape.f.binder.id,⟨before.cells.length⟩)::environment) (closureHeap shape.f context environment before) state.runtime.graph.nodeOccurrencesUnique literalTyped
    rw [shape.literalValue] at literalTrace
    obtain ⟨firstHeap,firstTrace,firstAppend⟩ := stored.invoke stateNext wellFormed shape.wordCall (.inl rfl) wordTyped literalTrace
    have stateAfter := stateNext.after_expression wellFormed wordTyped firstTrace
    have allocatedPrefix : HeapAppends before (closureHeap shape.f context environment before) := ⟨_,rfl⟩
    have flagNext := ((flagStored.mono allocatedPrefix).under ⟨before.cells.length⟩ shape.fFlag).mono firstAppend
    obtain ⟨after,secondTrace,secondAppend⟩ := (stored.mono firstAppend).invoke stateAfter wellFormed
      shape.boolCall (.inr rfl) boolTyped (read_value shape.flagRead flagNext)
    have tupleTrace := shape.tuple.evaluates firstTrace secondTrace
    refine ⟨middle,after,.cons declaration ?_,allocatedPrefix.trans (firstAppend.trans secondAppend)⟩
    apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
    · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
    · exact .returnValue (lookupStatement?_sound shape.returned.found) shape.returned.formEq tupleTrace

end Tests.SourceCoreGeneralizedBodyExpression
