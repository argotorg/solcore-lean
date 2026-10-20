import Solcore.Frontend.SourceInference.ForItemInferenceContinuation

/-! A for statement's actual condition, body, post sequence and two saved
scopes connect each header to the statement's returned inference state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.ForStatementInferenceContinuation
open TypeSystem Detail

def loopContext (context : Context) : Context :=
  { context with loopDepth := context.loopDepth + 1 }

def node (source : Syntax.Statement) (initial : State) (initializers : InferredForItems)
    (condition : InferredExpression) (body : BlockResult) (post : InferredForItems) : StatementNode :=
  { id := initial.allocateStatementId.1, span := source.span, type := .unit,
    form := .forLoop initializers.items condition.id post.items body.statements }

def finish (source : Syntax.Statement) (initial : State) (initializers : InferredForItems)
    (condition : InferredExpression) (body : BlockResult) (post : InferredForItems) : StatementResult :=
  { id := initial.allocateStatementId.1, type := .unit, hasValue := false, sawReturn := false,
    state := (post.state.restoreLexicalScope initial.allocateStatementId.2.lexicalScope).recordNode
      (.statement (node source initial initializers condition body post)) }

structure Receipt (fuel : Nat) (context : Context) (source : Syntax.Statement)
    (initializers : List Syntax.ForItem) (condition : Syntax.Expr) (post : List Syntax.ForItem)
    (body : Syntax.Located (List Syntax.Statement)) (expected : Ty) (initial : State) (result : StatementResult) where
  initialized : InferredForItems
  test : InferredExpression
  testState : State
  bodyResult : BlockResult
  postResult : InferredForItems
  initialization : inferForItemsFuel fuel context initializers initial.allocateStatementId.2 = .ok initialized
  tested : inferExprFuel fuel context condition (some .bool) initialized.state = .ok (test, testState)
  bodyAccepted : inferStatementsFuel fuel (loopContext context) body.value expected testState = .ok bodyResult
  postAccepted : inferForItemsFuel fuel (loopContext context) post
    (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) = .ok postResult
  completed : result = finish source initial initialized test bodyResult postResult

theorem of_accepted {fuel : Nat} {context : Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expected : Ty} {initial : State} {result : StatementResult}
    {headerSpan : Syntax.SourceSpan}
    (form : source.value = .forLoop headerSpan initializers condition post body)
    (accepted : inferStatementFuel (fuel + 1) context source expected initial = .ok result) :
    Nonempty (Receipt fuel context source initializers condition post body expected initial result) := by
  unfold inferStatementFuel at accepted
  simp only [form, bind, Except.bind] at accepted
  cases initRun : inferForItemsFuel fuel context initializers initial.allocateStatementId.2 with
  | error error => simp [initRun] at accepted
  | ok initialized =>
      cases testRun : inferExprFuel fuel context condition (some .bool) initialized.state with
      | error error => simp [initRun, testRun] at accepted
      | ok pair =>
          rcases pair with ⟨test, testState⟩
          cases bodyRun : inferStatementsFuel fuel (loopContext context) body.value expected testState with
          | error error =>
              simp only [loopContext] at bodyRun
              simp [initRun, testRun, bodyRun] at accepted
          | ok bodyResult =>
              simp only [loopContext] at bodyRun
              cases postRun : inferForItemsFuel fuel (loopContext context) post
                  (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) with
              | error error =>
                  simp only [loopContext] at postRun
                  simp [initRun, testRun, bodyRun, postRun] at accepted
              | ok postResult =>
                  simp only [loopContext] at postRun
                  simp only [initRun, testRun, bodyRun, postRun,
                    pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
                  exact ⟨⟨initialized, test, testState, bodyResult, postResult,
                    initRun, testRun, bodyRun, postRun, accepted.symm⟩⟩

namespace Receipt
variable {fuel : Nat} {context : Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expected : Ty} {initial : State} {result : StatementResult}

theorem inference_eq (receipt : Receipt fuel context source initializers condition post body expected initial result) :
    result.state.inference = receipt.postResult.state.inference :=
  congrArg (fun value : StatementResult => value.state.inference) receipt.completed

theorem recorded (receipt : Receipt fuel context source initializers condition post body expected initial result) :
    .statement (node source initial receipt.initialized receipt.test receipt.bodyResult receipt.postResult) ∈ result.state.nodes := by
  have same := congrArg (fun value : StatementResult => value.state.nodes) receipt.completed
  rw [same]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Initial and post header callers are both ready at their genuine entry;
each actual header return has a continuation to the same final statement. -/
theorem inference (receipt : Receipt fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next) :
    initial.allocateStatementId.2.InferenceReady ∧
      (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope).InferenceReady ∧
      receipt.initialized.state.InferenceProgress result.state ∧
      receipt.postResult.state.InferenceProgress result.state := by
  have allocated := State.InferenceProgress.allocateStatementId initial ready.solved
  have initProperties := inferForItemsFuel_inferenceProperties ready.allocateStatementId
    formation canonical receipt.initialization
  have testProperties := inferExprFuel_inferenceProperties initProperties.2 formation canonical
    (by intro type member; cases Option.some.inj member; simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]) receipt.tested
  have bounds := expectedBelow.weaken (allocated.trans (initProperties.1.trans testProperties.1)).next_le
  have bodyProperties := inferStatementsFuel_inferenceProperties (context := loopContext context) testProperties.2.1 formation canonical
    bounds receipt.bodyAccepted
  have restored := State.restoreLexicalScope_inferenceProperties initProperties.2
    (testProperties.1.trans bodyProperties.1)
  have postProperties := inferForItemsFuel_inferenceProperties (context := loopContext context) restored.2 formation canonical receipt.postAccepted
  have last := State.InferenceProgress.of_inference_eq postProperties.2.solved receipt.inference_eq
  exact ⟨ready.allocateStatementId, restored.2, restored.1.trans (postProperties.1.trans last), last⟩

end Receipt
end Solcore.Frontend.SourceInference.ForStatementInferenceContinuation
