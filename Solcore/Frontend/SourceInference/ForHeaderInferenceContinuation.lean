import Solcore.Frontend.SourceInference.ForStatementInferenceContinuation

/-! Both positions in a for header retain their actual binder and initializer
through the complete for statement. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.ForStatementInferenceContinuation
open TypeSystem Detail

structure HeaderContinuation (context : Context) (source : Syntax.ForItem)
    (final : State) (statement : StatementNode) where
  childFuel : Nat
  entry : State
  result : ForItemForm × State
  receipt : LocalHeaderRequirementTiming.Receipt childFuel context source entry result
  ready : receipt.ready.InferenceReady
  continuation : receipt.ready.InferenceProgress final
  retained : receipt.binding.1 ∈ statement.form.initializedLetBinders

theorem Receipt.initialized_header {fuel : Nat} {context : Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expected : Ty} {initial : State} {result : StatementResult}
    (receipt : Receipt fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (isPost : Bool) {index : Nat} {headerSource : Syntax.ForItem}
    (position : (if isPost then post else initializers)[index]? = some headerSource)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : headerSource.value = .letDecl name annotation (some initializer)) :
    Nonempty (HeaderContinuation (if isPost then loopContext context else context) headerSource result.state
      (node source initial receipt.initialized receipt.test receipt.bodyResult receipt.postResult)) := by
  have facts := receipt.inference ready formation canonical expectedBelow
  cases isPost with
  | false =>
      obtain ⟨occurrence⟩ := ForItemInferenceContinuation.of_position facts.1 formation canonical
        receipt.initialization position
      obtain ⟨childFuel, header, childReady, continuation, member⟩ := occurrence.initialized form formation canonical
      refine ⟨⟨childFuel, occurrence.entry, occurrence.result, header, childReady,
        continuation.trans facts.2.2.1, ?_⟩⟩
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨_, member, List.mem_singleton_self _⟩
  | true =>
      obtain ⟨occurrence⟩ := ForItemInferenceContinuation.of_position (context := loopContext context)
        facts.2.1 formation canonical receipt.postAccepted position
      obtain ⟨childFuel, header, childReady, continuation, member⟩ := occurrence.initialized form formation canonical
      refine ⟨⟨childFuel, occurrence.entry, occurrence.result, header, childReady,
        continuation.trans facts.2.2.2, ?_⟩⟩
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨_, member, List.mem_singleton_self _⟩

end Solcore.Frontend.SourceInference.ForStatementInferenceContinuation
