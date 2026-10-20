import Solcore.Frontend.SourceInference.LocalGeneralizationBoundaryReceipts
import Solcore.Frontend.SourceInference.ExpressionProperties

/-! Inference readiness at an initialized declaration comes from the actual
initializer computation. The allocation following it preserves the exact
inference state, so its continuation starts at that computation's return. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference
open TypeSystem Detail

namespace LocalLetRequirementTiming

theorem Annotation.variablesBelow {context : Context} {source : Option Syntax.TypeExpr}
    {expected : Option Ty} (annotation : Annotation context source expected) (next : Nat) :
    ∀ type ∈ expected, type.VariablesBelow next := by
  cases annotation with
  | none => simp
  | some accepted =>
      intro type member
      cases Option.some.inj member
      exact resolveSourceType_success_variablesBelow accepted next

namespace Receipt
variable {fuel : Nat} {context : Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}

theorem inference_eq (receipt : Receipt fuel context source initial result) :
    result.state.inference = receipt.ready.inference :=
  congrArg (fun value : StatementResult => value.state.inference) receipt.completed

theorem initializer_inference (receipt : Receipt fuel context source initial result)
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    initial.InferenceProgress receipt.ready ∧ receipt.ready.InferenceReady ∧
      receipt.value.type.VariablesBelow receipt.ready.inference.next := by
  have child := inferExprFuel_inferenceProperties ready.allocateStatementId formation canonical
    (receipt.annotationAccepted.variablesBelow _) receipt.child
  exact ⟨(State.InferenceProgress.allocateStatementId initial ready.solved).trans child.1,
    child.2⟩

theorem continuation (receipt : Receipt fuel context source initial result)
    (solved : receipt.ready.inference.Solved) : receipt.ready.InferenceProgress result.state :=
  State.InferenceProgress.of_inference_eq solved receipt.inference_eq

end Receipt
end LocalLetRequirementTiming

namespace LocalHeaderRequirementTiming.Receipt
variable {fuel : Nat} {context : Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}

theorem inference_eq (receipt : Receipt fuel context source initial result) :
    result.2.inference = receipt.ready.inference :=
  congrArg (fun value : ForItemForm × State => value.2.inference) receipt.completed

theorem initializer_inference (receipt : Receipt fuel context source initial result)
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    initial.InferenceProgress receipt.ready ∧ receipt.ready.InferenceReady ∧
      receipt.value.type.VariablesBelow receipt.ready.inference.next :=
  inferExprFuel_inferenceProperties ready formation canonical
    (receipt.annotationAccepted.variablesBelow _) receipt.child

theorem continuation (receipt : Receipt fuel context source initial result)
    (solved : receipt.ready.inference.Solved) : receipt.ready.InferenceProgress result.2 :=
  State.InferenceProgress.of_inference_eq solved receipt.inference_eq

end LocalHeaderRequirementTiming.Receipt
end Solcore.Frontend.SourceInference
