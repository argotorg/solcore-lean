import Solcore.SourceSemantics.Staging.SelectedExpressionSuccessPreservation
import Solcore.SourceSemantics.Staging.SelectedExpressionFaultPreservation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem expression_step (selectedBodies : SelectedBodies program registry) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (appliesIH : ∀ smaller, smaller < size → AppliesAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (rawIH : ∀ smaller, smaller < size → RawFormAt program registry smaller)
    (pathIH : ∀ smaller, smaller < size → CoercionPathAt program registry smaller) :
    ExpressionAt program registry size := by
  intro scope context environment before after id outcome type runtime covers locals heap typed trace
  cases outcome with
  | value value =>
      have post := expression_value_step selectedBodies size expressionIH expressionsIH appliesIH statementsIH
        rawIH pathIH runtime covers locals heap typed trace
      exact ⟨post.heap_typed, post.heap_extends, by intro actual equal; cases equal; exact post.value_typed⟩
  | fault failure =>
      have post := FaultPreservation.expression_fault_step selectedBodies size
        (fun n smaller => ExpressionAt.fault (expressionIH n smaller))
        (fun n smaller => ExpressionsAt.fault (expressionsIH n smaller))
        (fun n smaller => AppliesAt.fault (appliesIH n smaller))
        (fun n smaller => StatementsAt.fault (statementsIH n smaller))
        (fun n smaller => RawFormAt.fault (rawIH n smaller))
        (fun n smaller => CoercionPathAt.fault (pathIH n smaller))
        expressionIH expressionsIH rawIH runtime covers locals heap typed trace
      exact ⟨post.1, post.2, by intro value equal; cases equal⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
