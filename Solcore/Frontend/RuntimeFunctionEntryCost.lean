import Solcore.Frontend.RuntimeFunctionEntryProperties
import Solcore.Frontend.TypedLetReturnBodyRunnerProperties

/-! Independent cost for a complete restricted entry contract. Preparation
provenance is mandatory; a prepared record alone supplies no such meaning.
The entry wrapper adds no transitions to the return body. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive RuntimeFunctionEvaluatesWithCost (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    Core.Store → Core.Ty → Core.Value → Core.Store → Nat → Prop where
  | intro {prepared : PreparedRuntimeFunction} {initialStore finalStore : Core.Store}
      {value : Core.Value} {cost : Nat}
      (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared)
      (bodyCost : TypedLetReturnBodyEvaluatesWithCost owner prepared.inputs.names prepared.inputs.environment
        initialStore declaration.value.body value finalStore cost) :
      RuntimeFunctionEvaluatesWithCost types owner declaration arguments
        initialStore prepared.returnType value finalStore cost

namespace RuntimeFunctionEvaluatesWithCost

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
  {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {cost : Nat}

theorem hasType (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
    initialStore type value finalStore cost) :
    RuntimeFunctionHasType types owner declaration arguments type := by
  cases evaluation with
  | intro preparation _ => exact preparation.hasType

theorem preserves_type (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
    initialStore type value finalStore cost) : Core.ValueHasType value type := by
  cases evaluation with
  | @intro prepared _ _ _ _ preparation bodyCost =>
      rw [← LocalInputs.toTypeInputs_names prepared.inputs] at bodyCost
      exact (bodyCost.erase.preserves_type preparation.body.hasType
        (by simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.sameIds)
        (by simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.environmentTyped)).1

theorem store_eq (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
    initialStore type value finalStore cost) : finalStore = initialStore := by
  cases evaluation with
  | intro _ bodyCost => exact bodyCost.store_eq

theorem cost_pos (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
    initialStore type value finalStore cost) : 0 < cost := by
  cases evaluation with
  | intro _ bodyCost => exact bodyCost.cost_pos

theorem deterministic {leftType rightType : Core.Ty} {left right : Core.Value}
    {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore leftType left leftStore leftCost)
    (second : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore rightType right rightStore rightCost) :
    leftType = rightType ∧ left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  cases first with
  | intro firstPreparation firstCost =>
      cases second with
      | intro secondPreparation secondCost =>
          cases firstPreparation.result_unique secondPreparation
          exact ⟨rfl, firstCost.deterministic secondCost⟩

end RuntimeFunctionEvaluatesWithCost
end Solcore.Frontend
