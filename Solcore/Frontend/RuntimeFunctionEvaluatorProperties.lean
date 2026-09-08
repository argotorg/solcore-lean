import Solcore.Frontend.RuntimeFunctionEvaluator
import Solcore.Frontend.RuntimeFunctionEntryCost
import Solcore.Frontend.TypedLetReturnTreeEvaluatorProperties

/-! Exact direct results retain the complete preparation contract. Preparation
already supplies actual typed inputs, so successful gating cannot be followed
by raw evaluation failure. No Core execution or invented argument is needed. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem evaluated_sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {type : Core.Ty} {value : Core.Value} {cost : Nat}
    (accepted : evaluateRuntimeFunctionWithCost? types owner declaration arguments = some (type, value, cost))
    (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost types owner declaration arguments store type value store cost := by
  simp only [evaluateRuntimeFunctionWithCost?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨prepared, preparedAt, ⟨actual, actualCost⟩, bodyAt, same⟩ := accepted
  cases same
  exact .intro (prepareRuntimeFunction?_sound preparedAt) (evaluateTypedLetReturnTreeWithCost?_sound bodyAt store)

private theorem evaluated_complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost : Nat}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost) :
    evaluateRuntimeFunctionWithCost? types owner declaration arguments = some (type, value, cost) := by
  cases evaluation with
  | intro preparation bodyCost =>
      simp only [evaluateRuntimeFunctionWithCost?, preparation.complete,
        evaluateTypedLetReturnTreeWithCost?_complete bodyCost, bind, Option.bind_some, pure]

theorem runtimeFunctionEvaluatesWithCost_iff_evaluate
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost : Nat} :
    RuntimeFunctionEvaluatesWithCost types owner declaration arguments initialStore type value finalStore cost ↔
      finalStore = initialStore ∧
        evaluateRuntimeFunctionWithCost? types owner declaration arguments = some (type, value, cost) := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluated_complete evaluation⟩
  · rintro ⟨rfl, accepted⟩
    exact evaluated_sound accepted _

theorem evaluateRuntimeFunctionWithCost?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} :
    evaluateRuntimeFunctionWithCost? types owner declaration arguments = none ↔
      prepareRuntimeFunction? types owner declaration arguments = none := by
  constructor
  · intro absent
    cases preparedAt : prepareRuntimeFunction? types owner declaration arguments with
    | none => rfl
    | some prepared =>
        have preparation := prepareRuntimeFunction?_sound preparedAt
        obtain ⟨value, raw, _⟩ := preparation.body.hasType.evaluates
          (by simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.sameIds)
          (by simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.environmentTyped) []
        obtain ⟨cost, costed⟩ := raw.exists_cost
        have accepted := evaluated_complete (RuntimeFunctionEvaluatesWithCost.intro preparation
          (by simpa only [LocalInputs.toTypeInputs_names] using costed))
        rw [absent] at accepted
        cases accepted
  · intro rejected
    simp only [evaluateRuntimeFunctionWithCost?, rejected, bind, Option.bind_none]

end Solcore.Frontend
