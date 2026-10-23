import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerCompilation

/-! A contextual lambda callback retains the actual nested initializer bundle.
Its first initializer lookup and exact catalog lookup identify the same full
binding, including the initializer used by every candidate compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaInitializerReceipt
open Core Frontend SourceInference SourceCoreLocalPolymorphism
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalInitializerCompilation (Receipt)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ} {result : α}
    (accepted : action.mapError change = .ok result) : action = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

private theorem selected_binding {catalog : Catalog} {caller : Key} {id : ExpressionId}
    {initial binding : Binding}
    (selected : catalog.bindings.find? (fun candidate =>
      decide (candidate.caller = caller ∧ candidate.initializer = id)) = some initial)
    (located : catalog.binding caller initial.binder.id = .ok binding) :
    binding = initial ∧ binding.initializer = id := by
  have member := List.mem_of_find?_eq_some selected
  have matchedKeys : initial.caller = caller ∧ initial.initializer = id := by
    simpa only [decide_eq_true_eq] using List.find?_some selected
  have present : initial ∈ catalog.bindings.filter (fun entry =>
      decide (entry.caller = caller ∧ entry.binder.id = initial.binder.id)) :=
    List.mem_filter.mpr ⟨member, by simp [matchedKeys.1]⟩
  unfold Catalog.binding at located
  generalize filtered : catalog.bindings.filter (fun entry =>
    decide (entry.caller = caller ∧ entry.binder.id = initial.binder.id)) = entries at located
  rw [filtered] at present
  cases entries with
  | nil => cases located
  | cons entry rest =>
    cases rest with
    | cons next tail => cases located
    | nil =>
      cases located
      have same : initial = binding := List.mem_singleton.mp present
      exact ⟨same.symm, same ▸ matchedKeys.2⟩

/-- These are exactly the fields updated by the accepted contextual special
branch, including its current child budget and enclosing prepared context. -/
def contextualInputs (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared)
    (fuel budget : Nat) (current : SourceCoreFunctions.Context)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Word) : Inputs :=
  { inputs with representation := GeneralizedLocalLambdaCompilation.representation inputs prepared
                current := current
                parent := some prepared
                budget := budget
                fuel := fuel
                initializer := id
                scope := scope
                reasonAt := reasonAt }

/-- The real two lookups select the same binding. No initializer-selection
law or source node shape is assumed beyond the accepted callback branch. -/
theorem of_special_output {inputs : Inputs} {prepared : SourceCoreLocalEvidence.Prepared}
    {fuel budget : Nat} {current : SourceCoreFunctions.Context}
    {child : SourceCoreFunctions.ExpressionLowerer} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {initial : Binding} {output : Option SourceCoreBasic.LoweredExpr}
    (selected : inputs.locals.bindings.find? (fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)) = some initial)
    (notSelf : id ≠ inputs.initializer)
    (accepted : GeneralizedLocalLambdaCompilation.special inputs prepared fuel current child
      budget source scope id reasonAt = .ok output) :
    ∃ binding lowered, output = some lowered ∧
      inputs.locals.binding current.owner initial.binder.id = .ok binding ∧
      binding = initial ∧ binding.initializer = id ∧
      Nonempty (Receipt (contextualInputs inputs prepared fuel budget current scope id reasonAt)
        binding prepared.substitution lowered) := by
  unfold GeneralizedLocalLambdaCompilation.special at accepted
  obtain ⟨viewed, _, accepted⟩ := bind_ok accepted
  cases found : viewed.lookupExpression? id with
  | none => simp [found, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  | some node =>
    simp only [found, bind, Except.bind, pure, Except.pure] at accepted
    have different : inputs.initializer ≠ id := Ne.symm notSelf
    simp only [selected, Option.filter_some, ne_eq, Option.some.injEq, different,
      not_false_eq_true, decide_true, ↓reduceIte] at accepted
    obtain ⟨binding, located, accepted⟩ := bind_ok accepted
    have located := mapError_ok located
    obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
    have generated := mapError_ok generated
    obtain ⟨same, initializer⟩ := selected_binding selected located
    exact ⟨binding, lowered, (Except.ok.inj accepted).symm, located, same, initializer,
      GeneralizedLocalInitializerCompilation.of_accepted generated⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaInitializerReceipt
