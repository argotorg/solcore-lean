import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts

/-! A successful exact catalog lookup retains both requested key components.
The actual read certificate therefore identifies its complete binding. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceCoreLocalPolymorphism

theorem Catalog.binding_identity {catalog : Catalog} {caller : Key}
    {binder : Resolved.LocalId} {binding : Binding}
    (located : catalog.binding caller binder = .ok binding) :
    binding.caller = caller ∧ binding.binder.id = binder := by
  unfold Catalog.binding at located
  generalize filtered : catalog.bindings.filter
    (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) = entries at located
  cases entries with
  | nil => cases located
  | cons entry rest =>
    cases rest with
    | cons next tail => cases located
    | nil =>
      cases located
      have selected := List.mem_filter.mp (show binding ∈ catalog.bindings.filter
        (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) from by
          rw [filtered]
          exact List.mem_cons_self)
      exact of_decide_eq_true selected.2

end Solcore.Frontend.SourceCoreLocalPolymorphism

namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

theorem Certificate.binding_identity {catalog : Catalog} {caller : Key}
    {active : Substitution} {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate catalog caller active source scope id reason lowered) :
    receipt.binding.caller = caller ∧ receipt.binding.binder.id = receipt.binder :=
  Catalog.binding_identity receipt.bindingFound

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts
