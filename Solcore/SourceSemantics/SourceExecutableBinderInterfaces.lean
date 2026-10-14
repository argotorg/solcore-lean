import Solcore.Frontend.SourceInference.Resolution

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.ExecutableBinderInterfaces
open Frontend SourceInference TypeSystem

/-- The source table includes initialized declarations in statement bodies
and loop headers. This predicate does not require their types to be closed. -/
def SourceMonomorphic (source : TypedSource) : Prop :=
  ∀ binder ∈ source.initializedLetBinders, binder.scheme.quantified = []

private theorem item_binders_apply (substitution : Substitution) (item : ForItemForm) :
    (item.applySubstitution substitution).initializedLetBinders =
      item.initializedLetBinders.map (TypedBinder.applySubstitution substitution) := by
  cases item <;> try rfl
  case letDecl binder initializer => cases initializer <;> rfl

private theorem statement_binders_apply (substitution : Substitution) (form : StatementForm) :
    (form.applySubstitution substitution).initializedLetBinders =
      form.initializedLetBinders.map (TypedBinder.applySubstitution substitution) := by
  cases form <;> try rfl
  case letDecl binder initializer => cases initializer <;> rfl
  case forLoop initializer condition post body =>
    simp only [StatementForm.applySubstitution, StatementForm.initializedLetBinders,
      List.flatMap_map, List.map_append, List.map_flatMap, item_binders_apply]

private theorem node_binders_apply (substitution : Substitution) (node : Node) :
    (node.applySubstitution substitution).initializedLetBinders =
      node.initializedLetBinders.map (TypedBinder.applySubstitution substitution) := by
  cases node with
  | expression _ => rfl
  | statement statement => exact statement_binders_apply substitution statement.form

theorem initializedLetBinders_apply (substitution : Substitution) (source : TypedSource) :
    (source.applySubstitution substitution).initializedLetBinders =
      source.initializedLetBinders.map (TypedBinder.applySubstitution substitution) := by
  simp only [TypedSource.applySubstitution, TypedSource.initializedLetBinders,
    List.flatMap_map, List.map_flatMap, node_binders_apply]

theorem SourceMonomorphic.beforeSubstitution {source : TypedSource} {substitution : Substitution}
    (monomorphic : SourceMonomorphic (source.applySubstitution substitution)) : SourceMonomorphic source := by
  intro binder member
  have mapped : binder.applySubstitution substitution ∈
      (source.applySubstitution substitution).initializedLetBinders := by
    rw [initializedLetBinders_apply]
    exact List.mem_map.mpr ⟨binder, member, rfl⟩
  exact monomorphic (binder.applySubstitution substitution) mapped

theorem SourceMonomorphic.afterSubstitution {source : TypedSource} {substitution : Substitution}
    (monomorphic : SourceMonomorphic source) : SourceMonomorphic (source.applySubstitution substitution) := by
  intro binder member
  rw [initializedLetBinders_apply] at member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact monomorphic original originalMember

end Solcore.SourceSemantics.ExecutableBinderInterfaces
