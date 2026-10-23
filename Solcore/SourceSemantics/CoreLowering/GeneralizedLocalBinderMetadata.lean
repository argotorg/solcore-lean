import Solcore.Frontend.SourceCoreLocalPolymorphism

/-! The actual generalized binder compiler checks the complete contextual
binder metadata before returning its bundle type. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceCoreLocalPolymorphism
open SourceInference TypeSystem

theorem lowerBinder_success
    {catalog : Catalog} {caller : Key} {active : Substitution} {source : TypedSource}
    {scope : Scope} {binder : TypedBinder} {type : Core.Ty}
    (accepted : lowerBinder catalog caller active source scope binder = .ok type) :
    ∃ binding, catalog.binding caller binder.id = .ok binding ∧
      binding.binder.applySubstitution active = binder ∧
      type = binding.bundleType active := by
  unfold lowerBinder at accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  cases located : catalog.binding caller binder.id with
  | error error => simp only [located] at accepted; cases accepted
  | ok binding =>
    simp only [located] at accepted
    split at accepted
    · contradiction
    · exact ⟨binding, rfl, Classical.byContradiction ‹¬binding.binder.applySubstitution active ≠ binder›, (Except.ok.inj accepted).symm⟩

theorem lowerBinder_quantified
    {catalog : Catalog} {caller : Key} {active : Substitution} {source : TypedSource}
    {scope : Scope} {binder : TypedBinder} {type : Core.Ty} {binding : Binding}
    (accepted : lowerBinder catalog caller active source scope binder = .ok type)
    (located : catalog.binding caller binder.id = .ok binding) :
    binder.scheme.quantified = binding.binder.scheme.quantified := by
  obtain ⟨actual, selected, metadata, _⟩ := lowerBinder_success accepted
  have same : actual = binding := Except.ok.inj (selected.symm.trans located)
  subst actual
  rw [← metadata]
  rfl

end Solcore.Frontend.SourceCoreLocalPolymorphism
