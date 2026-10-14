import Solcore.SourceSemantics.SourceInferenceSoundness

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness.MonomorphicGeneralization

open Frontend Frontend.SourceInference TypeSystem

/-- Closing a monomorphic scheme after an earlier inference substitution is
the same as closing its original scheme with the final extension. -/
theorem scheme_apply_extension
    {scheme : Scheme} {previous final : Substitution}
    (monomorphic : scheme.quantified = [])
    (extension : final.SemanticallyExtends previous) :
    (scheme.apply previous).apply final = scheme.apply final := by
  cases scheme with
  | mk quantified body =>
      simp only at monomorphic
      subst quantified
      simpa [Scheme.apply, Substitution.without] using
        congrArg (fun body => Scheme.mk [] body) (extension body)

/-- The canonical binder environment retains the empty quantifier lists of
all active binders after the initializer's current substitution. -/
theorem binderEnvironment_monomorphic
    {state : State} {substitution : Substitution}
    (monomorphic : ∀ binder ∈ state.localBinders,
      binder.scheme.quantified = []) :
    ∀ entry ∈ state.binderEnvironment.apply substitution,
      entry.2.quantified = [] := by
  intro entry member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨binder, binderMember, rfl⟩ := List.mem_map.mp originalMember
  exact monomorphic binder binderMember

/-- Each actual generalization-local scheme closes to the scheme at the
same stable binder identity in the final semantic context. -/
theorem binderEnvironment_localPresent
    {state : State} {previous final : Substitution}
    {target : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned state final target)
    (monomorphic : ∀ binder ∈ state.localBinders,
      binder.scheme.quantified = [])
    (extension : final.SemanticallyExtends previous) :
    ∀ entry ∈ state.binderEnvironment.apply previous,
      ∃ id, (id, entry.2.apply final) ∈ target.locals := by
  intro entry member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨binder, binderMember, rfl⟩ := List.mem_map.mp originalMember
  refine ⟨binder.id, aligned.locals_perm.mem_iff.mp ?_⟩
  have mono := monomorphic binder binderMember
  have same : (binder.scheme.apply previous).apply final =
      (binder.applySubstitution final).scheme := by
    rw [scheme_apply_extension mono extension]
    simp [TypedBinder.applySubstitution, Scheme.apply, mono,
      Substitution.without]
  change (binder.id, (binder.scheme.apply previous).apply final) ∈ _
  rw [same]
  exact List.mem_map.mpr ⟨binder, binderMember, rfl⟩

/-- Successful initializer inference restores the original active binder
stack. The environment that the checker really passes to generalization
therefore supplies both finite local premises of the blocker proof. -/
theorem initializer_locals
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {initializer : Syntax.Expr} {inferred : InferredExpression}
    {initial allocated initializerState : State} {id : StatementId}
    {final : Substitution} {target : SourceSemantics.Context}
    {locals : Environment}
    (allocation : initial.allocateStatementId = (id, allocated))
    (accepted : Detail.inferExprFuel fuel inferenceContext initializer none
      allocated = .ok (inferred, initializerState))
    (localsEq : locals = initializerState.binderEnvironment.apply
      initializerState.inference.substitution)
    (aligned : LocalEnvironmentAligned initial final target)
    (monomorphic : ∀ binder ∈ initial.localBinders,
      binder.scheme.quantified = [])
    (extension : final.SemanticallyExtends
      initializerState.inference.substitution) :
    (∀ entry ∈ locals, entry.2.quantified = []) ∧
    (∀ entry ∈ locals, ∃ id, (id, entry.2.apply final) ∈ target.locals) := by
  have childEq : initializerState.localBinders = allocated.localBinders := by
    exact congrArg LexicalScope.binders
      (Detail.inferExprFuel_success_lexicalScope_eq accepted)
  have allocatedEq : allocated.localBinders = initial.localBinders := by
    have same := congrArg (fun pair : StatementId × State => pair.2.localBinders)
      allocation
    exact same.symm
  have bindersEq := childEq.trans allocatedEq
  have childMonomorphic : ∀ binder ∈ initializerState.localBinders,
      binder.scheme.quantified = [] := by
    simpa only [bindersEq] using monomorphic
  rw [localsEq]
  exact ⟨binderEnvironment_monomorphic childMonomorphic,
    binderEnvironment_localPresent (aligned.congr_localBinders bindersEq)
      childMonomorphic extension⟩

end Solcore.SourceSemantics.SourceInferenceSoundness.MonomorphicGeneralization
