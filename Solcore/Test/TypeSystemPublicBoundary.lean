import Solcore.TypeSystem

set_option autoImplicit false

namespace Tests

example := @Solcore.TypeSystem.Ty.mem_freeVariables_application_iff
example := @Solcore.TypeSystem.Ty.mem_freeVariables_function_iff
example := @Solcore.TypeSystem.Ty.mem_freeVariables_product_iff
example := @Solcore.TypeSystem.Ty.mem_freeVariables_mapping_iff
example := @Solcore.TypeSystem.Ty.VariablesBelow
example := @Solcore.TypeSystem.Ty.variablesBelow_variable_iff
example := @Solcore.TypeSystem.Ty.variablesBelow_application_iff
example := @Solcore.TypeSystem.Ty.variablesBelow_function_iff
example := @Solcore.TypeSystem.Ty.variablesBelow_product_iff
example := @Solcore.TypeSystem.Ty.variablesBelow_mapping_iff
example := @Solcore.TypeSystem.Ty.containsVariable_eq_false_iff
example := @Solcore.TypeSystem.Substitution.lookup?_eq_none_iff_not_mem_domain
example := @Solcore.TypeSystem.Substitution.lookup?_eq_some_mem
example := @Solcore.TypeSystem.Substitution.domain_compose
example := @Solcore.TypeSystem.Substitution.mem_domain_compose_iff
example := @Solcore.TypeSystem.Substitution.domain_compose_nodup
example := @Solcore.TypeSystem.Substitution.mem_compose_iff
example := @Solcore.TypeSystem.Substitution.RangeAvoidsDomain
example := @Solcore.TypeSystem.Ty.apply_eq_self_of_domain_disjoint_freeVariables
example := @Solcore.TypeSystem.Substitution.SolvedBelow
example := @Solcore.TypeSystem.Substitution.SolvedBelow.empty
example := @Solcore.TypeSystem.Substitution.SolvedBelow.weaken
example := @Solcore.TypeSystem.Substitution.SolvedBelow.mono
example := @Solcore.TypeSystem.Substitution.SolvedBelow.lookup_range_outside_domain
example := @Solcore.TypeSystem.Substitution.SolvedBelow.apply_variables_below
example := @Solcore.TypeSystem.Substitution.SolvedBelow.variablesBelow_apply
example := @Solcore.TypeSystem.Substitution.SolvedBelow.apply_variables_outside_domain
example :=
  @Solcore.TypeSystem.Substitution.RangeAvoidsDomain.apply_variables_outside_older_domain
example := @Solcore.TypeSystem.Substitution.SolvedBelow.range_fixed
example := @Solcore.TypeSystem.Substitution.SolvedBelow.apply_idempotent
example := @Solcore.TypeSystem.Substitution.SolvedBelow.compose
example := @Solcore.TypeSystem.Substitution.RangeAvoidsDomain.compose
example := @Solcore.TypeSystem.Constraint.VariablesBelow
example := @Solcore.TypeSystem.Constraint.VariablesBelow.apply
example := @Solcore.TypeSystem.Constraint.VariablesOutsideDomain
example := @Solcore.TypeSystem.Constraint.VariablesOutsideDomain.apply
example := @Solcore.TypeSystem.ConstraintsBelow
example := @Solcore.TypeSystem.ConstraintsOutsideDomain
example := @Solcore.TypeSystem.Unification.unifyWithFuel_solvedBelow
example := @Solcore.TypeSystem.Unification.unifyWithFuel_rangeAvoidsDomain
example := @Solcore.TypeSystem.Unification.unify_solvedBelow
example := @Solcore.TypeSystem.Unification.unify_rangeAvoidsDomain
example := @Solcore.TypeSystem.Unification.unifyTypes_solvedBelow
example := @Solcore.TypeSystem.Unification.unifyTypes_rangeAvoidsDomain
example := @Solcore.TypeSystem.Scheme.instantiate_next_le
example := @Solcore.TypeSystem.DeclarationScheme.instantiate_next_le

private def solvedMetavariable : Solcore.TypeSystem.TypeVarId := ⟨0⟩

private def survivingMetavariable : Solcore.TypeSystem.TypeVarId := ⟨1⟩

private def nonemptySolvedSubstitution : Solcore.TypeSystem.Substitution :=
  [(solvedMetavariable, .variable survivingMetavariable)]

private theorem nonemptySolvedSubstitution_solved :
    Solcore.TypeSystem.Substitution.SolvedBelow
      nonemptySolvedSubstitution 2 := by
  apply Solcore.TypeSystem.Substitution.SolvedBelow.mono
  · decide
  · intro rangeVariable member
    have same : rangeVariable = survivingMetavariable := by
      simpa [Solcore.TypeSystem.Ty.freeVariables] using member
    subst rangeVariable
    decide
  · simp [Solcore.TypeSystem.Ty.freeVariables, solvedMetavariable,
      survivingMetavariable]

/-- A nonempty solved substitution is observationally idempotent on a type
containing both its replaced and surviving variables. -/
example :
    nonemptySolvedSubstitution.apply
        (nonemptySolvedSubstitution.apply
          (.product (.variable solvedMetavariable)
            (.variable survivingMetavariable))) =
      nonemptySolvedSubstitution.apply
        (.product (.variable solvedMetavariable)
          (.variable survivingMetavariable)) := by
  exact nonemptySolvedSubstitution_solved.apply_idempotent _

private def reverseSolvedSubstitution : Solcore.TypeSystem.Substitution :=
  [(survivingMetavariable, .variable solvedMetavariable)]

private theorem reverseSolvedSubstitution_solved :
    Solcore.TypeSystem.Substitution.SolvedBelow
      reverseSolvedSubstitution 2 := by
  apply Solcore.TypeSystem.Substitution.SolvedBelow.mono
  · decide
  · intro rangeVariable member
    have same : rangeVariable = solvedMetavariable := by
      simpa [Solcore.TypeSystem.Ty.freeVariables] using member
    subst rangeVariable
    decide
  · simp [Solcore.TypeSystem.Ty.freeVariables, solvedMetavariable,
      survivingMetavariable]

/-- Each side of the cyclic pair satisfies `SolvedBelow` independently. -/
example :
    Solcore.TypeSystem.Substitution.SolvedBelow reverseSolvedSubstitution 2 ∧
      Solcore.TypeSystem.Substitution.SolvedBelow nonemptySolvedSubstitution 2 :=
  ⟨reverseSolvedSubstitution_solved, nonemptySolvedSubstitution_solved⟩

/-- Two individually solved substitutions can compose to a range which
re-enters the combined domain when the cross invariant is absent. -/
example : reverseSolvedSubstitution.compose nonemptySolvedSubstitution =
    [(solvedMetavariable, .variable solvedMetavariable),
      (survivingMetavariable, .variable solvedMetavariable)] := by
  rfl

/-- The cyclic pair is rejected precisely by the explicit cross invariant. -/
example : ¬ Solcore.TypeSystem.Substitution.RangeAvoidsDomain
    reverseSolvedSubstitution nonemptySolvedSubstitution := by
  intro cross
  have outside := cross
    (metavariable := survivingMetavariable)
    (replacement := .variable solvedMetavariable)
    (by simp [reverseSolvedSubstitution]) solvedMetavariable
    (by simp [Solcore.TypeSystem.Ty.freeVariables])
  apply outside
  simp [nonemptySolvedSubstitution, Solcore.TypeSystem.Substitution.domain]

private def nestedConstraints : List Solcore.TypeSystem.Constraint := [{
  left := .product (.variable solvedMetavariable)
    (.variable survivingMetavariable)
  right := .product (.variable survivingMetavariable) .word
}]

private def nestedSolvedSubstitution : Solcore.TypeSystem.Substitution :=
  [(solvedMetavariable, .word), (survivingMetavariable, .word)]

/-- Composite decomposition followed by an occurs-safe variable alias closes
both ranges before the successful unifier returns. -/
example : Solcore.TypeSystem.Unification.unify nestedConstraints =
    .ok nestedSolvedSubstitution := by
  rfl

example : Solcore.TypeSystem.Substitution.SolvedBelow
    nestedSolvedSubstitution 2 := by
  apply Solcore.TypeSystem.Unification.unify_solvedBelow
    (constraints := nestedConstraints)
  · intro constraint member
    have same : constraint = {
        left := .product (.variable solvedMetavariable)
          (.variable survivingMetavariable)
        right := .product (.variable survivingMetavariable) .word
      } := by
      simpa [nestedConstraints] using member
    subst constraint
    constructor <;>
      simp [Solcore.TypeSystem.Ty.VariablesBelow,
        Solcore.TypeSystem.Ty.freeVariables] <;> decide
  · rfl

example := @Solcore.TypeSystem.InferState.fresh_substitution
example := @Solcore.TypeSystem.InferState.fresh_next
example := @Solcore.TypeSystem.InferState.instantiate_substitution
example := @Solcore.TypeSystem.InferState.instantiate_next_le
example := @Solcore.TypeSystem.InferState.instantiateDeclaration_substitution
example := @Solcore.TypeSystem.InferState.instantiateDeclaration_next_le
example := @Solcore.TypeSystem.InferState.unify_next
example := @Solcore.TypeSystem.InferState.solve_next
example := @Solcore.TypeSystem.InferState.Solved
example := @Solcore.TypeSystem.InferState.Solved.initial
example := @Solcore.TypeSystem.InferState.Solved.fresh
example := @Solcore.TypeSystem.InferState.Solved.instantiate
example := @Solcore.TypeSystem.InferState.Solved.instantiateDeclaration
example := @Solcore.TypeSystem.InferState.Solved.unify
example := @Solcore.TypeSystem.InferState.Solved.solve

private def outOfBoundMetavariable : Solcore.TypeSystem.TypeVarId := ⟨0⟩

private def zeroBoundState : Solcore.TypeSystem.InferState :=
  .initial 0

private def zeroBoundSolvedResult : Solcore.TypeSystem.InferState :=
  { next := 0
    substitution := [(outOfBoundMetavariable, .word)] }

/-- Without the resolved-input bound required by `InferState.Solved.unify`,
unification may solve a variable which is not below the state's allocator. -/
example : zeroBoundState.unify (.variable outOfBoundMetavariable) .word =
    .ok zeroBoundSolvedResult := by
  rfl

example : ¬ zeroBoundSolvedResult.Solved := by
  intro solved
  have below := solved.domain_below outOfBoundMetavariable (by
    simp [zeroBoundSolvedResult, Solcore.TypeSystem.Substitution.domain])
  exact (Nat.not_lt_zero 0) below

end Tests
