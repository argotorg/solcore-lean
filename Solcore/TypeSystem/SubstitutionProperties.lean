import Solcore.TypeSystem.Substitution

/-! Structural invariants for flexible metavariable substitutions. -/

set_option autoImplicit false

namespace Solcore.TypeSystem

namespace Substitution

/-- Lookup misses exactly the variables outside the ordered substitution
domain. -/
theorem lookup?_eq_none_iff_not_mem_domain (substitution : Substitution)
    (metavariable : TypeVarId) :
    substitution.lookup? metavariable = none ↔
      metavariable ∉ substitution.domain := by
  induction substitution with
  | nil => simp [lookup?, domain]
  | cons entry rest induction =>
      rcases entry with ⟨candidate, replacement⟩
      by_cases same : candidate = metavariable
      · simp [lookup?, domain, same]
      · simp [lookup?, domain, same, Ne.symm same, induction]

/-- Every successful first-match lookup names an actual substitution entry. -/
theorem lookup?_eq_some_mem
    {substitution : Substitution} {metavariable : TypeVarId}
    {replacement : Ty}
    (found : substitution.lookup? metavariable = some replacement) :
    (metavariable, replacement) ∈ substitution := by
  induction substitution with
  | nil => simp [lookup?] at found
  | cons entry rest induction =>
      rcases entry with ⟨candidate, candidateReplacement⟩
      by_cases same : candidate = metavariable
      · subst candidate
        simp [lookup?] at found
        cases found
        simp
      · have tailFound :
            Substitution.lookup? rest metavariable = some replacement := by
          simpa [lookup?, same] using found
        exact List.mem_cons_of_mem _ (induction tailFound)

/-- A solved substitution has a unique bounded domain, bounded replacement
variables, and no replacement variable that remains in its own domain. -/
structure SolvedBelow (substitution : Substitution) (next : Nat) : Prop where
  domain_nodup : substitution.domain.Nodup
  domain_below : ∀ metavariable, metavariable ∈ substitution.domain →
    metavariable.index < next
  range_below : ∀ {metavariable replacement},
    (metavariable, replacement) ∈ substitution →
      ∀ rangeVariable, rangeVariable ∈ replacement.freeVariables →
        rangeVariable.index < next
  range_outside_domain : ∀ {metavariable replacement},
    (metavariable, replacement) ∈ substitution →
      ∀ rangeVariable, rangeVariable ∈ replacement.freeVariables →
        rangeVariable ∉ substitution.domain

namespace SolvedBelow

/-- The empty substitution is solved below every fresh-variable bound. -/
theorem empty (next : Nat) : SolvedBelow Substitution.empty next := by
  constructor <;> simp [Substitution.empty, Substitution.domain]

/-- One occurs-check-safe bounded binding is a solved substitution. -/
theorem mono {metavariable : TypeVarId} {replacement : Ty} {next : Nat}
    (domain_below : metavariable.index < next)
    (range_below : ∀ rangeVariable,
      rangeVariable ∈ replacement.freeVariables →
        rangeVariable.index < next)
    (occurs_check : metavariable ∉ replacement.freeVariables) :
    SolvedBelow [(metavariable, replacement)] next := by
  constructor
  · simp [Substitution.domain]
  · intro candidate member
    simp only [Substitution.domain, List.map_cons, List.map_nil,
      List.mem_singleton] at member
    subst candidate
    exact domain_below
  · intro candidate candidateReplacement member rangeVariable occurs
    simp only [List.mem_singleton] at member
    cases member
    exact range_below rangeVariable occurs
  · intro candidate candidateReplacement member rangeVariable occurs
    simp only [List.mem_singleton] at member
    cases member
    simp only [Substitution.domain, List.map_cons, List.map_nil,
      List.mem_singleton]
    intro same
    subst rangeVariable
    exact occurs_check occurs

/-- A looked-up replacement cannot contain any variable in the solved
substitution's domain. -/
theorem lookup_range_outside_domain
    {substitution : Substitution} {next : Nat}
    (solved : SolvedBelow substitution next)
    {metavariable : TypeVarId} {replacement : Ty}
    (found : substitution.lookup? metavariable = some replacement)
    {rangeVariable : TypeVarId}
    (occurs : rangeVariable ∈ replacement.freeVariables) :
    rangeVariable ∉ substitution.domain := by
  exact solved.range_outside_domain (lookup?_eq_some_mem found)
    rangeVariable occurs

end SolvedBelow

end Substitution

namespace Ty

/-- A substitution fixes a type when its domain is disjoint from every free
variable of that type. -/
theorem apply_eq_self_of_domain_disjoint_freeVariables
    (substitution : Substitution) (type : Ty)
    (disjoint : ∀ metavariable,
      metavariable ∈ substitution.domain →
        metavariable ∉ type.freeVariables) :
    substitution.apply type = type := by
  induction type with
  | «variable» metavariable =>
      have absent : metavariable ∉ substitution.domain := by
        intro member
        exact disjoint metavariable member (by simp [Ty.freeVariables])
      have missing :=
        (Substitution.lookup?_eq_none_iff_not_mem_domain substitution
          metavariable).mpr absent
      simp [Substitution.apply, missing]
  | parameter parameter => rfl
  | constructor constructor => rfl
  | application left right leftInduction rightInduction =>
      have leftEq := leftInduction (by
        intro metavariable member occurs
        apply disjoint metavariable member
        exact (Ty.mem_freeVariables_application_iff metavariable left right).mpr
          (Or.inl occurs))
      have rightEq := rightInduction (by
        intro metavariable member occurs
        apply disjoint metavariable member
        exact (Ty.mem_freeVariables_application_iff metavariable left right).mpr
          (Or.inr occurs))
      simp [Substitution.apply, leftEq, rightEq]
  | function parameter result parameterInduction resultInduction =>
      have parameterEq := parameterInduction (by
        intro metavariable member occurs
        apply disjoint metavariable member
        exact (Ty.mem_freeVariables_function_iff
          metavariable parameter result).mpr (Or.inl occurs))
      have resultEq := resultInduction (by
        intro metavariable member occurs
        apply disjoint metavariable member
        exact (Ty.mem_freeVariables_function_iff
          metavariable parameter result).mpr (Or.inr occurs))
      simp [Substitution.apply, parameterEq, resultEq]
  | product left right leftInduction rightInduction =>
      have leftEq := leftInduction (by
        intro metavariable member occurs
        apply disjoint metavariable member
        exact (Ty.mem_freeVariables_product_iff metavariable left right).mpr
          (Or.inl occurs))
      have rightEq := rightInduction (by
        intro metavariable member occurs
        apply disjoint metavariable member
        exact (Ty.mem_freeVariables_product_iff metavariable left right).mpr
          (Or.inr occurs))
      simp [Substitution.apply, leftEq, rightEq]
  | mapping key value keyInduction valueInduction =>
      have keyEq := keyInduction (by
        intro metavariable member occurs
        apply disjoint metavariable member
        exact (Ty.mem_freeVariables_mapping_iff metavariable key value).mpr
          (Or.inl occurs))
      have valueEq := valueInduction (by
        intro metavariable member occurs
        apply disjoint metavariable member
        exact (Ty.mem_freeVariables_mapping_iff metavariable key value).mpr
          (Or.inr occurs))
      simp [Substitution.apply, keyEq, valueEq]
  | proxy inner induction =>
      simp only [Substitution.apply]
      rw [induction]
      exact disjoint
  | comptime inner induction =>
      simp only [Substitution.apply]
      rw [induction]
      exact disjoint
  | error => rfl

end Ty

namespace Substitution.SolvedBelow

/-- Every replacement stored in a solved substitution is already fixed by
that substitution. -/
theorem range_fixed
    {substitution : Substitution} {next : Nat}
    (solved : Substitution.SolvedBelow substitution next)
    {metavariable : TypeVarId} {replacement : Ty}
    (member : (metavariable, replacement) ∈ substitution) :
    substitution.apply replacement = replacement := by
  apply Ty.apply_eq_self_of_domain_disjoint_freeVariables
  intro rangeVariable domainMember occurs
  exact solved.range_outside_domain member rangeVariable occurs domainMember

/-- Applying a solved substitution twice has the same effect as applying it
once. -/
theorem apply_idempotent
    {substitution : Substitution} {next : Nat}
    (solved : Substitution.SolvedBelow substitution next) (type : Ty) :
    substitution.apply (substitution.apply type) =
      substitution.apply type := by
  induction type with
  | «variable» metavariable =>
      cases found : substitution.lookup? metavariable with
      | none => simp [Substitution.apply, found]
      | some replacement =>
          have member := Substitution.lookup?_eq_some_mem found
          simpa [Substitution.apply, found] using solved.range_fixed member
  | parameter parameter => rfl
  | constructor constructor => rfl
  | application function argument functionInduction argumentInduction =>
      simp [Substitution.apply, functionInduction, argumentInduction]
  | function parameter result parameterInduction resultInduction =>
      simp [Substitution.apply, parameterInduction, resultInduction]
  | product left right leftInduction rightInduction =>
      simp [Substitution.apply, leftInduction, rightInduction]
  | mapping key value keyInduction valueInduction =>
      simp [Substitution.apply, keyInduction, valueInduction]
  | proxy inner induction => simp [Substitution.apply, induction]
  | comptime inner induction => simp [Substitution.apply, induction]
  | error => rfl

end Substitution.SolvedBelow

end Solcore.TypeSystem
