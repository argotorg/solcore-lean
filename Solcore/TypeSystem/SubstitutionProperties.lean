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

private theorem lookup?_append (left right : Substitution)
    (metavariable : TypeVarId) :
    lookup? (left ++ right) metavariable =
      match left.lookup? metavariable with
      | some replacement => some replacement
      | none => right.lookup? metavariable := by
  induction left with
  | nil => rfl
  | cons entry rest induction =>
      rcases entry with ⟨candidate, replacement⟩
      by_cases same : candidate = metavariable
      · simp [lookup?, same]
      · simp [lookup?, same, induction]

private theorem lookup?_map_apply (newer older : Substitution)
    (metavariable : TypeVarId) :
    lookup? (older.map fun entry => (entry.1, newer.apply entry.2))
        metavariable =
      (older.lookup? metavariable).map newer.apply := by
  induction older with
  | nil => rfl
  | cons entry rest induction =>
      rcases entry with ⟨candidate, replacement⟩
      by_cases same : candidate = metavariable
      · simp [lookup?, same]
      · simp [lookup?, same, induction]

private theorem lookup?_filter_not_mem (substitution : Substitution)
    (excluded : List TypeVarId) (metavariable : TypeVarId) :
    lookup? (substitution.filter fun entry => !(entry.1 ∈ excluded))
        metavariable =
      if metavariable ∈ excluded then none
      else substitution.lookup? metavariable := by
  induction substitution with
  | nil => simp [lookup?]
  | cons entry rest induction =>
      rcases entry with ⟨candidate, replacement⟩
      by_cases candidateExcluded : candidate ∈ excluded
      · by_cases same : candidate = metavariable
        · subst candidate
          simpa [candidateExcluded] using induction
        · simp [lookup?, candidateExcluded, same, induction]
      · by_cases same : candidate = metavariable
        · subst candidate
          simp [lookup?, candidateExcluded]
        · simp [lookup?, candidateExcluded, same, induction]

/-- Composition lookup implements older lookup followed by newer lookup. -/
theorem lookup?_compose (newer older : Substitution)
    (metavariable : TypeVarId) :
    (newer.compose older).lookup? metavariable =
      match older.lookup? metavariable with
      | some replacement => some (newer.apply replacement)
      | none => newer.lookup? metavariable := by
  rw [compose, lookup?_append, lookup?_map_apply, lookup?_filter_not_mem]
  cases found : older.lookup? metavariable with
  | none =>
      have missing : metavariable ∉ older.domain :=
        (lookup?_eq_none_iff_not_mem_domain older metavariable).mp found
      have missingMap : metavariable ∉ older.map Prod.fst := by
        simpa only [domain] using missing
      simp only [Option.map_none, missingMap, if_false]
  | some replacement => rfl

/-- Applying a composed substitution is the same as applying the older
substitution first and the newer substitution second. -/
theorem compose_apply (newer older : Substitution) (type : Ty) :
    (newer.compose older).apply type =
      newer.apply (older.apply type) := by
  induction type with
  | «variable» metavariable =>
      simp only [apply, lookup?_compose]
      cases older.lookup? metavariable <;> rfl
  | parameter parameter => rfl
  | constructor constructor => rfl
  | application function argument functionInduction argumentInduction =>
      simp only [apply, functionInduction, argumentInduction]
  | function parameter result parameterInduction resultInduction =>
      simp only [apply, parameterInduction, resultInduction]
  | product left right leftInduction rightInduction =>
      simp only [apply, leftInduction, rightInduction]
  | mapping key value keyInduction valueInduction =>
      simp only [apply, keyInduction, valueInduction]
  | proxy inner innerInduction => simp only [apply, innerInduction]
  | comptime inner innerInduction => simp only [apply, innerInduction]
  | error => rfl

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

/-- Flexible substitution distributes through a left-associated application
spine. -/
theorem apply_applyMany (substitution : Substitution) (head : Ty)
    (arguments : List Ty) :
    substitution.apply (Ty.applyMany head arguments) =
      Ty.applyMany (substitution.apply head)
        (arguments.map substitution.apply) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument rest induction =>
      exact induction (.application head argument)

/-- Flexible substitution distributes through a right-associated product
spine. -/
theorem apply_productMany (substitution : Substitution) (types : List Ty) :
    substitution.apply (Ty.productMany types) =
      Ty.productMany (types.map substitution.apply) := by
  induction types with
  | nil => rfl
  | cons head tail induction =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          simp only [Ty.productMany, Substitution.apply, List.map_cons]
          rw [induction]
          rfl

/-- Applying a substitution is allocator-bounded when every stored range is
bounded and every surviving source variable is bounded. -/
theorem apply_variables_below_of_range
    {substitution : Substitution} {next : Nat} {type : Ty}
    (rangeBelow : ∀ {metavariable replacement},
      (metavariable, replacement) ∈ substitution →
        replacement.VariablesBelow next)
    (sourceBelow : ∀ metavariable,
      metavariable ∈ type.freeVariables →
        metavariable ∉ substitution.domain →
          metavariable.index < next) :
    (substitution.apply type).VariablesBelow next := by
  induction type with
  | «variable» candidate =>
      cases found : substitution.lookup? candidate with
      | none =>
          simp only [Substitution.apply, found, Option.getD_none,
            Ty.variablesBelow_variable_iff]
          exact sourceBelow candidate (by simp [Ty.freeVariables])
            ((lookup?_eq_none_iff_not_mem_domain substitution candidate).mp
              found)
      | some replacement =>
          simp only [Substitution.apply, found, Option.getD_some]
          exact rangeBelow (lookup?_eq_some_mem found)
  | parameter parameter => simp [Substitution.apply]
  | constructor constructor => simp [Substitution.apply]
  | application left right leftInduction rightInduction =>
      simp only [Substitution.apply, Ty.variablesBelow_application_iff]
      constructor
      · apply leftInduction
        intro metavariable member outside
        exact sourceBelow metavariable
          ((Ty.mem_freeVariables_application_iff metavariable left right).mpr
            (Or.inl member)) outside
      · apply rightInduction
        intro metavariable member outside
        exact sourceBelow metavariable
          ((Ty.mem_freeVariables_application_iff metavariable left right).mpr
            (Or.inr member)) outside
  | function parameter result parameterInduction resultInduction =>
      simp only [Substitution.apply, Ty.variablesBelow_function_iff]
      constructor
      · apply parameterInduction
        intro metavariable member outside
        exact sourceBelow metavariable
          ((Ty.mem_freeVariables_function_iff
            metavariable parameter result).mpr (Or.inl member)) outside
      · apply resultInduction
        intro metavariable member outside
        exact sourceBelow metavariable
          ((Ty.mem_freeVariables_function_iff
            metavariable parameter result).mpr (Or.inr member)) outside
  | product left right leftInduction rightInduction =>
      simp only [Substitution.apply, Ty.variablesBelow_product_iff]
      constructor
      · apply leftInduction
        intro metavariable member outside
        exact sourceBelow metavariable
          ((Ty.mem_freeVariables_product_iff metavariable left right).mpr
            (Or.inl member)) outside
      · apply rightInduction
        intro metavariable member outside
        exact sourceBelow metavariable
          ((Ty.mem_freeVariables_product_iff metavariable left right).mpr
            (Or.inr member)) outside
  | mapping key value keyInduction valueInduction =>
      simp only [Substitution.apply, Ty.variablesBelow_mapping_iff]
      constructor
      · apply keyInduction
        intro metavariable member outside
        exact sourceBelow metavariable
          ((Ty.mem_freeVariables_mapping_iff metavariable key value).mpr
            (Or.inl member)) outside
      · apply valueInduction
        intro metavariable member outside
        exact sourceBelow metavariable
          ((Ty.mem_freeVariables_mapping_iff metavariable key value).mpr
            (Or.inr member)) outside
  | proxy inner induction =>
      simp only [Substitution.apply, Ty.variablesBelow_proxy_iff]
      exact induction sourceBelow
  | comptime inner induction =>
      simp only [Substitution.apply, Ty.variablesBelow_comptime_iff]
      exact induction sourceBelow
  | error => simp [Substitution.apply]

/-- Erasing one domain key never creates a new substitution entry. -/
theorem mem_of_mem_erase
    {substitution : Substitution} {erased : TypeVarId}
    {entry : TypeVarId × Ty}
    (member : entry ∈ substitution.erase erased) :
    entry ∈ substitution := by
  exact (List.mem_filter.mp member).1

/-- Removing quantified keys never creates a new substitution entry. -/
theorem mem_of_mem_without
    {substitution : Substitution} {variables : List TypeVarId}
    {entry : TypeVarId × Ty}
    (member : entry ∈ substitution.without variables) :
    entry ∈ substitution := by
  induction variables generalizing substitution with
  | nil => simpa [without] using member
  | cons erased variables induction =>
      rw [without, List.foldl_cons] at member
      exact mem_of_mem_erase (induction member)

private theorem map_fst_filter_not_mem_domain
    (substitution : Substitution) (excluded : List TypeVarId) :
    (substitution.filter fun entry => !(entry.1 ∈ excluded)).map Prod.fst =
      substitution.domain.filter fun metavariable => !(metavariable ∈ excluded) := by
  induction substitution with
  | nil => rfl
  | cons entry rest induction =>
      rcases entry with ⟨metavariable, replacement⟩
      by_cases excludedMember : metavariable ∈ excluded
      · simp [domain, excludedMember, induction]
      · simp [domain, excludedMember, induction]

/-- Composition retains the complete older domain, followed by precisely the
newer variables which are not already present there. -/
theorem domain_compose (newer older : Substitution) :
    (newer.compose older).domain =
      older.domain ++ newer.domain.filter fun metavariable =>
        !(metavariable ∈ older.domain) := by
  simp [compose, domain, List.map_map, Function.comp_def,
    map_fst_filter_not_mem_domain]
  rfl

/-- Composition covers exactly the union of the two input domains. -/
theorem mem_domain_compose_iff (newer older : Substitution)
    (metavariable : TypeVarId) :
    metavariable ∈ (newer.compose older).domain ↔
      metavariable ∈ older.domain ∨ metavariable ∈ newer.domain := by
  rw [domain_compose]
  by_cases olderMember : metavariable ∈ older.domain <;>
    simp [olderMember]

/-- Composition preserves domain uniqueness when both input domains are
unique. -/
theorem domain_compose_nodup
    {newer older : Substitution}
    (newerNodup : newer.domain.Nodup)
    (olderNodup : older.domain.Nodup) :
    (newer.compose older).domain.Nodup := by
  rw [domain_compose, List.nodup_append]
  refine ⟨olderNodup, newerNodup.filter _, ?_⟩
  intro metavariable olderMember
  intro newerVariable newerMember same
  subst newerVariable
  have fresh := (List.mem_filter.mp newerMember).2
  simp [olderMember] at fresh

/-- Exact entry provenance for composition: an output entry is either an
older entry with its range updated by `newer`, or a genuinely new entry. -/
theorem mem_compose_iff
    {newer older : Substitution}
    {metavariable : TypeVarId} {replacement : Ty} :
    (metavariable, replacement) ∈ newer.compose older ↔
      (∃ olderReplacement,
        (metavariable, olderReplacement) ∈ older ∧
          replacement = newer.apply olderReplacement) ∨
      ((metavariable, replacement) ∈ newer ∧
        metavariable ∉ older.domain) := by
  unfold compose
  constructor
  · intro member
    rcases List.mem_append.mp member with olderMember | newerMember
    · rcases List.mem_map.mp olderMember with ⟨entry, entryMember, entryEq⟩
      rcases entry with ⟨olderMetavariable, olderReplacement⟩
      simp only at entryEq
      cases entryEq
      exact Or.inl ⟨olderReplacement, entryMember, rfl⟩
    · have filtered := List.mem_filter.mp newerMember
      have noEntryWithKey : ∀ candidateReplacement,
          (metavariable, candidateReplacement) ∉ older := by
        simpa using filtered.2
      have fresh : metavariable ∉ older.domain := by
        intro domainMember
        rcases List.mem_map.mp domainMember with ⟨entry, entryMember, entryEq⟩
        rcases entry with ⟨candidate, candidateReplacement⟩
        simp only at entryEq
        subst candidate
        exact noEntryWithKey candidateReplacement entryMember
      exact Or.inr ⟨filtered.1, fresh⟩
  · rintro (⟨olderReplacement, olderMember, rfl⟩ | ⟨newerMember, fresh⟩)
    · exact List.mem_append_left _
        (List.mem_map.mpr ⟨_, olderMember, rfl⟩)
    · have noEntryWithKey : ∀ candidateReplacement,
          (metavariable, candidateReplacement) ∉ older := by
        intro candidateReplacement member
        apply fresh
        exact List.mem_map.mpr ⟨_, member, rfl⟩
      exact List.mem_append_right _
        (List.mem_filter.mpr ⟨newerMember, by
          simpa using noEntryWithKey⟩)

/-- Cross-substitution closure condition required by composition: no range
variable introduced by `newer` may re-enter the older domain. -/
def RangeAvoidsDomain (newer older : Substitution) : Prop :=
  ∀ {metavariable replacement},
    (metavariable, replacement) ∈ newer →
      ∀ rangeVariable, rangeVariable ∈ replacement.freeVariables →
        rangeVariable ∉ older.domain

/-- `result` semantically extends `previous` when reapplying the previous
substitution before the result cannot change any type. -/
def SemanticallyExtends (result previous : Substitution) : Prop :=
  ∀ type, result.apply (previous.apply type) = result.apply type

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

/-- A solved substitution remains solved when the allocator bound grows. -/
theorem weaken
    {substitution : Substitution} {lower upper : Nat}
    (solved : SolvedBelow substitution lower) (bound : lower ≤ upper) :
    SolvedBelow substitution upper := by
  constructor
  · exact solved.domain_nodup
  · intro metavariable member
    exact Nat.lt_of_lt_of_le (solved.domain_below metavariable member) bound
  · intro metavariable replacement member rangeVariable occurs
    exact Nat.lt_of_lt_of_le
      (solved.range_below member rangeVariable occurs) bound
  · exact solved.range_outside_domain

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

/-- Applying a solved substitution to a bounded type cannot introduce a
variable at or above the same bound. -/
theorem apply_variables_below
    {substitution : Substitution} {next : Nat}
    (solved : SolvedBelow substitution next) (type : Ty)
    (sourceBelow : ∀ metavariable,
      metavariable ∈ type.freeVariables → metavariable.index < next) :
    ∀ metavariable,
      metavariable ∈ (substitution.apply type).freeVariables →
        metavariable.index < next := by
  induction type with
  | «variable» candidate =>
      intro metavariable occurs
      cases found : substitution.lookup? candidate with
      | none =>
          simp only [Substitution.apply, found, Option.getD_none,
            Ty.freeVariables, List.mem_singleton] at occurs
          subst metavariable
          exact sourceBelow candidate (by simp [Ty.freeVariables])
      | some replacement =>
          simp only [Substitution.apply, found, Option.getD_some] at occurs
          exact solved.range_below (lookup?_eq_some_mem found)
            metavariable occurs
  | parameter parameter => simp [Substitution.apply, Ty.freeVariables]
  | constructor constructor => simp [Substitution.apply, Ty.freeVariables]
  | application left right leftInduction rightInduction =>
      intro metavariable occurs
      simp only [Substitution.apply] at occurs
      rw [Ty.mem_freeVariables_application_iff] at occurs
      rcases occurs with occurs | occurs
      · exact leftInduction (fun candidate member =>
          sourceBelow candidate
            ((Ty.mem_freeVariables_application_iff candidate left right).mpr
              (Or.inl member))) metavariable occurs
      · exact rightInduction (fun candidate member =>
          sourceBelow candidate
            ((Ty.mem_freeVariables_application_iff candidate left right).mpr
              (Or.inr member))) metavariable occurs
  | function parameter result parameterInduction resultInduction =>
      intro metavariable occurs
      simp only [Substitution.apply] at occurs
      rw [Ty.mem_freeVariables_function_iff] at occurs
      rcases occurs with occurs | occurs
      · exact parameterInduction (fun candidate member =>
          sourceBelow candidate
            ((Ty.mem_freeVariables_function_iff
              candidate parameter result).mpr (Or.inl member)))
          metavariable occurs
      · exact resultInduction (fun candidate member =>
          sourceBelow candidate
            ((Ty.mem_freeVariables_function_iff
              candidate parameter result).mpr (Or.inr member)))
          metavariable occurs
  | product left right leftInduction rightInduction =>
      intro metavariable occurs
      simp only [Substitution.apply] at occurs
      rw [Ty.mem_freeVariables_product_iff] at occurs
      rcases occurs with occurs | occurs
      · exact leftInduction (fun candidate member =>
          sourceBelow candidate
            ((Ty.mem_freeVariables_product_iff candidate left right).mpr
              (Or.inl member))) metavariable occurs
      · exact rightInduction (fun candidate member =>
          sourceBelow candidate
            ((Ty.mem_freeVariables_product_iff candidate left right).mpr
              (Or.inr member))) metavariable occurs
  | mapping key value keyInduction valueInduction =>
      intro metavariable occurs
      simp only [Substitution.apply] at occurs
      rw [Ty.mem_freeVariables_mapping_iff] at occurs
      rcases occurs with occurs | occurs
      · exact keyInduction (fun candidate member =>
          sourceBelow candidate
            ((Ty.mem_freeVariables_mapping_iff candidate key value).mpr
              (Or.inl member))) metavariable occurs
      · exact valueInduction (fun candidate member =>
          sourceBelow candidate
            ((Ty.mem_freeVariables_mapping_iff candidate key value).mpr
              (Or.inr member))) metavariable occurs
  | proxy inner induction =>
      exact induction sourceBelow
  | comptime inner induction =>
      exact induction sourceBelow
  | error => simp [Substitution.apply, Ty.freeVariables]

/-- Type-level form of `apply_variables_below`. -/
theorem variablesBelow_apply
    {substitution : Substitution} {next : Nat}
    (solved : SolvedBelow substitution next) {type : Ty}
    (below : Ty.VariablesBelow next type) :
    Ty.VariablesBelow next (substitution.apply type) :=
  solved.apply_variables_below type below

/-- Every variable surviving application of a solved substitution lies
outside that substitution's domain. -/
theorem apply_variables_outside_domain
    {substitution : Substitution} {next : Nat}
    (solved : SolvedBelow substitution next) (type : Ty) :
    ∀ metavariable,
      metavariable ∈ (substitution.apply type).freeVariables →
        metavariable ∉ substitution.domain := by
  induction type with
  | «variable» candidate =>
      intro metavariable occurs
      cases found : substitution.lookup? candidate with
      | none =>
          simp only [Substitution.apply, found, Option.getD_none,
            Ty.freeVariables, List.mem_singleton] at occurs
          subst metavariable
          exact (lookup?_eq_none_iff_not_mem_domain substitution candidate).mp
            found
      | some replacement =>
          simp only [Substitution.apply, found, Option.getD_some] at occurs
          exact solved.lookup_range_outside_domain found occurs
  | parameter parameter => simp [Substitution.apply, Ty.freeVariables]
  | constructor constructor => simp [Substitution.apply, Ty.freeVariables]
  | application left right leftInduction rightInduction =>
      intro metavariable occurs
      simp only [Substitution.apply] at occurs
      rw [Ty.mem_freeVariables_application_iff] at occurs
      exact occurs.elim (leftInduction metavariable)
        (rightInduction metavariable)
  | function parameter result parameterInduction resultInduction =>
      intro metavariable occurs
      simp only [Substitution.apply] at occurs
      rw [Ty.mem_freeVariables_function_iff] at occurs
      exact occurs.elim (parameterInduction metavariable)
        (resultInduction metavariable)
  | product left right leftInduction rightInduction =>
      intro metavariable occurs
      simp only [Substitution.apply] at occurs
      rw [Ty.mem_freeVariables_product_iff] at occurs
      exact occurs.elim (leftInduction metavariable)
        (rightInduction metavariable)
  | mapping key value keyInduction valueInduction =>
      intro metavariable occurs
      simp only [Substitution.apply] at occurs
      rw [Ty.mem_freeVariables_mapping_iff] at occurs
      exact occurs.elim (keyInduction metavariable)
        (valueInduction metavariable)
  | proxy inner induction => exact induction
  | comptime inner induction => exact induction
  | error => simp [Substitution.apply, Ty.freeVariables]

end SolvedBelow

namespace RangeAvoidsDomain

/-- Applying `newer` preserves avoidance of `older`'s domain when both its
source type and every newer replacement already avoid that domain. -/
theorem apply_variables_outside_older_domain
    {newer older : Substitution}
    (cross : RangeAvoidsDomain newer older) (type : Ty)
    (sourceOutside : ∀ metavariable,
      metavariable ∈ type.freeVariables →
        metavariable ∉ older.domain) :
    ∀ metavariable,
      metavariable ∈ (newer.apply type).freeVariables →
        metavariable ∉ older.domain := by
  induction type with
  | «variable» candidate =>
      intro metavariable occurs
      cases found : newer.lookup? candidate with
      | none =>
          simp only [Substitution.apply, found, Option.getD_none,
            Ty.freeVariables, List.mem_singleton] at occurs
          subst metavariable
          exact sourceOutside candidate (by simp [Ty.freeVariables])
      | some replacement =>
          simp only [Substitution.apply, found, Option.getD_some] at occurs
          exact cross (lookup?_eq_some_mem found) metavariable occurs
  | parameter parameter => simp [Substitution.apply, Ty.freeVariables]
  | constructor constructor => simp [Substitution.apply, Ty.freeVariables]
  | application left right leftInduction rightInduction =>
      intro metavariable occurs
      simp only [Substitution.apply] at occurs
      rw [Ty.mem_freeVariables_application_iff] at occurs
      rcases occurs with occurs | occurs
      · exact leftInduction (fun candidate member =>
          sourceOutside candidate
            ((Ty.mem_freeVariables_application_iff candidate left right).mpr
              (Or.inl member))) metavariable occurs
      · exact rightInduction (fun candidate member =>
          sourceOutside candidate
            ((Ty.mem_freeVariables_application_iff candidate left right).mpr
              (Or.inr member))) metavariable occurs
  | function parameter result parameterInduction resultInduction =>
      intro metavariable occurs
      simp only [Substitution.apply] at occurs
      rw [Ty.mem_freeVariables_function_iff] at occurs
      rcases occurs with occurs | occurs
      · exact parameterInduction (fun candidate member =>
          sourceOutside candidate
            ((Ty.mem_freeVariables_function_iff
              candidate parameter result).mpr (Or.inl member)))
          metavariable occurs
      · exact resultInduction (fun candidate member =>
          sourceOutside candidate
            ((Ty.mem_freeVariables_function_iff
              candidate parameter result).mpr (Or.inr member)))
          metavariable occurs
  | product left right leftInduction rightInduction =>
      intro metavariable occurs
      simp only [Substitution.apply] at occurs
      rw [Ty.mem_freeVariables_product_iff] at occurs
      rcases occurs with occurs | occurs
      · exact leftInduction (fun candidate member =>
          sourceOutside candidate
            ((Ty.mem_freeVariables_product_iff candidate left right).mpr
              (Or.inl member))) metavariable occurs
      · exact rightInduction (fun candidate member =>
          sourceOutside candidate
            ((Ty.mem_freeVariables_product_iff candidate left right).mpr
              (Or.inr member))) metavariable occurs
  | mapping key value keyInduction valueInduction =>
      intro metavariable occurs
      simp only [Substitution.apply] at occurs
      rw [Ty.mem_freeVariables_mapping_iff] at occurs
      rcases occurs with occurs | occurs
      · exact keyInduction (fun candidate member =>
          sourceOutside candidate
            ((Ty.mem_freeVariables_mapping_iff candidate key value).mpr
              (Or.inl member))) metavariable occurs
      · exact valueInduction (fun candidate member =>
          sourceOutside candidate
            ((Ty.mem_freeVariables_mapping_iff candidate key value).mpr
              (Or.inr member))) metavariable occurs
  | proxy inner induction => exact induction sourceOutside
  | comptime inner induction => exact induction sourceOutside
  | error => simp [Substitution.apply, Ty.freeVariables]

/-- Avoidance of a fixed older domain is closed under substitution
composition. -/
theorem compose
    {newer middle older : Substitution}
    (newerAvoids : RangeAvoidsDomain newer older)
    (middleAvoids : RangeAvoidsDomain middle older) :
    RangeAvoidsDomain (newer.compose middle) older := by
  intro metavariable replacement member rangeVariable occurs
  rw [mem_compose_iff] at member
  rcases member with
    ⟨middleReplacement, middleMember, replacementEq⟩ |
      ⟨newerMember, newerFresh⟩
  · subst replacement
    exact newerAvoids.apply_variables_outside_older_domain middleReplacement
      (middleAvoids middleMember) rangeVariable occurs
  · exact newerAvoids newerMember rangeVariable occurs

end RangeAvoidsDomain

end Substitution

namespace ParameterSubstitution

/-- Every successful rigid-parameter lookup names an actual substitution
entry. -/
theorem lookup?_eq_some_mem
    {substitution : ParameterSubstitution}
    {parameter : TypeParameterId} {replacement : Ty}
    (found : substitution.lookup? parameter = some replacement) :
    (parameter, replacement) ∈ substitution := by
  induction substitution with
  | nil => simp [lookup?] at found
  | cons entry rest induction =>
      rcases entry with ⟨candidate, candidateReplacement⟩
      by_cases same : candidate = parameter
      · subst candidate
        simp [lookup?] at found
        cases found
        simp
      · have tailFound :
            ParameterSubstitution.lookup? rest parameter =
              some replacement := by
          simpa [lookup?, same] using found
        exact List.mem_cons_of_mem _ (induction tailFound)

/-- Instantiating rigid parameters preserves an allocator bound when every
replacement range and every flexible source variable are bounded. -/
theorem apply_variables_below
    {substitution : ParameterSubstitution} {next : Nat} {type : Ty}
    (rangeBelow : ∀ {parameter replacement},
      (parameter, replacement) ∈ substitution →
        replacement.VariablesBelow next)
    (sourceBelow : type.VariablesBelow next) :
    (substitution.apply type).VariablesBelow next := by
  induction type with
  | «variable» metavariable =>
      simpa [ParameterSubstitution.apply] using sourceBelow
  | parameter candidate =>
      cases found : substitution.lookup? candidate with
      | none => simp [ParameterSubstitution.apply, found]
      | some replacement =>
          simp only [ParameterSubstitution.apply, found, Option.getD_some]
          exact rangeBelow (lookup?_eq_some_mem found)
  | constructor constructor => simp [ParameterSubstitution.apply]
  | application left right leftInduction rightInduction =>
      have parts := (Ty.variablesBelow_application_iff next left right).mp
        sourceBelow
      simp only [ParameterSubstitution.apply,
        Ty.variablesBelow_application_iff]
      exact ⟨leftInduction parts.1, rightInduction parts.2⟩
  | function parameter result parameterInduction resultInduction =>
      have parts := (Ty.variablesBelow_function_iff next parameter result).mp
        sourceBelow
      simp only [ParameterSubstitution.apply,
        Ty.variablesBelow_function_iff]
      exact ⟨parameterInduction parts.1, resultInduction parts.2⟩
  | product left right leftInduction rightInduction =>
      have parts := (Ty.variablesBelow_product_iff next left right).mp
        sourceBelow
      simp only [ParameterSubstitution.apply,
        Ty.variablesBelow_product_iff]
      exact ⟨leftInduction parts.1, rightInduction parts.2⟩
  | mapping key value keyInduction valueInduction =>
      have parts := (Ty.variablesBelow_mapping_iff next key value).mp
        sourceBelow
      simp only [ParameterSubstitution.apply,
        Ty.variablesBelow_mapping_iff]
      exact ⟨keyInduction parts.1, valueInduction parts.2⟩
  | proxy inner induction =>
      simp only [ParameterSubstitution.apply,
        Ty.variablesBelow_proxy_iff]
      exact induction sourceBelow
  | comptime inner induction =>
      simp only [ParameterSubstitution.apply,
        Ty.variablesBelow_comptime_iff]
      exact induction sourceBelow
  | error => simp [ParameterSubstitution.apply]

end ParameterSubstitution

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

/-- Composition preserves solved substitutions under the explicit condition
that the newer range cannot reintroduce a variable solved by the older
substitution. -/
theorem compose
    {newer older : Substitution} {next : Nat}
    (newerSolved : Substitution.SolvedBelow newer next)
    (olderSolved : Substitution.SolvedBelow older next)
    (cross : Substitution.RangeAvoidsDomain newer older) :
    Substitution.SolvedBelow (newer.compose older) next := by
  constructor
  · exact Substitution.domain_compose_nodup
      newerSolved.domain_nodup olderSolved.domain_nodup
  · intro metavariable member
    rw [Substitution.mem_domain_compose_iff] at member
    exact member.elim (olderSolved.domain_below metavariable)
      (newerSolved.domain_below metavariable)
  · intro metavariable replacement member rangeVariable occurs
    rw [Substitution.mem_compose_iff] at member
    rcases member with
      ⟨olderReplacement, olderMember, replacementEq⟩ |
        ⟨newerMember, newerFresh⟩
    · subst replacement
      exact newerSolved.apply_variables_below olderReplacement
        (olderSolved.range_below olderMember) rangeVariable occurs
    · exact newerSolved.range_below newerMember rangeVariable occurs
  · intro metavariable replacement member rangeVariable occurs
    rw [Substitution.mem_compose_iff] at member
    rcases member with
      ⟨olderReplacement, olderMember, replacementEq⟩ |
        ⟨newerMember, newerFresh⟩
    · subst replacement
      have outsideOlder : rangeVariable ∉ older.domain :=
        Substitution.RangeAvoidsDomain.apply_variables_outside_older_domain
          cross olderReplacement
          (olderSolved.range_outside_domain olderMember) rangeVariable occurs
      have outsideNewer : rangeVariable ∉ newer.domain :=
        newerSolved.apply_variables_outside_domain olderReplacement
          rangeVariable occurs
      intro composedMember
      rw [Substitution.mem_domain_compose_iff] at composedMember
      exact composedMember.elim outsideOlder outsideNewer
    · have outsideOlder : rangeVariable ∉ older.domain :=
        cross newerMember rangeVariable occurs
      have outsideNewer : rangeVariable ∉ newer.domain :=
        newerSolved.range_outside_domain newerMember rangeVariable occurs
      intro composedMember
      rw [Substitution.mem_domain_compose_iff] at composedMember
      exact composedMember.elim outsideOlder outsideNewer

end Substitution.SolvedBelow

namespace Substitution.SemanticallyExtends

/-- A solved substitution semantically extends itself. -/
theorem refl_of_solved
    {substitution : Substitution} {next : Nat}
    (solved : substitution.SolvedBelow next) :
    substitution.SemanticallyExtends substitution := by
  exact solved.apply_idempotent

/-- Left composition semantically extends a solved older substitution. -/
theorem compose_left
    (newer : Substitution) {older : Substitution} {next : Nat}
    (solved : older.SolvedBelow next) :
    (newer.compose older).SemanticallyExtends older := by
  intro type
  rw [Substitution.compose_apply, Substitution.compose_apply,
    solved.apply_idempotent]

/-- Semantic extension is transitive. -/
theorem trans
    {newest middle oldest : Substitution}
    (newestMiddle : newest.SemanticallyExtends middle)
    (middleOldest : middle.SemanticallyExtends oldest) :
    newest.SemanticallyExtends oldest := by
  intro type
  calc
    newest.apply (oldest.apply type) =
        newest.apply (middle.apply (oldest.apply type)) :=
      (newestMiddle (oldest.apply type)).symm
    _ = newest.apply (middle.apply type) :=
      congrArg newest.apply (middleOldest type)
    _ = newest.apply type := newestMiddle type

end Substitution.SemanticallyExtends

end Solcore.TypeSystem
