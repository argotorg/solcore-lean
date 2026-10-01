import Solcore.TypeSystem.SubstitutionProperties

set_option autoImplicit false

namespace Solcore.TypeSystem

private theorem foldl_max_mono
    {α : Type} (values : List α) (measure : α → Nat) (initial : Nat) :
    initial ≤ values.foldl (fun bound value => max bound (measure value))
      initial := by
  induction values generalizing initial with
  | nil => exact Nat.le_refl initial
  | cons value values induction =>
      exact Nat.le_trans (Nat.le_max_left initial (measure value))
        (induction (max initial (measure value)))

private theorem measure_le_foldl_max_of_mem
    {α : Type} (values : List α) (measure : α → Nat) (initial : Nat)
    {value : α} (member : value ∈ values) :
    measure value ≤
      values.foldl (fun bound candidate => max bound (measure candidate))
        initial := by
  induction values generalizing initial with
  | nil => simp at member
  | cons head values induction =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp member with same | member
      · subst head
        exact Nat.le_trans (Nat.le_max_right initial (measure value))
          (foldl_max_mono values measure
            (max initial (measure value)))
      · exact induction (max initial (measure head)) member

/-- A rank-1 type scheme. -/
structure Scheme where
  quantified : List TypeVarId
  body : Ty
  deriving Repr, DecidableEq

namespace Scheme

/-- The shared fresh-variable mapping produced when instantiating a scheme.
Consumers with metadata indexed by the quantified variables can reuse
`substitution` so the metadata and `body` stay in lockstep. -/
structure Instantiation where
  substitution : Substitution
  body : Ty
  next : Nat
  deriving Repr, DecidableEq

def mono (type : Ty) : Scheme :=
  { quantified := [], body := type }

/-- Apply a substitution without entering quantified variables. -/
def apply (substitution : Substitution) (scheme : Scheme) : Scheme :=
  { scheme with body := (substitution.without scheme.quantified).apply scheme.body }

def freeVariables (scheme : Scheme) : List TypeVarId :=
  scheme.body.freeVariables.filter fun metavariable => !(metavariable ∈ scheme.quantified)

/-- Every unquantified flexible variable of a scheme lies below an allocator
bound. -/
def FreeVariablesBelow (next : Nat) (scheme : Scheme) : Prop :=
  ∀ metavariable, metavariable ∈ scheme.freeVariables →
    metavariable.index < next

def nextVariable (scheme : Scheme) : Nat :=
  let bodyNext := scheme.body.nextVariable
  scheme.quantified.foldl
    (fun next metavariable => max next (metavariable.index + 1)) bodyNext

/-- A scheme's allocator summary bounds every flexible variable in its body. -/
theorem body_variablesBelow_nextVariable (scheme : Scheme) :
    scheme.body.VariablesBelow scheme.nextVariable := by
  exact scheme.body.variablesBelow_nextVariable.weaken
    (foldl_max_mono scheme.quantified
      (fun metavariable => metavariable.index + 1)
      scheme.body.nextVariable)

/-- Bounding the whole body bounds the scheme's unquantified free variables. -/
theorem FreeVariablesBelow.of_body
    {scheme : Scheme} {next : Nat}
    (bodyBelow : scheme.body.VariablesBelow next) :
    scheme.FreeVariablesBelow next := by
  intro metavariable member
  exact bodyBelow metavariable (List.mem_filter.mp member).1

/-- Applying a solved substitution preserves a bound on a scheme body, even
though quantified variables are protected from substitution. -/
theorem apply_body_variablesBelow
    {scheme : Scheme} {substitution : Substitution} {next : Nat}
    (solved : substitution.SolvedBelow next)
    (bodyBelow : scheme.body.VariablesBelow next) :
    (scheme.apply substitution).body.VariablesBelow next := by
  change ((substitution.without scheme.quantified).apply
    scheme.body).VariablesBelow next
  apply Substitution.apply_variables_below_of_range
  · intro metavariable replacement member
    exact solved.range_below
      (Substitution.mem_of_mem_without member)
  · intro metavariable member outside
    exact bodyBelow metavariable member

private def freshSubstitution :
    List TypeVarId → Nat → Substitution → Substitution × Nat
  | [], next, substitution => (substitution, next)
  | metavariable :: variables, next, substitution =>
      match substitution.lookup? metavariable with
      | some _ => freshSubstitution variables next substitution
      | none =>
          freshSubstitution variables (next + 1)
            ((metavariable, .variable ⟨next⟩) :: substitution)

private theorem freshSubstitution_next_le
    (variables : List TypeVarId) (next : Nat)
    (substitution : Substitution) :
    next ≤ (freshSubstitution variables next substitution).2 := by
  induction variables generalizing next substitution with
  | nil => exact Nat.le_refl next
  | cons metavariable variables induction =>
      simp only [freshSubstitution]
      split
      · exact induction next substitution
      · exact Nat.le_trans (Nat.le_succ next)
          (induction (next + 1)
            ((metavariable, .variable ⟨next⟩) :: substitution))

private theorem freshSubstitution_ranges_below
    (variables : List TypeVarId) (next : Nat)
    (substitution : Substitution)
    (rangesBelow : ∀ {metavariable replacement},
      (metavariable, replacement) ∈ substitution →
        replacement.VariablesBelow next) :
    ∀ {metavariable replacement},
      (metavariable, replacement) ∈
          (freshSubstitution variables next substitution).1 →
        replacement.VariablesBelow
          (freshSubstitution variables next substitution).2 := by
  induction variables generalizing next substitution with
  | nil => exact rangesBelow
  | cons metavariable variables induction =>
      cases found : substitution.lookup? metavariable with
      | some existing =>
          simp only [freshSubstitution, found]
          exact induction next substitution rangesBelow
      | none =>
          simp only [freshSubstitution, found]
          apply induction (next + 1)
            ((metavariable, .variable ⟨next⟩) :: substitution)
          intro candidate replacement member
          rcases List.mem_cons.mp member with same | member
          · cases same
            simp [Ty.VariablesBelow, Ty.freeVariables]
          · exact (rangesBelow member).weaken (Nat.le_succ next)

private theorem freshSubstitution_domain_covers
    (variables : List TypeVarId) (next : Nat)
    (substitution : Substitution) :
    ∀ metavariable,
      metavariable ∈ variables ∨ metavariable ∈ substitution.domain →
        metavariable ∈
          (freshSubstitution variables next substitution).1.domain := by
  induction variables generalizing next substitution with
  | nil =>
      intro metavariable source
      rcases source with quantified | existing
      · simp at quantified
      · exact existing
  | cons head variables induction =>
      cases found : substitution.lookup? head with
      | some replacement =>
          simp only [freshSubstitution, found]
          intro metavariable source
          apply induction next substitution metavariable
          rcases source with quantified | existing
          · rcases List.mem_cons.mp quantified with same | quantified
            · subst metavariable
              exact Or.inr <| List.mem_map.mpr
                ⟨(head, replacement), Substitution.lookup?_eq_some_mem found,
                  rfl⟩
            · exact Or.inl quantified
          · exact Or.inr existing
      | none =>
          simp only [freshSubstitution, found]
          intro metavariable source
          apply induction (next + 1)
            ((head, .variable ⟨next⟩) :: substitution) metavariable
          rcases source with quantified | existing
          · rcases List.mem_cons.mp quantified with same | quantified
            · subst metavariable
              exact Or.inr (by simp [Substitution.domain])
            · exact Or.inl quantified
          · exact Or.inr (by
              simp only [Substitution.domain, List.map_cons, List.mem_cons]
              exact Or.inr existing)

private theorem freshSubstitution_domain_eq_reverse_append
    (variables : List TypeVarId) (next : Nat)
    (substitution : Substitution)
    (variablesUnique : variables.Nodup)
    (variablesFresh : ∀ metavariable, metavariable ∈ variables →
      metavariable ∉ substitution.domain) :
    (freshSubstitution variables next substitution).1.domain =
      variables.reverse ++ substitution.domain := by
  induction variables generalizing next substitution with
  | nil => simp [freshSubstitution]
  | cons head variables induction =>
      simp only [List.nodup_cons] at variablesUnique
      have headMissing : head ∉ substitution.domain :=
        variablesFresh head (by simp)
      have found : substitution.lookup? head = none :=
        (Substitution.lookup?_eq_none_iff_not_mem_domain substitution head).mpr
          headMissing
      simp only [freshSubstitution, found]
      rw [induction (next + 1)
        ((head, .variable ⟨next⟩) :: substitution)
        variablesUnique.2]
      · simp [Substitution.domain, List.reverse_cons, List.append_assoc]
      · intro metavariable member
        have different : metavariable ≠ head := by
          intro same
          subst metavariable
          exact variablesUnique.1 member
        simp only [Substitution.domain, List.map_cons, List.mem_cons, not_or]
        exact ⟨different, variablesFresh metavariable (by simp [member])⟩

private theorem freshSubstitution_range_fresh_or_mem
    (variables : List TypeVarId) (next : Nat)
    (substitution : Substitution) :
    ∀ {metavariable replacement},
      (metavariable, replacement) ∈
          (freshSubstitution variables next substitution).1 →
        (metavariable, replacement) ∈ substitution ∨
          ∃ fresh,
            replacement = .variable fresh ∧
              next ≤ fresh.index ∧
              fresh.index <
                (freshSubstitution variables next substitution).2 := by
  induction variables generalizing next substitution with
  | nil =>
      intro metavariable replacement member
      exact Or.inl member
  | cons head variables induction =>
      intro metavariable replacement member
      cases found : substitution.lookup? head with
      | some existing =>
          simp only [freshSubstitution, found] at member ⊢
          exact induction next substitution member
      | none =>
          simp only [freshSubstitution, found] at member ⊢
          rcases induction (next + 1)
              ((head, .variable ⟨next⟩) :: substitution) member with
            seeded | ⟨fresh, replacement_eq, lower, upper⟩
          · rcases List.mem_cons.mp seeded with same | existing
            · cases same
              exact Or.inr ⟨⟨next⟩, rfl, Nat.le_refl next,
                Nat.lt_of_lt_of_le (Nat.lt_succ_self next)
                  (freshSubstitution_next_le variables (next + 1)
                    ((head, .variable ⟨next⟩) :: substitution))⟩
            · exact Or.inl existing
          · exact Or.inr ⟨fresh, replacement_eq,
              Nat.le_trans (Nat.le_succ next) lower, upper⟩

private theorem list_perm_reverse {value : Type} (values : List value) :
    values.Perm values.reverse := by
  induction values with
  | nil => exact .nil
  | cons head tail induction =>
      rw [List.reverse_cons]
      exact (List.Perm.cons head induction).trans (by
        simpa only [List.singleton_append] using
          (List.perm_append_comm :
            ([head] ++ tail.reverse).Perm (tail.reverse ++ [head])))

/-- Instantiate every quantified variable and expose the shared substitution. -/
def instantiateWithSubstitution (scheme : Scheme) (next : Nat) : Instantiation :=
  let (substitution, next) := freshSubstitution scheme.quantified next []
  { substitution, body := substitution.apply scheme.body, next }

/-- With duplicate-free quantified binders, shared-substitution instantiation
covers every quantified variable exactly once.  The implementation stores the
fresh assignments in reverse allocation order, so coverage is stated up to
permutation. -/
theorem instantiateWithSubstitution_substitution_domain_permutation
    (scheme : Scheme) (next : Nat)
    (quantifiedUnique : scheme.quantified.Nodup) :
    (scheme.instantiateWithSubstitution next).substitution.domain.Perm
      scheme.quantified := by
  change (freshSubstitution scheme.quantified next []).1.domain.Perm
    scheme.quantified
  rw [freshSubstitution_domain_eq_reverse_append scheme.quantified next []
    quantifiedUnique (by
      intro metavariable member
      simp [Substitution.domain])]
  simpa only [Substitution.domain, List.map_nil, List.append_nil] using
    (list_perm_reverse scheme.quantified).symm

/-- Every range entry produced by shared-substitution instantiation is a
fresh flexible variable.  Its index starts at or above the input allocator and
lies strictly below the returned allocator. -/
theorem instantiateWithSubstitution_substitution_range_fresh
    (scheme : Scheme) (next : Nat) :
    ∀ {metavariable replacement},
      (metavariable, replacement) ∈
          (scheme.instantiateWithSubstitution next).substitution →
        ∃ fresh,
          replacement = .variable fresh ∧
            next ≤ fresh.index ∧
            fresh.index < (scheme.instantiateWithSubstitution next).next := by
  intro metavariable replacement member
  change (metavariable, replacement) ∈
    (freshSubstitution scheme.quantified next []).1 at member
  rcases freshSubstitution_range_fresh_or_mem scheme.quantified next []
      member with existing | fresh
  · simp at existing
  · exact fresh

/-- Scheme instantiation with its shared substitution never moves the
fresh-variable allocator backwards. -/
theorem instantiateWithSubstitution_next_le (scheme : Scheme) (next : Nat) :
    next ≤ (scheme.instantiateWithSubstitution next).next := by
  exact freshSubstitution_next_le scheme.quantified next []

/-- Every replacement generated by shared-substitution instantiation lies
below the returned allocator bound. -/
theorem instantiateWithSubstitution_substitution_range_variablesBelow
    (scheme : Scheme) (next : Nat) :
    ∀ {metavariable replacement},
      (metavariable, replacement) ∈
          (scheme.instantiateWithSubstitution next).substitution →
        replacement.VariablesBelow
          (scheme.instantiateWithSubstitution next).next := by
  change ∀ {metavariable replacement},
    (metavariable, replacement) ∈
        (freshSubstitution scheme.quantified next []).1 →
      replacement.VariablesBelow
        (freshSubstitution scheme.quantified next []).2
  exact freshSubstitution_ranges_below scheme.quantified next [] (by simp)

/-- Shared-substitution instantiation bounds every returned body variable
when the scheme's unquantified variables lie below the input allocator. -/
theorem instantiateWithSubstitution_body_variablesBelow
    (scheme : Scheme) (next : Nat)
    (freeBelow : scheme.FreeVariablesBelow next) :
    (scheme.instantiateWithSubstitution next).body.VariablesBelow
      (scheme.instantiateWithSubstitution next).next := by
  change
    ((freshSubstitution scheme.quantified next []).1.apply
      scheme.body).VariablesBelow
        (freshSubstitution scheme.quantified next []).2
  apply Substitution.apply_variables_below_of_range
  · exact
      instantiateWithSubstitution_substitution_range_variablesBelow scheme next
  · intro metavariable member outside
    have notQuantified : metavariable ∉ scheme.quantified := by
      intro quantified
      exact outside (freshSubstitution_domain_covers scheme.quantified next []
        metavariable (Or.inl quantified))
    have freeMember : metavariable ∈ scheme.freeVariables := by
      simp [Scheme.freeVariables, member, notQuantified]
    exact Nat.lt_of_lt_of_le (freeBelow metavariable freeMember)
      (instantiateWithSubstitution_next_le scheme next)

/-- Instantiate every quantified variable with a distinct fresh metavariable. -/
def instantiate (scheme : Scheme) (next : Nat) : Ty × Nat :=
  let instantiated := scheme.instantiateWithSubstitution next
  (instantiated.body, instantiated.next)

/-- Structurally match a scheme body against one occurrence type.  Only the
listed quantified variables may acquire assignments, and repeated appearances
must agree with the first assignment. -/
def matchBody? (quantified : List TypeVarId) :
    Ty → Ty → Substitution → Option Substitution
  | .variable metavariable, actual, substitution =>
      if quantified.contains metavariable then
        match substitution.lookup? metavariable with
        | some previous =>
            if previous = actual then some substitution else none
        | none => some ((metavariable, actual) :: substitution)
      else if Ty.variable metavariable = actual then some substitution else none
  | .parameter expected, .parameter actual, substitution =>
      if expected = actual then some substitution else none
  | .constructor expected, .constructor actual, substitution =>
      if expected = actual then some substitution else none
  | .application expectedFunction expectedArgument,
      .application actualFunction actualArgument, substitution => do
      let substitution ← matchBody? quantified expectedFunction
        actualFunction substitution
      matchBody? quantified expectedArgument actualArgument substitution
  | .function expectedParameter expectedResult,
      .function actualParameter actualResult, substitution => do
      let substitution ← matchBody? quantified expectedParameter
        actualParameter substitution
      matchBody? quantified expectedResult actualResult substitution
  | .product expectedLeft expectedRight,
      .product actualLeft actualRight, substitution => do
      let substitution ← matchBody? quantified expectedLeft actualLeft
        substitution
      matchBody? quantified expectedRight actualRight substitution
  | .mapping expectedKey expectedValue,
      .mapping actualKey actualValue, substitution => do
      let substitution ← matchBody? quantified expectedKey actualKey
        substitution
      matchBody? quantified expectedValue actualValue substitution
  | .proxy expected, .proxy actual, substitution =>
      matchBody? quantified expected actual substitution
  | .comptime expected, .comptime actual, substitution =>
      matchBody? quantified expected actual substitution
  | .error, .error, substitution => some substitution
  | _, _, _ => none

structure InstanceMatch (scheme : Scheme) (actual : Ty) where
  substitution : Substitution
  quantifiedUnique : scheme.quantified.Nodup
  domainExact : Substitution.domain substitution = scheme.quantified
  applies : Substitution.apply substitution scheme.body = actual

def matchInstanceCertificate? (scheme : Scheme) (actual : Ty) :
    Option (InstanceMatch scheme actual) :=
  if quantifiedUnique : scheme.quantified.Nodup then do
    let matched ← matchBody? scheme.quantified scheme.body actual []
    let substitution : Substitution ← scheme.quantified.mapM fun metavariable => do
      pure (metavariable, ← matched.lookup? metavariable)
    if domainExact : Substitution.domain substitution = scheme.quantified then
      if applies : Substitution.apply substitution scheme.body = actual then
        some { substitution, quantifiedUnique, domainExact, applies }
      else
        none
    else
      none
  else
    none

/-- Recover the complete substitution witnessing one rank-1 scheme instance.

The structural matcher proposes assignments, then this public boundary
reorders them to the quantified binder list and validates the complete
certificate.  The final checks make success independent of matcher internals
and provide a compact proof boundary for source typing. -/
def matchInstance? (scheme : Scheme) (actual : Ty) : Option Substitution :=
  (matchInstanceCertificate? scheme actual).map
    (fun certificate => certificate.substitution)

/-- A successful scheme match is a complete, duplicate-free instantiation
certificate for the requested occurrence type. -/
theorem matchInstance?_sound
    {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (accepted : scheme.matchInstance? actual = some substitution) :
    scheme.quantified.Nodup ∧
      substitution.domain = scheme.quantified ∧
      substitution.apply scheme.body = actual := by
  unfold matchInstance? at accepted
  cases certificateResult : matchInstanceCertificate? scheme actual with
  | none => simp [certificateResult] at accepted
  | some certificate =>
      simp only [certificateResult, Option.map_some, Option.some.injEq]
        at accepted
      subst substitution
      exact ⟨certificate.quantifiedUnique, certificate.domainExact,
        certificate.applies⟩

/-- Scheme instantiation never moves the fresh-variable allocator backwards. -/
theorem instantiate_next_le (scheme : Scheme) (next : Nat) :
    next ≤ (scheme.instantiate next).2 := by
  exact instantiateWithSubstitution_next_le scheme next

/-- Instantiation bounds every returned flexible variable under the standard
allocator-well-formedness condition: the scheme's unquantified free variables
already lie below the input allocator.  Quantified variables may use arbitrary
source indices because instantiation replaces them with fresh variables. -/
theorem instantiate_variablesBelow
    (scheme : Scheme) (next : Nat)
    (freeBelow : scheme.FreeVariablesBelow next) :
    (scheme.instantiate next).1.VariablesBelow
      (scheme.instantiate next).2 := by
  exact instantiateWithSubstitution_body_variablesBelow scheme next freeBelow

end Scheme

/-- A resolved declaration whose generic binders remain rigid until use. -/
structure DeclarationScheme where
  parameters : List TypeParameterId
  body : Ty
  deriving Repr, DecidableEq

namespace DeclarationScheme

private def freshParameterSubstitution :
    List TypeParameterId → Nat → ParameterSubstitution → ParameterSubstitution × Nat
  | [], next, substitution => (substitution, next)
  | parameter :: parameters, next, substitution =>
      match substitution.lookup? parameter with
      | some _ => freshParameterSubstitution parameters next substitution
      | none =>
          freshParameterSubstitution parameters (next + 1)
            ((parameter, .variable ⟨next⟩) :: substitution)

private theorem freshParameterSubstitution_next_le
    (parameters : List TypeParameterId) (next : Nat)
    (substitution : ParameterSubstitution) :
    next ≤ (freshParameterSubstitution parameters next substitution).2 := by
  induction parameters generalizing next substitution with
  | nil => exact Nat.le_refl next
  | cons parameter parameters induction =>
      simp only [freshParameterSubstitution]
      split
      · exact induction next substitution
      · exact Nat.le_trans (Nat.le_succ next)
          (induction (next + 1)
            ((parameter, .variable ⟨next⟩) :: substitution))

private theorem freshParameterSubstitution_ranges_below
    (parameters : List TypeParameterId) (next : Nat)
    (substitution : ParameterSubstitution)
    (rangesBelow : ∀ {parameter replacement},
      (parameter, replacement) ∈ substitution →
        replacement.VariablesBelow next) :
    ∀ {parameter replacement},
      (parameter, replacement) ∈
          (freshParameterSubstitution parameters next substitution).1 →
        replacement.VariablesBelow
          (freshParameterSubstitution parameters next substitution).2 := by
  induction parameters generalizing next substitution with
  | nil => exact rangesBelow
  | cons parameter parameters induction =>
      cases found : substitution.lookup? parameter with
      | some existing =>
          simp only [freshParameterSubstitution, found]
          exact induction next substitution rangesBelow
      | none =>
          simp only [freshParameterSubstitution, found]
          apply induction (next + 1)
            ((parameter, .variable ⟨next⟩) :: substitution)
          intro candidate replacement member
          rcases List.mem_cons.mp member with same | member
          · cases same
            simp [Ty.VariablesBelow, Ty.freeVariables]
          · exact (rangesBelow member).weaken (Nat.le_succ next)

/-- Turn rigid declaration parameters into fresh inference metavariables. -/
def instantiate (scheme : DeclarationScheme) (next : Nat) : Ty × Nat :=
  let (substitution, next) :=
    freshParameterSubstitution scheme.parameters next []
  (substitution.apply scheme.body, next)

/-- Declaration instantiation never moves the fresh-variable allocator
backwards. -/
theorem instantiate_next_le (scheme : DeclarationScheme) (next : Nat) :
    next ≤ (scheme.instantiate next).2 := by
  exact freshParameterSubstitution_next_le scheme.parameters next []

/-- Declaration instantiation bounds every returned flexible variable when
the flexible variables already present in the declaration body lie below the
input allocator. -/
theorem instantiate_variablesBelow
    (scheme : DeclarationScheme) (next : Nat)
    (bodyBelow : scheme.body.VariablesBelow next) :
    (scheme.instantiate next).1.VariablesBelow
      (scheme.instantiate next).2 := by
  change
    ((freshParameterSubstitution scheme.parameters next []).1.apply
      scheme.body).VariablesBelow
        (freshParameterSubstitution scheme.parameters next []).2
  apply ParameterSubstitution.apply_variables_below
  · exact freshParameterSubstitution_ranges_below scheme.parameters next []
      (by simp)
  · exact bodyBelow.weaken
      (freshParameterSubstitution_next_le scheme.parameters next [])

end DeclarationScheme

/-- First-match term typing environment. -/
abbrev Environment := List (String × Scheme)

namespace Environment

def lookup? : Environment → String → Option Scheme
  | [], _ => none
  | (candidate, scheme) :: rest, name =>
      if candidate = name then some scheme else lookup? rest name

def apply (substitution : Substitution) (environment : Environment) : Environment :=
  environment.map fun entry => (entry.1, entry.2.apply substitution)

private def insertVariable (variables : List TypeVarId) (metavariable : TypeVarId) :
    List TypeVarId :=
  if metavariable ∈ variables then variables else variables ++ [metavariable]

def freeVariables (environment : Environment) : List TypeVarId :=
  environment.foldl
    (fun variables entry => entry.2.freeVariables.foldl insertVariable variables) []

private theorem mem_foldl_insertVariable_iff
    (metavariable : TypeVarId) (initial values : List TypeVarId) :
    metavariable ∈ values.foldl insertVariable initial ↔
      metavariable ∈ initial ∨ metavariable ∈ values := by
  induction values generalizing initial with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction]
      unfold insertVariable
      by_cases present : head ∈ initial
      · simp only [if_pos present, List.mem_cons]
        constructor
        · rintro (member | member)
          · exact Or.inl member
          · exact Or.inr (Or.inr member)
        · rintro (member | same | member)
          · exact Or.inl member
          · exact Or.inl (by simpa [same] using present)
          · exact Or.inr member
      · simp [present, or_assoc]

private theorem mem_foldl_schemeFreeVariables_iff
    (metavariable : TypeVarId) (initial : List TypeVarId)
    (environment : Environment) :
    metavariable ∈ environment.foldl
        (fun variables entry =>
          entry.2.freeVariables.foldl insertVariable variables) initial ↔
      metavariable ∈ initial ∨
        ∃ entry ∈ environment, metavariable ∈ entry.2.freeVariables := by
  induction environment generalizing initial with
  | nil => simp
  | cons entry rest induction =>
      rw [List.foldl_cons, induction,
        mem_foldl_insertVariable_iff]
      simp only [List.mem_cons]
      constructor
      · rintro ((initialMember | headMember) | ⟨candidate, restMember,
          candidateMember⟩)
        · exact Or.inl initialMember
        · exact Or.inr ⟨entry, Or.inl rfl, headMember⟩
        · exact Or.inr
            ⟨candidate, Or.inr restMember, candidateMember⟩
      · rintro (initialMember | ⟨candidate, same | restMember,
          candidateMember⟩)
        · exact Or.inl (Or.inl initialMember)
        · subst candidate
          exact Or.inl (Or.inr candidateMember)
        · exact Or.inr ⟨candidate, restMember, candidateMember⟩

/-- A flexible variable is free in an environment exactly when it is free in
one of the environment's retained schemes. -/
@[simp] theorem mem_freeVariables_iff
    (metavariable : TypeVarId) (environment : Environment) :
    metavariable ∈ environment.freeVariables ↔
      ∃ entry ∈ environment, metavariable ∈ entry.2.freeVariables := by
  unfold freeVariables
  simpa using
    (mem_foldl_schemeFreeVariables_iff metavariable [] environment)

def nextVariable (environment : Environment) : Nat :=
  environment.foldl (fun next entry => max next entry.2.nextVariable) 0

/-- Every scheme body in an environment lies below a shared allocator
bound. -/
def BodiesBelow (next : Nat) (environment : Environment) : Prop :=
  ∀ entry, entry ∈ environment → entry.2.body.VariablesBelow next

namespace BodiesBelow

/-- Environment bounds are monotone in the allocator limit. -/
theorem weaken
    {environment : Environment} {lower upper : Nat}
    (below : BodiesBelow lower environment) (bound : lower ≤ upper) :
    BodiesBelow upper environment := by
  intro entry member
  exact (below entry member).weaken bound

/-- Extending a bounded environment with one bounded scheme preserves the
shared bound. -/
theorem cons
    {environment : Environment} {next : Nat} {name : String}
    {scheme : Scheme}
    (headBelow : scheme.body.VariablesBelow next)
    (tailBelow : BodiesBelow next environment) :
    BodiesBelow next ((name, scheme) :: environment) := by
  intro entry member
  rcases List.mem_cons.mp member with same | member
  · cases same
    exact headBelow
  · exact tailBelow entry member

/-- Applying a solved substitution to every scheme preserves environment
body bounds. -/
theorem apply
    {environment : Environment} {substitution : Substitution} {next : Nat}
    (below : BodiesBelow next environment)
    (solved : substitution.SolvedBelow next) :
    BodiesBelow next (environment.apply substitution) := by
  intro entry member
  rcases List.mem_map.mp member with ⟨source, sourceMember, sourceEq⟩
  rcases source with ⟨name, scheme⟩
  cases sourceEq
  exact Scheme.apply_body_variablesBelow solved
    (below (name, scheme) sourceMember)

end BodiesBelow

/-- A successful first-match lookup returns an actual environment entry. -/
theorem lookup?_eq_some_mem
    {environment : Environment} {name : String} {scheme : Scheme}
    (found : environment.lookup? name = some scheme) :
    (name, scheme) ∈ environment := by
  induction environment with
  | nil => simp [lookup?] at found
  | cons entry rest induction =>
      rcases entry with ⟨candidate, candidateScheme⟩
      by_cases same : candidate = name
      · subst candidate
        simp [lookup?] at found
        cases found
        simp
      · have tailFound : Environment.lookup? rest name = some scheme := by
          simpa [lookup?, same] using found
        exact List.mem_cons_of_mem _ (induction tailFound)

/-- The allocator summary of an environment bounds every scheme body in it. -/
theorem bodiesBelow_nextVariable (environment : Environment) :
    environment.BodiesBelow environment.nextVariable := by
  intro entry member
  apply entry.2.body_variablesBelow_nextVariable.weaken
  exact measure_le_foldl_max_of_mem environment
    (fun candidate => candidate.2.nextVariable) 0 member

/-- Quantify exactly those flexible variables not free in the environment. -/
def generalize (environment : Environment) (type : Ty) : Scheme :=
  let environmentVariables := environment.freeVariables
  { quantified := type.freeVariables.filter fun metavariable => !(metavariable ∈ environmentVariables)
    body := type }

end Environment

end Solcore.TypeSystem
