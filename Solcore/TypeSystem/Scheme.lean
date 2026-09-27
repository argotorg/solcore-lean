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

/-- Instantiate every quantified variable and expose the shared substitution. -/
def instantiateWithSubstitution (scheme : Scheme) (next : Nat) : Instantiation :=
  let (substitution, next) := freshSubstitution scheme.quantified next []
  { substitution, body := substitution.apply scheme.body, next }

/-- Instantiate every quantified variable with a distinct fresh metavariable. -/
def instantiate (scheme : Scheme) (next : Nat) : Ty × Nat :=
  let instantiated := scheme.instantiateWithSubstitution next
  (instantiated.body, instantiated.next)

/-- Scheme instantiation never moves the fresh-variable allocator backwards. -/
theorem instantiate_next_le (scheme : Scheme) (next : Nat) :
    next ≤ (scheme.instantiate next).2 := by
  exact freshSubstitution_next_le scheme.quantified next []

/-- Instantiation bounds every returned flexible variable under the standard
allocator-well-formedness condition: the scheme's unquantified free variables
already lie below the input allocator.  Quantified variables may use arbitrary
source indices because instantiation replaces them with fresh variables. -/
theorem instantiate_variablesBelow
    (scheme : Scheme) (next : Nat)
    (freeBelow : scheme.FreeVariablesBelow next) :
    (scheme.instantiate next).1.VariablesBelow
      (scheme.instantiate next).2 := by
  change
    ((freshSubstitution scheme.quantified next []).1.apply
      scheme.body).VariablesBelow
        (freshSubstitution scheme.quantified next []).2
  apply Substitution.apply_variables_below_of_range
  · exact freshSubstitution_ranges_below scheme.quantified next [] (by simp)
  · intro metavariable member outside
    have notQuantified : metavariable ∉ scheme.quantified := by
      intro quantified
      exact outside (freshSubstitution_domain_covers scheme.quantified next []
        metavariable (Or.inl quantified))
    have freeMember : metavariable ∈ scheme.freeVariables := by
      simp [Scheme.freeVariables, member, notQuantified]
    exact Nat.lt_of_lt_of_le (freeBelow metavariable freeMember)
      (freshSubstitution_next_le scheme.quantified next [])

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
