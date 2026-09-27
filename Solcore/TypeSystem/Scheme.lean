import Solcore.TypeSystem.Substitution

set_option autoImplicit false

namespace Solcore.TypeSystem

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

def nextVariable (scheme : Scheme) : Nat :=
  let bodyNext := scheme.body.nextVariable
  scheme.quantified.foldl
    (fun next metavariable => max next (metavariable.index + 1)) bodyNext

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

/-- Quantify exactly those flexible variables not free in the environment. -/
def generalize (environment : Environment) (type : Ty) : Scheme :=
  let environmentVariables := environment.freeVariables
  { quantified := type.freeVariables.filter fun metavariable => !(metavariable ∈ environmentVariables)
    body := type }

end Environment

end Solcore.TypeSystem
