import Solcore.Frontend.ProgramSignatures
import Solcore.Frontend.SourceInference.Types
import Solcore.Resolved.LocalScope
import Solcore.TypeSystem.Scheme

/-!
Contexts for the declarative source semantics.

This module deliberately contains no lookup or inference algorithm.  A context
is only the collection of assumptions against which source-level judgments are
stated: the resolved whole-program signature catalog, schemes for lexical
locals, and trait predicates that may be used as hypotheses.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

/-- Assumptions available to one source-level static-semantics judgment. -/
structure Context where
  /-- Resolved top-level functions, data declarations, traits, and impls. -/
  signatures : Frontend.ProgramSignatures
  /-- Declaration whose rigid type parameters are currently in scope. -/
  currentDeclaration : Option Resolved.DeclarationId := none
  /-- Rigid type parameters bound by `currentDeclaration`. -/
  typeParameters : List TypeSystem.TypeParameterId := []
  /-- Flexible variables temporarily in scope while checking the initializer
  of a generalized local binding.  Whole-program and runtime contexts keep
  this list empty; unlike `typeParameters`, these variables are inference
  variables bound by a rank-1 local scheme rather than by a declaration. -/
  typeVariables : List TypeSystem.TypeVarId := []
  /-- Whether body-wide residual inference variables are admitted.  The
  frontend may retain a fresh metavariable at an unconstrained use site even
  after final substitution (for example, a discarded polymorphic reference).
  This scope is existential over the resolved body and is deliberately
  separate from the lexical variables introduced by `withTypeVariables`. -/
  residualTypeVariables : Bool := false
  /-- Lexical bindings, keyed by stable resolved local identities. -/
  locals : Resolved.LocalScope TypeSystem.Scheme
  /-- Trait obligations supplied by the surrounding declaration. -/
  assumptions : List Frontend.ProgramPredicate
  /-- Globally solved, stable-ID obligations retained by this typed source. -/
  solvedRequirements : List Frontend.SourceInference.SolvedRequirement := []
  deriving Repr

namespace Context

/-- The empty lexical and predicate extension of a whole-program catalog. -/
def ofSignatures (signatures : Frontend.ProgramSignatures) : Context := {
  signatures
  currentDeclaration := none
  typeParameters := []
  typeVariables := []
  residualTypeVariables := false
  locals := []
  assumptions := []
  solvedRequirements := []
}

/-- Extend the lexical scope without changing whole-program assumptions. -/
def withLocal (context : Context) (id : Resolved.LocalId)
    (scheme : TypeSystem.Scheme) : Context :=
  { context with locals := (id, scheme) :: context.locals }

/-- Enter the flexible-variable scope of a generalized initializer.  The
new variables are appended so a nested generalized binding retains the
ambient flexible scope. -/
def withTypeVariables (context : Context)
    (variables : List TypeSystem.TypeVarId) : Context :=
  { context with typeVariables := context.typeVariables ++ variables }

/-- Admit body-wide residual inference metavariables without adding them to
the lexical generalization barrier. -/
def withResidualTypeVariables (context : Context) : Context :=
  { context with residualTypeVariables := true }

/-- Extend the available trait hypotheses in source order. -/
def withAssumption (context : Context)
    (predicate : Frontend.ProgramPredicate) : Context :=
  { context with assumptions := context.assumptions ++ [predicate] }

/-- Replace the declaration-level assumption set in source order. -/
def withAssumptions (context : Context)
    (predicates : List Frontend.ProgramPredicate) : Context :=
  { context with assumptions := predicates }

/-- Install the complete solved-requirement ledger for one typed source. -/
def withSolvedRequirements (context : Context)
    (requirements : List Frontend.SourceInference.SolvedRequirement) : Context :=
  { context with solvedRequirements := requirements }

/-- Enter one declaration's rigid generic scope. -/
def forDeclaration (context : Context) (declaration : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId) : Context :=
  { context with
    currentDeclaration := some declaration
    typeParameters := parameters }

/-- Leave the current rigid generic scope. -/
def withoutDeclaration (context : Context) : Context :=
  { context with currentDeclaration := none, typeParameters := [] }

@[simp] theorem withTypeVariables_nil (context : Context) :
    context.withTypeVariables [] = context := by
  simp [withTypeVariables]

@[simp] theorem withResidualTypeVariables_idempotent (context : Context) :
    context.withResidualTypeVariables.withResidualTypeVariables =
      context.withResidualTypeVariables := by
  simp [withResidualTypeVariables]

/-- Declarative local lookup inherits the first-match rule of resolved scopes. -/
abbrev LocalLookup (context : Context) (id : Resolved.LocalId)
    (scheme : TypeSystem.Scheme) : Prop :=
  Resolved.LocalScope.Lookup context.locals id scheme

/-- A predicate is available as an explicit hypothesis of the context. -/
def HasAssumption (context : Context)
    (predicate : Frontend.ProgramPredicate) : Prop :=
  predicate ∈ context.assumptions

theorem localLookup_withLocal_self (context : Context)
    (id : Resolved.LocalId) (scheme : TypeSystem.Scheme) :
    (context.withLocal id scheme).LocalLookup id scheme := by
  exact .head

theorem hasAssumption_withAssumption_self (context : Context)
    (predicate : Frontend.ProgramPredicate) :
    (context.withAssumption predicate).HasAssumption predicate := by
  simp [HasAssumption, withAssumption]

end Context

end Solcore.SourceSemantics
