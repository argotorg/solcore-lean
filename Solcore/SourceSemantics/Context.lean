import Solcore.Frontend.ProgramSignatures
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
  /-- Lexical bindings, keyed by stable resolved local identities. -/
  locals : Resolved.LocalScope TypeSystem.Scheme
  /-- Trait obligations supplied by the surrounding declaration. -/
  assumptions : List Frontend.ProgramPredicate
  deriving Repr

namespace Context

/-- The empty lexical and predicate extension of a whole-program catalog. -/
def ofSignatures (signatures : Frontend.ProgramSignatures) : Context := {
  signatures
  locals := []
  assumptions := []
}

/-- Extend the lexical scope without changing whole-program assumptions. -/
def withLocal (context : Context) (id : Resolved.LocalId)
    (scheme : TypeSystem.Scheme) : Context :=
  { context with locals := (id, scheme) :: context.locals }

/-- Extend the available trait hypotheses in source order. -/
def withAssumption (context : Context)
    (predicate : Frontend.ProgramPredicate) : Context :=
  { context with assumptions := context.assumptions ++ [predicate] }

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
