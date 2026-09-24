import Solcore.SourceSemantics.TraitSubstitutionProperties
import Solcore.SourceSemantics.Dynamic.Evidence

/-!
Flexible substitution preserves closed runtime evidence environments.

The central lookup lemma is deliberately stated as an inversion.  Mapping
dictionary keys is not injective: two distinct source predicates can become
the same instantiated predicate, so a particular source lookup does not
necessarily remain first after mapping.  Every mapped first-match result does,
however, originate in a source first-match result.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open TypeSystem

namespace EvidenceEnvironment.LooksUp

/-- Invert a first-match lookup through dictionary substitution.  The selected
mapped entry originates in a source first-match entry even when earlier source
keys collapse after substitution. -/
theorem of_applySubstitution
    {environment : EvidenceEnvironment} {substitution : Substitution}
    {goal : ProgramPredicate} {evidence : TraitEvidence}
    (found : (environment.applySubstitution substitution).LooksUp goal evidence) :
    ∃ sourceGoal sourceEvidence,
      environment.LooksUp sourceGoal sourceEvidence ∧
      TypedTraitResolution.applySubstitution substitution sourceGoal = goal ∧
      FlexibleSubstitution.applyTraitEvidence substitution sourceEvidence =
        evidence := by
  induction environment generalizing goal evidence with
  | nil =>
      simp [EvidenceEnvironment.applySubstitution] at found
      cases found
  | cons entry rest induction =>
      rcases entry with ⟨headGoal, headEvidence⟩
      simp only [EvidenceEnvironment.applySubstitution, List.map_cons] at found
      cases found with
      | head =>
          exact ⟨headGoal, headEvidence, .head, rfl, rfl⟩
      | tail different restFound =>
          rcases induction restFound with
            ⟨sourceGoal, sourceEvidence, sourceFound, goalEq, evidenceEq⟩
          refine ⟨sourceGoal, sourceEvidence, .tail ?_ sourceFound,
            goalEq, evidenceEq⟩
          intro same
          apply different
          rw [same]
          exact goalEq

end EvidenceEnvironment.LooksUp

namespace EvidenceEnvironment.Valid

/-- Substituting a closed runtime dictionary preserves semantic validity.
Lookup inversion, rather than forward lookup transport, handles mapped-key
collisions. -/
theorem applySubstitution
    {rules : List ProgramImplRule} {environment : EvidenceEnvironment}
    (substitution : Substitution) (valid : environment.Valid rules) :
    (environment.applySubstitution substitution).Valid rules := by
  intro goal evidence found
  rcases found.of_applySubstitution with
    ⟨sourceGoal, sourceEvidence, sourceFound, goalEq, evidenceEq⟩
  subst goal
  subst evidence
  exact FlexibleSubstitution.EvidenceValid.applySubstitution substitution
    (valid sourceGoal sourceEvidence sourceFound)

end EvidenceEnvironment.Valid

namespace EvidenceEnvironment.Covers

/-- A covering runtime dictionary continues to cover the context obtained by
closing its flexible variables.  Assumption coverage only needs existence of
a first match, so mapped-key collisions are harmless. -/
theorem applySubstitution
    {context : Context} {environment : EvidenceEnvironment}
    (substitution : Substitution) (covers : environment.Covers context) :
    (environment.applySubstitution substitution).Covers
      (FlexibleSubstitution.closeContext substitution context) := by
  constructor
  · simpa using covers.1.applySubstitution substitution
  · intro predicate member
    rw [FlexibleSubstitution.closeContext_assumptions] at member
    rcases List.mem_map.mp member with
      ⟨sourcePredicate, sourceMember, predicateEq⟩
    subst predicate
    rcases covers.2 sourcePredicate sourceMember with ⟨evidence, found⟩
    exact EvidenceEnvironment.LooksUp.exists_of_key_mem
      (EvidenceEnvironment.key_mem_applySubstitution substitution found.key_mem)

end EvidenceEnvironment.Covers

end Solcore.SourceSemantics.Dynamic
