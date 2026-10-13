import Solcore.SourceSemantics.CoreLowering.RecursiveMethodDictionaryIdentity

/-! A trait whose matching catalog rules share one implementation identity and
have no premises has a unique complete evidence tree. These are factual catalog
conditions; method body behavior is not involved. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.LeafTraitEvidenceCoherence
open Frontend SourceInference
open RecursiveMethodDictionaryIdentity

structure Catalog (rules : List ProgramImplRule) (trait : ProgramTraitId)
    (implementation : ProgramImplId) : Prop where
  entries : ∀ rule ∈ rules, rule.head.trait = trait →
    rule.id = implementation ∧ rule.wherePredicates = []

theorem evidence_eq {rules : List ProgramImplRule} {trait : ProgramTraitId}
    {implementation : ProgramImplId} (catalog : Catalog rules trait implementation)
    {goal : ProgramPredicate} {tree : TraitEvidence}
    (goalTrait : goal.trait = trait)
    (valid : EvidenceValid [] rules goal tree) :
    tree = .implementation goal implementation [] := by
  cases valid with
  | assumption member => cases member
  | implementation member identity instantiated premises =>
    cases instantiated with
    | intro substitution _ head premisesEq =>
      have traitEq : _ = trait :=
        (congrArg (fun predicate : ProgramPredicate => predicate.trait) head).trans goalTrait
      obtain ⟨same, empty⟩ := catalog.entries _ member traitEq
      rw [empty, List.map_nil] at premisesEq
      cases premisesEq
      cases premises
      cases identity.symm.trans same
      rfl

theorem coherent {rules : List ProgramImplRule} {trait : ProgramTraitId}
    {implementation : ProgramImplId} (catalog : Catalog rules trait implementation)
    {goals : List ProgramPredicate} (traits : ∀ goal ∈ goals, goal.trait = trait) :
    Coherent rules goals := by
  intro goal member left right first second
  exact (evidence_eq catalog (traits goal member) first).trans
    (evidence_eq catalog (traits goal member) second).symm

end Solcore.SourceSemantics.CoreLowering.LeafTraitEvidenceCoherence
