import Solcore.SourceSemantics.Dynamic.Evidence

/-!
Runtime instantiation evidence for one use of a generalized local scheme.

Static local-reference typing already requires one flexible substitution to
determine both the occurrence type and every qualified predicate.  This module
adds the corresponding dynamic witness: the same substitution also drives
closure of the occurrence's retained requirement identities into a concrete
evidence environment.  It is deliberately independent of value storage and
evaluation, so introducing the witness does not change the current runtime
boundary for generalized local values.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference
open TypeSystem

namespace RequirementsProduceEnvironment

/-- Dynamically closing an ordered requirement spine retains its static proof
of the same ordered predicate spine. -/
theorem toRequirementSequenceProves
    {context : Context} {callerEvidence producedEvidence : EvidenceEnvironment}
    {requirements : List RequirementId}
    {predicates : List ProgramPredicate}
    (produces : RequirementsProduceEnvironment context callerEvidence
      requirements predicates producedEvidence) :
    RequirementSequenceProves context requirements predicates := by
  induction produces with
  | nil => exact .nil
  | cons head _ induction =>
      exact .cons head.requirement_valid induction

end RequirementsProduceEnvironment

/-- One runtime use of a generalized local scheme.  A single flexible
substitution determines the selected occurrence type and its complete ordered
predicate spine; the attached requirement identities then close that spine
against the caller dictionary into `producedEvidence`. -/
structure LocalSchemeRuntimeInstantiation
    (context : Context) (callerEvidence : EvidenceEnvironment)
    (binder : TypedBinder) (type : Ty)
    (actualRequirements : List RequirementId)
    (substitution : Substitution)
    (producedEvidence : EvidenceEnvironment) : Prop where
  formation : LocalSchemeRequirementsWellFormed context binder
  scheme_well_formed : SchemeWellFormed context binder.scheme
  exact : ExactSubstitution substitution binder.scheme.quantified
  /-- Runtime instances are ground.  Static use-site instantiation permits
  admissible residual variables, but executable closure code must not turn an
  outer generalized variable into a fresh residual variable. -/
  range : SubstitutionRangeWellFormed context substitution
  result : substitution.apply binder.scheme.body = type
  actual_requirements_unique : actualRequirements.Nodup
  actual_templates_disjoint :
    ∀ id, id ∈ actualRequirements → id ∉ localSchemeTemplateIds binder
  produces : RequirementsProduceEnvironment context callerEvidence
    actualRequirements (instantiateLocalSchemePredicates substitution binder)
    producedEvidence

namespace LocalSchemeRuntimeInstantiation

/-- Forget dynamic evidence closure while retaining the complete static
use-site instantiation judgment. -/
theorem toLocalSchemeInstantiationValid
    {context : Context} {callerEvidence producedEvidence : EvidenceEnvironment}
    {binder : TypedBinder} {type : Ty}
    {actualRequirements : List RequirementId}
    {substitution : Substitution}
    (instantiation : LocalSchemeRuntimeInstantiation context callerEvidence
      binder type actualRequirements substitution producedEvidence) :
    LocalSchemeInstantiationValid context binder type actualRequirements := by
  exact .intro instantiation.formation instantiation.scheme_well_formed
    substitution instantiation.exact instantiation.range.toAdmissible
    instantiation.result
    instantiation.actual_requirements_unique
    instantiation.actual_templates_disjoint
    instantiation.produces.toRequirementSequenceProves

/-- Every replacement selected for executable local-scheme code is closed in
the caller context. -/
theorem substitution_range_well_formed
    {context : Context} {callerEvidence producedEvidence : EvidenceEnvironment}
    {binder : TypedBinder} {type : Ty}
    {actualRequirements : List RequirementId}
    {substitution : Substitution}
    (instantiation : LocalSchemeRuntimeInstantiation context callerEvidence
      binder type actualRequirements substitution producedEvidence) :
    SubstitutionRangeWellFormed context substitution :=
  instantiation.range

/-- Runtime closure preserves the source-ordered qualified-predicate arity. -/
theorem actual_requirements_length_eq
    {context : Context} {callerEvidence producedEvidence : EvidenceEnvironment}
    {binder : TypedBinder} {type : Ty}
    {actualRequirements : List RequirementId}
    {substitution : Substitution}
    (instantiation : LocalSchemeRuntimeInstantiation context callerEvidence
      binder type actualRequirements substitution producedEvidence) :
    actualRequirements.length = binder.schemeRequirements.length := by
  exact instantiation.toLocalSchemeInstantiationValid.requirements_length_eq

/-- Runtime-instantiated requirement identities remain pairwise distinct. -/
theorem actual_requirements_nodup
    {context : Context} {callerEvidence producedEvidence : EvidenceEnvironment}
    {binder : TypedBinder} {type : Ty}
    {actualRequirements : List RequirementId}
    {substitution : Substitution}
    (instantiation : LocalSchemeRuntimeInstantiation context callerEvidence
      binder type actualRequirements substitution producedEvidence) :
    actualRequirements.Nodup :=
  instantiation.actual_requirements_unique

/-- A use-site requirement cannot recycle an initializer-only template ID. -/
theorem actual_requirement_templates_disjoint
    {context : Context} {callerEvidence producedEvidence : EvidenceEnvironment}
    {binder : TypedBinder} {type : Ty}
    {actualRequirements : List RequirementId}
    {substitution : Substitution}
    (instantiation : LocalSchemeRuntimeInstantiation context callerEvidence
      binder type actualRequirements substitution producedEvidence) :
    ∀ id, id ∈ actualRequirements → id ∉ localSchemeTemplateIds binder :=
  instantiation.actual_templates_disjoint

/-- Every dictionary produced for a local-scheme use is closed and valid
under the whole-program resolution catalog. -/
theorem produced_evidence_valid
    {context : Context} {callerEvidence producedEvidence : EvidenceEnvironment}
    {binder : TypedBinder} {type : Ty}
    {actualRequirements : List RequirementId}
    {substitution : Substitution}
    (instantiation : LocalSchemeRuntimeInstantiation context callerEvidence
      binder type actualRequirements substitution producedEvidence) :
    producedEvidence.Valid context.signatures.resolutionRules :=
  instantiation.produces.valid

/-- Assemble the use-site evidence with the lexical caller dictionary for a
generalized local initializer.  Local evidence is kept first.  If an outer
assumption has the same goal, its valid local entry safely supplies that goal;
the stronger claim that the exact caller entry survives first-match lookup is
available only through `Supplies.append_right_of_disjoint` and its explicit
disjointness premise. -/
theorem combined_evidence_covers
    {context : Context} {callerEvidence producedEvidence : EvidenceEnvironment}
    {binder : TypedBinder} {type : Ty}
    {actualRequirements : List RequirementId}
    {substitution : Substitution}
    (instantiation : LocalSchemeRuntimeInstantiation context callerEvidence
      binder type actualRequirements substitution producedEvidence)
    (caller_covers : callerEvidence.Covers context) :
    (producedEvidence ++ callerEvidence).Covers
      (context.withAssumptions
        (context.assumptions ++
          instantiateLocalSchemePredicates substitution binder)) := by
  constructor
  · exact instantiation.produced_evidence_valid.append caller_covers.1
  · apply (instantiation.produces.supplies.append caller_covers.2).of_subset
    intro predicate member
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append.mpr (.inr member)
    · exact List.mem_append.mpr (.inl member)

end LocalSchemeRuntimeInstantiation

end Solcore.SourceSemantics.Dynamic
