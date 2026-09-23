import Solcore.Frontend.SourceSpecialization
import Solcore.SourceSemantics.Substitution

/-!
Correspondence between normative structural source substitution and the
frontend specialization helper.

The frontend helper remains an implementation detail.  These equations make
its agreement with the independent source-semantics operation explicit rather
than using specialization success as a premise of a semantic judgment.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.StructuralSubstitution

open Frontend
open Frontend.SourceInference
open TypeSystem

theorem applyTypedSource_frontend_eq
    (substitution : ParameterSubstitution) (source : TypedSource) :
    applyTypedSource substitution source =
      Frontend.SourceSpecialization.applyTypedSource substitution source := by
  rfl

mutual

  theorem applyEvidence_frontend_eq
      (substitution : ParameterSubstitution)
      (evidence : TypedTraitResolution.Evidence) :
      applyEvidence substitution evidence =
        Frontend.SourceSpecialization.applyEvidence substitution evidence := by
    cases evidence with
    | byImpl goal implementation premises =>
        simp only [applyEvidence,
          Frontend.SourceSpecialization.applyEvidence]
        rw [applyEvidences_frontend_eq substitution premises]

  theorem applyEvidences_frontend_eq
      (substitution : ParameterSubstitution)
      (evidences : List TypedTraitResolution.Evidence) :
      applyEvidences substitution evidences =
        Frontend.SourceSpecialization.applyEvidences substitution evidences := by
    cases evidences with
    | nil => rfl
    | cons evidence rest =>
        simp only [applyEvidences,
          Frontend.SourceSpecialization.applyEvidences]
        rw [applyEvidence_frontend_eq substitution evidence,
          applyEvidences_frontend_eq substitution rest]

end

theorem applyPredicateEvidence_frontend_eq
    (substitution : ParameterSubstitution) (evidence : PredicateEvidence) :
    applyPredicateEvidence substitution evidence =
      Frontend.SourceSpecialization.applyPredicateEvidence substitution
        evidence := by
  cases evidence with
  | assumption predicate => rfl
  | implementation evidence =>
      simp only [applyPredicateEvidence,
        Frontend.SourceSpecialization.applyPredicateEvidence]
      rw [applyEvidence_frontend_eq substitution evidence]

theorem applySolvedRequirement_frontend_eq
    (substitution : ParameterSubstitution) (requirement : SolvedRequirement) :
    applySolvedRequirement substitution requirement =
      Frontend.SourceSpecialization.applySolvedRequirement substitution
        requirement := by
  cases requirement
  simp only [applySolvedRequirement,
    Frontend.SourceSpecialization.applySolvedRequirement]
  rw [applyPredicateEvidence_frontend_eq]

end Solcore.SourceSemantics.StructuralSubstitution
