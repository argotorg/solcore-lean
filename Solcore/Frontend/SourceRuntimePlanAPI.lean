import Solcore.Frontend.SourceCompilationPlan

/-! Historical source plan names remain available through the pure runtime
carriers. These aliases import no source execution code. -/

namespace Solcore.Frontend.SourceTypedRuntime

/- Compatibility names for the shared compilation-plan API. -/
export SourceCompilationPlan (
  exactSpecialization
  runtimeEvidenceGoal
  validateRuntimeEvidence
  validateAuthenticatedRuntimeEvidence
  validateRuntimeEvidence_success_matches
  validateAuthenticatedRuntimeEvidence_success_matches
  materializeCallEvidence
  materializeCallEvidence_success_matches
  exactDirectCallRuntimeEvidence
  exactDeclarationReferenceRuntimeEvidence
  exactDirectCallRuntimeEvidence_success_matches
  exactDeclarationReferenceRuntimeEvidence_success_matches
  exactRuntimeRequirementEvidence
  exactRuntimeRequirementEvidence_success_goal
  exactRuntimeRequirementEvidenceList
  exactRuntimeRequirementEvidenceList_success_matches
  validateExecutablePlan
  validateCanonicalInputPlan
  prepareExecutablePlanEvidenceWithBudget
  prepareExecutablePlanEvidence
  validateExecutablePlanEvidence)

end Solcore.Frontend.SourceTypedRuntime
