import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationOrigins
import Solcore.Frontend.SourceSpecializationAcceptance

/-!
The real executable-plan preparation action supplies a specialization receipt
for each returned row. The actual rigid checker then supplies concrete and
flexible-closed replacements at that row's exact substitution lookup.

The original input plan and inserted methods are authenticated internally.
This result does not identify different original templates or infer source,
stage, guard-frame or execution coherence from a concrete replacement.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationRanges

open Frontend SourceInference TypeSystem SourceSpecializationWorklist

/-- Every actual retained lookup is checked by the genuine rigid specializer;
its accepted replacement contains no flexible variable. -/
theorem of_preparation {program : CheckedProgram} {before after : Plan}
    {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      program before fuel budget = .ok after) :
    ∀ specialized ∈ after.specializations, ∀ parameter replacement,
      specialized.parameterSubstitution.lookup? parameter = some replacement →
      SourceSpecialization.firstNonConcrete replacement = none ∧
        replacement.freeVariables = [] := by
  intro specialized member parameter replacement found
  obtain ⟨signature, generic, supplied, specializedEq⟩ :=
    CallablePreparedFinalSpecializationOrigins.of_preparation accepted
      specialized member
  exact ⟨SourceSpecializationAcceptance.specializeFunction_parameterReplacement_concrete
      specializedEq parameter replacement found,
    SourceSpecializationAcceptance.specializeFunction_parameterReplacement_flexibleClosed
      specializedEq parameter replacement found⟩

/-- Default public preparation keeps the same complete retained-row result. -/
theorem of_default_preparation {program : CheckedProgram} {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidence
      program before = .ok after) :
    ∀ specialized ∈ after.specializations, ∀ parameter replacement,
      specialized.parameterSubstitution.lookup? parameter = some replacement →
      SourceSpecialization.firstNonConcrete replacement = none ∧
        replacement.freeVariables = [] :=
  of_preparation accepted

end Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationRanges
