import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyAdmission

/-! The aligned Header identifies the actual assignment callbacks. Refinement
retains the same accepted body, source, scope, fuel and emitted result. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyRefinement
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open AcceptedNamedBodyAdmission (BodyAt)

/-- The assignment profile comes from the same genuine named compiler Header. -/
theorem of_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    ∃ receipt : BodyAt header, receipt.tree.Ready := by
  obtain ⟨actual⟩ := body_of_accepted aligned.accepted
  have matched : CompatibleAssignmentStatements.AssignmentPolicy header.policy
      (.initial compiled.compatible.checked)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidOperand prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact RecursiveNamedPreparedHeaderPolicies.Prepared.assignments prepared
  obtain ⟨tree, ready⟩ := actual.tree.refine matched
  exact ⟨⟨actual.flow, tree, actual.emitted⟩, ready⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyRefinement
