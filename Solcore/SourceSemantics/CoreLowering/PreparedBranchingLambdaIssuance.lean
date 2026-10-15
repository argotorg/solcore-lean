import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralIssuedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedRecipes

/-! The actual selected compilation authenticates the prepared body issuer.
Root-table replacement leaves both original assignment and place inventories intact. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingLambdaIssuance
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralPlaceDiagnosticShells
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))

theorem of_compilation
    {lowered : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed caller.named lowered namedCode)
    (issuedAt : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed lowered)
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named)) :
    ∃ issued : IssuedSource compiled caller.named.signature.key (source caller.named),
      issued.assignments = compilation.own.assignments ∧
      PlaceReasonsEq issued.diagnostics.program lowered := by
  obtain ⟨diagnostics, found, sameBase, samePlaces⟩ := issuedAt
  obtain ⟨root, extra, prepared, collected⟩ :=
    CallableIndexedOwnedPublicPlaceMissingDiagnostics.inventory_at_header caller found
  have basePrepared := CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base prepared
  have selected := compilation.diagnostic
  rw [sameBase] at selected
  obtain ⟨first, assignmentsPrepared⟩ := SourceCoreProgramFaultSites.prepare_assignments_at
    basePrepared (CallableIndexedActualNamedSourceReceipts.header_record compiled caller) selected
  change SourceCoreAssignmentFaultSites.prepare (source caller.named) first =
    .ok compilation.own.assignments at assignmentsPrepared
  rw [caller.agreement.source] at collected
  let issued : IssuedSource compiled caller.named.signature.key (source caller.named) := {
    first := first
    assignments := compilation.own.assignments
    assignmentsPrepared := assignmentsPrepared
    typing := typing
    plan := compiled.indexed.base.plan
    root := root
    extra := extra
    diagnostics := diagnostics
    prepared := prepared
    collected := collected }
  exact ⟨issued, rfl, placeReasons_of_places samePlaces.symm⟩

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingLambdaIssuance
