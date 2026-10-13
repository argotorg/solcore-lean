import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection

/-! Executable recovery of the exact primary and ordered method roots from an
actual checked operator selection. This reuses the original requirement action
and retains all method premises without projecting their trees. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodSelectedRoots
open Frontend SourceInference
abbrev Dictionary := SourceTypedRuntime.RuntimeEvidenceEnvironment

private def solvedRow (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId) (requirement : RequirementId) :
    Except SourceTypedRuntime.RuntimeError SolvedRequirement :=
  match caller.function.solvedRequirements.filter (fun solved => decide (solved.id = requirement)) with
  | [] => .error (.missingSolvedRequirement caller.key occurrence requirement)
  | [solved] => .ok solved
  | solved => .error (.duplicateSolvedRequirements caller.key occurrence requirement solved.length)

def rawRoots (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : Dictionary)
    (selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod) :
    Except SourceTypedRuntime.RuntimeError Dictionary := do
  let solved ← solvedRow caller node.id selection.primaryRequirement
  let primary ← SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available
    selection.primaryRequirement solved.predicate
  pure (primary :: selection.method.methodPremises)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem primary_row {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : Dictionary} {id : RequirementId} {goal : ProgramPredicate}
    {raw : TypedTraitResolution.Evidence}
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available id goal = .ok raw) :
    ∃ solved, solvedRow caller node.id id = .ok solved ∧
      solved.predicate = goal := by
  simp only [SourceCompilationPlan.exactRuntimeRequirementEvidence, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  obtain ⟨solved, found, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
  · rename_i same
    exact ⟨solved, found, by simpa using same⟩

/-- The recovered raw roots equal the complete roots retained by the authentic
selector certificate, including ordered and repeated method premises. -/
theorem of_certificate {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : Dictionary} {primary : RequirementId}
    {methodIds : List RequirementId} {arity : Nat} {name : String}
    {method : ExecutableImplMethods.CheckedMethod}
    (roots : CallableCoercionMethodCertificates.Roots program caller node available primary methodIds arity name method) :
    rawRoots program caller node available ⟨primary, method⟩ = .ok (roots.primary :: roots.methodEvidence) := by
  obtain ⟨solved, found, same⟩ := primary_row roots.primarySelected
  simp only [rawRoots, found, bind, Except.bind, same, roots.primarySelected,
    roots.methods, pure, Except.pure]

theorem of_source_receipt {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
    {child : SourceCoreEvidence.Child} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Core.Word}
    {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
    {actual : CallablePreparedMethodSelection.Operator program project caller compilation child fuel
      source scope id reasonAt policy node output}
    (selected : CallablePreparedMethodSelection.SourceReceipt actual) :
    rawRoots program caller (CallableCoercionExpressionCertificates.rawNode node actual.requirements)
      actual.available actual.selection =
        .ok (selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence) :=
  of_certificate selected.certificate.roots

end Solcore.SourceSemantics.CoreLowering.CallableMethodSelectedRoots
