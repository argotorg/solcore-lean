import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts

/-! An aligned named Header exposes the literal contextual compiler action.
Its original cached slot and hook authenticate the same specialization record.
Successful action acceptance therefore produces the root policy receipt at
the original source, scope, reason and lowering, with its genuine predecessor
budget. No action or selection equality is assumed independently. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedHeaderRootPolicyReceipts
open Core Frontend SourceInference
open RecursiveNamedPublicSpecializationMeaning
open CallableIndexedOwnedContextualCompilerPolicyProfiles

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)
  {values : SourceCoreCompatibleValues.Context}
  {header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values
    compiled.indexed.layouts.definitions (Program.ofChecked compiled.sourceProgram)}
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned

/-- The original Header policy forwards precisely this selected second-pass
contextual action, including its diagnostic issuer and callable context. -/
theorem header_action :
    header.policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      compiled.indexed.base.sourceProgram
      ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext prepared.named.signature.key [])
      compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
      prepared.compilation.parents prepared.compilation.own.assignments prepared.diagnostics
      (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      compiled.indexed.base.callableContext none none := by
  rw [aligned.policy]
  rfl

/-- The real cached Header and hook select the same complete specialization.
The accepted expression action is unwrapped once at its successor budget. -/
theorem at_successor {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression (fuel + 1) source scope id header.reasonAt = .ok lowered) :
    Nonempty (RootPolicyReceipt (compiled := compiled) prepared.named prepared.diagnostics
      prepared.code prepared.compilation fuel source scope id header.reasonAt lowered) := by
  have record := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  rw [aligned.named] at record
  rw [header_action prepared aligned] at accepted
  exact RootPolicyReceipt.of_accepted prepared.compilation record accepted

/-- Zero is rejected by the literal contextual traversal. The returned receipt
keeps the actual callback's predecessor budget rather than choosing another
lowering or silently changing the source occurrence. -/
theorem at_accepted {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel source scope id header.reasonAt = .ok lowered) :
    ∃ predecessor, fuel = predecessor + 1 ∧
      Nonempty (RootPolicyReceipt (compiled := compiled) prepared.named prepared.diagnostics
        prepared.code prepared.compilation predecessor source scope id header.reasonAt lowered) := by
  cases fuel with
  | zero =>
    rw [header_action prepared aligned] at accepted
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    change Except.error (SourceCoreBasic.Error.traversalExhausted (.occurrence id.occurrence)) = .ok lowered at accepted
    cases accepted
  | succ predecessor =>
    exact ⟨predecessor, rfl, at_successor prepared aligned accepted⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedHeaderRootPolicyReceipts
