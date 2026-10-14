import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceArguments

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOperatorSourceTrace
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)
open CallablePreparedOperatorSourceBounds
open CallableIndexedOwnedPreparedStagedMethodSourceArguments (unary_dispatch binary_dispatch)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id reasonAt lowered)
  {stages : Staging.Recursive.Registry}
  (port : Port (compiled := compiled) receipt context invocation.evidence stages)


private theorem owned_eq {owned : List RequirementId}
    (layout : Dynamic.OrdinaryRequirementLayout receipt.node.requirements receipt.node.coercions owned) :
    owned = receipt.node.requirements := by
  simpa only [Dynamic.OrdinaryRequirementLayout, receipt.metadata.coercions, coercionRequirementIds, List.flatMap_nil, List.append_nil] using layout.symm

include port in
private theorem requirement_safe
    (unique : RequirementIdsUnique context)
    {failed : RequirementId}
    (fault : Dynamic.RequirementListFaults context invocation.evidence receipt.node.requirements failed) : False := by
  have selected := port.selected
  generalize idsEq : receipt.node.requirements = ids at selected fault
  cases selected with
  | intro primary _ _ _ _ _ _ _ _ _ remaining _ _ _ =>
    cases primary with
    | intro produced _ =>
      cases fault with
      | head unavailable =>
        exact CallableCoercionRequirementSafety.excludes_unavailable
          (fun _ _ => unique.contains_unique) produced unavailable
      | tail _ failed =>
        exact CallableCoercionRequirementSafety.excludes_list_fault
          (fun _ _ _ _ => unique.contains_unique) remaining failed

private theorem raw_inv {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (unique : RequirementIdsUnique context)
    (raw : RawOutcomeAt (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
      invocation.source environment before receipt.node outcome after) :
    RawTraceAt (Program.ofChecked compiled.sourceProgram) size context invocation.evidence port.principal.dictionary
      invocation.source environment before receipt.arguments port.principal.sourceBody outcome after := by
  have nonempty := CallableIndexedOwnedPreparedStagedMethodSourceInversion.requirements_nonempty port.selected
  cases requirementsEq : receipt.node.requirements with
  | nil => exact False.elim (nonempty requirementsEq)
  | cons primary remaining =>
    rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
    · have dispatch := unary_dispatch receipt port form
      rw [Receipt.arguments, arguments]
      cases outcome with
      | value value =>
        change SourceExecutionSize.ExpressionFormEvaluates _ _ _ _ _ _ _ _ _ _ _ _ at raw
        rw [form] at raw
        cases raw with
        | unary layout operandEvaluated applied =>
          rw [owned_eq receipt layout, requirementsEq] at applied
          cases applied with
          | method actualDispatch actual invoked =>
            rw [← requirementsEq] at actual
            obtain ⟨sameTrait, sameMethod⟩ := unary_dispatch_unique dispatch actualDispatch
            cases sameTrait
            cases sameMethod
            obtain ⟨rfl, rfl⟩ := port.agrees _ _ actual
            refine .apply (.cons operandEvaluated ?_ .nil) (.value invoked) ?_
            all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
      | fault reason =>
        change SourceExecutionSize.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _ _ at raw
        rw [form] at raw
        cases raw with
        | unaryOperand _ failed =>
          refine .argumentFault (.head failed ?_)
          all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
        | unaryApply layout operandEvaluated failed =>
          rw [owned_eq receipt layout, requirementsEq] at failed
          cases failed with
          | requirement fault => exact False.elim (requirement_safe receipt port unique (requirementsEq.symm ▸ fault))
          | method actualDispatch actual failed =>
            rw [← requirementsEq] at actual
            obtain ⟨sameTrait, sameMethod⟩ := unary_dispatch_unique dispatch actualDispatch
            cases sameTrait
            cases sameMethod
            obtain ⟨rfl, rfl⟩ := port.agrees _ _ actual
            refine .apply (.cons operandEvaluated ?_ .nil) (.fault failed) ?_
            all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
    · have dispatch := binary_dispatch receipt port form
      rw [Receipt.arguments, arguments]
      cases outcome with
      | value value =>
        change SourceExecutionSize.ExpressionFormEvaluates _ _ _ _ _ _ _ _ _ _ _ _ at raw
        rw [form] at raw
        cases raw with
        | binaryShortCircuit layout _ _ empty =>
          exact False.elim (CallableIndexedOwnedPreparedStagedMethodSourceInversion.requirements_nonempty port.selected ((owned_eq receipt layout).symm.trans empty))
        | binaryEvaluateRight layout leftEvaluated _ rightEvaluated applied =>
          rw [owned_eq receipt layout, requirementsEq] at applied
          cases applied with
          | method actualDispatch actual invoked =>
            rw [← requirementsEq] at actual
            obtain ⟨sameTrait, sameMethod⟩ := binary_dispatch_unique dispatch actualDispatch
            cases sameTrait
            cases sameMethod
            obtain ⟨rfl, rfl⟩ := port.agrees _ _ actual
            refine .apply (.cons leftEvaluated ?_ (.cons rightEvaluated ?_ .nil)) (.value invoked) ?_
            all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
      | fault reason =>
        change SourceExecutionSize.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _ _ at raw
        rw [form] at raw
        cases raw with
        | binaryLeft _ failed =>
          refine .argumentFault (.head failed ?_)
          all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
        | binaryLeftOperand _ _ invalid => exact False.elim (binary_dispatch_valid_left dispatch invalid)
        | binaryRight _ leftEvaluated _ failed =>
          refine .argumentFault (.tail leftEvaluated ?_ (.head failed ?_))
          all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
        | binaryApply layout leftEvaluated _ rightEvaluated failed =>
          rw [owned_eq receipt layout, requirementsEq] at failed
          cases failed with
          | requirement fault => exact False.elim (requirement_safe receipt port unique (requirementsEq.symm ▸ fault))
          | method actualDispatch actual failed =>
            rw [← requirementsEq] at actual
            obtain ⟨sameTrait, sameMethod⟩ := binary_dispatch_unique dispatch actualDispatch
            cases sameTrait
            cases sameMethod
            obtain ⟨rfl, rfl⟩ := port.agrees _ _ actual
            refine .apply (.cons leftEvaluated ?_ (.cons rightEvaluated ?_ .nil)) (.fault failed) ?_
            all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)


/-- Every operand and selected body retains its original grade, strictly below
this whole ordinary expression. Empty compiler coercions remove only the empty
suffix; the actual selected body and complete dictionary remain unchanged. -/
theorem source_inv {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (requirements : RequirementIdsUnique context)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      context invocation.evidence invocation.source environment before id outcome after) :
    RawTraceAt (Program.ofChecked compiled.sourceProgram) size context invocation.evidence port.principal.dictionary
      invocation.source environment before receipt.arguments port.principal.sourceBody outcome after := by
  have notLocal : ∀ name binder, receipt.node.form ≠ .reference name (.local binder) := by
    intro name binder impossible
    rcases receipt.operator.form with ⟨_, _, form, _⟩ | ⟨_, _, _, form, _⟩ <;>
      rw [form] at impossible <;> cases impossible
  have weaken {small outcome after} (within : small ≤ size)
      (raw : RawTraceAt (Program.ofChecked compiled.sourceProgram) small context invocation.evidence
        port.principal.dictionary invocation.source environment before receipt.arguments port.principal.sourceBody outcome after) :
      RawTraceAt (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
        port.principal.dictionary invocation.source environment before receipt.arguments port.principal.sourceBody outcome after := by
    have arguments {before ids values after}
        (trace : ArgumentsAt (Program.ofChecked compiled.sourceProgram) small context invocation.evidence
          invocation.source environment before ids values after) :
        ArgumentsAt (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
          invocation.source environment before ids values after := by
      induction trace with
      | nil => exact .nil
      | cons head strict _ ih => exact .cons head (Nat.lt_of_lt_of_le strict within) ih
    have failed {before ids reason after}
        (trace : ArgumentsFaultAt (Program.ofChecked compiled.sourceProgram) small context invocation.evidence
          invocation.source environment before ids reason after) :
        ArgumentsFaultAt (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
          invocation.source environment before ids reason after := by
      induction trace with
      | head failed strict => exact .head failed (Nat.lt_of_lt_of_le strict within)
      | tail head strict _ ih => exact .tail head (Nat.lt_of_lt_of_le strict within) ih
    cases raw with
    | argumentFault trace => exact .argumentFault (failed trace)
    | apply trace invoked strict => exact .apply (arguments trace) invoked (Nat.lt_of_lt_of_le strict within)
  cases raw_source_inv_sized receipt.metadata.found unique notLocal trace with
  | rawFault raw strict => exact weaken (Nat.le_of_lt strict) (raw_inv receipt port requirements raw)
  | path raw path rawStrict _ =>
    cases outcome with
    | value value =>
      change SourceExecutionSize.CoercionPathExecutes _ _ _ _ _ _ _ _ _ at path
      rw [receipt.metadata.coercions] at path
      cases path
      exact weaken (Nat.le_of_lt rawStrict) (raw_inv receipt port requirements raw)
    | fault reason =>
      change SourceExecutionSize.CoercionPathFaults _ _ _ _ _ _ _ _ _ at path
      rw [receipt.metadata.coercions] at path
      cases path

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOperatorSourceTrace
