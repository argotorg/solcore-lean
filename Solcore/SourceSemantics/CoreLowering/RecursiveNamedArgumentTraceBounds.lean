import Solcore.SourceSemantics.CoreLowering.NamedCallExpressionSource
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds

/-! The original sized expression derivation exposes ordered arguments and
named dispatch. Successful prefixes and first faults retain their own costs;
the ordinary declaration profile fixes evidence before source dispatch. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedArgumentTraceBounds
open Core Frontend SourceInference CompatibleExpressionPrimitives
open RecursiveNamedCallBounds

inductive TraceAt (program : Program) (context : SourceSemantics.Context)
    (caller invocation : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (ids : List ExpressionId)
    (instantiation : DeclarationInstantiation) (size : Nat) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | argumentFault {child reason after}
      (failed : SourceExecutionSize.ExpressionsFault program child context caller source environment before ids reason after)
      (smaller : child < size) : TraceAt program context caller invocation source environment before ids instantiation size (.fault reason) after
  | apply {argumentsSize callSize arguments middle outcome after}
      (argumentsEvaluated : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context caller source environment before ids arguments middle)
      (called : CallOutcome program callSize context caller invocation middle (.global ⟨instantiation, invocation⟩) arguments outcome after)
      (argumentsSmaller : argumentsSize < size) (callSmaller : callSize < size) :
      TraceAt program context caller invocation source environment before ids instantiation size outcome after

private theorem node_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

private theorem evaluation_raw_sized
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value} {size : Nat}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder)) (empty : node.coercions = [])
    (evaluation : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before id value after) :
    ∃ child, SourceExecutionSize.ExpressionFormEvaluates program child context evidence source environment before
      node.form node.requirements node.coercions value after ∧ child < size := by
  cases evaluation with
  | intro found raw coercions =>
    have same := node_unique unique found contains
    subst same
    rw [empty] at coercions
    cases coercions
    exact ⟨_, raw, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := node_unique unique found contains
    subst same
    exact False.elim (notLocal _ _ form)

private theorem fault_raw_sized
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {size : Nat}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder)) (empty : node.coercions = [])
    (fault : SourceExecutionSize.ExpressionFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.ExpressionFormFaults program child context evidence source environment before
      node.form node.requirements node.coercions reason after ∧ child < size := by
  cases fault with
  | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
  | form found raw =>
    exact ⟨_, node_unique unique found contains ▸ raw, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | coercion found _ failed =>
    have same := node_unique unique found contains
    subst same
    rw [empty] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := node_unique unique found contains
    subst same
    exact False.elim (notLocal _ _ form)

private theorem evidence_empty {context : SourceSemantics.Context} {caller output : Dynamic.EvidenceEnvironment}
    (produced : Dynamic.DirectCallProducesEvidence context caller [] [] [] output) : output = [] := by
  cases produced with
  | intro _ _ produces => simpa using produces.length_eq.2.symm

theorem source_inv
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id callee : ExpressionId}
    {node calleeNode : ExpressionNode} {type : Ty} {ids : List ExpressionId}
    {program : Program} {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {instantiation : DeclarationInstantiation} {invocation : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (metadata : Metadata checked source id node type)
    (form : node.form = .call callee ids (.declaration instantiation))
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (predicates : instantiation.predicates = []) (evidence : invocation = [])
    (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context caller source environment before id outcome after) :
    TraceAt program context caller invocation source environment before ids instantiation size outcome after := by
  subst invocation
  cases trace with
  | value evaluated =>
    obtain ⟨child, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | directCall _ _ _ _ _ argumentsEvaluated produced applied =>
      rw [predicates] at produced
      have empty := evidence_empty produced
      subst empty
      refine .apply argumentsEvaluated (.value applied) ?_ ?_
      · exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
      · exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
  | fault failed =>
    obtain ⟨child, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | directCalleeMissing absent =>
      exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound calleeFound))
    | directArguments _ _ failed =>
      exact .argumentFault failed (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | directRequirements _ unavailable => cases unavailable
    | directApply argumentsEvaluated produced failed =>
      rw [predicates] at produced
      have empty := evidence_empty produced
      subst empty
      refine .apply argumentsEvaluated (.fault failed) ?_ ?_
      · exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
      · exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller

theorem source_intro
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id callee : ExpressionId}
    {node calleeNode : ExpressionNode} {type : Ty} {ids : List ExpressionId} {name : String}
    {program : Program} {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment}
    {instantiation : DeclarationInstantiation} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (metadata : Metadata checked source id node type)
    (form : node.form = .call callee ids (.declaration instantiation))
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (predicates : instantiation.predicates = []) (evidence : invocation = [])
    (trace : TraceAt program context caller invocation source environment before ids instantiation size outcome after) :
    ∃ resultSize, ExpressionOutcome program resultSize context caller source environment before id outcome after := by
  have produced : Dynamic.DirectCallProducesEvidence context caller [] [] instantiation.predicates invocation := by
    rw [predicates, evidence]
    exact .intro (selected := []) (contextual := []) (signatureRequirements := []) rfl rfl .nil
  cases trace with
  | @argumentFault child reason after failed _ =>
    have raw := SourceExecutionSize.ExpressionFormFaults.directArguments
      (requirements := []) (coercions := []) (lookupExpression?_sound calleeFound) calleeForm failed
    refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [child]], .fault (.form (lookupExpression?_sound metadata.found) ?_)⟩
    simpa only [form, metadata.requirements, metadata.coercions] using raw
  | @apply argumentsSize callSize arguments middle outcome after argumentsEvaluated called _ _ =>
    cases called with
    | @value result after applied =>
      have raw := SourceExecutionSize.ExpressionFormEvaluates.directCall
        (lookupExpression?_sound calleeFound) calleeForm calleeRequirements calleeCoercions valid argumentsEvaluated produced applied
      have coercions : SourceExecutionSize.CoercionPathExecutes program (SourceExecutionSize.stepSize []) context caller after
          node.coercions result result after := metadata.coercions.symm ▸ SourceExecutionSize.CoercionPathExecutes.nil
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [argumentsSize, callSize], SourceExecutionSize.stepSize []], .value (.intro (lookupExpression?_sound metadata.found) ?_ coercions)⟩
      simpa only [form, metadata.requirements, metadata.coercions] using raw
    | fault failed =>
      have raw := SourceExecutionSize.ExpressionFormFaults.directApply (callee := callee) argumentsEvaluated produced failed
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [argumentsSize, callSize]], .fault (.form (lookupExpression?_sound metadata.found) ?_)⟩
      simpa only [form, metadata.requirements, metadata.coercions] using raw

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedArgumentTraceBounds
