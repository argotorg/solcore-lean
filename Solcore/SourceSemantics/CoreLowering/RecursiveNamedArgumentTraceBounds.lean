import Solcore.SourceSemantics.CoreLowering.NamedCallExpressionSource
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableEvidenceEnvironment

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

private theorem requirement_functional {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {id : RequirementId} {predicate : ProgramPredicate} {first second : TraitEvidence}
    (unique : RequirementIdsUnique context)
    (left : Dynamic.RequirementProducesEvidence context caller id predicate first)
    (right : Dynamic.RequirementProducesEvidence context caller id predicate second) : first = second := by
  cases left with
  | intro contains _ representation _ closes _ =>
    cases right with
    | intro otherContains _ otherRepresentation _ otherCloses _ =>
      have same := unique.contains_unique contains otherContains
      subst same
      have sameEvidence := representation.functional otherRepresentation
      subst sameEvidence
      exact CallableEvidenceEnvironment.closes_functional closes otherCloses

private theorem requirements_functional {context : SourceSemantics.Context} {caller first second : Dynamic.EvidenceEnvironment}
    {requirements : List RequirementId} {predicates : List ProgramPredicate}
    (unique : RequirementIdsUnique context)
    (left : Dynamic.RequirementsProduceEnvironment context caller requirements predicates first)
    (right : Dynamic.RequirementsProduceEnvironment context caller requirements predicates second) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons head tail ih =>
    cases right with
    | cons otherHead otherTail => rw [requirement_functional unique head otherHead, ih otherTail]

private theorem direct_requirements {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment}
    {requirements : List RequirementId} {predicates : List ProgramPredicate}
    (produced : Dynamic.DirectCallProducesEvidence context caller requirements [] predicates invocation) :
    Dynamic.RequirementsProduceEnvironment context caller requirements predicates invocation := by
  cases produced with
  | intro steps requirementsEq produces =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp steps.symm
    simp only [coercionRequirementIds, List.flatMap_nil, List.nil_append, List.append_nil] at requirementsEq
    rw [requirementsEq]
    exact produces

private theorem source_inv_main
    {source : TypedSource} {id callee : ExpressionId}
    {node calleeNode : ExpressionNode} {ids : List ExpressionId}
    {program : Program} {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {instantiation : DeclarationInstantiation} {invocation : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (found : source.lookupExpression? id = some node) (coercions : node.coercions = [])
    (form : node.form = .call callee ids (.declaration instantiation))
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (determined : ∀ {output}, Dynamic.DirectCallProducesEvidence context caller node.requirements [] instantiation.predicates output → output = invocation)
    (safe : ∀ failed, ¬ Dynamic.RequirementsFault context caller node.requirements instantiation.predicates failed)
    (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context caller source environment before id outcome after) :
    TraceAt program context caller invocation source environment before ids instantiation size outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨child, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound found)
      (by intros; simp [form]) coercions evaluated
    rw [form, coercions] at raw
    cases raw with
    | directCall _ _ _ _ _ argumentsEvaluated produced applied =>
      have same := determined produced
      subst same
      refine .apply argumentsEvaluated (.value applied) ?_ ?_
      · exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
      · exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
  | fault failed =>
    obtain ⟨child, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound found)
      (by intros; simp [form]) coercions failed
    rw [form, coercions] at raw
    cases raw with
    | directCalleeMissing absent =>
      exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound calleeFound))
    | directArguments _ _ failed =>
      exact .argumentFault failed (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | directRequirements _ unavailable => exact False.elim (safe _ unavailable)
    | directApply argumentsEvaluated produced failed =>
      have same := determined produced
      subst same
      refine .apply argumentsEvaluated (.fault failed) ?_ ?_
      · exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
      · exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller

/-- The exact retained requirement spine fixes the same invocation dictionary.
Only that reached evidence is consumed; no whole-ledger ordinary validity or
caller-independent dictionary law is required. -/
theorem source_inv_with_evidence
    {source : TypedSource} {id callee : ExpressionId}
    {node calleeNode : ExpressionNode} {ids : List ExpressionId}
    {program : Program} {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {instantiation : DeclarationInstantiation} {invocation : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (found : source.lookupExpression? id = some node) (coercions : node.coercions = [])
    (form : node.form = .call callee ids (.declaration instantiation))
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (produced : Dynamic.DirectCallProducesEvidence context caller node.requirements [] instantiation.predicates invocation)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context caller source environment before id outcome after) :
    TraceAt program context caller invocation source environment before ids instantiation size outcome after := by
  have exactRequirements := direct_requirements produced
  exact source_inv_main found coercions form calleeFound
    (fun other => requirements_functional idsUnique (direct_requirements other) exactRequirements)
    (fun _ failed => exactRequirements.excludes_fault idsUnique failed) unique trace

theorem source_intro_with_evidence
    {source : TypedSource} {id callee : ExpressionId}
    {node calleeNode : ExpressionNode} {ids : List ExpressionId} {name : String}
    {program : Program} {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment}
    {instantiation : DeclarationInstantiation} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (found : source.lookupExpression? id = some node) (coercions : node.coercions = [])
    (form : node.form = .call callee ids (.declaration instantiation))
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (produced : Dynamic.DirectCallProducesEvidence context caller node.requirements [] instantiation.predicates invocation)
    (trace : TraceAt program context caller invocation source environment before ids instantiation size outcome after) :
    ∃ resultSize, ExpressionOutcome program resultSize context caller source environment before id outcome after := by
  cases trace with
  | @argumentFault child reason after failed _ =>
    have raw := SourceExecutionSize.ExpressionFormFaults.directArguments
      (requirements := node.requirements) (coercions := []) (lookupExpression?_sound calleeFound) calleeForm failed
    refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [child]], .fault (.form (lookupExpression?_sound found) ?_)⟩
    simpa only [form, coercions] using raw
  | @apply argumentsSize callSize arguments middle outcome after argumentsEvaluated called _ _ =>
    cases called with
    | @value result after applied =>
      have raw := SourceExecutionSize.ExpressionFormEvaluates.directCall
        (lookupExpression?_sound calleeFound) calleeForm calleeRequirements calleeCoercions valid argumentsEvaluated produced applied
      have coercionTrace : SourceExecutionSize.CoercionPathExecutes program (SourceExecutionSize.stepSize []) context caller after
          node.coercions result result after := coercions.symm ▸ SourceExecutionSize.CoercionPathExecutes.nil
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [argumentsSize, callSize], SourceExecutionSize.stepSize []], .value (.intro (lookupExpression?_sound found) ?_ coercionTrace)⟩
      simpa only [form, coercions] using raw
    | fault failed =>
      have raw := SourceExecutionSize.ExpressionFormFaults.directApply (callee := callee) argumentsEvaluated produced failed
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [argumentsSize, callSize]], .fault (.form (lookupExpression?_sound found) ?_)⟩
      simpa only [form, coercions] using raw
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
  apply source_inv_main metadata.found metadata.coercions form calleeFound ?_ ?_ unique trace
  · intro output produced
    rw [metadata.requirements, predicates] at produced
    exact (evidence_empty produced).trans evidence.symm
  · intro failed unavailable
    rw [metadata.requirements, predicates] at unavailable
    cases unavailable

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
  have produced : Dynamic.DirectCallProducesEvidence context caller node.requirements [] instantiation.predicates invocation := by
    rw [metadata.requirements, predicates, evidence]
    exact .intro (selected := []) (contextual := []) (signatureRequirements := []) rfl rfl .nil
  exact source_intro_with_evidence metadata.found metadata.coercions form calleeFound calleeForm
    calleeRequirements calleeCoercions valid produced trace

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedArgumentTraceBounds
