import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageGroupLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds Staging.Recursive.Lifting
open CallableIndexedOwnedPreparedStagedGroupBounds (Group)
universe u

theorem child_of_group {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id inner : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .group inner) (empty : node.coercions = [])
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ child, child < size ∧ RecursiveNamedCallBounds.ExpressionOutcome program child context evidence source environment before inner outcome after := by
  have sameNode : ∀ {other}, ContainsExpression source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro contains raw coercions =>
      cases sameNode contains
      rw [empty] at coercions
      cases coercions
      rw [form] at raw
      cases raw with
      | group _ child =>
        refine ⟨_, ?_, .value child⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
    | generalizedLocal contains otherForm _ _ _ _ _ _ _ =>
      cases sameNode contains
      rw [form] at otherForm
      cases otherForm
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
    | form contains raw =>
      cases sameNode contains
      rw [form] at raw
      cases raw with
      | group _ child =>
        refine ⟨_, ?_, .fault child⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
    | coercion contains _ failed =>
      cases sameNode contains
      rw [empty] at failed
      cases failed
    | generalizedLocalRequirement contains otherForm _ _ _ _ _ _ _
    | generalizedLocalCoercion contains otherForm _ _ _ _ _ _ _ =>
      cases sameNode contains
      rw [form] at otherForm
      cases otherForm

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate}

theorem group (unique : NodeOccurrencesUnique invocation.source) (size : Nat)
    (childLift : ∀ childSize, childSize < size → LiftsAt bridge context model registry invocation children childSize) :
    LiftsAt bridge context model registry invocation (Group checked invocation.source children) size := by
  intro scope id lowered certificate actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  cases certificate with
  | actual metadata form innerFound sourceType child =>
    cases Option.some.inj (found.symm.trans metadata.found)
    obtain ⟨innerNode, otherFound, _, innerTyped⟩ := CompatibleExpressionProducts.group_source_types
      unique metadata.found form metadata.coercions typed
    cases Option.some.inj (otherFound.symm.trans innerFound)
    obtain ⟨childSize, smaller, evaluated⟩ := child_of_group unique metadata.found form metadata.coercions trace
    obtain ⟨staged, reached, lifted, adapted⟩ := childLift childSize smaller child innerFound innerTyped
      environments heaps locals agrees actualTyped initial admitted evaluated
    exact ⟨staged, reached, .group ⟨_, lookupExpression?_sound metadata.found, form,
      metadata.requirements, metadata.coercions⟩ lifted, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageGroupLifting
