import Solcore.SourceSemantics.Staging.RecursiveFaultPreservationSupport

/-! A nonempty original output path determines the staged raw-form and suffix
branches. Successful raw evaluation supplies genuine reached Source typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedExpressionSource
open Core Frontend SourceInference

variable {program : Program} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  {id : ExpressionId} {node : ExpressionNode}
  (found : invocation.source.lookupExpression? id = some node)
  (unique : NodeOccurrencesUnique invocation.source)

include found unique

private theorem same {other : ExpressionNode}
    (contains : ContainsExpression invocation.source id other) : other = node :=
  Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)

private theorem excludes (nonempty : node.coercions ≠ []) {other : ExpressionNode}
    (contains : ContainsExpression invocation.source id other) (empty : other.coercions = []) : False :=
  nonempty ((congrArg ExpressionNode.coercions (same found unique contains)).symm.trans empty)

private theorem excludes_occurrence (nonempty : node.coercions ≠ [])
    {form : ExpressionForm} {requirements : List RequirementId}
    (occurrence : Staging.Recursive.Occurrence invocation id form requirements) : False := by
  obtain ⟨other, contains, _form, _requirements, empty⟩ := occurrence
  exact excludes found unique nonempty contains empty

theorem branches (nonempty : node.coercions ≠ [])
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before id outcome after) :
    (∃ rawSize pathSize value middle,
      size = Staging.Recursive.Size.stepSize [rawSize, pathSize] ∧
      Staging.Recursive.Size.RawForm program stages rawSize invocation context environment before
        node.form node.requirements node.coercions (.value value) middle ∧
      Staging.Recursive.Size.CoercionPath program stages pathSize invocation context middle
        node.coercions value outcome after) ∨
    (∃ rawSize failure, size = Staging.Recursive.Size.stepSize [rawSize] ∧ outcome = .fault failure ∧
      Staging.Recursive.Size.RawForm program stages rawSize invocation context environment before
        node.form node.requirements node.coercions (.fault failure) after) := by
  cases trace with
  | coercedValue contains _ raw path =>
      cases same found unique contains
      exact .inl ⟨_, _, _, _, rfl, raw, path⟩
  | coercedFault contains _ raw =>
      cases same found unique contains
      exact .inr ⟨_, _, rfl, rfl, raw⟩
  | _ =>
      first
      | exact False.elim (excludes_occurrence found unique nonempty (by assumption))
      | exact False.elim (excludes found unique nonempty (by assumption) (by assumption))

theorem raw_value
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {size : Nat} {value : Dynamic.Value}
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heap : Dynamic.HeapWellTyped context before)
    (typed : ExpressionHasType invocation.source context id node.type)
    (trace : Staging.Recursive.Size.RawForm program stages size invocation context environment before
      node.form node.requirements node.coercions (.value value) after) :
    Dynamic.ValueHasType context after value node.rawType ∧ Dynamic.HeapWellTyped context after ∧
      Dynamic.HeapTypesExtend before after := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | @intro _ _ actual rawType plan contains raw rawEq _ _ valid =>
      cases same found unique contains
      rw [← rawEq] at raw
      exact Staging.Recursive.FaultPreservation.raw_form_value wellFormed runtime covers locals heap
        ⟨id, node, lookupExpression?_sound found, rfl, rfl⟩ raw (rawEq ▸ valid) trace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedExpressionSource
