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

/-- A generalized read selects its actual descriptor before the original
coercion path. Its requirement failure retains the unchanged Source heap. -/
inductive GeneralizedBranch (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (node : ExpressionNode) :
    Nat → Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | value {pathSize : Nat} {name : String} {binder : Resolved.LocalId}
      {owned : List RequirementId} {location : Dynamic.Location} {cell : Dynamic.Cell}
      {function : Dynamic.GeneralizedClosure} {substitution : TypeSystem.Substitution}
      {produced : Dynamic.EvidenceEnvironment} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
      (form : node.form = .reference name (.local binder))
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned)
      (lookup : Dynamic.Environment.LooksUp environment binder location)
      (read : Dynamic.Heap.Reads before location cell)
      (descriptor : cell.generalized = some function)
      (fields : Dynamic.RuntimeContextFields function.definitionContext context)
      (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context invocation.evidence
        function.binder node.rawType owned substitution produced)
      (path : Staging.Recursive.Size.CoercionPath program stages pathSize invocation context before node.coercions
        (.closure (function.instantiate substitution (produced ++ invocation.evidence.applySubstitution substitution)))
        outcome after) :
      GeneralizedBranch program stages invocation context environment before node
        (Staging.Recursive.Size.stepSize [pathSize]) outcome after
  | requirement {name : String} {binder : Resolved.LocalId} {owned : List RequirementId}
      {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
      {substitution : TypeSystem.Substitution} {failed : RequirementId}
      (form : node.form = .reference name (.local binder))
      (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned)
      (lookup : Dynamic.Environment.LooksUp environment binder location)
      (read : Dynamic.Heap.Reads before location cell)
      (descriptor : cell.generalized = some function)
      (fields : Dynamic.RuntimeContextFields function.definitionContext context)
      (selection : Dynamic.LocalSchemeRuntimeSelection context function.binder node.rawType owned substitution)
      (fault : Dynamic.RequirementsFault context invocation.evidence owned
        (instantiateLocalSchemePredicates substitution function.binder) failed) :
      GeneralizedBranch program stages invocation context environment before node
        (Staging.Recursive.Size.stepSize []) (.fault (.semantic (.unsatisfiedRequirement failed))) before

omit found unique in
theorem GeneralizedBranch.form {size : Nat} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Staging.Recursive.Outcome}
    (branch : GeneralizedBranch program stages invocation context environment before node size outcome after) :
    ∃ name binder, node.form = .reference name (.local binder) := by
  cases branch with
  | value form _ _ _ _ _ _ _ | requirement form _ _ _ _ _ _ _ => exact ⟨_, _, form⟩

theorem branches (nonempty : node.coercions ≠ [])
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before id outcome after) :
    ((∃ rawSize pathSize value middle,
      size = Staging.Recursive.Size.stepSize [rawSize, pathSize] ∧
      Staging.Recursive.Size.RawForm program stages rawSize invocation context environment before
        node.form node.requirements node.coercions (.value value) middle ∧
      Staging.Recursive.Size.CoercionPath program stages pathSize invocation context middle
        node.coercions value outcome after) ∨
    (∃ rawSize failure, size = Staging.Recursive.Size.stepSize [rawSize] ∧ outcome = .fault failure ∧
      Staging.Recursive.Size.RawForm program stages rawSize invocation context environment before
        node.form node.requirements node.coercions (.fault failure) after)) ∨
      GeneralizedBranch program stages invocation context environment before node size outcome after := by
  cases trace with
  | coercedValue contains _ raw path =>
      cases same found unique contains
      exact .inl (.inl ⟨_, _, _, _, rfl, raw, path⟩)
  | coercedFault contains _ raw =>
      cases same found unique contains
      exact .inl (.inr ⟨_, _, rfl, rfl, raw⟩)
  | generalizedLocal contains form layout lookup read descriptor fields instantiation path =>
      cases same found unique contains
      exact .inr (.value form layout lookup read descriptor fields instantiation path)
  | generalizedLocalRequirement contains form layout lookup read descriptor fields selection fault =>
      cases same found unique contains
      exact .inr (.requirement form layout lookup read descriptor fields selection fault)
  | _ =>
      first
      | exact False.elim (excludes_occurrence found unique nonempty (by assumption))
      | exact False.elim (excludes found unique nonempty (by assumption) (by assumption))

theorem ordinary_branches (nonempty : node.coercions ≠ [])
    (nonlocal : ∀ name binder, node.form ≠ .reference name (.local binder))
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
  rcases branches found unique nonempty trace with ordinary | generalized
  · exact ordinary
  · obtain ⟨name, binder, form⟩ := generalized.form
    exact False.elim (nonlocal name binder form)

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
