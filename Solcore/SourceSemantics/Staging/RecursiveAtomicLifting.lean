import Solcore.SourceSemantics.Staging.RecursiveLiftOutcomes

/-! Atomic ordinary traces enter staged semantics without changing their
result or heap. Readable local cells retain their actual descriptor; a
generalized closure read cannot be substituted for an ordinary cell read. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.Lifting
open Frontend Frontend.SourceInference

def OrdinaryReadAt (node : ExpressionNode) (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) : Prop :=
  ∀ name binder location cell,
    node.form = .reference name (.local binder) →
    Dynamic.Environment.LooksUp environment binder location →
    Dynamic.Heap.Reads heap location cell → cell.generalized = none

theorem OrdinaryReadAt.of_read {node : ExpressionNode} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} {name : String} {binder : Resolved.LocalId}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (form : node.form = .reference name (.local binder))
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads heap location cell) (ordinary : cell.generalized = none) :
    OrdinaryReadAt node environment heap := by
  intro otherName otherBinder otherLocation otherCell otherForm otherLookup otherRead
  rw [form] at otherForm
  cases otherForm
  cases otherLookup.functional lookup
  cases otherRead.functional read
  exact ordinary

theorem atomic {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique scope.source)
    (contains : ContainsExpression scope.source id node)
    (form : AtomicForm node.form) (uncoerced : node.coercions = [])
    (ordinary : OrdinaryReadAt node environment before)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context scope.evidence scope.source
      environment before id outcome after) :
    Expression program registry scope context environment before id (embed outcome) after := by
  have align : ∀ {other}, ContainsExpression scope.source id other → other = node := by
    intro other found
    exact Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique contains))
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro found raw coercions =>
      cases align found
      rw [uncoerced] at coercions
      cases coercions
      rw [uncoerced] at raw
      exact .atomicValue contains form uncoerced raw
    | generalizedLocal found reference _ lookup read descriptor _ _ _ =>
      cases align found
      rw [ordinary _ _ _ _ reference lookup read] at descriptor
      cases descriptor
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
    | form found raw =>
      cases align found
      rw [uncoerced] at raw
      exact .atomicFault contains form uncoerced raw
    | coercion found _ failed =>
      cases align found
      rw [uncoerced] at failed
      cases failed
    | generalizedLocalRequirement found reference _ lookup read descriptor _ _ _
    | generalizedLocalCoercion found reference _ lookup read descriptor _ _ _ =>
      cases align found
      rw [ordinary _ _ _ _ reference lookup read] at descriptor
      cases descriptor

theorem atomic_nonlocal {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique scope.source)
    (contains : ContainsExpression scope.source id node)
    (form : AtomicForm node.form) (uncoerced : node.coercions = [])
    (nonlocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    (trace : Dynamic.ExpressionEvaluatesOutcome program context scope.evidence scope.source
      environment before id outcome after) :
    Expression program registry scope context environment before id (embed outcome) after :=
  atomic unique contains form uncoerced
    (fun name binder _ _ reference _ _ => False.elim (nonlocal name binder reference)) trace

theorem atomic_read {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {outcome : Dynamic.ExpressionOutcome}
    {name : String} {binder : Resolved.LocalId} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (unique : NodeOccurrencesUnique scope.source)
    (contains : ContainsExpression scope.source id node)
    (form : node.form = .reference name (.local binder)) (uncoerced : node.coercions = [])
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads before location cell) (ordinary : cell.generalized = none)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context scope.evidence scope.source
      environment before id outcome after) :
    Expression program registry scope context environment before id (embed outcome) after :=
  atomic unique contains (form.symm ▸ .reference name (.local binder)) uncoerced
    (OrdinaryReadAt.of_read form lookup read ordinary) trace

end Solcore.SourceSemantics.Staging.Recursive.Lifting
