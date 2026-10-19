import Solcore.SourceSemantics.Staging.RecursiveAtomicLifting

/-! A real local read retains its original descriptor and requirement outcome.
With no output coercion, the staged read has exactly the same value or fault
and reached heap; no native execution or cell classification is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadLifting
open Frontend SourceInference Staging.Recursive Staging.Recursive.Lifting

theorem read {program : Program} {registry : Registry} {invocation : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder)) (empty : node.coercions = [])
    (trace : Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
      environment before id outcome after) :
    Expression program registry invocation context environment before id (embed outcome) after := by
  have same_node : ∀ {other}, ContainsExpression invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro contains raw path =>
      cases same_node contains
      rw [empty] at path
      cases path
      rw [empty] at raw
      exact .atomicValue contains (form.symm ▸ .reference name (.local binder)) empty raw
    | generalizedLocal contains reference layout lookup cell descriptor fields instantiated path =>
      cases same_node contains
      rw [empty] at path
      cases path
      exact .generalizedLocal contains reference layout lookup cell descriptor fields instantiated (empty ▸ .coercionsNil)
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
    | form contains raw =>
      cases same_node contains
      rw [empty] at raw
      exact .atomicFault contains (form.symm ▸ .reference name (.local binder)) empty raw
    | coercion contains _ failed =>
      cases same_node contains
      rw [empty] at failed
      cases failed
    | generalizedLocalRequirement contains reference layout lookup cell descriptor fields selection failed =>
      exact .generalizedLocalRequirement contains reference layout lookup cell descriptor fields selection failed
    | generalizedLocalCoercion contains _ _ _ _ _ _ _ failed =>
      cases same_node contains
      rw [empty] at failed
      cases failed

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadLifting
