import Solcore.SourceSemantics.CoreLowering.NamedCallSource

/-! Direct named-call outcomes retain the independently instantiated source
body. Arguments run before that body, and a first argument fault skips it. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedCalls.Arguments
open Frontend SourceInference

inductive Trace (program : Program) (context : SourceSemantics.Context)
    (caller invocation : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (ids : List ExpressionId)
    (body : Dynamic.BodyInstance) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | argumentFault {reason after}
      (failed : Dynamic.ExpressionsFault program context caller source environment before ids reason after) :
      Trace program context caller invocation source environment before ids body (.fault reason) after
  | apply {arguments middle outcome after}
      (evaluated : Dynamic.ExpressionsEvaluate program context caller source environment before ids arguments middle)
      (applied : NamedCalls.BodyOutcome program body invocation middle arguments outcome after) :
      Trace program context caller invocation source environment before ids body outcome after

/-- Build the actual independent direct-call occurrence, retaining its exact
callee metadata and source evidence. No compiler type selects a source body. -/
theorem expression {program : Program} {context : SourceSemantics.Context}
    {caller : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {ids : List ExpressionId} {id callee : ExpressionId}
    {node calleeNode : ExpressionNode} {name : String} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {outcome : Dynamic.ExpressionOutcome}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : node.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (closed : Dynamic.DirectCallProducesEvidence context caller node.requirements node.coercions instantiation.predicates function.evidence)
    (trace : Trace program context caller function.evidence source environment before ids body outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context caller source environment before id outcome after := by
  cases trace with
  | argumentFault failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound found)
    rw [form]
    exact .directArguments (lookupExpression?_sound calleeFound) calleeForm failed
  | apply evaluated applied =>
    have invoked := frame.call (callerContext := context) (caller := caller) applied
    cases invoked with
    | value applies =>
      apply Dynamic.ExpressionEvaluatesOutcome.value
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found)
      · rw [form]
        exact .directCall (lookupExpression?_sound calleeFound) calleeForm calleeRequirements calleeCoercions
          valid evaluated closed applies
      · rw [coercions]; exact .nil
    | fault failed =>
      apply Dynamic.ExpressionEvaluatesOutcome.fault
      apply Dynamic.ExpressionFaults.form (lookupExpression?_sound found)
      rw [form]
      exact .directApply evaluated closed failed

end Solcore.SourceSemantics.CoreLowering.NamedCalls.Arguments
