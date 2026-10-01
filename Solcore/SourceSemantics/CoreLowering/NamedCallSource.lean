import Solcore.SourceSemantics.CoreLowering.FunctionCallBody

/-! Exact source declarations at a concrete named body.  Structural source
instantiation and evidence are independent of native code authentication.
The body outcome is the existing declarative relation, not a semantic field in
a compiler certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedCalls
open Frontend SourceInference

structure SourceFrame (program : Program) (instantiation : DeclarationInstantiation)
    (bodyInstance : Dynamic.BodyInstance) (function : Dynamic.Closure) : Prop where
  instantiated : Dynamic.FunctionInstantiates program instantiation bodyInstance
  source : function.source = bodyInstance.source
  context : function.context = bodyInstance.context
  parameters : function.parameters = bodyInstance.source.inputs
  result : function.resultType = bodyInstance.resultType
  captured : function.captured = []
  roots : Dynamic.StatementRoots bodyInstance.source.roots function.body
  covers : function.evidence.Covers bodyInstance.context

inductive BodyOutcome (program : Program) (bodyInstance : Dynamic.BodyInstance)
    (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (arguments : List Dynamic.Value) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {result after} (execution : Dynamic.BodyInvokes program bodyInstance evidence before arguments result after) :
      BodyOutcome program bodyInstance evidence before arguments (.value result) after
  | fault {reason after} (execution : Dynamic.BodyFaults program bodyInstance evidence before arguments reason after) :
      BodyOutcome program bodyInstance evidence before arguments (.fault reason) after

variable {program : Program} {instantiation : DeclarationInstantiation}
  {bodyInstance : Dynamic.BodyInstance} {function : Dynamic.Closure}

theorem SourceFrame.call {callerContext : SourceSemantics.Context}
    {caller : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
    {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (frame : SourceFrame program instantiation bodyInstance function)
    (execution : BodyOutcome program bodyInstance function.evidence before arguments outcome after) :
    FunctionCallBody.Outcome program callerContext caller function.evidence before
      (.global ⟨instantiation, function.evidence⟩) arguments outcome after := by
  cases execution with
  | value executed => exact .value (.global frame.instantiated rfl frame.covers executed)
  | fault executed => exact .fault (.globalBody frame.instantiated rfl executed)

/-- The real named source body is a closure-shaped trace only as a proof
view. It retains the exact declaration bodyInstance and allocates from the empty
lexical frame; no lambda occurrence is fabricated. -/
theorem SourceFrame.body_of_trace {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {before bound after : Dynamic.Heap} {arguments : List Dynamic.Value}
    {environment : Dynamic.Environment} {outcome : Dynamic.ExpressionOutcome}
    (frame : SourceFrame program instantiation bodyInstance function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after) :
    BodyOutcome program bodyInstance function.evidence before arguments outcome after := by
  have extension : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs types context := by
    simpa only [frame.source, frame.context, frame.parameters] using extended
  have allocation : Dynamic.BindersAllocate [] before bodyInstance.source.inputs arguments environment bound :=
    frame.parameters ▸ allocated
  cases trace with
  | returned executed =>
      exact .value (.returned frame.covers frame.roots extension allocation (frame.source ▸ executed) rfl)
  | unit same executed =>
      exact .value (.unit frame.covers (frame.result ▸ same) frame.roots extension allocation
        (frame.source ▸ executed) ⟨_, rfl⟩)
  | fault failed =>
      exact .fault (.statements frame.roots extension allocation (frame.source ▸ failed))
  | escaped executed escape =>
      exact .fault (.controlEscape frame.roots extension allocation (frame.source ▸ executed) escape)

private theorem roots_functional {nodes : List NodeId} {left right : List StatementId}
    (first : Dynamic.StatementRoots nodes left) (second : Dynamic.StatementRoots nodes right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | @cons id nodes left first ih => cases second with | cons remaining => exact congrArg (List.cons id) (ih remaining)

/-- Invert the independent body invocation at the statically retained call
context. Exact roots and monomorphic binder extension identify that context;
arity excludes the separate source arity-fault rule. -/
theorem SourceFrame.trace_of_body {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (frame : SourceFrame program instantiation bodyInstance function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (arity : function.parameters.length = arguments.length)
    (executed : BodyOutcome program bodyInstance function.evidence before arguments outcome after) :
    ∃ environment bound,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after := by
  have rootsUnique : ∀ {roots}, Dynamic.StatementRoots bodyInstance.source.roots roots → roots = function.body := by
    intro roots selected
    exact roots_functional selected frame.roots
  have contextUnique : ∀ {inputTypes actualContext},
      MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs inputTypes actualContext →
      actualContext = context := by
    intro inputTypes actualContext extension
    have actual : MonoBindersExtend function.source.owner function.context function.parameters inputTypes actualContext := by
      simpa only [frame.source, frame.context, frame.parameters] using extension
    have same : types = inputTypes := extended.bodyTypes_eq.symm.trans actual.bodyTypes_eq
    subst inputTypes
    exact (extended.functional actual).symm
  cases executed with
  | value invokes =>
    cases invokes with
    | returned covers roots extension allocated execution returned =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      subst_vars
      exact ⟨_, _, frame.parameters.symm ▸ allocated, .returned (frame.source.symm ▸ execution)⟩
    | unit covers same roots extension allocated execution fellThrough =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      obtain ⟨_, rfl⟩ := fellThrough
      subst_vars
      exact ⟨_, _, frame.parameters.symm ▸ allocated, .unit (frame.result.symm ▸ same) (frame.source.symm ▸ execution)⟩
  | fault fails =>
    cases fails with
    | arity mismatch => exact False.elim (mismatch (by simpa only [frame.parameters] using arity))
    | statements roots extension allocated failed =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      subst_vars
      exact ⟨_, _, frame.parameters.symm ▸ allocated, .fault (frame.source.symm ▸ failed)⟩
    | controlEscape roots extension allocated executed escape =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      subst_vars
      exact ⟨_, _, frame.parameters.symm ▸ allocated, .escaped (frame.source.symm ▸ executed) escape⟩

/-- The closed nil-argument direct-call expression uses precisely the source
declaration/evidence selected by its occurrence metadata. -/
theorem direct_nil {context : SourceSemantics.Context} {evidence invocation : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {node calleeNode : ExpressionNode} {name : String}
    {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee [] (.declaration instantiation))
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : node.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (closed : Dynamic.DirectCallProducesEvidence context evidence node.requirements node.coercions instantiation.predicates invocation)
    (called : FunctionCallBody.Outcome program context evidence invocation before
      (.global ⟨instantiation, invocation⟩) [] outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases called with
  | value applies =>
    apply Dynamic.ExpressionEvaluatesOutcome.value
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found)
    · rw [form]
      exact .directCall (lookupExpression?_sound calleeFound) calleeForm calleeRequirements calleeCoercions
        valid .nil closed applies
    · rw [coercions]; exact .nil
  | fault failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound found)
    rw [form]
    exact .directApply .nil closed failed

/-- A declaration reference produces the exact source instantiation and its
closed evidence. Native global authentication is deliberately separate. -/
theorem reference {context : SourceSemantics.Context} {evidence produced : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {name : String}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.declaration instantiation))
    (coercions : node.coercions = [])
    (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (closed : Dynamic.RequirementsProduceEnvironment context evidence [] instantiation.predicates produced) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id
      (.global ⟨instantiation, produced⟩) heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found)
  · rw [form]
    exact .declaration layout valid closed
  · rw [coercions]
    exact .nil

end Solcore.SourceSemantics.CoreLowering.NamedCalls
