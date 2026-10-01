import Solcore.SourceSemantics.CoreLowering.BuiltinNamedCallMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveSource

/-! Independent ordinary named-call expressions select their exact retained
source body. Empty declaration predicates and occurrence requirements fix the
invocation evidence; declaration-owner uniqueness fixes the body. The argument
trace is recovered from the expression outcome rather than supplied separately.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedCallExpressions
open Core Frontend SourceInference CompatibleExpressionPrimitives

private theorem evidence_empty {context : SourceSemantics.Context}
    {caller output : Dynamic.EvidenceEnvironment}
    (produced : Dynamic.DirectCallProducesEvidence context caller [] [] [] output) :
    output = [] := by
  cases produced with
  | intro coercions requirements produces =>
    simpa using produces.length_eq.2.symm

private theorem arguments_length {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {ids : List ExpressionId} {values : List Dynamic.Value}
    (evaluated : Dynamic.ExpressionsEvaluate program context evidence source environment before ids values after) :
    ids.length = values.length := by
  induction ids generalizing before values with
  | nil => cases evaluated; rfl
  | cons id ids ih =>
    cases evaluated with
    | cons _ tail => exact congrArg Nat.succ (ih tail)

/-- Full expression outcome inversion for the closed ordinary declaration
profile. Arguments, including their first fault, precede actual source dispatch.
This theorem does not assume a source body execution in a static certificate. -/
theorem source_inv
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id callee : ExpressionId}
    {node calleeNode : ExpressionNode} {type : Ty} {ids : List ExpressionId} {name : String}
    {program : Program} {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {instantiation : DeclarationInstantiation} {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (metadata : Metadata checked source id node type)
    (form : node.form = .call callee ids (.declaration instantiation))
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (_calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (predicates : instantiation.predicates = [])
    (evidence : function.evidence = [])
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (arity : function.parameters.length = ids.length)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context caller source environment before id outcome after) :
    NamedCalls.Arguments.Trace program context caller function.evidence source environment before ids body outcome after := by
  have dispatch {arguments middle outcome after}
      (argumentsEvaluated : Dynamic.ExpressionsEvaluate program context caller source environment before ids arguments middle)
      (called : FunctionCallBody.Outcome program context caller [] middle (.global ⟨instantiation, []⟩) arguments outcome after) :
      NamedCalls.BodyOutcome program body function.evidence middle arguments outcome after := by
    apply BuiltinNamedCalls.source_dispatch owners frame (arity.trans (arguments_length argumentsEvaluated))
    simpa only [evidence] using called
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | directCall _ _ _ _ _ argumentsEvaluated produced applied =>
      rw [predicates] at produced
      have empty := evidence_empty produced
      subst empty
      exact .apply argumentsEvaluated (dispatch argumentsEvaluated (.value applied))
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | directCalleeMissing absent =>
      exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound calleeFound))
    | directArguments _ _ failed => exact .argumentFault failed
    | directRequirements argumentsEvaluated unavailable => cases unavailable
    | directApply argumentsEvaluated produced failed =>
      rw [predicates] at produced
      have empty := evidence_empty produced
      subst empty
      exact .apply argumentsEvaluated (dispatch argumentsEvaluated (.fault failed))

end Solcore.SourceSemantics.CoreLowering.NamedCallExpressions
