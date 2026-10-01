import Solcore.SourceSemantics.CoreLowering.BuiltinBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveSource
import Solcore.SourceSemantics.CoreLowering.FunctionCalls

/-! Direct builtin calls evaluate their arguments in source order. The callee
metadata is validated statically. Independent application and argument faults
remain explicit until the represented scalar inputs exclude invalid application.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinCalls
open Core Frontend SourceInference CompatibleExpressionPrimitives BuiltinBodyMeaning DataPatternValues

inductive SourceTrace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (arguments : List ExpressionId) (function : BuiltinFunctionId) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | argumentsFault {reason after}
      (failed : Dynamic.ExpressionsFault program context evidence source environment before arguments reason after) :
      SourceTrace program context evidence source environment before arguments function (.fault reason) after
  | apply {values middle outcome after}
      (argumentsEvaluated : Dynamic.ExpressionsEvaluate program context evidence source environment before arguments values middle)
      (applied : FunctionCallBody.Outcome program context evidence [] middle (.builtin ⟨function⟩) values outcome after) :
      SourceTrace program context evidence source environment before arguments function outcome after

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id callee : ExpressionId}
  {node : ExpressionNode} {type : Ty} {arguments : List ExpressionId} {function : BuiltinFunctionId}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}

theorem source_inv (metadata : Metadata checked source id node type)
    (form : node.form = .call callee arguments (.builtinFunction function)) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    SourceTrace program context evidence source environment before arguments function outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | builtinCall _ argumentsEvaluated applied => exact .apply argumentsEvaluated (.value applied)
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | builtinArguments _ argumentsFailed => exact .argumentsFault argumentsFailed
    | builtinApply _ argumentsEvaluated failed => exact .apply argumentsEvaluated (.fault failed)

theorem source_intro (metadata : Metadata checked source id node type)
    (form : node.form = .call callee arguments (.builtinFunction function))
    (trace : SourceTrace program context evidence source environment before arguments function outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | argumentsFault failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .builtinArguments rfl failed
  | apply argumentsEvaluated application =>
    cases application with
    | value applied =>
      apply Dynamic.ExpressionEvaluatesOutcome.value
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
      · rw [form, metadata.requirements, metadata.coercions]
        exact .builtinCall rfl argumentsEvaluated applied
      · rw [metadata.coercions]; exact .nil
    | fault failed =>
      apply Dynamic.ExpressionEvaluatesOutcome.fault
      apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
      rw [form, metadata.requirements, metadata.coercions]
      exact .builtinApply rfl argumentsEvaluated failed

private theorem types_exclude_mismatch {values : List Dynamic.Value} {types : List TypeSystem.Ty}
    (typed : ListRel Dynamic.ValueRuntimeType values types)
    {expected actual : TypeSystem.Ty} (mismatch : Dynamic.ValuesFirstTypeMismatch values types expected actual) : False := by
  induction typed with
  | nil => cases mismatch
  | cons head tail ih =>
    cases mismatch with
    | head actual different => exact different (head.functional actual).symm
    | tail _ fault => exact ih fault

theorem InputRep.source_argument_types {function : BuiltinFunctionId} {arguments : List Dynamic.Value} {input : Value}
    (inputs : InputRep function arguments input) :
    ListRel Dynamic.ValueRuntimeType arguments function.parameterTypes := by
  cases inputs <;> first
    | exact .cons (.integer _) (.cons (.integer _) .nil)
    | exact .cons (.integer _) .nil
    | exact .cons (.word _) .nil

theorem InputRep.excludes_callable_fault {function : BuiltinFunctionId} {arguments : List Dynamic.Value} {input : Value}
    (inputs : InputRep function arguments input)
    {program : Program} {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (fault : Dynamic.CallableFaults program context caller invocation before (.builtin ⟨function⟩) arguments reason after) : False := by
  cases fault with
  | notCallable invalid => exact invalid trivial
  | builtinArity mismatch =>
    cases inputs <;> exact mismatch rfl
  | builtinArgumentType _ mismatch => exact types_exclude_mismatch (InputRep.source_argument_types inputs) mismatch
end Solcore.SourceSemantics.CoreLowering.BuiltinCalls
