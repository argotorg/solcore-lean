import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodFrame

/-! Actual method frames expose the original body child without declaring the
method an ordinary function. These are formal consumers; existing operator
runtime suites remain the execution regression tests. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableMethodBodyTraceBounds
open Frontend SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedCallBounds

abbrev fields_only := @body_trace_of_fields
abbrev ordinary_entry := @body_trace

section Actual
variable {program : Program} {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
  {size : Nat} {types : List TypeSystem.Ty} {context : Context}
  {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}

/-- Both allocation and the strict child come from this supplied derivation. -/
theorem actual_method
    (frame : CallableCoercionMethodFrame.Frame body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (arity : function.parameters.length = arguments.length)
    (executed : BodyOutcome program size body function.evidence before arguments outcome after) :
    ∃ child environment bound,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      BodyTrace program child function context environment bound outcome after ∧ child < size :=
  body_trace_of_fields frame.source frame.context frame.parameters frame.result frame.roots extended arity executed

/-- The original input bound composes with the returned strict child; neither
source derivation is measured again. -/
theorem actual_method_below
    (frame : CallableCoercionMethodFrame.Frame body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (arity : function.parameters.length = arguments.length)
    (executed : BodyOutcome program size body function.evidence before arguments outcome after)
    {budget : Nat} (within : size ≤ budget) :
    ∃ child environment bound,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      BodyTrace program child function context environment bound outcome after ∧ child < budget := by
  obtain ⟨child, environment, bound, allocation, trace, smaller⟩ := actual_method frame extended arity executed
  exact ⟨child, environment, bound, allocation, trace, Nat.lt_of_lt_of_le smaller within⟩

/-- A nonempty dictionary and every heap cell retain their original indices. -/
theorem full_evidence_and_heap
    (frame : CallableCoercionMethodFrame.Frame body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (arity : function.parameters.length = arguments.length)
    (executed : BodyOutcome program size body function.evidence before arguments outcome after) :
    ∃ child environment bound,
      Dynamic.BindersAllocate [] before body.source.inputs arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧ child < size := by
  obtain ⟨child, environment, bound, allocation, trace, smaller⟩ := actual_method frame extended arity executed
  exact ⟨child, environment, bound, frame.parameters ▸ allocation, trace.sound, smaller⟩

/-- This consumer retains the old named signature and the same conclusion. -/
theorem actual_named {instantiation : SourceInference.DeclarationInstantiation}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (arity : function.parameters.length = arguments.length)
    (executed : BodyOutcome program size body function.evidence before arguments outcome after) :
    ∃ child environment bound,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      BodyTrace program child function context environment bound outcome after ∧ child < size :=
  body_trace frame extended arity executed
end Actual

section Boundaries
/-- Static body fields do not supply an ordinary declaration instantiation. -/
theorem method_frame_is_not_ordinary
    {program : Program} {instantiation : SourceInference.DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
    (_frame : CallableCoercionMethodFrame.Frame body function)
    (absent : ¬ Dynamic.FunctionInstantiates program instantiation body) :
    ¬ NamedCalls.SourceFrame program instantiation body function :=
  fun ordinary => absent ordinary.instantiated

/-- Arity is an independent prerequisite even for a real method frame. -/
theorem arity_fault_excluded
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {arguments : List Dynamic.Value}
    (frame : CallableCoercionMethodFrame.Frame body function)
    (arity : function.parameters.length = arguments.length) :
    ¬ body.source.inputs.length ≠ arguments.length := by
  simpa only [frame.parameters] using (not_not_intro arity)
end Boundaries
end Solcore.Test.SourceCoreCallableMethodBodyTraceBounds
