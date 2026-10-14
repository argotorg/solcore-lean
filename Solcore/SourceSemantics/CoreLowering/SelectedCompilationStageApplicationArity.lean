import Solcore.SourceSemantics.Staging.RecursiveLiftOutcomes
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds

/-! Genuine pre-body argument-count failures keep their ordinary result and
heap when lifted. Matching arity is reserved for the actual entry producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageApplicationArity
open Frontend SourceInference Staging.Recursive.Lifting

variable {program : Program} {stages : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment}
  {before after : Dynamic.Heap} {arguments : List Dynamic.Value}
  {size : Nat} {outcome : Dynamic.ExpressionOutcome}

theorem closure_mismatch {function : Dynamic.Closure}
    (mismatch : function.parameters.length ≠ arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome program size context caller invocation before
      (.closure function) arguments outcome after) :
    ApplicationLift program stages scope context before (.closure function) arguments outcome after := by
  cases trace with
  | value evaluated =>
    cases evaluated with
    | closure _ _ _ allocated _ _ => exact False.elim (mismatch allocated.length_eq)
    | closureUnit _ _ _ _ allocated _ _ => exact False.elim (mismatch allocated.length_eq)
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | closureArity rejected => exact ⟨_, _, .closureArity rejected, .completed⟩
    | closureBody _ _ _ allocated _ => exact False.elim (mismatch allocated.length_eq)
    | closureControlEscape _ _ _ allocated _ _ => exact False.elim (mismatch allocated.length_eq)

theorem global_mismatch {function : Dynamic.GlobalFunction} {body : Dynamic.BodyInstance}
    {closure : Dynamic.Closure}
    (unique : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (frame : NamedCalls.SourceFrame program function.instantiation body closure)
    (mismatch : closure.parameters.length ≠ arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome program size context caller invocation before
      (.global function) arguments outcome after) :
    ApplicationLift program stages scope context before (.global function) arguments outcome after := by
  have rawMismatch : body.source.inputs.length ≠ arguments.length := by
    simpa only [frame.parameters] using mismatch
  cases trace with
  | value evaluated =>
    cases evaluated with
    | global actual _ _ invoked =>
      cases BuiltinNamedCalls.instantiation_unique unique frame.instantiated actual
      cases invoked with
      | returned _ _ _ allocated _ _ => exact False.elim (rawMismatch allocated.length_eq)
      | unit _ _ _ _ allocated _ _ => exact False.elim (rawMismatch allocated.length_eq)
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | globalSignatureMissing missing =>
      cases frame.instantiated with
      | intro signatureMem _ declaration _ _ _ _ _ =>
        exact False.elim (missing _ signatureMem declaration.symm)
    | globalBodyMissing missing =>
      cases frame.instantiated with
      | intro _ definitionMem declaration owner _ _ _ _ =>
        exact False.elim (missing _ definitionMem (owner.trans declaration.symm))
    | globalArity actual rejected => exact ⟨_, _, .globalArity actual rejected, .completed⟩
    | globalBody actual _ failed =>
      cases BuiltinNamedCalls.instantiation_unique unique frame.instantiated actual
      cases failed with
      | arity rejected => exact ⟨_, _, .globalArity actual rejected, .completed⟩
      | statements _ _ allocated _ => exact False.elim (rawMismatch allocated.length_eq)
      | controlEscape _ _ allocated _ _ => exact False.elim (rawMismatch allocated.length_eq)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageApplicationArity
