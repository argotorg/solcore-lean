import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedBitNotSource

/-! Projected unary inversion retains the actual key endpoint and written suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedBitNotInversion
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

inductive Result (program : Program) (registry : Registry) (invocation : Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (assignment : AssignmentResolution) (rest : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (body : List StatementId) :
    Nat → BodyOutcome → Dynamic.Heap → Prop where
  | rootFault {reason}
      (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
      Result program registry invocation context environment before assignment rest test post body
        (Size.stepSize [Size.stepSize []]) (.fault (.semantic reason)) before
  | keysFault {keysSize failure after}
      (ready : ProjectedTarget.RootReady environment before assignment.target)
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
      Result program registry invocation context environment before assignment rest test post body
        (Size.stepSize [Size.stepSize [keysSize]]) (.fault failure) after
  | getterFault {keysSize values reason after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) after)
      (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
      Result program registry invocation context environment before assignment rest test post body
        (Size.stepSize [Size.stepSize [keysSize]]) (.fault (.semantic reason)) after
  | success {keysSize tailSize values target targetHeap updated written outcome after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
      (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        targetHeap target updated written)
      (next : Trace program registry invocation context environment written rest test post body tailSize outcome after) :
      Result program registry invocation context environment before assignment rest test post body
        (Size.stepSize [keysSize, tailSize]) outcome after

private theorem fault_grade (keys tail : Nat) :
    Size.stepSize [Size.stepSize [keys, tail]] = Size.stepSize [keys, Size.stepSize [tail]] := by
  simp [Size.stepSize]
  omega

private theorem loop_grade (keys tail loop : Nat) :
    Size.stepSize [Size.stepSize [keys, tail], loop] = Size.stepSize [keys, Size.stepSize [tail, loop]] := by
  simp [Size.stepSize]
  omega

theorem projected_bitNot {program : Program} {registry : Registry} {invocation : Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {assignment : AssignmentResolution} {test : ExpressionId}
    {items post : List ForItemForm} {body : List StatementId} {size : Nat} {outcome : BodyOutcome}
    (projected : assignment.target.projections ≠ [])
    (trace : Trace program registry invocation context environment before
      (.assignBitNot assignment :: items) test post body size outcome after) :
    Result program registry invocation context environment before assignment items test post body size outcome after := by
  cases trace with
  | initializerFault initial =>
    cases initial with
    | bitNot snapshot _ _ =>
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
    | bitNotFault empty _ => exact (projected empty).elim
    | projectedBitNotRootFault _ failed => exact .rootFault failed
    | projectedBitNotKeysFault _ ready keys => exact .keysFault ready keys
    | projectedBitNotGetterFault _ keys failed => exact .getterFault keys failed
    | projectedBitNot _ keys snapshot write next =>
      have result := Result.success (test := test) (post := post) (body := body) keys snapshot write (Trace.initializerFault next)
      simpa only [fault_grade] using result
  | loop initial loop =>
    cases initial with
    | bitNot snapshot _ _ =>
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
    | projectedBitNot _ keys snapshot write next =>
      have result := Result.success keys snapshot write (Trace.loop next loop)
      simpa only [loop_grade] using result

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedBitNotInversion
