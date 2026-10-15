import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedSource

/-! Projected assignment inversion retains each evaluated key, the getter
snapshot, the reached RHS heap and the actual statement suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedInversion
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

inductive Result (program : Program) (registry : Registry) (invocation : Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (rest : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (body : List StatementId) :
    Nat → BodyOutcome → Dynamic.Heap → Prop where
  | rootFault {reason}
      (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
      Result program registry invocation context environment before assignment operator rhs rest test post body
        (Size.stepSize [Size.stepSize []]) (.fault (.semantic reason)) before
  | keysFault {keysSize failure after}
      (ready : ProjectedTarget.RootReady environment before assignment.target)
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
      Result program registry invocation context environment before assignment operator rhs rest test post body
        (Size.stepSize [Size.stepSize [keysSize]]) (.fault failure) after
  | getterFault {keysSize values reason after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) after)
      (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
      Result program registry invocation context environment before assignment operator rhs rest test post body
        (Size.stepSize [Size.stepSize [keysSize]]) (.fault (.semantic reason)) after
  | rhsFault {keysSize childSize values target targetHeap failure after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
      (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
      (child : Size.Expression program registry childSize invocation context environment targetHeap rhs (.fault failure) after) :
      Result program registry invocation context environment before assignment operator rhs rest test post body
        (Size.stepSize [Size.stepSize [keysSize, childSize]]) (.fault failure) after
  | writeFault {keysSize childSize values target targetHeap right reason after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
      (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
      (child : Size.Expression program registry childSize invocation context environment targetHeap rhs (.value right) after)
      (failed : ProjectedTarget.WriteFault operator target right after reason) :
      Result program registry invocation context environment before assignment operator rhs rest test post body
        (Size.stepSize [Size.stepSize [keysSize, childSize]]) (.fault (.semantic reason)) after
  | success {keysSize childSize tailSize values target targetHeap right middle updated written outcome after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
      (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
      (child : Size.Expression program registry childSize invocation context environment targetHeap rhs (.value right) middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
        middle target updated written)
      (next : Trace program registry invocation context environment written rest test post body tailSize outcome after) :
      Result program registry invocation context environment before assignment operator rhs rest test post body
        (Size.stepSize [keysSize, childSize, tailSize]) outcome after

private theorem fault_grade (keys child tail : Nat) :
    Size.stepSize [Size.stepSize [keys, child, tail]] = Size.stepSize [keys, child, Size.stepSize [tail]] := by
  simp [Size.stepSize]
  omega

private theorem loop_grade (keys child tail loop : Nat) :
    Size.stepSize [Size.stepSize [keys, child, tail], loop] = Size.stepSize [keys, child, Size.stepSize [tail, loop]] := by
  simp [Size.stepSize]
  omega

theorem projected_assignment {program : Program} {registry : Registry} {invocation : Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs test : ExpressionId}
    {items post : List ForItemForm} {body : List StatementId} {size : Nat} {outcome : BodyOutcome}
    (projected : assignment.target.projections ≠ [])
    (trace : Trace program registry invocation context environment before
      (.assignValue assignment operator rhs :: items) test post body size outcome after) :
    Result program registry invocation context environment before assignment operator rhs items test post body size outcome after := by
  cases trace with
  | initializerFault initial =>
    cases initial with
    | assignment snapshot _ _ _ | assignmentFailure snapshot _ | assignmentOperands snapshot _ _ _ _ _ _ =>
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
    | unbound empty _ | dangling empty _ _ => exact (projected empty).elim
    | projectedAssignmentRootFault _ failed => exact .rootFault failed
    | projectedAssignmentKeysFault _ ready keys => exact .keysFault ready keys
    | projectedAssignmentGetterFault _ keys failed => exact .getterFault keys failed
    | projectedAssignmentRhsFault _ keys snapshot child => exact .rhsFault keys snapshot child
    | projectedAssignmentWriteFault _ keys snapshot child failed => exact .writeFault keys snapshot child failed
    | projectedAssignment _ keys snapshot child write next =>
      have result := Result.success (test := test) (post := post) (body := body) keys snapshot child write (Trace.initializerFault next)
      simpa only [fault_grade] using result
  | loop initial loop =>
    cases initial with
    | assignment snapshot _ _ _ =>
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
    | projectedAssignment _ keys snapshot child write next =>
      have result := Result.success keys snapshot child write (Trace.loop next loop)
      simpa only [loop_grade] using result

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedInversion
