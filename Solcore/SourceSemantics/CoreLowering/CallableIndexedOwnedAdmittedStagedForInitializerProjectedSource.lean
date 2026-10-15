import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

variable {program : Program} {stages : Registry} {invocation : Scope}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before targetHeap middle written after : Dynamic.Heap} {items post : List ForItemForm}
  {test : ExpressionId} {body : List StatementId} {size keysSize childSize : Nat} {outcome : BodyOutcome}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {values : List Dynamic.Value} {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value}
  {reason : Dynamic.SemanticFault} {failure : Failure}

private theorem projected_grade (keys child initial loop : Nat) :
    Size.stepSize [Size.stepSize [keys, child, initial], loop] =
      Size.stepSize [keys, child, Size.stepSize [initial, loop]] := by
  simp [Size.stepSize]
  omega

theorem prepend_projected_assignment
    (projected : assignment.target.projections ≠ [])
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
    (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
    (child : Size.Expression program stages childSize invocation context environment targetHeap rhs (.value right) middle)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated written)
    (next : Trace program stages invocation context environment written items test post body size outcome after) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [keysSize, childSize, size]) outcome after := by
  cases next with
  | initializerFault initial =>
      simpa only [BodyOutcome.restore, Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
        (Trace.initializerFault (Size.ForItems.projectedAssignment projected keys snapshot child write initial))
  | loop initial loop =>
      simpa only [projected_grade] using
        (Trace.loop (Size.ForItems.projectedAssignment projected keys snapshot child write initial) loop)

theorem projected_root_fault (projected : assignment.target.projections ≠ [])
    (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize []]) (.fault (.semantic reason)) before :=
  .initializerFault (.projectedAssignmentRootFault projected failed)

theorem projected_keys_fault (projected : assignment.target.projections ≠ [])
    (ready : ProjectedTarget.RootReady environment before assignment.target)
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize [keysSize]]) (.fault failure) after :=
  .initializerFault (.projectedAssignmentKeysFault projected ready keys)

theorem projected_getter_fault (projected : assignment.target.projections ≠ [])
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.values values) after)
    (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize [keysSize]]) (.fault (.semantic reason)) after :=
  .initializerFault (.projectedAssignmentGetterFault projected keys failed)

theorem projected_rhs_fault (projected : assignment.target.projections ≠ [])
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
    (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
    (child : Size.Expression program stages childSize invocation context environment targetHeap rhs (.fault failure) after) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize [keysSize, childSize]]) (.fault failure) after :=
  .initializerFault (.projectedAssignmentRhsFault projected keys snapshot child)

theorem projected_write_fault (projected : assignment.target.projections ≠ [])
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
    (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
    (child : Size.Expression program stages childSize invocation context environment targetHeap rhs (.value right) after)
    (failed : ProjectedTarget.WriteFault operator target right after reason) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize [keysSize, childSize]]) (.fault (.semantic reason)) after :=
  .initializerFault (.projectedAssignmentWriteFault projected keys snapshot child failed)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
