import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

variable {program : Program} {stages : Registry} {invocation : Scope}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before targetHeap written after : Dynamic.Heap} {items post : List ForItemForm}
  {test : ExpressionId} {body : List StatementId} {size keysSize : Nat} {outcome : BodyOutcome}
  {assignment : AssignmentResolution}
  {values : List Dynamic.Value} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
  {reason : Dynamic.SemanticFault} {failure : Failure}

private theorem projected_bitNot_grade (keys initial loop : Nat) :
    Size.stepSize [Size.stepSize [keys, initial], loop] =
      Size.stepSize [keys, Size.stepSize [initial, loop]] := by
  simp [Size.stepSize]
  omega

theorem prepend_projected_bitNot
    (projected : assignment.target.projections ≠ [])
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
    (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
      targetHeap target updated written)
    (next : Trace program stages invocation context environment written items test post body size outcome after) :
    Trace program stages invocation context environment before (.assignBitNot assignment :: items) test post body
      (Size.stepSize [keysSize, size]) outcome after := by
  cases next with
  | initializerFault initial =>
      simpa only [BodyOutcome.restore, Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
        (Trace.initializerFault (Size.ForItems.projectedBitNot projected keys snapshot write initial))
  | loop initial loop =>
      simpa only [projected_bitNot_grade] using
        (Trace.loop (Size.ForItems.projectedBitNot projected keys snapshot write initial) loop)

theorem projected_bitNot_root_fault (projected : assignment.target.projections ≠ [])
    (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
    Trace program stages invocation context environment before (.assignBitNot assignment :: items) test post body
      (Size.stepSize [Size.stepSize []]) (.fault (.semantic reason)) before :=
  .initializerFault (.projectedBitNotRootFault projected failed)

theorem projected_bitNot_keys_fault (projected : assignment.target.projections ≠ [])
    (ready : ProjectedTarget.RootReady environment before assignment.target)
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
    Trace program stages invocation context environment before (.assignBitNot assignment :: items) test post body
      (Size.stepSize [Size.stepSize [keysSize]]) (.fault failure) after :=
  .initializerFault (.projectedBitNotKeysFault projected ready keys)

theorem projected_bitNot_getter_fault (projected : assignment.target.projections ≠ [])
    (keys : Size.Expressions program stages keysSize invocation context environment before
      (ProjectedTarget.keys assignment.target.projections) (.values values) after)
    (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
    Trace program stages invocation context environment before (.assignBitNot assignment :: items) test post body
      (Size.stepSize [Size.stepSize [keysSize]]) (.fault (.semantic reason)) after :=
  .initializerFault (.projectedBitNotGetterFault projected keys failed)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
