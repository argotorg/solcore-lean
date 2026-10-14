import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeadContracts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

variable {program : Program} {stages : Registry} {invocation : Scope}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before written after : Dynamic.Heap} {items post : List ForItemForm}
  {test : ExpressionId} {body : List StatementId} {size : Nat} {outcome : BodyOutcome}

theorem prepend_bitNot {assignment : AssignmentResolution} {target : Dynamic.ResolvedPlace}
    {updated : Dynamic.Value}
    (snapshot : BareTarget environment before assignment.target target)
    (write : Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
      before target updated written)
    (next : Trace program stages invocation context environment written items test post body size outcome after) :
    Trace program stages invocation context environment before (.assignBitNot assignment :: items) test post body
      (Size.stepSize [size]) outcome after := by
  cases next with
  | initializerFault initial => exact .initializerFault (.bitNot snapshot write initial)
  | loop initial loop =>
      have grade (initial loop : Nat) : Size.stepSize [Size.stepSize [initial], loop] =
          Size.stepSize [Size.stepSize [initial, loop]] := by
        simp [Size.stepSize]
        omega
      simpa only [grade] using (Trace.loop (Size.ForItems.bitNot snapshot write initial) loop)

theorem bitNot_fault {assignment : AssignmentResolution} {reason : Dynamic.SemanticFault}
    (bare : assignment.target.projections = [])
    (failed : Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source
      environment before assignment.target reason before) :
    Trace program stages invocation context environment before (.assignBitNot assignment :: items) test post body
      (Size.stepSize [Size.stepSize []]) (.fault (.semantic reason)) before :=
  .initializerFault (.bitNotFault bare failed)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
