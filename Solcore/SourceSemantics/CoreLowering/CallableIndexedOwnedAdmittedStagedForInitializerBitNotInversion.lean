import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeadContracts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

variable {program : Program} {stages : Registry} {invocation : Scope}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {items post : List ForItemForm}
  {test : ExpressionId} {body : List StatementId} {size : Nat} {outcome : BodyOutcome}

theorem bitNot {assignment : AssignmentResolution}
    (bare : assignment.target.projections = [])
    (trace : Trace program stages invocation context environment before
      (.assignBitNot assignment :: items) test post body size outcome after) :
    (∃ reason, size = Size.stepSize [Size.stepSize []] ∧ outcome = .fault (.semantic reason) ∧
      after = before ∧ Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source
        environment before assignment.target reason before) ∨
    (∃ tailSize target updated written, size = Size.stepSize [tailSize] ∧
      BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated written ∧
      Trace program stages invocation context environment written items test post body tailSize outcome after) := by
  cases trace with
  | initializerFault initial =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.bitNot bare initial with failed | continued
      · obtain ⟨reason, rfl, _, same, sameHeap, failed⟩ := failed
        cases same
        exact .inl ⟨reason, rfl, rfl, sameHeap, failed⟩
      · obtain ⟨tailSize, target, updated, written, rfl, snapshot, write, next⟩ := continued
        exact .inr ⟨_, target, updated, written, rfl, snapshot, write, .initializerFault next⟩
  | loop initial loop =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.bitNot bare initial with failed | continued
      · obtain ⟨_, _, _, same, _⟩ := failed
        cases same
      · obtain ⟨tailSize, target, updated, written, rfl, snapshot, write, next⟩ := continued
        refine .inr ⟨_, target, updated, written, ?_, snapshot, write, .loop next loop⟩
        simp only [Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
