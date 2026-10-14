import Solcore.SourceSemantics.Staging.RecursiveBareBitNot

/-! The actual ordinary unary update is exactly a bare snapshot followed by
its real write. Its failure form retains the same incoming heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

variable {program : Program} {context : Context} {evidence : EvidenceEnvironment}
  {source : TypedSource} {environment : Environment} {before after : Heap}
  {place : PlaceResolution}

theorem bitNot_update_iff {updated : Value} (bare : place.projections = []) :
    SourcePlaceSnapshotUpdate program context evidence source BitNotSnapshot
      environment before place updated after ↔
    ∃ target, BareTarget environment before place target ∧
      ResolvedPlaceWrites (fun _ replacement => BitNotSnapshot target.selected replacement)
        before target updated after := by
  constructor
  · intro executed
    cases executed with
    | intro resolved written =>
      obtain ⟨rfl, snapshot⟩ := BareTarget.of_resolves bare resolved
      exact ⟨_, snapshot, written⟩
  · rintro ⟨target, snapshot, written⟩
    exact .intro (snapshot.resolves _ _ _ _) written

theorem bitNot_fault_iff {reason : SemanticFault} (bare : place.projections = []) :
    SourcePlaceBitNotFaults program context evidence source environment before place reason after ↔
    after = before ∧
      SourcePlaceBitNotFaults program context evidence source environment before place reason before := by
  constructor
  · intro failed
    have same := bitNot_fault_heap bare failed
    exact ⟨same, same ▸ failed⟩
  · rintro ⟨rfl, failed⟩
    exact failed

end Solcore.SourceSemantics.Staging.Recursive
