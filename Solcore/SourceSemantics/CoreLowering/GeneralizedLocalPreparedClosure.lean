import Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceClosure
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationInputIdentities
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedAllocation

/-! The evidence preparation factory itself checks real worklist membership.
Consequently every accepted Packet, and every materialized body index built
from it, has closed native replacement ranges. No catalog-membership field is
added to the shared invocation representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalPreparedClosure
open Core Frontend SourceInference TypeSystem
open CallableAncestryProfiles.SourceComposition
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem instance_substitution_eq
    {left right : SourceSpecializationWorklist.LocalLambdaInstance}
    (same : (left == right) = true) : left.substitution = right.substitution := by
  change (left.binding == right.binding && left.substitution == right.substitution) = true at same
  simp only [Bool.and_eq_true] at same
  exact eq_of_beq same.2

/-- Successful preparation validates discovery membership before it constructs
the contextual caller. The checked comparison includes the full substitution. -/
theorem candidate_closed {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared) :
    RangesClosed candidate.origin.substitution := by
  unfold SourceCoreLocalEvidence.prepare at accepted
  obtain ⟨caller, _, accepted⟩ := bind_ok accepted
  split at accepted <;> try contradiction
  obtain ⟨discovered, discoveredAt, accepted⟩ := bind_ok accepted
  have discoveredAt : SourceSpecializationWorklist.localLambdaInstances candidate.origin.source = .ok discovered := by
    cases actual : SourceSpecializationWorklist.localLambdaInstances candidate.origin.source with
    | error error => simp [actual, Except.mapError] at discoveredAt
    | ok values =>
      have same : values = discovered := by simpa only [actual, Except.mapError, Except.ok.injEq] using discoveredAt
      exact congrArg Except.ok same
  split at accepted <;> try contradiction
  have present : discovered.contains candidate.origin.localInstance = true := by assumption
  obtain ⟨actual, member, same⟩ := List.contains_iff_exists_mem_beq.mp present
  have closed := PreparedLocalInstanceClosure.read_origin_closed
    (SourceSpecializationWorklist.localLambdaInstances_read_origin discoveredAt actual member)
  rw [← instance_substitution_eq same] at closed
  exact closed

theorem prepared_closed {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared) :
    RangesClosed prepared.substitution := by
  obtain ⟨_, _, _, substitution, _⟩ := LambdaSourceAlignment.prepared_source accepted
  rw [substitution]
  exact candidate_closed accepted

theorem packet_closed {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
    (packet : Packet inputs candidate raw) : RangesClosed packet.original.emission.prepared.substitution :=
  prepared_closed packet.original.emission.authentic

theorem materialized_closed {compiled : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization compiled mapping world function relation) :
    RangesClosed material.code.active := by
  rw [material.active]
  exact packet_closed material.packet

theorem invocation_closed {compiled : SourceCoreUnifiedCompilation.Compiled}
    {relation : ActualBodyInvocation.BodyRelation}
    (index : ActualBodyInvocation.Index compiled relation) : RangesClosed index.active := by
  cases index with
  | named receipt selected => exact RangesClosed.empty
  | contextual material view => exact materialized_closed material

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalPreparedClosure
