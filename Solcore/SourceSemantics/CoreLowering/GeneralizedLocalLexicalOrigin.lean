import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalPreparedClosure
import Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality

/-! Accepted preparation retains real discovery ancestry. This strengthens the
origin evidence of the existing Packet; it does not replace its native code or
claim that every later read has the same lexical context as allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
open Core Frontend SourceInference TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open SourceSpecializationWorklist

-- Reflect the structural comparison used by the worklist, before the
-- callable-principal module installs its decidable comparison.
attribute [local instance 2000] SourceInference.instBEqTypedBinder
deriving instance ReflBEq, LawfulBEq for TypedBinder
deriving instance ReflBEq, LawfulBEq for LocalLambdaBinding
deriving instance ReflBEq, LawfulBEq for LocalLambdaInstance

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

/-- The actual discovery guard compares the complete instance, including all
binder fields and the cumulative substitution. -/
theorem candidate_origin {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared) :
    LocalLambdaInstance.LexicalReadOrigin candidate.origin.source candidate.origin.localInstance := by
  unfold SourceCoreLocalEvidence.prepare at accepted
  obtain ⟨caller, _, accepted⟩ := bind_ok accepted
  split at accepted <;> try contradiction
  obtain ⟨discovered, discoveredAt, accepted⟩ := bind_ok accepted
  have discoveredAt : localLambdaInstances candidate.origin.source = .ok discovered := by
    cases actual : localLambdaInstances candidate.origin.source with
    | error error => simp [actual, Except.mapError] at discoveredAt
    | ok values =>
      have same : values = discovered := by
        simpa only [actual, Except.mapError, Except.ok.injEq] using discoveredAt
      exact congrArg Except.ok same
  split at accepted <;> try contradiction
  have present : discovered.contains candidate.origin.localInstance = true := by assumption
  exact localLambdaInstances_lexical_read_origin discoveredAt _
    (List.contains_iff_mem.mp present)

theorem packet_origin {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
    {raw : Core.Expr} (packet : Packet inputs candidate raw) :
    LocalLambdaInstance.LexicalReadOrigin candidate.origin.source candidate.origin.localInstance :=
  candidate_origin packet.original.emission.authentic

theorem materialized_origin {compiled : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization compiled mapping world function relation) :
    LocalLambdaInstance.LexicalReadOrigin material.candidate.origin.source
      material.candidate.origin.localInstance :=
  packet_origin material.packet

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
