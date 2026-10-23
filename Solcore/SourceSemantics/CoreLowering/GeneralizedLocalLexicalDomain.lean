import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin

/-! Every native replacement key comes from an actual discovered owner's
quantified variables. This records ownership, without asserting separation
from an unrelated lexical context. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)

theorem domain_owner {source : TypedSource} {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin source localInstance)
    {metavariable : TypeVarId} (member : metavariable ∈ localInstance.substitution.domain) :
    ∃ owner : LocalLambdaInstance, LocalLambdaInstance.LexicalReadOrigin source owner ∧
      metavariable ∈ owner.binding.binder.scheme.quantified := by
  induction origin with
  | @root localInstance binding nodes selected expression present name form matched =>
      refine ⟨localInstance, .root binding nodes selected expression present name form matched, ?_⟩
      exact (SourceSpecialization.matchClosedSchemeInstance?_sound matched).2.2.1 ▸ member
  | @contextual localInstance parent parentOrigin binding nodes selected expression present
      name form child matched cumulative ih =>
      rw [cumulative, Substitution.mem_domain_compose_iff] at member
      rcases member with old | fresh
      · exact ih old
      · refine ⟨localInstance, .contextual parentOrigin binding nodes selected expression
          present name form child matched cumulative, ?_⟩
        exact (SourceSpecialization.matchClosedSchemeInstance?_sound matched).2.2.1 ▸ fresh

theorem packet_domain_owner {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
    {raw : Core.Expr} (packet : Packet inputs candidate raw)
    {metavariable : TypeVarId}
    (member : metavariable ∈ packet.original.emission.prepared.substitution.domain) :
    ∃ owner : LocalLambdaInstance,
      LocalLambdaInstance.LexicalReadOrigin candidate.origin.source owner ∧
      metavariable ∈ owner.binding.binder.scheme.quantified := by
  obtain ⟨_, _, _, substitution, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [substitution] at member
  exact domain_owner (packet_origin packet) member

theorem materialized_domain_owner {compiled : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization compiled mapping world function relation)
    {metavariable : TypeVarId} (member : metavariable ∈ material.code.active.domain) :
    ∃ owner : LocalLambdaInstance,
      LocalLambdaInstance.LexicalReadOrigin material.candidate.origin.source owner ∧
      metavariable ∈ owner.binding.binder.scheme.quantified := by
  rw [material.active] at member
  exact packet_domain_owner material.packet member

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
