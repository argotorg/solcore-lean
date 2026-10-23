import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalDomain

/-! Domain ownership follows the authentic discovery chain. The internal
ordering input concerns only its real contextual reads; the compiled-source
adapter supplies it from initialization and lexical read provenance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)

/-- The next instance is obtained from a read in the actual parent's lexical
body. Keeping that read in the premise prevents unrelated binder orders from
being used to order a discovery chain. -/
def ContextualReadOrder (source : TypedSource) : Prop :=
  ∀ parent, LocalLambdaInstance.LexicalReadOrigin source parent →
    ∀ nodes, localLambdaBodyNodes source parent = .ok nodes →
      ∀ expression, .expression expression ∈ nodes →
        ∀ name target, expression.form = .reference name (.local target) →
          target.binderIndex < parent.binding.binder.id.binderIndex

theorem domain_owner_at_or_after
    {source : TypedSource} {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin source localInstance)
    (ordered : ContextualReadOrder source)
    {metavariable : TypeVarId} (member : metavariable ∈ localInstance.substitution.domain) :
    ∃ owner : LocalLambdaInstance, LocalLambdaInstance.LexicalReadOrigin source owner ∧
      metavariable ∈ owner.binding.binder.scheme.quantified ∧
      localInstance.binding.binder.id.binderIndex ≤ owner.binding.binder.id.binderIndex := by
  induction origin with
  | @root localInstance binding nodes selected expression present name form matched =>
      refine ⟨localInstance, .root binding nodes selected expression present name form matched,
        ?_, Nat.le_refl _⟩
      exact (SourceSpecialization.matchClosedSchemeInstance?_sound matched).2.2.1 ▸ member
  | @contextual localInstance parent parentOrigin binding nodes selected expression present
      name form child matched cumulative ih =>
      rw [cumulative, Substitution.mem_domain_compose_iff] at member
      rcases member with old | fresh
      · obtain ⟨owner, authentic, quantified, afterParent⟩ := ih old
        have beforeParent := ordered parent parentOrigin nodes selected expression present
          name localInstance.binding.binder.id form
        exact ⟨owner, authentic, quantified, Nat.le_trans (Nat.le_of_lt beforeParent) afterParent⟩
      · refine ⟨localInstance, .contextual parentOrigin binding nodes selected expression
          present name form child matched cumulative, ?_, Nat.le_refl _⟩
        exact (SourceSpecialization.matchClosedSchemeInstance?_sound matched).2.2.1 ▸ fresh

theorem packet_domain_owner_at_or_after
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
    {raw : Core.Expr} (packet : Packet inputs candidate raw)
    (ordered : ContextualReadOrder candidate.origin.source)
    {metavariable : TypeVarId}
    (member : metavariable ∈ packet.original.emission.prepared.substitution.domain) :
    ∃ owner : LocalLambdaInstance,
      LocalLambdaInstance.LexicalReadOrigin candidate.origin.source owner ∧
      metavariable ∈ owner.binding.binder.scheme.quantified ∧
      candidate.origin.localInstance.binding.binder.id.binderIndex ≤
        owner.binding.binder.id.binderIndex := by
  obtain ⟨_, _, _, substitution, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [substitution] at member
  exact domain_owner_at_or_after (packet_origin packet) ordered member

theorem materialized_domain_owner_at_or_after
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization compiled mapping world function relation)
    (ordered : ContextualReadOrder material.candidate.origin.source)
    {metavariable : TypeVarId} (member : metavariable ∈ material.code.active.domain) :
    ∃ owner : LocalLambdaInstance,
      LocalLambdaInstance.LexicalReadOrigin material.candidate.origin.source owner ∧
      metavariable ∈ owner.binding.binder.scheme.quantified ∧
      material.candidate.origin.localInstance.binding.binder.id.binderIndex ≤
        owner.binding.binder.id.binderIndex := by
  rw [material.active] at member
  exact packet_domain_owner_at_or_after material.packet ordered member

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalOrigin
