import Solcore.SourceSemantics.SourceCompiledLocalDomainSeparation
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCachedSources

/-! The accepted contextual factory identifies its original cached body.
The resulting domain exclusion applies to the same Packet and native code. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalDomains
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceCompiledLocalFinalization
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)

private theorem exact_member {plan : Plan}
    {owner : SourceCompilationPlan.Key} {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok row) :
    row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected
  · cases selected
  · next candidate only =>
    cases selected
    have member : row ∈ [row] := by simp
    rw [← only] at member
    exact (List.mem_filter.mp member).1
  · cases selected

/-- The key exclusion is derived from this Packet's own accepted preparation,
the real cache position, and the original body checker. -/
theorem packet_domain_excludes_earlier
    {workspace : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
    {raw : Core.Expr} (packet : Packet inputs candidate raw)
    (indexed : Indexed cached.indexed packet)
    {earlier : InitializedLetBinding}
    (member : earlier ∈ initializedLetBindings candidate.origin.source)
    (before : earlier.binder.id.binderIndex <
      candidate.origin.localInstance.binding.binder.id.binderIndex)
    {q : TypeVarId} (quantified : q ∈ earlier.binder.scheme.quantified) :
    q ∉ packet.original.emission.prepared.substitution.domain := by
  obtain ⟨row, selected, source, substitution, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan] at selected
  obtain ⟨index, named, position, same⟩ :=
    SelectedCompilationCachedSources.row_position cached (exact_member selected)
  obtain ⟨body, _⟩ :=
    SourceBodyTemplateScope.cached_selection_scope artifact checked position
  have sameSource : named.specialized.function.typedBody = candidate.origin.source := by
    rw [same]
    exact source
  have origin : LocalLambdaInstance.LexicalReadOrigin
      named.specialized.function.typedBody candidate.origin.localInstance := by
    rw [sameSource]
    exact GeneralizedLocalLexicalOrigin.packet_origin packet
  have retained : earlier ∈ initializedLetBindings named.specialized.function.typedBody := by
    rwa [sameSource]
  rw [substitution]
  exact body.local_domain_excludes_earlier artifact checked position origin retained before quantified

/-- The native code's active substitution is the same accepted Packet's
substitution, so its domain has the same actual-owner exclusion. -/
theorem materialized_domain_excludes_earlier
    {workspace : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization
      cached mapping world function relation)
    {earlier : InitializedLetBinding}
    (member : earlier ∈ initializedLetBindings material.candidate.origin.source)
    (before : earlier.binder.id.binderIndex <
      material.candidate.origin.localInstance.binding.binder.id.binderIndex)
    {q : TypeVarId} (quantified : q ∈ earlier.binder.scheme.quantified) :
    q ∉ material.code.active.domain := by
  rw [material.active]
  exact packet_domain_excludes_earlier artifact checked material.packet material.indexed
    member before quantified

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalDomains
