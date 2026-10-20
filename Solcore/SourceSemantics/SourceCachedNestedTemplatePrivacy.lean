import Solcore.SourceSemantics.SourceCachedTemplateScope
import Solcore.SourceSemantics.SourceCompiledInitializerOccurrence

/-! Actual completed-cache template scope closes the requirements of a new outer
binder while preserving an inner binder's private quantified variables, including
ordinary helpers added by executable preparation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCachedNestedTemplatePrivacy
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledLocalFinalization

private theorem predicate_image {substitution : Substitution} {predicate : ProgramPredicate}
    {type : Ty} (member : type ∈ predicate.subject :: predicate.arguments)
    {v q : TypeVarId} (occurs : v ∈ type.freeVariables)
    (image : q ∈ (substitution.apply (.variable v)).freeVariables) :
    q ∈ TypedTraitResolution.predicateVariables
      (TypedTraitResolution.applySubstitution substitution predicate) := by
  have inside := MonomorphicGeneralization.replacement_occurs substitution type occurs image
  rcases List.mem_cons.mp member with rfl | member
  · exact TypedTraitResolution.mem_predicateVariables_iff.mpr (.inl inside)
  · exact TypedTraitResolution.mem_predicateVariables_iff.mpr
      (.inr ⟨substitution.apply type, List.mem_map.mpr ⟨type, member, rfl⟩, inside⟩)

/-- The inner binder's real finalizer check keeps each protected variable
fixed. The actual outer template then excludes those variables from every
live requirement, using the same source owner after finalization. -/
theorem outer_binder_safe {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (origin : CoreLowering.RecursiveNamedPublicSpecializationMeaning.Origin cached.sourceProgram named.specialized)
    {selected : Selected compiled named.specialized fuel} {outerSource innerSource : Syntax.Statement}
    (outer : InitializerOccurrence selected outerSource)
    (inner : InitializerOccurrence selected innerSource)
    (bodySafe : Safe inner.receipt.binding.1.scheme.quantified
      outer.receipt.ready outer.receipt.value.type) :
    BinderSafe inner.receipt.binding.1.scheme.quantified outer.result.state
      outer.receipt.binding.1 := by
  obtain ⟨_, _, _, _, _, _, specialized⟩ := origin
  have bodyEq : outer.receipt.binding.1.scheme.body =
      outer.receipt.ready.resolve outer.receipt.value.type := by
    exact Detail.generalizeValue_scheme_body _ _ _ _
  have innerCapture := selected.body.resources.local_no_capture _ (BodyInitializerOccurrence.retained inner)
  have outerCapture := selected.body.resources.local_no_capture _ (BodyInitializerOccurrence.retained outer)
  have fixed : ∀ q ∈ inner.receipt.binding.1.scheme.quantified,
      selected.body.finalized.substitution.apply (.variable q) = .variable q := by
    intro q quantified
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr
        (innerCapture.quantified_fresh q quantified), Option.getD_none]
  have resultResolve : ∀ type, outer.result.state.resolve type = outer.receipt.ready.resolve type := by
    intro type
    simp only [State.resolve, InferState.resolve, outer.receipt.inference_eq]
  constructor
  · intro v occurs q image privateMember
    rw [resultResolve] at image
    have inBody := (List.mem_filter.mp occurs).1
    have inResolved := MonomorphicGeneralization.replacement_occurs
      outer.receipt.ready.inference.substitution outer.receipt.binding.1.scheme.body inBody image
    rw [bodyEq] at inResolved
    exact safe_resolved outer.ready bodySafe q inResolved privateMember
  · intro requirement owned type typeMember v occurs _unbound q image privateMember
    rw [resultResolve] at image
    have finalImage := fixed_variable_occurs_at_final outer.extension (fixed q privateMember) image
    have predicateOccurs := predicate_image typeMember occurs finalImage
    let owner : LocalSchemeTemplateOwner :=
      ⟨outer.receipt.binding.1, .expression outer.receipt.value.id, requirement⟩
    have initialized : ({binder := outer.receipt.binding.1, initializer := .expression outer.receipt.value.id} :
        InitializedLetBinding) ∈ initializedLetBindings (SourceCompiledGeneralizedSoundness.evidenceSource selected.toBodySelection) :=
      List.mem_flatMap.mpr ⟨_, outer.recorded, List.mem_singleton_self _⟩
    have contains : ContainsLocalSchemeTemplate (SourceCompiledGeneralizedSoundness.evidenceSource selected.toBodySelection) owner :=
      List.mem_flatMap.mpr ⟨_, initialized, List.mem_map.mpr ⟨requirement, owned, rfl⟩⟩
    have finalizedContains := FlexibleSubstitution.ContainsLocalSchemeTemplate.applySubstitution
      selected.body.finalized.substitution contains
    simp only [SourceCompiledGeneralizedSoundness.evidenceSource,
      SourceCompiledGeneralizedSoundness.bodyRoots, Selected.toBodySelection] at finalizedContains
    rw [← selected.body.resources.source_eq] at finalizedContains
    have restricted : selected.body.finalized.substitution.without outer.receipt.binding.1.scheme.quantified =
        selected.body.finalized.substitution :=
      FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain _ _ outerCapture.quantified_fresh
    have finalizedOccurs : q ∈ TypedTraitResolution.predicateVariables
        (FlexibleSubstitution.applyLocalSchemeTemplateOwner selected.body.finalized.substitution owner).requirement.predicate := by
      change q ∈ TypedTraitResolution.predicateVariables
        (TypedTraitResolution.applySubstitution
          (selected.body.finalized.substitution.without outer.receipt.binding.1.scheme.quantified) requirement.predicate)
      rw [restricted]
      exact predicateOccurs
    have quantified := SourceCachedTemplateScope.original_template_scoped
      artifact checked position selected specialized finalizedContains q finalizedOccurs
    have outerOccurs : q ∈ (outer.receipt.ready.resolve outer.receipt.value.type).freeVariables :=
      (List.mem_filter.mp quantified).1
    exact bodySafe q outerOccurs privateMember

end Solcore.SourceSemantics.SourceCachedNestedTemplatePrivacy
