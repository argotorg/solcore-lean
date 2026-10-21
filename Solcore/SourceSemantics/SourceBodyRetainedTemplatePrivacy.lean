import Solcore.SourceSemantics.SourceBodyTemplateScope
import Solcore.SourceSemantics.SourceCompiledInitializerOccurrence

/-! Actual generalization receipts preserve an already retained binder's
private variables in newly allocated statement and for-header binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceBodyRetainedTemplatePrivacy
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


private theorem item_binders (item : ForItemForm) :
    item.initializedLetBinders = (forItemInitializedLetBindings item).map (·.binder) := by
  cases item <;> try rfl
  rename_i binder initializer
  cases initializer <;> rfl

private theorem statement_binders (form : StatementForm) :
    form.initializedLetBinders = (statementInitializedLetBindings form).map (·.binder) := by
  cases form <;> try rfl
  · rename_i binder initializer
    cases initializer <;> rfl
  · simp only [StatementForm.initializedLetBinders, statementInitializedLetBindings,
      List.map_append, List.map_flatMap]
    simp only [← item_binders]

private theorem source_binders (source : TypedSource) :
    source.initializedLetBinders = (initializedLetBindings source).map (·.binder) := by
  simp only [TypedSource.initializedLetBinders, initializedLetBindings, List.map_flatMap]
  apply congrArg (fun f : Node → List TypedBinder => source.nodes.flatMap f)
  funext node
  cases node with
  | expression expression => rfl
  | statement statement => exact statement_binders statement.form

private theorem template_origin {source : TypedSource} {binder : TypedBinder}
    (retained : binder ∈ source.initializedLetBinders) {requirement : LocalSchemeRequirement}
    (owned : requirement ∈ binder.schemeRequirements) :
    ∃ initializer, ContainsLocalSchemeTemplate source ⟨binder, initializer, requirement⟩ := by
  rw [source_binders] at retained
  obtain ⟨binding, present, same⟩ := List.mem_map.mp retained
  refine ⟨binding.initializer, List.mem_flatMap.mpr ⟨binding, present, ?_⟩⟩
  exact List.mem_map.mpr ⟨requirement, same ▸ owned, by cases binding; simp_all⟩

private theorem allocated_safe
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} (selected : BodySelection compiled row fuel)
    (templateScoped : ∀ owner, ContainsLocalSchemeTemplate selected.body.finalized.typedSource owner →
      ∀ v ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate,
        v ∈ owner.binder.scheme.quantified)
    {ready result : State} {valueType : Ty} {binder inner : TypedBinder}
    (readyWF : ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends ready.inference.substitution)
    (retained : binder ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (innerRetained : inner ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (resultSub : result.inference.substitution = ready.inference.substitution)
    (bodyEq : binder.scheme.body = ready.resolve valueType)
    (quantifiedSubset : binder.scheme.quantified ⊆ (ready.resolve valueType).freeVariables)
    (bodySafe : Safe inner.scheme.quantified ready valueType) :
    BinderSafe inner.scheme.quantified result binder := by
  have innerCapture := selected.body.resources.local_no_capture _ innerRetained
  have outerCapture := selected.body.resources.local_no_capture _ retained
  have fixed : ∀ q ∈ inner.scheme.quantified,
      selected.body.finalized.substitution.apply (.variable q) = .variable q := by
    intro q quantified
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr
        (innerCapture.quantified_fresh q quantified), Option.getD_none]
  have resultResolve : ∀ type, result.resolve type = ready.resolve type := by
    intro type
    simp only [State.resolve, InferState.resolve, resultSub]
  constructor
  · intro v occurs q image privateMember
    rw [resultResolve] at image
    have inBody := (List.mem_filter.mp occurs).1
    have inResolved := MonomorphicGeneralization.replacement_occurs
      ready.inference.substitution binder.scheme.body inBody image
    rw [bodyEq] at inResolved
    exact safe_resolved readyWF bodySafe q inResolved privateMember
  · intro requirement owned type typeMember v occurs _unbound q image privateMember
    rw [resultResolve] at image
    have finalImage := fixed_variable_occurs_at_final extension (fixed q privateMember) image
    have predicateOccurs := predicate_image typeMember occurs finalImage
    obtain ⟨initializer, contains⟩ := template_origin retained owned
    let owner : LocalSchemeTemplateOwner := ⟨binder, initializer, requirement⟩
    have finalizedContains := FlexibleSubstitution.ContainsLocalSchemeTemplate.applySubstitution
      selected.body.finalized.substitution contains
    rw [← selected.body.resources.source_eq] at finalizedContains
    have restricted : selected.body.finalized.substitution.without binder.scheme.quantified =
        selected.body.finalized.substitution :=
      FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain _ _ outerCapture.quantified_fresh
    have finalizedOccurs : q ∈ TypedTraitResolution.predicateVariables
        (FlexibleSubstitution.applyLocalSchemeTemplateOwner selected.body.finalized.substitution owner).requirement.predicate := by
      change q ∈ TypedTraitResolution.predicateVariables
        (TypedTraitResolution.applySubstitution
          (selected.body.finalized.substitution.without binder.scheme.quantified) requirement.predicate)
      rw [restricted]
      exact predicateOccurs
    have quantified := templateScoped _ finalizedContains q finalizedOccurs
    exact bodySafe q (quantifiedSubset quantified) privateMember

/-- The actual statement receipt needs only its ready state, final extension
and retained binder to preserve an earlier event's private variables. -/
theorem cached_statement_receipt {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    {selected : BodySelection compiled named.specialized fuel}
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {entry : State} {result : Detail.StatementResult}
    (outer : LocalLetRequirementTiming.Receipt childFuel context source entry result)
    (ready : outer.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends outer.ready.inference.substitution)
    (retained : outer.binding.1 ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (inner : TypedBinder)
    (innerRetained : inner ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (bodySafe : Safe inner.scheme.quantified outer.ready outer.value.type) :
    BinderSafe inner.scheme.quantified result.state outer.binding.1 := by
  apply allocated_safe selected (fun _ contains =>
    SourceBodyTemplateScope.cached_template_scoped artifact checked position selected contains)
    ready extension retained innerRetained
    (congrArg InferState.substitution outer.inference_eq)
    (Detail.generalizeValue_scheme_body _ _ _ _) ?_ bodySafe
  exact fun _ quantified => (List.mem_filter.mp quantified).1

/-- Completed-cache preparation supplies the same statement producer for
ordinary functions and implementation methods at their actual cache position. -/
theorem cached_statement {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    {selected : BodySelection compiled named.specialized fuel} {source : Syntax.Statement}
    (outer : BodyInitializerOccurrence selected source) (inner : TypedBinder)
    (innerRetained : inner ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (bodySafe : Safe inner.scheme.quantified outer.receipt.ready outer.receipt.value.type) :
    BinderSafe inner.scheme.quantified outer.result.state outer.receipt.binding.1 :=
  cached_statement_receipt artifact checked position outer.receipt outer.ready
    outer.extension outer.retained inner innerRetained bodySafe

/-- Actual cache preparation also supplies method template scope for headers. -/
theorem cached_header {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    {selected : BodySelection compiled named.specialized fuel}
    {childFuel : Nat} {context : Frontend.SourceInference.Context} {source : Syntax.ForItem}
    {entry : State} {result : ForItemForm × State}
    (outer : LocalHeaderRequirementTiming.Receipt childFuel context source entry result)
    (readyWF : outer.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends outer.ready.inference.substitution)
    (retained : outer.binding.1 ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (inner : TypedBinder)
    (innerRetained : inner ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (bodySafe : Safe inner.scheme.quantified outer.ready outer.value.type) :
    BinderSafe inner.scheme.quantified result.2 outer.binding.1 := by
  apply allocated_safe selected (fun _ contains =>
    SourceBodyTemplateScope.cached_template_scoped artifact checked position selected contains)
    readyWF extension retained innerRetained ?_
    (Detail.generalizeValue_scheme_body _ _ _ _) ?_ bodySafe
  · exact congrArg (fun output : ForItemForm × State => output.2.inference.substitution) outer.completed
  · exact fun _ quantified => (List.mem_filter.mp quantified).1

end Solcore.SourceSemantics.SourceBodyRetainedTemplatePrivacy
