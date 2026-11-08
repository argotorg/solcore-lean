import Solcore.SourceSemantics.Internal.Inference.LetCertificates
import Solcore.SourceSemantics.Internal.Selected.State
import Solcore.SourceSemantics.Internal.Inference.RootedContracts
import Solcore.SourceSemantics.Internal.Inference.ExpressionCalls

/-!
# Generalization barriers

Capture checks and the executable barrier establish privacy at a new generalized declaration, also
under residual substitutions.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedBarrierTransport
/-! Exact generalization under residual substitutions. The ordered frontier
is derived from retained quantifiers and the images of actual blocked variables;
replacement types may retain flexible variables. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem
namespace GeneralizedBarrierTransport

private def mergeVariables (left right : List TypeVarId) : List TypeVarId :=
  right.foldl (fun variables metavariable =>
    if metavariable ∈ variables then variables else variables ++ [metavariable]) left

private theorem filter_mergeVariables (keep : TypeVarId → Bool)
    (left right : List TypeVarId) :
    (mergeVariables left right).filter keep =
      mergeVariables (left.filter keep) (right.filter keep) := by
  induction right generalizing left with
  | nil => simp [mergeVariables]
  | cons head tail ih =>
    change (mergeVariables (if head ∈ left then left else left ++ [head]) tail).filter keep =
      mergeVariables (left.filter keep) ((head :: tail).filter keep)
    rw [ih]
    by_cases kept : keep head
    · by_cases present : head ∈ left
      · simp [mergeVariables, kept, present, List.mem_filter.mpr ⟨present, kept⟩]
      · have absent : head ∉ left.filter keep := by simp [present]
        simp [mergeVariables, kept, present, absent, List.filter_append]
    · by_cases present : head ∈ left
      · simp [mergeVariables, kept, present]
      · simp [mergeVariables, kept, present, List.filter_append]

/-- A pointwise metavariable-image argument preserves the stable order of the
surviving variables, including when substitutions introduce residual variables. -/
private theorem filtered_apply
    (outer : Substitution) (before after : TypeVarId → Bool) (type : Ty)
    (images : ∀ metavariable ∈ type.freeVariables,
      (outer.apply (.variable metavariable)).freeVariables.filter after =
        ([metavariable].filter before)) :
    (outer.apply type).freeVariables.filter after = type.freeVariables.filter before := by
  induction type with
  | «variable» metavariable => exact images metavariable (by simp [Ty.freeVariables])
  | parameter _ => rfl
  | constructor _ => rfl
  | error => rfl
  | proxy _ ih => exact ih images
  | comptime _ ih => exact ih images
  | application left right leftIH rightIH
  | function left right leftIH rightIH
  | product left right leftIH rightIH
  | mapping left right leftIH rightIH =>
    change (mergeVariables (outer.apply left).freeVariables (outer.apply right).freeVariables).filter after =
      (mergeVariables left.freeVariables right.freeVariables).filter before
    rw [filter_mergeVariables, filter_mergeVariables]
    congr 1
    · apply leftIH
      intro metavariable member
      apply images metavariable
      simp_all only [Ty.mem_freeVariables_application_iff, Ty.mem_freeVariables_function_iff,
        Ty.mem_freeVariables_product_iff, Ty.mem_freeVariables_mapping_iff, true_or]
    · apply rightIH
      intro metavariable member
      apply images metavariable
      simp_all only [Ty.mem_freeVariables_application_iff, Ty.mem_freeVariables_function_iff,
        Ty.mem_freeVariables_product_iff, Ty.mem_freeVariables_mapping_iff, or_true]

end GeneralizedBarrierTransport

/-- The actual generalized scheme and final capture check reduce exact
frontier transport to two provenance facts: images of old blockers stay
blocked, and this binder's private quantifiers do not enter the final barrier. -/
theorem generalizationBarrierTransport_of_blockedImages
    {state : State} {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    {outer : Substitution} {target : SourceSemantics.Context}
    {binder : TypedBinder} {exemptRequirements : List RequirementId}
    (schemeEq : binder.scheme =
      (Detail.generalizeValue state locals requirementStart valueType).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder)
    (blockedImages : ∀ metavariable ∈ valueType.freeVariables,
      metavariable ∈ Detail.generalizeValueBlockedVariables state locals requirementStart →
      ∀ replacement ∈ (outer.apply (.variable metavariable)).freeVariables,
        replacement ∈ GeneralizationBlockedVariablesExcept target exemptRequirements)
    (privateQuantifiers : ∀ metavariable ∈ binder.scheme.quantified,
      metavariable ∉ GeneralizationBlockedVariablesExcept target exemptRequirements) :
    GeneralizationBarrierTransport state locals requirementStart valueType
      outer target exemptRequirements := by
  apply GeneralizedBarrierTransport.filtered_apply
  intro metavariable occurs
  by_cases blocked : metavariable ∈ Detail.generalizeValueBlockedVariables state locals requirementStart
  · have empty : (outer.apply (.variable metavariable)).freeVariables.filter
        (fun replacement => !(GeneralizationBlockedVariablesExcept target exemptRequirements).contains replacement) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro replacement member
      simp [blockedImages metavariable occurs blocked replacement member]
    simpa [blocked] using empty
  · have quantified : metavariable ∈ binder.scheme.quantified := by
      rw [schemeEq, Detail.generalizeValue_scheme_quantified]
      exact List.mem_filter.mpr ⟨occurs, by simp [blocked]⟩
    have found : outer.lookup? metavariable = none :=
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr
        (noCapture.quantified_fresh metavariable quantified)
    simp [Substitution.apply, found, Ty.freeVariables, blocked,
      privateQuantifiers metavariable quantified]

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedBarrierReceipts
/-! Actual lexical schemes and solved ledger rows supply the forward half of
final generalization. Inference substitutions may retain flexible variables. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem
namespace GeneralizedBarrierTransport

private instance : LawfulBEq RequirementId where
  eq_of_beq := by
    intro a b same
    cases a; cases b
    simp_all [BEq.beq, instBEqRequirementId.beq]
  rfl := by intro a; cases a; simp [BEq.beq, instBEqRequirementId.beq]

private theorem eq_of_mem_of_nodup_map
    {α β : Type} {items : List α} {project : α → β}
    (unique : (items.map project).Nodup)
    {left right : α} (leftMember : left ∈ items)
    (rightMember : right ∈ items)
    (projectEq : project left = project right) : left = right := by
  induction items generalizing left right with
  | nil => simp at leftMember
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases unique with ⟨headFresh, tailUnique⟩
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · rfl
        · exact False.elim (headFresh (projectEq ▸
            List.mem_map_of_mem rightMember))
      · rcases rightMember with rfl | rightMember
        · exact False.elim (headFresh (projectEq.symm ▸
            List.mem_map_of_mem leftMember))
        · exact induction tailUnique leftMember rightMember projectEq

private theorem restricted_extension {outer inner : Substitution}
    (extension : outer.SemanticallyExtends inner) (removed : List TypeVarId) :
    outer.SemanticallyExtends (inner.without removed) := by
  intro type
  induction type with
  | «variable» v =>
    by_cases member : v ∈ removed
    · simp only [Substitution.apply, Substitution.lookup?_without_of_mem inner member, Option.getD_none]
    · simpa only [Substitution.apply,
        FlexibleSubstitution.Substitution.lookup?_without_of_not_mem inner member] using extension (.variable v)
  | parameter _ => rfl
  | constructor _ => rfl
  | error => rfl
  | proxy _ ih | comptime _ ih => simp only [Substitution.apply, ih]
  | application _ _ left right | function _ _ left right
  | product _ _ left right | mapping _ _ left right => simp only [Substitution.apply, left, right]

/-- A variable free in a genuinely resolved older scheme keeps every final
replacement outside that scheme's quantified variables. The actual finalizer
capture check is used on the original binder, not assumed for a rebuilt one. -/
theorem scheme_replacement_occurs {inner outer : Substitution} {binder : TypedBinder}
    (extension : outer.SemanticallyExtends inner)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder)
    {original replacement : TypeVarId}
    (occurs : original ∈ (binder.scheme.apply inner).freeVariables)
    (replaced : replacement ∈ (outer.apply (.variable original)).freeVariables) :
    replacement ∈ (binder.scheme.apply outer).freeVariables := by
  obtain ⟨inBody, outside⟩ := List.mem_filter.mp occurs
  have outside : original ∉ binder.scheme.quantified := by
    intro member
    simp [member] at outside
  have present := MonomorphicGeneralization.replacement_occurs outer
    ((inner.without binder.scheme.quantified).apply binder.scheme.body) inBody replaced
  rw [restricted_extension extension binder.scheme.quantified binder.scheme.body] at present
  have restricted : outer.without binder.scheme.quantified = outer :=
    FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain outer binder.scheme.quantified noCapture.quantified_fresh
  have notCaptured : replacement ∉ binder.scheme.quantified := by
    obtain ⟨source, sourceMember, sourceImage⟩ := ProtectedVariables.apply_variable_origin
      (inner.without binder.scheme.quantified) binder.scheme.body original inBody
    have sourceOutside : source ∉ binder.scheme.quantified := by
      intro quantified
      have same : original = source := by
        simpa only [Substitution.apply, Substitution.lookup?_without_of_mem inner quantified,
          Option.getD_none, Ty.freeVariables, List.mem_singleton] using sourceImage
      exact outside (same ▸ quantified)
    have finalImage := MonomorphicGeneralization.replacement_occurs outer
      ((inner.without binder.scheme.quantified).apply (.variable source)) sourceImage replaced
    have imageEq : (inner.without binder.scheme.quantified).apply (.variable source) = inner.apply (.variable source) := by
      simp only [Substitution.apply,
        FlexibleSubstitution.Substitution.lookup?_without_of_not_mem inner sourceOutside]
    rw [imageEq, extension] at finalImage
    cases found : outer.lookup? source with
    | none =>
      have same : replacement = source := by
        simpa only [Substitution.apply, found, Option.getD_none, Ty.freeVariables, List.mem_singleton] using finalImage
      exact same ▸ sourceOutside
    | some type =>
      have member : replacement ∈ type.freeVariables := by simpa only [Substitution.apply, found, Option.getD_some] using finalImage
      exact noCapture.body_range source sourceMember type found replacement member
  unfold Scheme.freeVariables Scheme.apply
  rw [restricted]
  apply List.mem_filter.mpr
  exact ⟨present, by simp [notCaptured]⟩

/-- A blocking row cannot also be a template of this same generalized binder:
template dependency and unique real requirement identities would place one of
its quantified variables back in the executable barrier. -/
theorem blocking_not_template {state : State} {locals : Environment} {cutoff : Nat} {type : Ty}
    (wellFormed : state.RequirementsWellFormed) {row : Requirement}
    (blocked : row ∈ Detail.generalizeValueBlockingRequirements state cutoff) :
    row.id ∉ (Detail.generalizeValue state locals cutoff type).requirements.map LocalSchemeRequirement.templateRequirement := by
  intro exempt
  obtain ⟨template, member, idEq⟩ := List.mem_map.mp exempt
  obtain ⟨raw, rawMember, rawId, predicateEq⟩ := Detail.generalizeValue_requirement_source state locals cutoff type template member
  have rowMember : row ∈ state.requirements := by
    rcases (Detail.mem_generalizeValueBlockingRequirements_iff _ _ _).mp blocked with old | ⟨new,_⟩
    · exact List.mem_of_mem_take old
    · exact List.mem_of_mem_drop new
  have ids : (state.requirements.map (fun requirement => requirement.id.index)).Nodup := by
    rw [wellFormed]
    exact List.nodup_range
  have same : raw = row := eq_of_mem_of_nodup_map ids rawMember rowMember (congrArg RequirementId.index (rawId.trans idEq))
  subst raw
  obtain ⟨v, quantified, occurs⟩ := Detail.generalizeValue_requirement_depends_on_quantified state locals cutoff type template member
  have notBlocked : v ∉ Detail.generalizeValueBlockedVariables state locals cutoff := by
    have selected := (List.mem_filter.mp quantified).2
    simpa using selected
  apply notBlocked
  apply (Detail.mem_generalizeValueBlockedVariables_iff _ _ _ _).mpr
  exact .inr ⟨row,blocked,predicateEq ▸ occurs⟩


private theorem solved_row {context : Frontend.SourceInference.Context} {state : State}
    {requirements : List Requirement} {solved : List SolvedRequirement}
    (rows : Forall₂ (fun requirement row => row.id = requirement.id ∧
      row.predicate = Detail.applyPredicate state requirement.predicate ∧
      Detail.solveRequirementEvidence context state requirement = .ok row.evidence) requirements solved)
    {requirement : Requirement} (member : requirement ∈ requirements) :
    ∃ row ∈ solved, row.id = requirement.id ∧ row.predicate = Detail.applyPredicate state requirement.predicate := by
  induction rows with
  | nil => cases member
  | @cons head row tail rows relation rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨row,List.mem_cons_self,relation.1,relation.2.1⟩
    · obtain ⟨selected,present,same⟩ := ih member
      exact ⟨selected,List.mem_cons_of_mem _ present,same⟩

/-- Actual resolved lexical binders and the final solver retain every image
of this initializer's blocking variables. Only this binder's actual template
identities are exempted from the semantic ledger. -/
theorem blocked_images_from_finalizer
    {wholeContext : Frontend.SourceInference.Context} {wholeReturn : Ty}
    {evidenceState state : State} {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {target : SourceSemantics.Context} {cutoff : Nat} {valueType : Ty}
    (wellFormed : state.RequirementsWellFormed)
    (aligned : LocalEnvironmentAligned state finalized.substitution target)
    (origins : ActiveBinderCaptureOrigins state (evidenceState.toTypedSource roots))
    (requirements : state.requirements ⊆ evidenceState.requirements)
    (extension : finalized.substitution.SemanticallyExtends state.inference.substitution)
    (solvedEq : target.solvedRequirements = finalized.solvedRequirements) :
    let locals := state.binderEnvironment.apply state.inference.substitution
    let templates := (Detail.generalizeValue state locals cutoff valueType).requirements.map LocalSchemeRequirement.templateRequirement
    ∀ original ∈ Detail.generalizeValueBlockedVariables state locals cutoff,
      ∀ replacement ∈ (finalized.substitution.apply (.variable original)).freeVariables,
        replacement ∈ GeneralizationBlockedVariablesExcept target templates := by
  dsimp only
  intro original blocked replacement replaced
  rcases (Detail.mem_generalizeValueBlockedVariables_iff _ _ _ _).mp blocked with
    ⟨entry,member,occurs⟩ | ⟨requirement,member,occurs⟩
  · have mapped : entry ∈ state.localBinders.map (fun binder =>
        (binder.name,binder.scheme.apply state.inference.substitution)) := by
      simpa only [State.binderEnvironment,Environment.apply,List.map_map,Function.comp_def] using member
    obtain ⟨binder,binderMember,same⟩ := List.mem_map.mp mapped
    subst entry
    have noCapture : Detail.LocalBinderInstantiationNoCapture finalized.substitution binder := by
      rcases origins.origin binder binderMember with monomorphic | initialized
      · exact .of_quantified_eq_nil monomorphic
      · exact resources.local_no_capture binder initialized
    have finalMember := scheme_replacement_occurs extension noCapture occurs replaced
    have present : (binder.id,binder.scheme.apply finalized.substitution) ∈ target.locals := by
      apply aligned.locals_perm.mem_iff.mp
      exact List.mem_map.mpr ⟨binder,binderMember,by simp only [FlexibleSubstitution.applyTypedBinder_scheme]⟩
    exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr
      (List.mem_flatMap.mpr ⟨(binder.id,binder.scheme.apply finalized.substitution),present,finalMember⟩))))
  · have inState : requirement ∈ state.requirements := by
      rcases (Detail.mem_generalizeValueBlockingRequirements_iff _ _ _).mp member with old | ⟨new,_⟩
      · exact List.mem_of_mem_take old
      · exact List.mem_of_mem_drop new
    have inFinal : requirement ∈ resources.finalState.requirements := by
      rw [resources.requirements_eq]
      exact requirements inState
    obtain ⟨row,rowMember,rowId,predicateEq⟩ := solved_row (solveRequirements_corresponds resources.solve_success) inFinal
    have rowOccurs := MonomorphicGeneralization.predicate_replacement_occurs finalized.substitution
      (Detail.applyPredicate state requirement.predicate) occurs replaced
    rw [Detail.applyPredicate,TypedTraitResolution.applySubstitution_semanticallyExtends extension] at rowOccurs
    have finalOccurs : replacement ∈ TypedTraitResolution.predicateVariables row.predicate := by
      rw [predicateEq,Detail.applyPredicate,← resources.substitution_eq]
      exact rowOccurs
    apply List.mem_append.mpr
    apply Or.inr
    apply List.mem_flatMap.mpr
    refine ⟨row,List.mem_filter.mpr ⟨?_,?_⟩,finalOccurs⟩
    · simpa only [solvedEq] using rowMember
    · have absent := blocking_not_template (locals := state.binderEnvironment.apply state.inference.substitution)
        (type := valueType) wellFormed member
      rw [rowId]
      simp [absent]


/-- The retained finalizer and actual lexical environment discharge the
forward barrier obligation. Only the backwards privacy statement remains for
the mutually recursive inference continuation to supply. -/
theorem barrier_from_finalizer
    {wholeContext : Frontend.SourceInference.Context} {wholeReturn : Ty}
    {evidenceState state : State} {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {target : SourceSemantics.Context} {cutoff : Nat} {valueType : Ty} {binder : TypedBinder}
    (wellFormed : state.RequirementsWellFormed)
    (aligned : LocalEnvironmentAligned state finalized.substitution target)
    (origins : ActiveBinderCaptureOrigins state (evidenceState.toTypedSource roots))
    (requirements : state.requirements ⊆ evidenceState.requirements)
    (extension : finalized.substitution.SemanticallyExtends state.inference.substitution)
    (solvedEq : target.solvedRequirements = finalized.solvedRequirements)
    (retained : binder ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (schemeEq : binder.scheme = (Detail.generalizeValue state
      (state.binderEnvironment.apply state.inference.substitution) cutoff valueType).scheme)
    (requirementsEq : binder.schemeRequirements = (Detail.generalizeValue state
      (state.binderEnvironment.apply state.inference.substitution) cutoff valueType).requirements)
    (privateQuantifiers : ∀ v ∈ binder.scheme.quantified,
      v ∉ GeneralizationBlockedVariablesExcept target
        (localSchemeTemplateIds (binder.applySubstitution finalized.substitution))) :
    GeneralizationBarrierTransport state (state.binderEnvironment.apply state.inference.substitution)
      cutoff valueType finalized.substitution target
        (localSchemeTemplateIds (binder.applySubstitution finalized.substitution)) := by
  have templates : localSchemeTemplateIds (binder.applySubstitution finalized.substitution) =
      (Detail.generalizeValue state (state.binderEnvironment.apply state.inference.substitution)
        cutoff valueType).requirements.map LocalSchemeRequirement.templateRequirement := by
    simp only [localSchemeTemplateIds,FlexibleSubstitution.applyTypedBinder_schemeRequirements,
      List.map_map,Function.comp_def,FlexibleSubstitution.applyLocalSchemeRequirement_templateRequirement,requirementsEq]
  apply generalizationBarrierTransport_of_blockedImages schemeEq (resources.local_no_capture binder retained) ?_ privateQuantifiers
  intro v _ blocked replacement replaced
  rw [templates]
  exact blocked_images_from_finalizer resources wellFormed aligned origins requirements extension solvedEq v blocked replacement replaced

end GeneralizedBarrierTransport
end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedInitializerContext
/-! Entering a retained generalized initializer enlarges its lexical type and
predicate scopes. The caller's local typing invariant remains available at
that exact child boundary, including already generalized local bindings. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem

namespace GeneralizedInitializerContext

private structure Expansion (source target : SourceSemantics.Context) : Prop where
  signatures : target.signatures = source.signatures
  parameters : target.typeParameters = source.typeParameters
  declaration : target.currentDeclaration = source.currentDeclaration
  variables : source.typeVariables ⊆ target.typeVariables
  residual : target.residualTypeVariables = source.residualTypeVariables
  solved : target.solvedRequirements = source.solvedRequirements

private theorem Expansion.admissibleVariables {source target : SourceSemantics.Context}
    (expanded : Expansion source target) (type : Ty) :
    admissibleTypeVariables source type ⊆ admissibleTypeVariables target type := by
  intro metavariable member
  simp only [admissibleTypeVariables, expanded.residual, List.mem_append] at member ⊢
  exact member.imp (fun proof => expanded.variables proof) id

private theorem Expansion.admissible {source target : SourceSemantics.Context}
    (expanded : Expansion source target) {type : Ty}
    (formed : TypeAdmissible source type) : TypeAdmissible target type := by
  refine ⟨StructuralSubstitution.TypeParameterBindersWellFormed.transportContext
    expanded.parameters expanded.declaration formed.binders, ?_⟩
  exact TypeWellScoped.weakenTo (fun _ member => expanded.admissibleVariables type member)
    (StructuralSubstitution.TypeWellScoped.transportContext expanded.signatures
      expanded.parameters expanded.declaration formed.typeWellScoped)

private theorem Expansion.scheme {source target : SourceSemantics.Context}
    (expanded : Expansion source target) {scheme : Scheme}
    (formed : SchemeWellFormed source scheme) : SchemeWellFormed target scheme := by
  refine ⟨StructuralSubstitution.TypeParameterBindersWellFormed.transportContext
    expanded.parameters expanded.declaration formed.binders, formed.quantified_nodup, ?_⟩
  apply TypeWellScoped.weakenTo ?_
    (StructuralSubstitution.TypeWellScoped.transportContext expanded.signatures
      expanded.parameters expanded.declaration formed.body)
  intro metavariable member
  simp only [List.mem_append] at member ⊢
  exact member.imp (fun proof => expanded.admissibleVariables scheme.body proof) id

private theorem Expansion.predicate {source target : SourceSemantics.Context}
    (expanded : Expansion source target) {predicate : ProgramPredicate}
    (formed : PredicateAdmissible source predicate) : PredicateAdmissible target predicate := by
  refine ⟨expanded.admissible formed.subject,
    fun argument member => expanded.admissible (formed.arguments argument member), ?_⟩
  simpa only [expanded.signatures] using formed.trait

private theorem Expansion.initializer {source target : SourceSemantics.Context}
    (expanded : Expansion source target) (binder : TypedBinder) :
    Expansion (localSchemeInitializerContext source binder)
      (localSchemeInitializerContext target binder) := by
  refine ⟨expanded.signatures, expanded.parameters, expanded.declaration, ?_,
    expanded.residual, expanded.solved⟩
  intro metavariable member
  change metavariable ∈ source.typeVariables ++ binder.scheme.quantified at member
  change metavariable ∈ target.typeVariables ++ binder.scheme.quantified
  exact List.mem_append.mpr ((List.mem_append.mp member).imp (fun proof => expanded.variables proof) id)

private theorem Expansion.requirements {source target : SourceSemantics.Context}
    (expanded : Expansion source target) {binder : TypedBinder}
    (formed : LocalSchemeRequirementsWellFormed source binder) :
    LocalSchemeRequirementsWellFormed target binder := by
  refine ⟨formed.ids_unique, ?_⟩
  intro requirement member
  have entry := formed.entries requirement member
  refine ⟨(expanded.initializer binder).predicate entry.predicate,
    entry.depends_on_quantified, ?_⟩
  simpa only [expanded.solved] using entry.template

private theorem initializerExpansion (context : SourceSemantics.Context) (binder : TypedBinder) :
    Expansion context (localSchemeInitializerContext context binder) := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl⟩
  intro metavariable member
  exact List.mem_append_left _ member

end GeneralizedInitializerContext

theorem ActiveLocalContextInvariant.generalizedInitializer
    {state : State} {substitution : Substitution} {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant state substitution context) (binder : TypedBinder) :
    ActiveLocalContextInvariant state substitution (localSchemeInitializerContext context binder) := by
  have expanded := GeneralizedInitializerContext.initializerExpansion context binder
  exact ⟨⟨invariant.aligned.ids_nodup, invariant.aligned.locals_perm, invariant.aligned.requirements_perm⟩, {
    schemes := fun candidate member => expanded.scheme (invariant.formation.schemes candidate member)
    requirements := fun candidate member => expanded.requirements (invariant.formation.requirements candidate member)
  }⟩

theorem RecursiveExpressionInvariant.generalizedInitializer
    {wholeContext : Frontend.SourceInference.Context} {finalized : Frontend.SourceInference.Result}
    {state : State} {context : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant wholeContext finalized state context) (binder : TypedBinder) :
    RecursiveExpressionInvariant wholeContext finalized state (localSchemeInitializerContext context binder) := by
  exact {
    invariant with
    active := invariant.active.generalizedInitializer binder
    assumptionsMono := fun _ member => List.mem_append_left _ (invariant.assumptionsMono member)
  }

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedPrivacyBoundary
/-! The actual finalizer capture checks and executable generalization barrier
establish privacy at a new generalized declaration. Older scheme quantifiers
need not be assumed disjoint from the new ones. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem
namespace ProtectedVariables

/-- A variable which the final substitution leaves fixed cannot disappear
between the current inference state and that final substitution. -/
theorem fixed_variable_occurs_at_final
    {inner outer : Substitution} (extension : outer.SemanticallyExtends inner)
    {type : Ty} {v : TypeVarId}
    (fixed : outer.apply (.variable v) = .variable v)
    (occurs : v ∈ (inner.apply type).freeVariables) :
    v ∈ (outer.apply type).freeVariables := by
  have replacement : v ∈ (outer.apply (.variable v)).freeVariables := by
    simp only [fixed, Ty.freeVariables, List.mem_singleton]
  have transported := MonomorphicGeneralization.replacement_occurs outer
    (inner.apply type) occurs replacement
  rwa [extension] at transported

/-- An older binder's actual capture check excludes its own quantified
variables from every live unquantified source variable. -/
theorem safe_from_final_range
    {state : State} {outer : Substitution} {protectedVars : List TypeVarId}
    {type : Ty} {v : TypeVarId}
    (extension : outer.SemanticallyExtends state.inference.substitution)
    (fixed : ∀ q ∈ protectedVars, outer.apply (.variable q) = .variable q)
    (range : outer.RangeAvoidsVariablesOn protectedVars type)
    (occurs : v ∈ type.freeVariables) (outside : v ∉ protectedVars) :
    Safe protectedVars state (.variable v) := by
  intro q image member
  have finalImage := fixed_variable_occurs_at_final extension (fixed q member) image
  cases found : outer.lookup? v with
  | none =>
    have same : q = v := by
      simpa only [Substitution.apply, found, Option.getD_none,
        Ty.freeVariables, List.mem_singleton] using finalImage
    exact outside (same ▸ member)
  | some replacement =>
    have present : q ∈ replacement.freeVariables := by
      simpa only [Substitution.apply, found, Option.getD_some] using finalImage
    exact range v occurs replacement found q present member

/-- If a protected variable is free in the current image of an older scheme,
the actual executable barrier blocks it. If it is bound by that scheme, the
actual finalizer capture check excludes it instead. -/
theorem generalized_live_body_private
    {state : State} {outer : Substitution} {cutoff : Nat} {type : Ty}
    {binder : TypedBinder}
    (member : binder ∈ state.localBinders)
    (extension : outer.SemanticallyExtends state.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder)
    (fixed : ∀ q ∈ (Detail.generalizeValue state
        (state.binderEnvironment.apply state.inference.substitution) cutoff type).scheme.quantified,
      outer.apply (.variable q) = .variable q) :
    ∀ v ∈ binder.scheme.freeVariables,
      Safe (Detail.generalizeValue state
        (state.binderEnvironment.apply state.inference.substitution) cutoff type).scheme.quantified
        state (.variable v) := by
  intro v occurs q image quantified
  obtain ⟨inBody, outsideBool⟩ := List.mem_filter.mp occurs
  have outside : v ∉ binder.scheme.quantified := by simpa using outsideBool
  by_cases bound : q ∈ binder.scheme.quantified
  · have finalImage := fixed_variable_occurs_at_final extension (fixed q quantified) image
    cases found : outer.lookup? v with
    | none =>
      have same : q = v := by
        simpa only [Substitution.apply, found, Option.getD_none,
          Ty.freeVariables, List.mem_singleton] using finalImage
      exact outside (same ▸ bound)
    | some replacement =>
      have present : q ∈ replacement.freeVariables := by
        simpa only [Substitution.apply, found, Option.getD_some] using finalImage
      exact noCapture.body_range v inBody replacement found q present bound
  · have restrictedImage :
        q ∈ ((state.inference.substitution.without binder.scheme.quantified).apply
          (.variable v)).freeVariables := by
      simpa only [State.resolve, InferState.resolve, Substitution.apply,
        FlexibleSubstitution.Substitution.lookup?_without_of_not_mem
          state.inference.substitution outside] using image
    have bodyImage := MonomorphicGeneralization.replacement_occurs
      (state.inference.substitution.without binder.scheme.quantified) binder.scheme.body
      inBody restrictedImage
    have free : q ∈ (binder.scheme.apply state.inference.substitution).freeVariables := by
      apply List.mem_filter.mpr
      exact ⟨bodyImage, by simp [bound]⟩
    have blocked : q ∈ Detail.generalizeValueBlockedVariables state
        (state.binderEnvironment.apply state.inference.substitution) cutoff := by
      apply (Detail.mem_generalizeValueBlockedVariables_iff _ _ _ _).mpr
      apply Or.inl
      refine ⟨(binder.name, binder.scheme.apply state.inference.substitution), ?_, free⟩
      simp only [State.binderEnvironment, Environment.apply, List.map_map, Function.comp_def]
      exact List.mem_map.mpr ⟨binder, member, rfl⟩
    have notBlocked := (List.mem_filter.mp quantified).2
    simp [blocked] at notBlocked

/-- The exact requirement rows behind an older live binder precede the new
initializer cutoff. Predicates are compared after actual current resolution. -/
def BinderTemplatesBefore (state : State) (cutoff : Nat) (binder : TypedBinder) : Prop :=
  ∀ requirement ∈ binder.schemeRequirements,
    ∃ raw ∈ state.requirements.take cutoff,
      Detail.applyPredicate state requirement.predicate = Detail.applyPredicate state raw.predicate

theorem generalized_live_requirements_private
    {state : State} {cutoff : Nat} {type : Ty} {binder : TypedBinder}
    (backed : BinderTemplatesBefore state cutoff binder) :
    ∀ requirement ∈ binder.schemeRequirements,
      ∀ sourceType ∈ requirement.predicate.subject :: requirement.predicate.arguments,
        ∀ v ∈ sourceType.freeVariables,
          Safe (Detail.generalizeValue state
            (state.binderEnvironment.apply state.inference.substitution) cutoff type).scheme.quantified
            state (.variable v) := by
  intro requirement member sourceType typeMember v occurs q image quantified
  obtain ⟨raw, rawMember, same⟩ := backed requirement member
  have inPredicate : v ∈ TypedTraitResolution.predicateVariables requirement.predicate := by
    apply TypedTraitResolution.mem_predicateVariables_iff.mpr
    rcases List.mem_cons.mp typeMember with rfl | argumentMember
    · exact .inl occurs
    · exact .inr ⟨sourceType, argumentMember, occurs⟩
  have resolved := MonomorphicGeneralization.predicate_replacement_occurs
    state.inference.substitution requirement.predicate inPredicate image
  change q ∈ TypedTraitResolution.predicateVariables
    (Detail.applyPredicate state requirement.predicate) at resolved
  rw [same] at resolved
  have blocked : q ∈ Detail.generalizeValueBlockedVariables state
      (state.binderEnvironment.apply state.inference.substitution) cutoff := by
    apply (Detail.mem_generalizeValueBlockedVariables_iff _ _ _ _).mpr
    exact .inr ⟨raw,
      (Detail.mem_generalizeValueBlockingRequirements_iff _ _ _).mpr (.inl rawMember), resolved⟩
  have notBlocked := (List.mem_filter.mp quantified).2
  simp [blocked] at notBlocked

/-- The older live stack is private for the exact variables chosen by the
actual generalizer. Capture checks handle older bound variables; the genuine
pre-initializer ledger handles retained qualified templates. -/
theorem generalized_live_private
    {state : State} {outer : Substitution} {cutoff : Nat} {type : Ty}
    (extension : outer.SemanticallyExtends state.inference.substitution)
    (noCapture : ∀ binder ∈ state.localBinders,
      Detail.LocalBinderInstantiationNoCapture outer binder)
    (fixed : ∀ q ∈ (Detail.generalizeValue state
        (state.binderEnvironment.apply state.inference.substitution) cutoff type).scheme.quantified,
      outer.apply (.variable q) = .variable q)
    (backed : ∀ binder ∈ state.localBinders, BinderTemplatesBefore state cutoff binder) :
    LiveBindersSafe (Detail.generalizeValue state
      (state.binderEnvironment.apply state.inference.substitution) cutoff type).scheme.quantified state := by
  intro binder member
  exact ⟨generalized_live_body_private member extension (noCapture binder member) fixed,
    fun requirement present sourceType typeMember v occurs _ =>
      generalized_live_requirements_private (backed binder member)
        requirement present sourceType typeMember v occurs⟩

/-- A newly retained binder is private for its own quantified variables by
the actual finalizer check, including all its qualified template types. -/
theorem binder_private_own_quantifiers
    {state : State} {outer : Substitution} {binder : TypedBinder}
    (extension : outer.SemanticallyExtends state.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder) :
    BinderSafe binder.scheme.quantified state binder := by
  have fixed : ∀ q ∈ binder.scheme.quantified, outer.apply (.variable q) = .variable q := by
    intro q member
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain outer q).mpr
        (noCapture.quantified_fresh q member),
      Option.getD_none]
  constructor
  · intro v member
    obtain ⟨occurs, outside⟩ := List.mem_filter.mp member
    exact safe_from_final_range extension fixed noCapture.body_range occurs (by simpa using outside)
  · intro requirement member sourceType typeMember v occurs outside
    have range : outer.RangeAvoidsVariablesOn binder.scheme.quantified sourceType := by
      rcases List.mem_cons.mp typeMember with rfl | argumentMember
      · exact (noCapture.requirement_ranges requirement member).1
      · exact (noCapture.requirement_ranges requirement member).2 sourceType argumentMember
    exact safe_from_final_range extension fixed range occurs outside

/-- Real retained binder occurrences supply every capture check used above.
Only the current old-template provenance is required from the inference
traversal; no initial privacy or quantifier-disjointness law is assumed. -/
theorem generalized_live_from_finalizer
    {wholeContext : Frontend.SourceInference.Context} {wholeReturn : Ty}
    {evidenceState state : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {cutoff : Nat} {type : Ty} {binder : TypedBinder}
    (origins : ActiveBinderCaptureOrigins state (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends state.inference.substitution)
    (retained : binder ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (schemeEq : binder.scheme = (Detail.generalizeValue state
      (state.binderEnvironment.apply state.inference.substitution) cutoff type).scheme)
    (backed : ∀ older ∈ state.localBinders, BinderTemplatesBefore state cutoff older) :
    LiveBindersSafe binder.scheme.quantified state := by
  have noCapture := resources.local_no_capture binder retained
  rw [schemeEq]
  apply generalized_live_private extension ?_ ?_ backed
  · intro older member
    rcases origins.origin older member with monomorphic | initialized
    · exact .of_quantified_eq_nil monomorphic
    · exact resources.local_no_capture older initialized
  · intro q member
    have present : q ∈ binder.scheme.quantified := by simpa only [schemeEq] using member
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain finalized.substitution q).mpr
        (noCapture.quantified_fresh q present), Option.getD_none]

/-- Entering the exact retained generalized binder preserves the derived
privacy of the old stack and adds the new binder's real capture check. -/
theorem allocate_generalized_live_from_finalizer
    {wholeContext : Frontend.SourceInference.Context} {wholeReturn : Ty}
    {evidenceState state : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (cutoff : Nat) (type : Ty) (name : String)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (origins : ActiveBinderCaptureOrigins state (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends state.inference.substitution)
    (backed : ∀ older ∈ state.localBinders, BinderTemplatesBefore state cutoff older)
    (retained :
      (state.allocateBinder name (Detail.generalizeValue state
        (state.binderEnvironment.apply state.inference.substitution) cutoff type).scheme
        span comptime (Detail.generalizeValue state
          (state.binderEnvironment.apply state.inference.substitution) cutoff type).requirements).1 ∈
      (evidenceState.toTypedSource roots).initializedLetBinders) :
    let generalized := Detail.generalizeValue state
      (state.binderEnvironment.apply state.inference.substitution) cutoff type
    LiveBindersSafe generalized.scheme.quantified
      (state.allocateBinder name generalized.scheme span comptime generalized.requirements).2 := by
  dsimp only
  have live := generalized_live_from_finalizer resources origins extension retained rfl backed
  have own := binder_private_own_quantifiers extension (resources.local_no_capture _ retained)
  intro actual member
  rcases List.mem_cons.mp member with rfl | member
  · exact own.transport (.of_substitution_eq rfl)
  · exact (live actual member).transport (.of_substitution_eq rfl)

end ProtectedVariables
end Solcore.SourceSemantics.SourceInferenceSoundness
end
