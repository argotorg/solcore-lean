import Solcore.SourceSemantics.SourceInferenceGeneralizedBarrierTransport
import Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicGeneralization

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
