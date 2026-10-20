import Solcore.SourceSemantics.SourceInferenceGeneralizedBarrierReceipts

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
