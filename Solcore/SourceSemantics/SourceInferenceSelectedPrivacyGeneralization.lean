import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyDeclarations
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyOperators

/-! A new binder inherits privacy from its actual initializer and the new
requirement rows selected by executable generalization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem safe_variable_member {protectedVars : List TypeVarId} {state : State}
    {type : Ty} (safe : Safe protectedVars state type) {metavariable : TypeVarId}
    (member : metavariable ∈ type.freeVariables) :
    Safe protectedVars state (.variable metavariable) := by
  induction type with
  | «variable» actual =>
    have same : metavariable = actual := by simpa [Ty.freeVariables] using member
    subst metavariable
    exact safe
  | parameter _ => simp [Ty.freeVariables] at member
  | constructor _ => simp [Ty.freeVariables] at member
  | error => simp [Ty.freeVariables] at member
  | proxy _ ih => exact ih safe member
  | comptime _ ih => exact ih safe member
  | application left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_application_iff _ _ _).mp member with member | member
    · exact leftIH ((safe_application_iff _ _ _ _).mp safe).1 member
    · exact rightIH ((safe_application_iff _ _ _ _).mp safe).2 member
  | function left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_function_iff _ _ _).mp member with member | member
    · exact leftIH ((safe_function_iff _ _ _ _).mp safe).1 member
    · exact rightIH ((safe_function_iff _ _ _ _).mp safe).2 member
  | product left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_product_iff _ _ _).mp member with member | member
    · exact leftIH ((safe_product_iff _ _ _ _).mp safe).1 member
    · exact rightIH ((safe_product_iff _ _ _ _).mp safe).2 member
  | mapping left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_mapping_iff _ _ _).mp member with member | member
    · exact leftIH ((safe_mapping_iff _ _ _ _).mp safe).1 member
    · exact rightIH ((safe_mapping_iff _ _ _ _).mp safe).2 member

private theorem generalized_requirement_new_source (state : State)
    (locals : Environment) (cutoff : Nat) (type : Ty) (template : LocalSchemeRequirement)
    (member : template ∈ (Detail.generalizeValue state locals cutoff type).requirements) :
    ∃ raw, raw ∈ state.requirements.drop cutoff ∧
      template.predicate = Detail.applyPredicate state raw.predicate := by
  unfold Detail.generalizeValue at member
  dsimp only at member
  obtain ⟨raw, eligible, produced⟩ := List.mem_filterMap.mp member
  split at produced
  · cases Option.some.inj produced
    exact ⟨raw, (List.mem_filter.mp eligible).1, rfl⟩
  · cases produced

private theorem predicate_resolved_private {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady) {predicate : ProgramPredicate}
    (safe : PredicateSafe protectedVars state predicate) :
    PredicateSafe protectedVars state (Detail.applyPredicate state predicate) := by
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · exact safe_resolved ready (safe _ (by simp))
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact safe_resolved ready (safe _ (List.mem_cons.mpr (.inr originalMember)))

/-- The real requirement cutoff separates every selected template from the
old ledger. Only genuinely new rows need privacy; old generalized templates
may still contain their own quantified variables. -/
theorem generalized_binder_private {protectedVars : List TypeVarId}
    {before state : State} {type : Ty} (locals : Environment) (name : String)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (beforeWellFormed : before.RequirementsWellFormed)
    (wellFormed : state.RequirementsWellFormed)
    (ready : state.InferenceReady)
    (typeSafe : Safe protectedVars state type)
    (newRows : ∀ row ∈ state.requirements, row ∉ before.requirements →
      PredicateSafe protectedVars state row.predicate) :
    let generalized := Detail.generalizeValue state locals before.nextRequirement type
    BinderSafe protectedVars state
      (state.allocateBinder name generalized.scheme span comptime generalized.requirements).1 := by
  dsimp only
  constructor
  · intro metavariable member
    have occurs : metavariable ∈ type.freeVariables := by
      exact (List.mem_filter.mp member).1
    exact safe_variable_member typeSafe occurs
  · intro requirement member predicateType typeMember metavariable occurs outside
    obtain ⟨raw, dropped, predicateEq⟩ :=
      generalized_requirement_new_source state locals before.nextRequirement type requirement member
    obtain ⟨rawMember, lower⟩ :=
      (State.mem_drop_requirements_iff state wellFormed _ raw).mp dropped
    have fresh : raw ∉ before.requirements := by
      intro old
      exact (Nat.not_lt.mpr lower)
        (State.requirement_id_lt_nextRequirement before beforeWellFormed old)
    have safe := predicate_resolved_private ready (newRows raw rawMember fresh)
    rw [predicateEq] at typeMember
    exact safe_variable_member (safe predicateType typeMember) occurs

/-- Executable binder allocation preserves existing live privacy and enters
its actual generalized binder with the inherited initializer certificate. -/
theorem allocate_generalized_private {protectedVars : List TypeVarId}
    {before state : State} {type : Ty} (locals : Environment) (name : String)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (beforeWellFormed : before.RequirementsWellFormed)
    (wellFormed : state.RequirementsWellFormed) (ready : state.InferenceReady)
    (typeSafe : Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (newRows : ∀ row ∈ state.requirements, row ∉ before.requirements →
      PredicateSafe protectedVars state row.predicate) :
    let generalized := Detail.generalizeValue state locals before.nextRequirement type
    let allocated := (state.allocateBinder name generalized.scheme span comptime generalized.requirements).2
    SafeTransport protectedVars state allocated ∧ LiveBindersSafe protectedVars allocated := by
  dsimp only
  have transport : SafeTransport protectedVars state
      (state.allocateBinder name (Detail.generalizeValue state locals before.nextRequirement type).scheme
        span comptime (Detail.generalizeValue state locals before.nextRequirement type).requirements).2 :=
    .of_substitution_eq rfl
  refine ⟨transport, ?_⟩
  intro binder member
  rcases List.mem_cons.mp member with rfl | old
  · exact (generalized_binder_private locals name span comptime beforeWellFormed
      wellFormed ready typeSafe newRows).transport transport
  · exact (live binder old).transport transport

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
