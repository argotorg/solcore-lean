import Solcore.SourceSemantics.SourceInferenceUnannotatedLetCertificate

/-! Old metavariables in live inference types remain supported by the same entry
roots while those roots are normalized by each genuine unifier update. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
namespace InferenceSupport

def Supported (cutoff : Nat) (roots : List Ty) (type : Ty) : Prop :=
  ∀ metavariable, metavariable ∈ type.freeVariables → metavariable.index < cutoff →
    ∃ root ∈ roots, metavariable ∈ root.freeVariables

def Resolved (cutoff : Nat) (roots : List Ty) (state : State) (type : Ty) : Prop :=
  Supported cutoff (roots.map state.resolve) (state.resolve type)

def Transport (cutoff : Nat) (roots : List Ty) (before after : State) : Prop :=
  ∀ type, Resolved cutoff roots before type → Resolved cutoff roots after type

theorem mem_apply_of_lookup_none (substitution : Substitution)
    (metavariable : TypeVarId) (type : Ty)
    (found : substitution.lookup? metavariable = none)
    (member : metavariable ∈ type.freeVariables) :
    metavariable ∈ (substitution.apply type).freeVariables := by
  induction type with
  | «variable» source =>
    have same : metavariable = source := by simpa [Ty.freeVariables] using member
    subst source
    simp [Substitution.apply, found, Ty.freeVariables]
  | parameter name => simp [Ty.freeVariables] at member
  | constructor name => simp [Ty.freeVariables] at member
  | application left right leftIH rightIH =>
    rw [Ty.mem_freeVariables_application_iff] at member
    simp only [Substitution.apply, Ty.mem_freeVariables_application_iff]
    exact member.elim (fun occurs => Or.inl (leftIH occurs))
      (fun occurs => Or.inr (rightIH occurs))
  | function left right leftIH rightIH =>
    rw [Ty.mem_freeVariables_function_iff] at member
    simp only [Substitution.apply, Ty.mem_freeVariables_function_iff]
    exact member.elim (fun occurs => Or.inl (leftIH occurs))
      (fun occurs => Or.inr (rightIH occurs))
  | product left right leftIH rightIH =>
    rw [Ty.mem_freeVariables_product_iff] at member
    simp only [Substitution.apply, Ty.mem_freeVariables_product_iff]
    exact member.elim (fun occurs => Or.inl (leftIH occurs))
      (fun occurs => Or.inr (rightIH occurs))
  | mapping left right leftIH rightIH =>
    rw [Ty.mem_freeVariables_mapping_iff] at member
    simp only [Substitution.apply, Ty.mem_freeVariables_mapping_iff]
    exact member.elim (fun occurs => Or.inl (leftIH occurs))
      (fun occurs => Or.inr (rightIH occurs))
  | proxy inner induction => exact induction member
  | comptime inner induction => exact induction member
  | error => simp [Ty.freeVariables] at member

theorem range_supported_of_unifyTypes
    {cutoff : Nat} {roots : List Ty} {left right : Ty} {update : Substitution}
    (leftSupported : Supported cutoff roots left)
    (rightSupported : Supported cutoff roots right)
    (accepted : Unification.unifyTypes left right = .ok update) :
    ∀ {key replacement}, (key, replacement) ∈ update →
      Supported cutoff roots replacement := by
  intro key replacement entry metavariable member old
  classical
  by_cases supported : ∃ root ∈ roots, metavariable ∈ root.freeVariables
  · exact supported
  have absent := supported
  apply False.elim
  let guard : Substitution := [(metavariable, Ty.unit)]
  have outsideLeft : ∀ candidate, candidate ∈ left.freeVariables →
      candidate ∉ guard.domain := by
    intro candidate occurs guarded
    have same : candidate = metavariable := by
      simpa [guard, Substitution.domain] using guarded
    subst candidate
    exact absent (leftSupported metavariable occurs old)
  have outsideRight : ∀ candidate, candidate ∈ right.freeVariables →
      candidate ∉ guard.domain := by
    intro candidate occurs guarded
    have same : candidate = metavariable := by
      simpa [guard, Substitution.domain] using guarded
    subst candidate
    exact absent (rightSupported metavariable occurs old)
  have avoids : update.RangeAvoidsDomain guard := Unification.unifyTypes_rangeAvoidsDomain
    outsideLeft outsideRight accepted
  exact avoids entry metavariable member (by simp [guard, Substitution.domain])

theorem supported_apply {cutoff next : Nat} {roots : List Ty}
    {substitution : Substitution} (type : Ty)
    (solved : substitution.SolvedBelow next)
    (rangeSupported : ∀ {key replacement}, (key, replacement) ∈ substitution →
      Supported cutoff roots replacement)
    (supported : Supported cutoff roots type) :
    Supported cutoff (roots.map substitution.apply) (substitution.apply type) := by
  have retained : ∀ metavariable, metavariable ∉ substitution.domain →
      (∃ root ∈ roots, metavariable ∈ root.freeVariables) →
      ∃ root ∈ roots.map substitution.apply, metavariable ∈ root.freeVariables := by
    intro metavariable outside source
    obtain ⟨root, member, occurs⟩ := source
    refine ⟨substitution.apply root, List.mem_map.mpr ⟨root, member, rfl⟩, ?_⟩
    exact mem_apply_of_lookup_none substitution metavariable root
      ((Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside) occurs
  induction type with
  | «variable» source =>
    intro metavariable member old
    cases found : substitution.lookup? source with
    | none =>
      have same : metavariable = source := by
        simpa [Substitution.apply, found, Ty.freeVariables] using member
      subst source
      exact retained metavariable
        ((Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mp found)
        (supported metavariable (by simp [Ty.freeVariables]) old)
    | some replacement =>
      have occurs : metavariable ∈ replacement.freeVariables := by
        simpa [Substitution.apply, found] using member
      exact retained metavariable (solved.lookup_range_outside_domain found occurs)
        (rangeSupported (Substitution.lookup?_eq_some_mem found) metavariable occurs old)
  | parameter name => simp [Supported, Substitution.apply, Ty.freeVariables]
  | constructor name => simp [Supported, Substitution.apply, Ty.freeVariables]
  | application left right leftIH rightIH =>
    intro metavariable member old
    simp only [Substitution.apply, Ty.mem_freeVariables_application_iff] at member
    rcases member with occurs | occurs
    · exact leftIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_application_iff _ _ _).mpr (Or.inl member)) lower)
        metavariable occurs old
    · exact rightIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_application_iff _ _ _).mpr (Or.inr member)) lower)
        metavariable occurs old
  | function left right leftIH rightIH =>
    intro metavariable member old
    simp only [Substitution.apply, Ty.mem_freeVariables_function_iff] at member
    rcases member with occurs | occurs
    · exact leftIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_function_iff _ _ _).mpr (Or.inl member)) lower)
        metavariable occurs old
    · exact rightIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_function_iff _ _ _).mpr (Or.inr member)) lower)
        metavariable occurs old
  | product left right leftIH rightIH =>
    intro metavariable member old
    simp only [Substitution.apply, Ty.mem_freeVariables_product_iff] at member
    rcases member with occurs | occurs
    · exact leftIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_product_iff _ _ _).mpr (Or.inl member)) lower)
        metavariable occurs old
    · exact rightIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_product_iff _ _ _).mpr (Or.inr member)) lower)
        metavariable occurs old
  | mapping left right leftIH rightIH =>
    intro metavariable member old
    simp only [Substitution.apply, Ty.mem_freeVariables_mapping_iff] at member
    rcases member with occurs | occurs
    · exact leftIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_mapping_iff _ _ _).mpr (Or.inl member)) lower)
        metavariable occurs old
    · exact rightIH (fun candidate member lower => supported candidate
        ((Ty.mem_freeVariables_mapping_iff _ _ _).mpr (Or.inr member)) lower)
        metavariable occurs old
  | proxy inner induction => exact induction supported
  | comptime inner induction => exact induction supported
  | error => simp [Supported, Substitution.apply, Ty.freeVariables]

theorem unify {cutoff : Nat} {roots : List Ty} {before after : State}
    {left right : Ty}
    (ready : before.InferenceReady)
    (leftBelow : left.VariablesBelow before.inference.next)
    (rightBelow : right.VariablesBelow before.inference.next)
    (leftSupported : Resolved cutoff roots before left)
    (rightSupported : Resolved cutoff roots before right)
    (accepted : Detail.unify before left right = .ok after) :
    Transport cutoff roots before after := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind,
      pure, Pure.pure, Except.pure] at accepted
    cases accepted
    unfold InferState.unify at unified
    cases update : Unification.unifyTypes (before.inference.resolve left)
        (before.inference.resolve right) with
    | error error => simp [update, bind, Except.bind] at unified
    | ok substitution =>
      simp only [update, bind, Except.bind, pure, Pure.pure, Except.pure] at unified
      cases unified
      have solved := Unification.unifyTypes_solvedBelow
        (ready.solved.variablesBelow_apply leftBelow)
        (ready.solved.variablesBelow_apply rightBelow) update
      have rangeSupported : ∀ {key replacement}, (key, replacement) ∈ substitution →
          Supported cutoff (roots.map before.resolve) replacement :=
        range_supported_of_unifyTypes leftSupported rightSupported update
      intro type supported
      have transported := supported_apply (before.resolve type) solved
        rangeSupported supported
      change Supported cutoff
        (roots.map fun type => (substitution.compose before.inference.substitution).apply type)
        ((substitution.compose before.inference.substitution).apply type)
      simpa only [State.resolve, InferState.resolve,
        Substitution.compose_apply, List.map_map, Function.comp_def] using transported

theorem Transport.refl (cutoff : Nat) (roots : List Ty) (state : State) :
    Transport cutoff roots state state := by intro _ supported; exact supported

theorem Transport.trans {cutoff : Nat} {roots : List Ty}
    {first second third : State}
    (left : Transport cutoff roots first second)
    (right : Transport cutoff roots second third) :
    Transport cutoff roots first third := by
  intro type supported
  exact right type (left type supported)

theorem Transport.of_substitution_eq {cutoff : Nat} {roots : List Ty}
    {before after : State}
    (same : after.inference.substitution = before.inference.substitution) :
    Transport cutoff roots before after := by
  intro type supported
  change Supported cutoff (roots.map fun type => after.inference.substitution.apply type)
    (after.inference.substitution.apply type)
  rw [same]
  exact supported


theorem Transport.of_resolve_eq {cutoff : Nat} {roots : List Ty}
    {before after : State}
    (same : ∀ type, after.resolve type = before.resolve type) :
    Transport cutoff roots before after := by
  intro type supported
  have functions : after.resolve = before.resolve := funext same
  simpa only [Resolved, functions] using supported

theorem resolved_normalized {cutoff : Nat} {roots : List Ty}
    {state : State} {type : Ty} (ready : state.InferenceReady)
    (supported : Resolved cutoff roots state type) :
    Resolved cutoff roots state (state.resolve type) := by
  simpa only [Resolved, State.resolve, InferState.resolve,
    ready.solved.apply_idempotent] using supported

theorem resolved_root {cutoff : Nat} {roots : List Ty}
    {state : State} {type : Ty} (member : type ∈ roots) :
    Resolved cutoff roots state type := by
  intro metavariable occurs _
  exact ⟨state.resolve type, List.mem_map.mpr ⟨type, member, rfl⟩, occurs⟩

theorem resolved_closed (cutoff : Nat) (roots : List Ty) (state : State)
    {type : Ty} (closed : type.freeVariables = []) :
    Resolved cutoff roots state type := by
  have fixed : state.resolve type = type := by
    apply Ty.apply_eq_self_of_domain_disjoint_freeVariables
    intro metavariable _ member
    simp only [closed, List.not_mem_nil] at member
  intro metavariable member _
  rw [fixed, closed] at member
  simp at member

theorem fresh {cutoff : Nat} {roots : List Ty} {state : State} :
    Transport cutoff roots state state.fresh.2 :=
  .of_substitution_eq rfl

theorem fresh_type {cutoff : Nat} {roots : List Ty} {state : State}
    (ready : state.InferenceReady) (bound : cutoff ≤ state.inference.next) :
    Resolved cutoff roots state.fresh.2 state.fresh.1 := by
  have notDomain : (TypeVarId.mk state.inference.next) ∉ state.inference.substitution.domain := by
    intro member
    exact Nat.lt_irrefl _ (ready.solved.domain_below _ member)
  have found : state.inference.substitution.lookup? ⟨state.inference.next⟩ = none :=
    (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr notDomain
  intro metavariable member old
  change metavariable ∈
    (state.inference.substitution.apply (.variable ⟨state.inference.next⟩)).freeVariables at member
  simp only [Substitution.apply, found, Option.getD_none,
    Ty.freeVariables, List.mem_singleton] at member
  subst metavariable
  exact False.elim ((Nat.not_lt.mpr bound) old)

theorem withExpected {cutoff : Nat} {roots : List Ty}
    {context : Frontend.SourceInference.Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : Detail.ExpectationResult}
    (ready : state.InferenceReady)
    (actualBelow : actual.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (actualSupported : Resolved cutoff roots state actual.type)
    (expectedSupported : ∀ type ∈ expected, Resolved cutoff roots state type)
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    Transport cutoff roots state result.state ∧
      Resolved cutoff roots result.state result.expression.type := by
  have properties := Detail.withExpected_inferenceProperties ready actualBelow
    expectedBelow accepted
  cases expected with
  | none =>
    simp only [Detail.withExpected] at accepted
    cases accepted
    exact ⟨.refl _ _ _, resolved_normalized ready actualSupported⟩
  | some expected =>
    have expectedBound := expectedBelow expected (by simp)
    have supported := expectedSupported expected (by simp)
    cases unification : state.inference.unify actual.type expected with
    | ok inference =>
      simp only [Detail.withExpected, unification] at accepted
      cases accepted
      have unified : Detail.unify state actual.type expected =
          .ok {state with inference} := by
        simp [Detail.unify, Detail.liftUnification, unification,
          bind, Except.bind, pure, Pure.pure, Except.pure]
      have transport := unify ready actualBelow expectedBound actualSupported
        supported unified
      exact ⟨transport, resolved_normalized properties.2.1
        (transport expected supported)⟩
    | error error =>
      cases error with
      | occursCheck metavariable type => simp [Detail.withExpected, unification] at accepted
      | exhausted => simp [Detail.withExpected, unification] at accepted
      | mismatch left right =>
        simp only [Detail.withExpected, unification] at accepted
        cases planResult : Detail.coercionPlan? context state
            (state.resolve actual.type) (state.resolve expected) with
        | error error => simp [planResult, bind, Except.bind] at accepted
        | ok planOption =>
          cases planOption with
          | none => simp [planResult, bind, Except.bind] at accepted
          | some plan =>
            simp only [planResult, bind, Except.bind] at accepted
            change Except.ok _ = Except.ok result at accepted
            cases accepted
            have transport : Transport cutoff roots state
                (Detail.commitCoercionPlan state plan).2 :=
              .of_resolve_eq (Detail.commitCoercionPlan_resolve state plan)
            exact ⟨transport, transport (state.resolve expected)
              (resolved_normalized ready supported)⟩

end InferenceSupport
end Solcore.SourceSemantics.SourceInferenceSoundness
