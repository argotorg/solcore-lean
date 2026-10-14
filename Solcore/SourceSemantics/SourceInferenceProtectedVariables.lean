import Solcore.SourceSemantics.SourceInferenceUnannotatedLetCertificate

/-! Variable privacy is tracked only at live types. A substitution may retain
old entries from a generalized initializer, so its full range is unrestricted. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
namespace ProtectedVariables

def guard (protectedVars : List TypeVarId) : Substitution :=
  protectedVars.map fun metavariable => (metavariable, Ty.unit)

@[simp] theorem guard_domain (protectedVars : List TypeVarId) :
    (guard protectedVars).domain = protectedVars := by
  simp [guard, Substitution.domain, List.map_map, Function.comp_def]

def Avoids (protectedVars : List TypeVarId) (type : Ty) : Prop :=
  ∀ metavariable, metavariable ∈ type.freeVariables → metavariable ∉ protectedVars

def Safe (protectedVars : List TypeVarId) (state : State) (type : Ty) : Prop :=
  Avoids protectedVars (state.resolve type)

def SafeTransport (protectedVars : List TypeVarId) (before after : State) : Prop :=
  ∀ type, Safe protectedVars before type → Safe protectedVars after type

theorem SafeTransport.refl (protectedVars : List TypeVarId) (state : State) :
    SafeTransport protectedVars state state := by intro _ safe; exact safe

theorem SafeTransport.trans {protectedVars : List TypeVarId} {first second third : State}
    (left : SafeTransport protectedVars first second)
    (right : SafeTransport protectedVars second third) :
    SafeTransport protectedVars first third := by
  intro type safe
  exact right type (left type safe)

theorem SafeTransport.of_substitution_eq {protectedVars : List TypeVarId} {before after : State}
    (same : after.inference.substitution = before.inference.substitution) :
    SafeTransport protectedVars before after := by
  intro type safe
  simpa only [Safe, State.resolve, InferState.resolve, same] using safe

theorem Avoids.apply {protectedVars : List TypeVarId} {type : Ty} {substitution : Substitution}
    (outside : Avoids protectedVars type)
    (range : substitution.RangeAvoidsDomain (guard protectedVars)) :
    Avoids protectedVars (substitution.apply type) := by
  simpa only [guard_domain, Avoids] using
    range.apply_variables_outside_older_domain type (by simpa only [guard_domain] using (show ∀ v, v ∈ type.freeVariables → v ∉ protectedVars from outside))

theorem safe_resolved {protectedVars : List TypeVarId} {state : State} {type : Ty}
    (ready : state.InferenceReady) (safe : Safe protectedVars state type) :
    Safe protectedVars state (state.resolve type) := by
  simpa [Safe, State.resolve, InferState.resolve,
    ready.solved.apply_idempotent] using safe

theorem safe_of_range_on {protectedVars : List TypeVarId} {state : State} {type : Ty}
    (outside : Avoids protectedVars type)
    (range : state.inference.substitution.RangeAvoidsVariablesOn protectedVars type) :
    Safe protectedVars state type :=
  rangeAvoidsVariablesOn_apply_variables_outside _ _ _ range outside

theorem unify {protectedVars : List TypeVarId} {before after : State} {left right : Ty}
    (leftSafe : Safe protectedVars before left)
    (rightSafe : Safe protectedVars before right)
    (accepted : Detail.unify before left right = .ok after) :
    SafeTransport protectedVars before after := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    unfold InferState.unify at unified
    cases update : Unification.unifyTypes (before.inference.resolve left) (before.inference.resolve right) with
    | error error => simp [update, bind, Except.bind] at unified
    | ok substitution =>
      simp only [update, bind, Except.bind, pure, Pure.pure, Except.pure] at unified
      cases unified
      have range : substitution.RangeAvoidsDomain (guard protectedVars) :=
        Unification.unifyTypes_rangeAvoidsDomain
          (by simpa only [guard_domain, Safe, Avoids, State.resolve] using leftSafe)
          (by simpa only [guard_domain, Safe, Avoids, State.resolve] using rightSafe) update
      intro type safe
      simpa only [Safe, State.resolve, InferState.resolve, Substitution.compose_apply] using
        Avoids.apply safe range

theorem fresh {protectedVars : List TypeVarId} {state : State} :
    SafeTransport protectedVars state state.fresh.2 :=
  .of_substitution_eq rfl

theorem fresh_type {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) :
    Safe protectedVars state.fresh.2 state.fresh.1 := by
  have notDomain : (TypeVarId.mk state.inference.next) ∉ state.inference.substitution.domain := by
    intro member
    exact Nat.lt_irrefl _ (ready.solved.domain_below _ member)
  have found : state.inference.substitution.lookup? ⟨state.inference.next⟩ = none :=
    (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr notDomain
  change Avoids protectedVars (state.inference.substitution.apply (.variable ⟨state.inference.next⟩))
  intro metavariable member protectedMember
  simp only [Substitution.apply, found, Option.getD_none, Ty.freeVariables, List.mem_singleton] at member
  subst metavariable
  exact Nat.lt_irrefl _ (bound _ protectedMember)

@[simp] theorem safe_application_iff (protectedVars : List TypeVarId) (state : State) (left right : Ty) :
    Safe protectedVars state (.application left right) ↔ Safe protectedVars state left ∧ Safe protectedVars state right := by
  simp only [Safe, Avoids, State.resolve, InferState.resolve, Substitution.apply,
    Ty.mem_freeVariables_application_iff, or_imp, forall_and]

@[simp] theorem safe_function_iff (protectedVars : List TypeVarId) (state : State) (left right : Ty) :
    Safe protectedVars state (.function left right) ↔ Safe protectedVars state left ∧ Safe protectedVars state right := by
  simp only [Safe, Avoids, State.resolve, InferState.resolve, Substitution.apply,
    Ty.mem_freeVariables_function_iff, or_imp, forall_and]

@[simp] theorem safe_product_iff (protectedVars : List TypeVarId) (state : State) (left right : Ty) :
    Safe protectedVars state (.product left right) ↔ Safe protectedVars state left ∧ Safe protectedVars state right := by
  simp only [Safe, Avoids, State.resolve, InferState.resolve, Substitution.apply,
    Ty.mem_freeVariables_product_iff, or_imp, forall_and]

@[simp] theorem safe_mapping_iff (protectedVars : List TypeVarId) (state : State) (left right : Ty) :
    Safe protectedVars state (.mapping left right) ↔ Safe protectedVars state left ∧ Safe protectedVars state right := by
  simp only [Safe, Avoids, State.resolve, InferState.resolve, Substitution.apply,
    Ty.mem_freeVariables_mapping_iff, or_imp, forall_and]

@[simp] theorem safe_proxy_iff (protectedVars : List TypeVarId) (state : State) (inner : Ty) :
    Safe protectedVars state (.proxy inner) ↔ Safe protectedVars state inner := Iff.rfl

@[simp] theorem safe_comptime_iff (protectedVars : List TypeVarId) (state : State) (inner : Ty) :
    Safe protectedVars state (.comptime inner) ↔ Safe protectedVars state inner := Iff.rfl

theorem safe_parameterApply {protectedVars : List TypeVarId} {state : State}
    {substitution : ParameterSubstitution} {type : Ty}
    (range : ∀ parameter replacement, (parameter, replacement) ∈ substitution → Safe protectedVars state replacement)
    (source : Safe protectedVars state type) :
    Safe protectedVars state (substitution.apply type) := by
  induction type with
  | «variable» metavariable => exact source
  | parameter candidate =>
    cases found : substitution.lookup? candidate with
    | none => simpa only [ParameterSubstitution.apply, found, Option.getD_none] using source
    | some replacement =>
      simpa only [ParameterSubstitution.apply, found, Option.getD_some] using
        range candidate replacement (ParameterSubstitution.lookup?_eq_some_mem found)
  | constructor constructor => exact source
  | application left right leftIH rightIH =>
    exact (safe_application_iff _ _ _ _).mpr
      ⟨leftIH ((safe_application_iff _ _ _ _).mp source).1,
        rightIH ((safe_application_iff _ _ _ _).mp source).2⟩
  | function left right leftIH rightIH =>
    exact (safe_function_iff _ _ _ _).mpr
      ⟨leftIH ((safe_function_iff _ _ _ _).mp source).1,
        rightIH ((safe_function_iff _ _ _ _).mp source).2⟩
  | product left right leftIH rightIH =>
    exact (safe_product_iff _ _ _ _).mpr
      ⟨leftIH ((safe_product_iff _ _ _ _).mp source).1,
        rightIH ((safe_product_iff _ _ _ _).mp source).2⟩
  | mapping left right leftIH rightIH =>
    exact (safe_mapping_iff _ _ _ _).mpr
      ⟨leftIH ((safe_mapping_iff _ _ _ _).mp source).1,
        rightIH ((safe_mapping_iff _ _ _ _).mp source).2⟩
  | proxy inner induction => exact induction source
  | comptime inner induction => exact induction source
  | error => exact source

theorem safe_closed (protectedVars : List TypeVarId) (state : State) {type : Ty}
    (closed : type.VariablesBelow 0) : Safe protectedVars state type := by
  have empty : type.freeVariables = [] := List.eq_nil_iff_forall_not_mem.mpr (by
    intro metavariable member
    exact Nat.not_lt_zero _ (closed metavariable member))
  have fixed := Ty.apply_eq_self_of_domain_disjoint_freeVariables state.inference.substitution type
    (by simp [empty])
  simp [Safe, Avoids, State.resolve, InferState.resolve, fixed, empty]

theorem safe_applyMany (protectedVars : List TypeVarId) (state : State) (base : Ty) (arguments : List Ty)
    (baseSafe : Safe protectedVars state base)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument) :
    Safe protectedVars state (Ty.applyMany base arguments) := by
  induction arguments generalizing base with
  | nil => exact baseSafe
  | cons first rest induction =>
    apply induction
    · exact (safe_application_iff _ _ _ _).mpr ⟨baseSafe, argumentsSafe first (by simp)⟩
    · intro argument member
      exact argumentsSafe argument (by simp [member])

theorem safe_productMany (protectedVars : List TypeVarId) (state : State) (types : List Ty)
    (members : ∀ type ∈ types, Safe protectedVars state type) :
    Safe protectedVars state (Ty.productMany types) := by
  induction types with
  | nil => exact safe_closed _ _ (by simp [Ty.productMany, Ty.VariablesBelow, Ty.unit, Ty.freeVariables])
  | cons first rest induction =>
    cases rest with
    | nil => exact members first (by simp)
    | cons next tail =>
      exact (safe_product_iff _ _ _ _).mpr
        ⟨members first (by simp), induction (fun type member => members type (by simp [member]))⟩

theorem freshTypes (count : Nat) {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) :
    SafeTransport protectedVars state (Detail.freshTypes count state).2 ∧
      ∀ type ∈ (Detail.freshTypes count state).1, Safe protectedVars (Detail.freshTypes count state).2 type := by
  induction count generalizing state with
  | zero => exact ⟨.refl _ _, by simp [Detail.freshTypes]⟩
  | succ count induction =>
    have child := induction (state := state.fresh.2) ready.fresh (by
      intro metavariable member
      exact Nat.lt_trans (bound metavariable member) (Nat.lt_succ_self _))
    refine ⟨fresh.trans child.1, ?_⟩
    intro type member
    change type ∈ state.fresh.1 :: (Detail.freshTypes count state.fresh.2).1 at member
    rcases List.mem_cons.mp member with rfl | rest
    · exact child.1 _ (fresh_type ready bound)
    · exact child.2 type rest

theorem safe_applyMany_members {protectedVars : List TypeVarId} {state : State} {base : Ty} {arguments : List Ty}
    (safe : Safe protectedVars state (Ty.applyMany base arguments)) :
    Safe protectedVars state base ∧ ∀ argument ∈ arguments, Safe protectedVars state argument := by
  induction arguments generalizing base with
  | nil => exact ⟨safe, by simp⟩
  | cons first rest induction =>
    have child := induction (base := .application base first) safe
    obtain ⟨baseSafe, firstSafe⟩ := (safe_application_iff _ _ _ _).mp child.1
    exact ⟨baseSafe, fun argument member => (List.mem_cons.mp member).elim (fun same => same ▸ firstSafe) (child.2 argument)⟩

theorem safe_instantiation {protectedVars : List TypeVarId} {state : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (payloads : ∀ payload ∈ constructor.payloadTypes, payload.VariablesBelow 0)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument) :
    (∀ payload ∈ (Detail.instantiateDataConstructor dataType constructor arguments).payloadTypes,
      Safe protectedVars state payload) ∧
      Safe protectedVars state (Detail.instantiateDataConstructor dataType constructor arguments).resultType := by
  constructor
  · intro payload member
    rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
    exact safe_parameterApply (fun _ _ entry => argumentsSafe _ (List.of_mem_zip entry).2)
      (safe_closed _ _ (payloads original originalMember))
  · exact safe_applyMany _ _ _ _ (safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.freeVariables])) argumentsSafe

theorem contextual_constructor {protectedVars : List TypeVarId} {state : State}
    {context : Frontend.SourceInference.Context} {expected : Ty} {name : String}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (ready : state.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (safe : Safe protectedVars state expected)
    (accepted : Detail.contextualConstructorCandidate context state (some expected) name =
      .ok (dataType, constructor, arguments)) :
    (∀ payload ∈ (Detail.instantiateDataConstructor dataType constructor arguments).payloadTypes,
      Safe protectedVars state payload) ∧
      Safe protectedVars state (Detail.instantiateDataConstructor dataType constructor arguments).resultType := by
  obtain ⟨dataMember, constructorMember, actual, expectedEq, nominalEq⟩ :=
    Detail.contextualConstructorCandidate_success_facts accepted
  cases Option.some.inj expectedEq
  have nominalSafe : Safe protectedVars state (Ty.nominal dataType.id arguments) := by
    rw [← nominalEq]
    exact safe_resolved ready safe
  apply safe_instantiation
  · exact formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember 0
  · exact (safe_applyMany_members nominalSafe).2

private theorem fresh_constructor_arguments
    (parameters : List TypeParameterId) (arguments : List Ty) (state : State)
    (protectedVars : List TypeVarId)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (safe : ∀ argument ∈ arguments, Safe protectedVars state argument) :
    let allocated := parameters.foldl (fun (result : List Ty × State) _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2)) (arguments, state)
    SafeTransport protectedVars state allocated.2 ∧
      ∀ argument ∈ allocated.1, Safe protectedVars allocated.2 argument := by
  induction parameters generalizing arguments state with
  | nil => exact ⟨.refl _ _, safe⟩
  | cons first rest induction =>
    have child := induction (arguments ++ [state.fresh.1]) state.fresh.2 ready.fresh
      (by intro metavariable member; exact Nat.lt_trans (bound metavariable member) (Nat.lt_succ_self _))
      (by
        intro argument member
        rcases List.mem_append.mp member with prior | new
        · exact fresh argument (safe argument prior)
        · have same := List.mem_singleton.mp new
          subst argument
          exact fresh_type ready bound)
    exact ⟨fresh.trans child.1, child.2⟩

theorem fresh_constructor {protectedVars : List TypeVarId} {state : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (payloads : ∀ payload ∈ constructor.payloadTypes, payload.VariablesBelow 0) :
    let result := Detail.freshDataConstructorInstantiation dataType constructor state
    SafeTransport protectedVars state result.2 ∧
      (∀ payload ∈ result.1.payloadTypes, Safe protectedVars result.2 payload) ∧
      Safe protectedVars result.2 result.1.resultType := by
  have allocated := fresh_constructor_arguments dataType.parameters [] state protectedVars ready bound (by simp)
  exact ⟨allocated.1, safe_instantiation payloads allocated.2⟩

theorem unify_next {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    after.inference.next = before.inference.next := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    exact InferState.unify_next unified

end ProtectedVariables
end Solcore.SourceSemantics.SourceInferenceSoundness
