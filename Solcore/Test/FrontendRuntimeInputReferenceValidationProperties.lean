import Solcore.Frontend.RuntimeInputValidation

/-! The combined public validator consumes existing structural evidence. Actual
nested values and even unused captures matter; unselected tags do not allocate. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeInputReferenceValidation
open Solcore Solcore.Frontend

private def reference (type : Core.Ty) (location : Nat) : TypedRuntimeArgument :=
  ⟨.cell type,.cellRef type location,.cellRef⟩
private theorem structuralEnvironment (args : List TypedRuntimeArgument) :
    Core.EnvironmentHasTypes (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons arg rest ih => exact .cons arg.valueTyped ih
private theorem runtimeEnvironment {world : Core.StoreTyping} {args : List TypedRuntimeArgument}
    (typed : ∀ a ∈ args, Core.RuntimeValueHasType world a.value a.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons arg rest ih => exact .cons (typed arg (by simp)) (ih (fun a member => typed a (by simp [member])))
private def identity (signature : Core.Ty) (captured : List TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.function signature signature,.closure signature signature (.var 0) (captured.map (·.value)),
    .closure (structuralEnvironment captured) (.var rfl)⟩
private def nested (unused signature : Core.Ty) (suffix : List TypedRuntimeArgument) : Nat → TypedRuntimeArgument → TypedRuntimeArgument
  | 0, arg => arg
  | n+1, arg =>
      let inner := nested unused signature suffix n arg
      ⟨.product (.sum inner.type unused) (.function signature signature),
        .pair (.inLeft unused inner.value) (identity signature (inner::suffix)).value,
        .pair (.inLeft inner.valueTyped) (identity signature (inner::suffix)).valueTyped⟩
private theorem identityTyped {world : Core.StoreTyping} {signature : Core.Ty} {captured : List TypedRuntimeArgument}
    (typed : ∀ a ∈ captured, Core.RuntimeValueHasType world a.value a.type) :
    Core.RuntimeValueHasType world (identity signature captured).value (identity signature captured).type :=
  .closure (runtimeEnvironment typed) (.var rfl)
private theorem nestedTyped {world : Core.StoreTyping} {unused signature : Core.Ty} {suffix : List TypedRuntimeArgument}
    {arg : TypedRuntimeArgument} (typed : Core.RuntimeValueHasType world arg.value arg.type)
    (captured : ∀ a ∈ suffix, Core.RuntimeValueHasType world a.value a.type) (depth : Nat) :
    Core.RuntimeValueHasType world (nested unused signature suffix depth arg).value (nested unused signature suffix depth arg).type := by
  induction depth with
  | zero => exact typed
  | succ depth ih =>
      exact .pair (.inLeft ih) (identityTyped (by
        intro a member
        rcases List.mem_cons.mp member with rfl | member
        · exact ih
        · exact captured a member))
private theorem nestedPayload {world : Core.StoreTyping} {unused signature : Core.Ty} {suffix : List TypedRuntimeArgument}
    {arg : TypedRuntimeArgument} (depth : Nat)
    (typed : Core.RuntimeValueHasType world (nested unused signature suffix depth arg).value (nested unused signature suffix depth arg).type) :
    Core.RuntimeValueHasType world arg.value arg.type := by
  induction depth with
  | zero => exact typed
  | succ depth ih => cases typed with | pair selected _ => cases selected with | inLeft inner => exact ih inner
private theorem acceptsSingle {world : Core.StoreTyping} {store : Core.Store} {arg : TypedRuntimeArgument}
    (typed : Core.RuntimeValueHasType world arg.value arg.type) (stored : Core.StoreHasTypes world store) :
    validateRuntimeInputs world [arg] store = true :=
  validateRuntimeInputs_iff.mpr ⟨by simpa using typed,stored⟩
private theorem rejectsSingle {world : Core.StoreTyping} {store : Core.Store} {arg : TypedRuntimeArgument}
    (untyped : ¬ Core.RuntimeValueHasType world arg.value arg.type) :
    validateRuntimeInputs world [arg] store = false := by
  cases checked : validateRuntimeInputs world [arg] store with
  | false => rfl
  | true => exact False.elim (untyped ((validateRuntimeInputs_iff.mp checked).1 arg (by simp)))
private theorem capturedLookup {definitions : Core.DataEnvironment} {world : Core.StoreTyping} {environment : Core.Environment} {context : Core.Context}
    (typed : Core.RuntimeEnvironmentHasTypes world environment context definitions)
    {index : Nat} {value : Core.Value} (found : environment[index]? = some value) :
    ∃ type, Core.RuntimeValueHasType world value type definitions := by
  induction typed using Core.RuntimeEnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True) generalizing index with
  | unit | bool | word | pair | inLeft | inRight | closure | cellRef | constructed => trivial
  | nil => simp at found
  | cons head _ _ ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at found; subst value; exact ⟨_,head⟩
      | succ index => exact ih (by simpa using found)

theorem arbitrary_nested_pairs_sums_and_actual_captured_suffix_validate
    {world : Core.StoreTyping} {store : Core.Store} (unused signature : Core.Ty)
    (arg : TypedRuntimeArgument) (suffix : List TypedRuntimeArgument) (depth : Nat)
    (typed : Core.RuntimeValueHasType world arg.value arg.type)
    (captured : ∀ a ∈ suffix, Core.RuntimeValueHasType world a.value a.type)
    (stored : Core.StoreHasTypes world store) :
    validateRuntimeInputs world [nested unused signature suffix depth arg] store = true ∧
    Core.RuntimeValueHasType world (nested unused signature suffix depth arg).value (nested unused signature suffix depth arg).type ∧
    Core.StoreHasTypes world store := by
  have checked : validateRuntimeInputs world [nested unused signature suffix depth arg] store = true :=
    acceptsSingle (nestedTyped typed captured depth) stored
  exact ⟨checked,(validateRuntimeInputs_iff.mp checked).1 _ (by simp),(validateRuntimeInputs_iff.mp checked).2⟩

theorem all_nested_levels_preserve_an_unallocated_700_rejection
    (world : Core.StoreTyping) (store : Core.Store) (unused signature : Core.Ty)
    (suffix : List TypedRuntimeArgument) (depth : Nat) (short : world.length ≤ 700) :
    Core.ValueHasType (nested unused signature suffix depth (reference .word 700)).value
      (nested unused signature suffix depth (reference .word 700)).type ∧
    validateRuntimeInputs world [nested unused signature suffix depth (reference .word 700)] store = false := by
  refine ⟨(nested unused signature suffix depth (reference .word 700)).valueTyped,rejectsSingle ?_⟩
  intro typed
  have missing := nestedPayload depth typed
  cases missing with
  | cellRef found => have bound := (List.getElem?_eq_some_iff.mp found).1; omega

theorem an_unused_capture_is_checked_before_any_body_execution
    (world : Core.StoreTyping) (store : Core.Store) (signature type : Core.Ty)
    (leading suffix : List TypedRuntimeArgument) (location : Nat) (missing : world[location]? ≠ some type) :
    Core.ValueHasType (identity signature (leading ++ reference type location::suffix)).value (.function signature signature) ∧
    validateRuntimeInputs world [identity signature (leading ++ reference type location::suffix)] store = false := by
  refine ⟨(identity signature (leading ++ reference type location::suffix)).valueTyped,rejectsSingle ?_⟩
  intro typed
  cases typed with
  | closure environment _ =>
      have found : ((leading ++ reference type location::suffix).map (·.value))[leading.length]? = some (.cellRef type location) := by
        simp [reference]
      obtain ⟨_,referenceTyped⟩ := capturedLookup environment found
      cases referenceTyped with | cellRef found => exact missing found

theorem a_nested_unused_closure_capture_is_not_just_an_outer_tag
    (world : Core.StoreTyping) (store : Core.Store) (outer inner type : Core.Ty)
    (suffix : List TypedRuntimeArgument) (location : Nat) (missing : world[location]? ≠ some type) :
    validateRuntimeInputs world
      [identity outer [identity inner (reference type location::suffix)]] store = false := by
  apply rejectsSingle
  intro typed
  cases typed with
  | closure environment _ => cases environment with
    | cons innerTyped _ => cases innerTyped with
      | closure captured _ => cases captured with
        | cons head _ => cases head with | cellRef found => exact missing found

theorem separately_accepted_references_cannot_use_incompatible_actual_worlds (word : Core.Word) (b : Bool) :
    validateRuntimeInputs [.word] [reference .word 0] [.word word] = true ∧
    validateRuntimeInputs [.bool] [reference .bool 0] [.bool b] = true ∧
    ∀ world store, validateRuntimeInputs world [reference .word 0,reference .bool 0] store = false := by
  refine ⟨acceptsSingle (.cellRef rfl) (Core.StoreHasTypes.nil.allocate .word .word),
    acceptsSingle (.cellRef rfl) (Core.StoreHasTypes.nil.allocate .bool .bool),?_⟩
  intro world store
  cases checked : validateRuntimeInputs world [reference .word 0,reference .bool 0] store with
  | false => rfl
  | true =>
      have typed := (validateRuntimeInputs_iff.mp checked).1
      have left := typed (reference .word 0) (by simp)
      have right := typed (reference .bool 0) (by simp)
      cases left with
      | cellRef first => cases right with | cellRef second => rw [first] at second; cases second

private def selected (unused : Core.Ty) : TypedRuntimeArgument := ⟨.sum .unit unused,.inLeft unused .unit,.inLeft .unit⟩
private def selectedRight (unused : Core.Ty) (arg : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.sum unused arg.type,.inRight unused arg.value,.inRight arg.valueTyped⟩
theorem right_selected_sum_preserves_exact_actual_argument_and_store_validation
    (world : Core.StoreTyping) (store : Core.Store) (unused : Core.Ty) (arg : TypedRuntimeArgument) :
    validateRuntimeInputs world [selectedRight unused arg] store = true ↔
      validateRuntimeInputs world [arg] store = true := by
  rw [validateRuntimeInputs_iff,validateRuntimeInputs_iff]
  simp only [List.mem_singleton,forall_eq]
  constructor
  · rintro ⟨typed,stored⟩
    cases typed with | inRight payload => exact ⟨payload,stored⟩
  · rintro ⟨typed,stored⟩
    exact ⟨.inRight typed,stored⟩

theorem nominal_and_function_tags_in_unused_positions_do_not_reject_arguments
    (nominal : Core.DataTypeId) (signature : Core.Ty) :
    validateRuntimeInputs [] [selected (.namedData nominal),selected (.function signature (.namedData nominal)),
      identity (.namedData nominal) [],identity (.function signature (.namedData nominal)) []] [] = true := by
  apply validateRuntimeInputs_iff.mpr
  refine ⟨?_,.nil⟩
  intro arg member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · exact .inLeft .unit
  · exact .inLeft .unit
  · exact .closure .nil (.var rfl)
  · exact .closure .nil (.var rfl)

theorem unselected_nominal_is_an_argument_but_not_a_cell_payload (nominal : Core.DataTypeId) :
    validateRuntimeInputs [] [selected (.namedData nominal)] [] = true ∧
    validateRuntimeInputs [.sum .unit (.namedData nominal)] [] [.inLeft (.namedData nominal) .unit] = false := by
  refine ⟨acceptsSingle (.inLeft .unit) .nil,?_⟩
  cases checked : validateRuntimeInputs [.sum .unit (.namedData nominal)] [] [.inLeft (.namedData nominal) .unit] with
  | false => rfl
  | true =>
      obtain ⟨_,_,payload,_⟩ := (validateRuntimeInputs_iff.mp checked).2.lookup (location := 0) rfl
      cases payload with | sum _ right => cases right

private def forged : Core.Value := .closure .word .word (.bool false) []
theorem a_correct_raw_tag_and_empty_captures_do_not_make_a_typed_argument :
    forged.type = .function .word .word ∧
    (¬ Core.ValueHasType forged (.function .word .word)) ∧
    (¬ ∃ argument : TypedRuntimeArgument, argument.value = forged) ∧
    Core.runStateful 6 (.initial (.apply (.var 0) (.word Core.Word.zero)) [forged] []) = .done (.bool false) [] := by
  have untyped : ¬ Core.ValueHasType forged (.function .word .word) := by
    intro typed
    cases typed with | closure _ body => cases body
  refine ⟨rfl,untyped,?_,rfl⟩
  rintro ⟨argument,same⟩
  have tag := argument.valueTyped.type_eq
  rw [same] at tag
  have typed := argument.valueTyped
  rw [same,← tag] at typed
  exact untyped typed

theorem host_tags_and_unused_host_captures_cannot_bypass_structural_evidence (host : Core.HostFunction) :
    (Core.Value.hostFunction host).type = host.functionType ∧
    (¬ ∃ argument : TypedRuntimeArgument, argument.value = .hostFunction host) ∧
    ¬ ∃ argument : TypedRuntimeArgument,
      argument.value = .closure .unit .unit (.var 0) [.hostFunction host] := by
  refine ⟨rfl,?_,?_⟩
  · rintro ⟨argument,same⟩
    have typed := argument.valueTyped
    rw [same] at typed
    cases typed
  · rintro ⟨argument,same⟩
    have typed := argument.valueTyped
    rw [same] at typed
    have tag := typed.type_eq
    change .function .unit .unit = argument.type at tag
    rw [← tag] at typed
    cases typed with | closure captured _ => cases captured with | cons head _ => cases head

end Tests.FrontendRuntimeInputReferenceValidation
