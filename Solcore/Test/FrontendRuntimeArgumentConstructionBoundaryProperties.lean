import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Frontend.RuntimeInputValidation

/-! Raw actual values precede construction. Structural acceptance checks actual
bodies/captures but neither adds type well-formedness nor establishes allocation. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeArgumentConstructionBoundary
open Solcore Solcore.Frontend

private def identity (signature : Core.Ty) (captured : Core.Environment) : Core.Value :=
  .closure signature signature (.var 0) captured
private def nested (unused signature : Core.Ty) (suffix : Core.Environment) : Nat → Core.Value → Core.Value
  | 0, value => value
  | n+1, value =>
      let inner := nested unused signature suffix n value
      .pair (.inLeft unused inner) (.inRight unused (identity signature (inner::suffix)))
private theorem environmentTyped {captured : Core.Environment}
    (typed : ∀ value ∈ captured, Core.ValueHasType value value.type) :
    Core.EnvironmentHasTypes captured (captured.map Core.Value.type) := by
  induction captured with
  | nil => exact .nil
  | cons value rest ih => exact .cons (typed value (by simp)) (ih (fun v member => typed v (by simp [member])))
private theorem nestedTyped (unused signature : Core.Ty) (suffix : Core.Environment) (depth : Nat) (value : Core.Value)
    (typed : Core.ValueHasType value value.type) (captured : ∀ v ∈ suffix, Core.ValueHasType v v.type) :
    Core.ValueHasType (nested unused signature suffix depth value) (nested unused signature suffix depth value).type := by
  induction depth with
  | zero => exact typed
  | succ depth ih => exact .pair (.inLeft ih) (.inRight (.closure (.cons ih (environmentTyped captured)) (.var rfl)))
private theorem nestedPayload {unused signature : Core.Ty} {suffix : Core.Environment} {value : Core.Value}
    (depth : Nat) {type : Core.Ty} (typed : Core.ValueHasType (nested unused signature suffix depth value) type) :
    ∃ type, Core.ValueHasType value type := by
  induction depth generalizing type with
  | zero => exact ⟨_,typed⟩
  | succ depth ih => cases typed with | pair left _ => cases left with | inLeft inner => exact ih inner
private theorem capturedLookup {definitions : Core.DataEnvironment} {captured : Core.Environment} {context : Core.Context}
    (typed : Core.EnvironmentHasTypes captured context definitions)
    {index : Nat} {value : Core.Value} (found : captured[index]? = some value) :
    ∃ type, Core.ValueHasType value type definitions := by
  induction typed using Core.EnvironmentHasTypes.rec (motive_1 := fun _ _ _ _ => True) generalizing index with
  | unit | bool | word | pair | inLeft | inRight | closure | cellRef | constructed => trivial
  | nil => simp at found
  | cons head _ _ ih => cases index with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at found; subst value; exact ⟨_,head⟩
    | succ index => exact ih (by simpa using found)
private theorem builds {value : Core.Value} (typed : Core.ValueHasType value value.type) :
    buildRuntimeArgument? value = some ⟨value.type,value,typed⟩ := buildRuntimeArgument?_iff.mpr rfl
private theorem rejects {value : Core.Value} (untyped : ∀ type, ¬ Core.ValueHasType value type) :
    buildRuntimeArgument? value = none := by
  cases checked : buildRuntimeArgument? value with
  | none => rfl
  | some argument =>
      have same := buildRuntimeArgument?_iff.mp checked
      have typed := argument.valueTyped
      rw [same] at typed
      exact False.elim (untyped _ typed)

theorem arbitrary_nested_actual_values_and_captured_suffixes_are_retained
    (unused signature : Core.Ty) (suffix : Core.Environment) (depth : Nat) (value : Core.Value)
    (typed : Core.ValueHasType value value.type) (captured : ∀ v ∈ suffix, Core.ValueHasType v v.type) :
    ∃ argument, buildRuntimeArgument? (nested unused signature suffix depth value) = some argument ∧
      argument.value = nested unused signature suffix depth value ∧ argument.type = (nested unused signature suffix depth value).type :=
  ⟨_,builds (nestedTyped unused signature suffix depth value typed captured),rfl,rfl⟩

theorem no_nested_pair_or_sum_layer_repairs_an_untypable_actual_payload
    (unused signature : Core.Ty) (suffix : Core.Environment) (depth : Nat) (value : Core.Value)
    (untyped : ∀ type, ¬ Core.ValueHasType value type) :
    buildRuntimeArgument? (nested unused signature suffix depth value) = none := by
  apply rejects
  intro type typed
  obtain ⟨type,typed⟩ := nestedPayload depth typed
  exact untyped type typed

theorem unused_invalid_captures_at_arbitrary_positions_are_rejected
    (signature : Core.Ty) (leading suffix : Core.Environment) (bad : Core.Value)
    (untyped : ∀ type, ¬ Core.ValueHasType bad type) :
    buildRuntimeArgument? (identity signature (leading ++ bad::suffix)) = none := by
  apply rejects
  intro type typed
  cases typed with
  | closure captured _ =>
      obtain ⟨type,typed⟩ := capturedLookup captured (show (leading ++ bad::suffix)[leading.length]? = some bad by simp)
      exact untyped type typed

private def forged : Core.Value := .closure .word .word (.bool false) []
private theorem forgedUntyped (type : Core.Ty) : ¬ Core.ValueHasType forged type := by
  intro typed; cases typed with | closure _ body => cases body
theorem unused_bad_closures_and_hosts_are_rejected_at_arbitrary_capture_positions
    (signature : Core.Ty) (leading suffix : Core.Environment) (host : Core.HostFunction) :
    buildRuntimeArgument? (identity signature (leading ++ forged::suffix)) = none ∧
    buildRuntimeArgument? (identity signature (leading ++ .hostFunction host::suffix)) = none := by
  exact ⟨unused_invalid_captures_at_arbitrary_positions_are_rejected signature leading suffix forged forgedUntyped,
    unused_invalid_captures_at_arbitrary_positions_are_rejected signature leading suffix (.hostFunction host)
      (by intro type typed; cases typed)⟩

theorem identical_function_tags_do_not_determine_construction_or_raw_results (word : Core.Word) :
    (identity .word []).type = forged.type ∧
    (buildRuntimeArgument? (identity .word [])).isSome = true ∧ buildRuntimeArgument? forged = none ∧
    Core.runStateful 6 (.initial (.apply (.var 0) (.word word)) [identity .word []] []) = .done (.word word) [] ∧
    Core.runStateful 6 (.initial (.apply (.var 0) (.word word)) [forged] []) = .done (.bool false) [] := by
  refine ⟨rfl,?_,rejects forgedUntyped,rfl,rfl⟩
  simp only [identity]
  rw [builds (.closure .nil (.var rfl))]; rfl

private def unbound : Core.Value := .closure .unit .unit (.var 1) []
theorem an_out_of_range_body_is_rejected_without_repairing_its_raw_fault :
    buildRuntimeArgument? unbound = none ∧
    Core.runStateful 5 (.initial (.apply (.var 0) .unit) [unbound] []) =
      .fault (.unboundVariable 1) ⟨.eval (.var 1) [.unit],[],[]⟩ := by
  refine ⟨rejects ?_,rfl⟩
  intro type typed
  cases typed with | closure captured body => cases captured with | nil => cases body with | var found => cases found

theorem nominal_signatures_are_accepted_without_typing_a_rebuilt_lambda (nominal : Core.DataTypeId) :
    (buildRuntimeArgument? (identity (.namedData nominal) [])).isSome = true ∧
    Core.infer? [] (.lambda (.namedData nominal) (.namedData nominal) (.var 0)) = none := by
  refine ⟨?_,rfl⟩
  simp only [identity]
  rw [builds (.closure .nil (.var rfl))]; rfl

theorem unselected_sum_types_are_not_extra_well_formedness_checks (unused : Core.Ty) :
    (buildRuntimeArgument? (.inLeft unused .unit)).isSome = true ∧
    (buildRuntimeArgument? (.inRight unused .unit)).isSome = true ∧
    (∀ nominal : Core.DataTypeId, Core.infer? [] (.inLeft (.namedData nominal) .unit) = none ∧
      Core.infer? [] (.inRight (.namedData nominal) .unit) = none) := by
  refine ⟨?_,?_,fun _ => ⟨rfl,rfl⟩⟩
  · rw [builds (.inLeft .unit)]; rfl
  · rw [builds (.inRight .unit)]; rfl

theorem structural_cell_construction_does_not_assert_any_allocation
    (element : Core.Ty) (location : Nat) (world : Core.StoreTyping) (store : Core.Store)
    (missing : world[location]? ≠ some element) :
    buildRuntimeArgument? (.cellRef element location) = some ⟨.cell element,.cellRef element location,.cellRef⟩ ∧
    validateRuntimeInputs world [⟨.cell element,.cellRef element location,.cellRef⟩] store = false := by
  refine ⟨builds .cellRef,?_⟩
  cases checked : validateRuntimeInputs world [⟨.cell element,.cellRef element location,.cellRef⟩] store with
  | false => rfl
  | true =>
      have typed := (validateRuntimeInputs_iff.mp checked).1 _ (List.mem_singleton_self _)
      cases typed with | cellRef found => exact False.elim (missing found)

theorem hosts_and_empty_definition_constructors_are_rejected_with_actual_payloads
    (host : Core.HostFunction) (constructor : Core.ConstructorId) (payload : Core.Value) :
    buildRuntimeArgument? (.hostFunction host) = none ∧ buildRuntimeArgument? (.constructed constructor payload) = none := by
  constructor
  · apply rejects; intro type typed; cases typed
  · apply rejects; intro type typed; cases typed with | constructed found _ => cases found

theorem actual_captured_order_not_only_capture_tags_controls_body_typing (word : Core.Word) (b : Bool) :
    (buildRuntimeArgument? (.closure .unit .word (.var 2) [.bool b,.word word])).isSome = true ∧
    buildRuntimeArgument? (.closure .unit .word (.var 2) [.word word,.bool b]) = none ∧
    Core.runStateful 6 (.initial (.apply (.var 0) .unit) [.closure .unit .word (.var 2) [.bool b,.word word]] []) = .done (.word word) [] ∧
    Core.runStateful 6 (.initial (.apply (.var 0) .unit) [.closure .unit .word (.var 2) [.word word,.bool b]] []) = .done (.bool b) [] := by
  refine ⟨?_,rejects ?_,rfl,rfl⟩
  · rw [builds (.closure (.cons .bool (.cons .word .nil)) (.var rfl))]; rfl
  · intro type typed
    cases typed with | closure captured body => cases captured with | cons first tail => cases first with | word =>
      cases tail with | cons second rest => cases second with | bool => cases rest with | nil =>
        cases body with | var found => cases found

private def projected (value : Core.Value) : Option (Core.Value × Core.Ty) :=
  (buildRuntimeArgument? value).map (fun argument => (argument.value,argument.type))
theorem literal_boundary_computations_use_only_the_public_builder :
    projected (nested (.namedData ⟨77⟩) (.namedData ⟨88⟩) [.cellRef .word 700] 2 (.word Core.Word.zero)) =
      some (nested (.namedData ⟨77⟩) (.namedData ⟨88⟩) [.cellRef .word 700] 2 (.word Core.Word.zero),
        (nested (.namedData ⟨77⟩) (.namedData ⟨88⟩) [.cellRef .word 700] 2 (.word Core.Word.zero)).type) ∧
    projected forged = none ∧ projected unbound = none ∧
    projected (identity .unit [.bool true,forged,.unit]) = none ∧
    projected (.hostFunction .storageRead) = none ∧
    projected (identity .unit [.word Core.Word.zero,.hostFunction .storageRead,.bool false]) = none ∧
    projected (.constructed ⟨⟨3⟩,7⟩ .unit) = none ∧
    projected (.cellRef .word 700) = some (.cellRef .word 700,.cell .word) := by
  decide +kernel

end Tests.FrontendRuntimeArgumentConstructionBoundary
