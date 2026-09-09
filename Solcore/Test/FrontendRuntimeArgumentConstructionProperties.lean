import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Frontend.RuntimeInputValidation
import Solcore.Frontend.RecursiveComputationFunction

/-! Public construction preserves original records, list order and all existing
entry results. Structural acceptance alone never supplies an allocated world. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeArgumentConstruction
open Solcore Solcore.Frontend

theorem every_existing_record_is_reconstructed (argument : TypedRuntimeArgument) :
    buildRuntimeArgument? argument.value = some argument :=
  buildRuntimeArgument?_iff.mpr rfl

theorem successful_construction_retains_the_literal_value_and_tag
    {value : Core.Value} {argument : TypedRuntimeArgument}
    (built : buildRuntimeArgument? value = some argument) :
    argument.value = value ∧ argument.type = value.type := by
  have same := buildRuntimeArgument?_iff.mp built
  exact ⟨same,by rw [← same]; exact argument.valueTyped.type_eq.symm⟩

theorem every_structurally_typed_original_value_has_its_exact_record
    {value : Core.Value} {type : Core.Ty} (typed : Core.ValueHasType value type) :
    ∃ argument, buildRuntimeArgument? value = some argument ∧
      argument.value = value ∧ argument.type = type :=
  ⟨⟨type,value,typed⟩,buildRuntimeArgument?_iff.mpr rfl,rfl,rfl⟩

theorem absence_is_exactly_the_lack_of_structural_evidence (value : Core.Value) :
    buildRuntimeArgument? value = none ↔ ¬ ∃ type, Core.ValueHasType value type := by
  constructor
  · intro absent ⟨type,typed⟩
    have built := (buildRuntimeArgument?_iff (argument := ⟨type,value,typed⟩)).mpr rfl
    rw [absent] at built
    cases built
  · intro untyped
    cases built : buildRuntimeArgument? value with
    | none => rfl
    | some argument =>
        have same := buildRuntimeArgument?_iff.mp built
        exact False.elim (untyped ⟨argument.type,same ▸ argument.valueTyped⟩)

theorem ordered_list_construction_preserves_every_exact_record
    (values : List Core.Value) (arguments : List TypedRuntimeArgument) :
    values.mapM buildRuntimeArgument? = some arguments ↔
      arguments.map (·.value) = values := by
  induction values generalizing arguments with
  | nil => cases arguments <;> simp
  | cons value rest ih =>
      cases arguments with
      | nil =>
          rw [List.mapM_cons]
          change ((buildRuntimeArgument? value).bind fun head =>
            (rest.mapM buildRuntimeArgument?).bind fun others => some (head :: others)) = some [] ↔ _
          simp only [Option.bind_eq_some_iff,Option.some.injEq,List.cons_ne_nil,
            and_false,exists_false,List.map_nil]
          simp
      | cons argument tail =>
          rw [List.mapM_cons]
          change ((buildRuntimeArgument? value).bind fun head =>
            (rest.mapM buildRuntimeArgument?).bind fun others => some (head :: others)) = some (argument :: tail) ↔ _
          simp only [Option.bind_eq_some_iff,Option.some.injEq,List.map_cons,List.cons.injEq]
          constructor
          · rintro ⟨head,built,found⟩
            rcases found with ⟨others,builtRest,same⟩
            rcases same with ⟨rfl,rfl⟩
            exact ⟨buildRuntimeArgument?_iff.mp built,ih _ |>.mp builtRest⟩
          · rintro ⟨sameHead,sameTail⟩
            exact ⟨argument,buildRuntimeArgument?_iff.mpr sameHead,tail,(ih _).mpr sameTail,rfl,rfl⟩

theorem identical_original_lists_reconstruct_once_without_reordering
    (arguments : List TypedRuntimeArgument) :
    (arguments.map (·.value)).mapM buildRuntimeArgument? = some arguments :=
  (ordered_list_construction_preserves_every_exact_record _ _).mpr rfl

theorem a_list_is_rejected_exactly_when_one_original_value_has_no_structural_type
    (values : List Core.Value) :
    values.mapM buildRuntimeArgument? = none ↔
      ∃ value ∈ values, ¬ ∃ type, Core.ValueHasType value type := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      cases built : buildRuntimeArgument? value with
      | none =>
          simp only [List.mapM_cons,built,bind,Option.bind_none,true_iff]
          exact ⟨value,by simp,(absence_is_exactly_the_lack_of_structural_evidence value).mp built⟩
      | some argument =>
          have same := buildRuntimeArgument?_iff.mp built
          have typed : ∃ type, Core.ValueHasType value type :=
            ⟨argument.type,same ▸ argument.valueTyped⟩
          cases restBuilt : rest.mapM buildRuntimeArgument? with
          | none =>
              simp only [List.mapM_cons,built,restBuilt,bind,Option.bind_some,Option.bind_none,true_iff]
              obtain ⟨item,member,bad⟩ := ih.mp restBuilt
              exact ⟨item,by simp [member],bad⟩
          | some tail =>
              simp only [List.mapM_cons,built,restBuilt,bind,Option.bind_some,pure,reduceCtorEq,false_iff]
              rintro ⟨item,member,bad⟩
              rcases List.mem_cons.mp member with rfl | member
              · exact bad typed
              · have impossible := ih.mpr ⟨item,member,bad⟩
                rw [restBuilt] at impossible
                cases impossible

theorem reconstructed_arguments_leave_existing_preparation_and_full_runner_unchanged
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (source : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    ((arguments.map (·.value)).mapM buildRuntimeArgument?).bind
        (prepareRecursiveComputationFunction? types owner source) =
      prepareRecursiveComputationFunction? types owner source arguments ∧
    ((arguments.map (·.value)).mapM buildRuntimeArgument?).bind
        (fun actual => runRecursiveComputationFunction? types owner source actual fuel store) =
      runRecursiveComputationFunction? types owner source arguments fuel store := by
  rw [identical_original_lists_reconstruct_once_without_reordering]
  exact ⟨rfl,rfl⟩

theorem construction_and_same_world_validation_have_separate_exact_conditions
    (values : List Core.Value) (arguments : List TypedRuntimeArgument)
    (world : Core.StoreTyping) (store : Core.Store) :
    (values.mapM buildRuntimeArgument? = some arguments ∧
      validateRuntimeInputs world arguments store = true) ↔
    arguments.map (·.value) = values ∧
      (∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type) ∧
      Core.StoreHasTypes world store := by
  rw [ordered_list_construction_preserves_every_exact_record,validateRuntimeInputs_iff]

theorem distinct_actual_values_never_collapse_to_the_same_constructed_record
    (first second : TypedRuntimeArgument) (different : first.value ≠ second.value) :
    buildRuntimeArgument? first.value ≠ buildRuntimeArgument? second.value := by
  rw [every_existing_record_is_reconstructed,every_existing_record_is_reconstructed]
  intro equal
  exact different (congrArg TypedRuntimeArgument.value (Option.some.inj equal))

end Tests.FrontendRuntimeArgumentConstruction
