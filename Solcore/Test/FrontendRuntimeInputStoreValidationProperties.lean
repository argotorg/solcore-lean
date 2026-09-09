import Solcore.Frontend.RuntimeInputValidation

/-! Whole-store validation checks every supplied row, independently of which
cells the arguments reference. Arguments and cell payloads have different limits. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeInputStoreValidation
open Solcore Solcore.Frontend

private theorem rejected {world : Core.StoreTyping} {store : Core.Store}
    (arguments : List TypedRuntimeArgument) (invalid : ¬ Core.StoreHasTypes world store) :
    validateRuntimeInputs world arguments store = false := by
  cases checked : validateRuntimeInputs world arguments store with
  | false => rfl
  | true => exact False.elim (invalid (validateRuntimeInputs_iff.mp checked).2)

theorem empty_arguments_still_validate_exactly_the_whole_store
    (world : Core.StoreTyping) (store : Core.Store) :
    validateRuntimeInputs world [] store = true ↔ Core.StoreHasTypes world store := by
  constructor
  · exact fun checked => (validateRuntimeInputs_iff.mp checked).2
  · intro stored; exact validateRuntimeInputs_iff.mpr ⟨by simp, stored⟩

theorem acceptance_checks_every_cell_even_when_unreferenced
    {world : Core.StoreTyping} {arguments : List TypedRuntimeArgument} {store : Core.Store}
    (accepted : validateRuntimeInputs world arguments store = true) :
    world.length = store.length ∧
    ∀ {location type}, world[location]? = some type →
      ∃ value, store.read? location = some value ∧ Core.CellPayload type ∧ Core.ValueHasType value type := by
  have stored := (validateRuntimeInputs_iff.mp accepted).2
  exact ⟨stored.length_eq, stored.lookup⟩

theorem all_original_arguments_survive_an_allowed_extra_cell
    {world : Core.StoreTyping} {arguments : List TypedRuntimeArgument} {store : Core.Store}
    (accepted : validateRuntimeInputs world arguments store = true)
    {type : Core.Ty} {value : Core.Value} (payload : Core.CellPayload type)
    (typed : Core.ValueHasType value type) :
    validateRuntimeInputs (world ++ [type]) arguments (store ++ [value]) = true := by
  obtain ⟨args, stored⟩ := validateRuntimeInputs_iff.mp accepted
  exact validateRuntimeInputs_iff.mpr ⟨fun argument member =>
    (args argument member).weaken ⟨[type], rfl⟩, stored.allocate payload typed⟩

theorem an_unused_wrong_last_cell_rejects_arbitrary_original_arguments
    {world : Core.StoreTyping} {store : Core.Store} (stored : Core.StoreHasTypes world store)
    (arguments : List TypedRuntimeArgument) (b : Bool) :
    validateRuntimeInputs (world ++ [.word]) arguments (store ++ [.bool b]) = false := by
  apply rejected arguments
  intro allCells
  obtain ⟨value, found, _, typed⟩ := allCells.lookup (location := world.length) (elementType := .word) (by simp)
  have same : value = .bool b := by
    simpa only [Core.Store.read?, stored.length_eq, List.getElem?_concat_length, Option.some.injEq] using found.symm
  subst value; cases typed

theorem matching_prefixes_do_not_allow_extra_world_or_store_rows
    {world : Core.StoreTyping} {store : Core.Store} (stored : Core.StoreHasTypes world store)
    (arguments : List TypedRuntimeArgument) (type : Core.Ty) (value : Core.Value) :
    validateRuntimeInputs (world ++ [type]) arguments store = false ∧
    validateRuntimeInputs world arguments (store ++ [value]) = false := by
  constructor
  · apply rejected arguments; intro full
    have mismatch := full.length_eq; simp [stored.length_eq] at mismatch
  · apply rejected arguments; intro full
    have mismatch := full.length_eq; simp [stored.length_eq] at mismatch

private def rowType : Core.Ty := .product (.sum .word .bool) (.sum .unit (.product .word .bool))
private def row (left right : Core.Word) (b : Bool) : Core.Value :=
  .pair (.inLeft .bool (.word left)) (.inRight .unit (.pair (.word right) (.bool b)))
private def rowReference : TypedRuntimeArgument := ⟨.cell rowType,.cellRef rowType 0,.cellRef⟩
private theorem rowTyped (left right : Core.Word) (b : Bool) : Core.ValueHasType (row left right b) rowType :=
  .pair (.inLeft .word) (.inRight (.pair .word .bool))
private theorem rowPayload : Core.CellPayload rowType :=
  .product (.sum .word .bool) (.sum .unit (.product .word .bool))

theorem nested_pairs_and_both_selected_sum_payloads_are_accepted (left right : Core.Word) (b : Bool) :
    validateRuntimeInputs [rowType,.unit] [rowReference] [row left right b,.unit] = true ∧
    Core.StoreHasTypes [rowType,.unit] [row left right b,.unit] ∧
    Core.RuntimeValueHasType [rowType,.unit] rowReference.value rowReference.type := by
  have independentlyStored : Core.StoreHasTypes [rowType,.unit] [row left right b,.unit] :=
    (Core.StoreHasTypes.nil.allocate rowPayload (rowTyped left right b)).allocate .unit .unit
  have checked : validateRuntimeInputs [rowType,.unit] [rowReference] [row left right b,.unit] = true :=
    validateRuntimeInputs_iff.mpr ⟨by intro argument member; simp only [List.mem_singleton] at member; subst argument; exact .cellRef rfl, independentlyStored⟩
  exact ⟨checked,independentlyStored,(validateRuntimeInputs_iff.mp checked).1 rowReference (by simp)⟩

private def leftArgument (unselected : Core.Ty) : TypedRuntimeArgument :=
  ⟨.sum .unit unselected,.inLeft unselected .unit,.inLeft .unit⟩
private def rightArgument (unselected : Core.Ty) : TypedRuntimeArgument :=
  ⟨.sum unselected .unit,.inRight unselected .unit,.inRight .unit⟩

theorem unselected_argument_types_do_not_relax_either_cell_sum_branch (unselected : Core.Ty) :
    validateRuntimeInputs [] [leftArgument unselected,rightArgument unselected] [] = true ∧
    (validateRuntimeInputs [.sum .unit unselected] [] [(leftArgument unselected).value] = true ↔ Core.CellPayload unselected) ∧
    (validateRuntimeInputs [.sum unselected .unit] [] [(rightArgument unselected).value] = true ↔ Core.CellPayload unselected) := by
  refine ⟨validateRuntimeInputs_iff.mpr ⟨?_, .nil⟩, ?_, ?_⟩
  · intro argument member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact .inLeft .unit
    · exact .inRight .unit
  · constructor
    · intro checked
      obtain ⟨_,_,payload,_⟩ := (validateRuntimeInputs_iff.mp checked).2.lookup (location := 0) rfl
      cases payload with | sum _ selected => exact selected
    · intro allowed
      exact validateRuntimeInputs_iff.mpr ⟨by simp,Core.StoreHasTypes.nil.allocate (.sum .unit allowed) (.inLeft .unit)⟩
  · constructor
    · intro checked
      obtain ⟨_,_,payload,_⟩ := (validateRuntimeInputs_iff.mp checked).2.lookup (location := 0) rfl
      cases payload with | sum selected _ => exact selected
    · intro allowed
      exact validateRuntimeInputs_iff.mpr ⟨by simp,Core.StoreHasTypes.nil.allocate (.sum allowed .unit) (.inRight .unit)⟩

theorem function_reference_and_nominal_unselected_types_are_argument_only :
    validateRuntimeInputs [] [leftArgument (.function .unit .unit),rightArgument (.cell .word),
      leftArgument (.namedData ⟨77⟩)] [] = true ∧
    validateRuntimeInputs [.sum .unit (.function .unit .unit)] [] [(leftArgument (.function .unit .unit)).value] = false ∧
    validateRuntimeInputs [.sum (.cell .word) .unit] [] [(rightArgument (.cell .word)).value] = false ∧
    validateRuntimeInputs [.sum .unit (.namedData ⟨77⟩)] [] [(leftArgument (.namedData ⟨77⟩)).value] = false :=
  ⟨by decide +kernel,rfl,rfl,rfl⟩

private def nominal : Core.Ty := .namedData ⟨77⟩
private def identityArgument : TypedRuntimeArgument :=
  ⟨.function nominal nominal,.closure nominal nominal (.var 0) [],.closure .nil (.var rfl)⟩
private def referenceArgument : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 0,.cellRef⟩

theorem actual_function_signatures_and_allocated_references_are_not_cell_payloads (word : Core.Word) :
    validateRuntimeInputs [.word] [identityArgument,referenceArgument] [.word word] = true ∧
    Core.RuntimeValueHasType [.word] identityArgument.value identityArgument.type ∧
    Core.RuntimeValueHasType [.word] referenceArgument.value referenceArgument.type ∧
    validateRuntimeInputs [identityArgument.type] [] [identityArgument.value] = false ∧
    validateRuntimeInputs [referenceArgument.type] [] [referenceArgument.value] = false := by
  have checked : validateRuntimeInputs [.word] [identityArgument,referenceArgument] [.word word] = true :=
    validateRuntimeInputs_iff.mpr ⟨by
      intro argument member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact .closure .nil (.var rfl)
      · exact .cellRef rfl, Core.StoreHasTypes.nil.allocate .word .word⟩
  have arguments := (validateRuntimeInputs_iff.mp checked).1
  exact ⟨checked,arguments identityArgument (by simp),arguments referenceArgument (by simp),rfl,rfl⟩

theorem no_empty_definition_nominal_value_is_fabricated
    (world : Core.StoreTyping) (value : Core.Value) (dataType : Core.DataTypeId) :
    ¬ Core.RuntimeValueHasType world value (.namedData dataType) := by
  intro typed; cases typed with | constructed lookup _ => cases lookup

theorem literal_validation_checks_compute_without_private_helper_access :
    validateRuntimeInputs [rowType,.unit] [rowReference]
      [row (Core.Word.ofNatModulo 17) (Core.Word.ofNatModulo 9) true,.unit] = true ∧
    validateRuntimeInputs [.word] [identityArgument,referenceArgument] [.word (Core.Word.ofNatModulo 17)] = true ∧
    validateRuntimeInputs [.word,.word,.unit] [referenceArgument]
      [.word (Core.Word.ofNatModulo 17),.bool true,.unit] = false ∧
    validateRuntimeInputs [.word,.word] [] [.word (Core.Word.ofNatModulo 17)] = false ∧
    validateRuntimeInputs [.word] [] [.word (Core.Word.ofNatModulo 17),.word (Core.Word.ofNatModulo 9)] = false := by
  decide +kernel

theorem every_host_function_tag_is_function_shaped_but_never_a_stored_payload (f : Core.HostFunction) :
    (Core.Value.hostFunction f).type = .function f.parameterType f.resultType ∧
    validateRuntimeInputs [f.functionType] [] [.hostFunction f] = false ∧
    ∀ type, ¬ Core.ValueHasType (.hostFunction f) type := by
  refine ⟨rfl,rfl,?_⟩
  intro type typed; cases typed

end Tests.FrontendRuntimeInputStoreValidation
