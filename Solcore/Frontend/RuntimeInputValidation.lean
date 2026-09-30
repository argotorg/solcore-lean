import Solcore.Frontend.RuntimeParameters

/-! Opt-in checking of actual argument references and every cell in one supplied
world. Structural argument evidence already validates closure bodies/captures;
this is not a validator for unproved raw values or an automatic entry guard. -/

set_option autoImplicit false

namespace Solcore.Frontend

mutual
  private def valueReferencesValid (world : Core.StoreTyping) : Core.Value → Bool
    | .unit | .bool _ | .word _ | .integer _ => true
    | .hostFunction _ => false
    | .pair left right => valueReferencesValid world left && valueReferencesValid world right
    | .closure _ _ _ captured => environmentReferencesValid world captured
    | .inLeft _ payload | .inRight _ payload | .constructed _ payload => valueReferencesValid world payload
    | .cellRef type location => decide (world[location]? = some type)
  termination_by value => sizeOf value

  private def environmentReferencesValid (world : Core.StoreTyping) : Core.Environment → Bool
    | [] => true
    | value :: rest => valueReferencesValid world value && environmentReferencesValid world rest
  termination_by environment => sizeOf environment
end

private def storeValid : Core.StoreTyping → Core.Store → Bool
  | [], [] => true
  | type :: types, value :: values =>
      type.isCellPayload && decide (value.type = type) && storeValid types values
  | _, _ => false

/-- Validate runtime premises for the existing structurally typed arguments and
the whole supplied store, without changing either input or inferring a world. -/
def validateRuntimeInputs (world : Core.StoreTyping) (arguments : List TypedRuntimeArgument)
    (store : Core.Store) : Bool :=
  arguments.all (fun argument => valueReferencesValid world argument.value) && storeValid world store

private theorem valueReferencesValid_iff
    {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {type : Core.Ty}
    (structural : Core.ValueHasType value type definitions) :
    valueReferencesValid world value = true ↔ Core.RuntimeValueHasType world value type definitions := by
  constructor
  · induction structural using Core.ValueHasType.rec
        (motive_2 := fun environment context definitions _ =>
          environmentReferencesValid world environment = true →
            Core.RuntimeEnvironmentHasTypes world environment context definitions) with
    | unit => intro _; exact .unit
    | bool => intro _; exact .bool
    | word => intro _; exact .word
    | integer => intro _; exact .integer
    | pair _ _ leftIH rightIH =>
        intro checked
        simp only [valueReferencesValid, Bool.and_eq_true] at checked
        exact .pair (leftIH checked.1) (rightIH checked.2)
    | inLeft _ ih => intro checked; exact .inLeft (ih (by simpa only [valueReferencesValid] using checked))
    | inRight _ ih => intro checked; exact .inRight (ih (by simpa only [valueReferencesValid] using checked))
    | closure _ body ih => intro checked; exact .closure (ih (by simpa only [valueReferencesValid] using checked)) body
    | cellRef =>
        intro checked
        exact .cellRef (of_decide_eq_true (by simpa only [valueReferencesValid] using checked))
    | constructed lookup _ ih => intro checked; exact .constructed lookup (ih (by simpa only [valueReferencesValid] using checked))
    | nil => exact .nil
    | cons _ _ valueIH tailIH =>
        rename_i checked
        simp only [environmentReferencesValid, Bool.and_eq_true] at checked
        exact .cons (valueIH checked.1) (tailIH checked.2)
  · intro runtime
    clear structural
    induction runtime using Core.RuntimeValueHasType.rec
        (motive_2 := fun environment _ _ _ => environmentReferencesValid world environment = true) with
    | unit | bool | word | integer => simp only [valueReferencesValid]
    | nil => simp only [environmentReferencesValid]
    | pair _ _ leftIH rightIH => simp only [valueReferencesValid, leftIH, rightIH, Bool.and_self]
    | inLeft _ ih | inRight _ ih | constructed _ _ ih => simpa only [valueReferencesValid] using ih
    | closure _ _ ih => simpa only [valueReferencesValid] using ih
    | cellRef found => simpa only [valueReferencesValid] using decide_eq_true found
    | cons _ _ valueIH tailIH => simp only [environmentReferencesValid, valueIH, tailIH, Bool.and_self]

private theorem payload_tag_hasType {type : Core.Ty} (payload : Core.CellPayload type)
    {value : Core.Value} (tag : value.type = type) : Core.ValueHasType value type := by
  induction payload generalizing value with
  | unit => cases value <;> simp_all [Core.Value.type, Core.HostFunction.functionType]; exact .unit
  | bool => cases value <;> simp_all [Core.Value.type, Core.HostFunction.functionType]; exact .bool
  | word => cases value <;> simp_all [Core.Value.type, Core.HostFunction.functionType]; exact .word
  | integer => cases value <;> simp_all [Core.Value.type, Core.HostFunction.functionType]; exact .integer
  | product left right leftIH rightIH =>
      cases value <;> simp_all [Core.Value.type, Core.HostFunction.functionType]
      exact .pair (leftIH tag.1) (rightIH tag.2)
  | sum left right leftIH rightIH =>
      cases value <;> simp_all [Core.Value.type, Core.HostFunction.functionType]
      · rcases tag with ⟨tag, rfl⟩; exact .inLeft (leftIH tag)
      · rcases tag with ⟨rfl, tag⟩; exact .inRight (rightIH tag)

private theorem storeValid_iff {world : Core.StoreTyping} {store : Core.Store} :
    storeValid world store = true ↔ Core.StoreHasTypes world store := by
  induction world generalizing store with
  | nil =>
      cases store with
      | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
      | cons value values =>
          constructor
          · intro accepted; cases accepted
          · intro typed; have length := typed.length_eq; cases length
  | cons type types ih =>
      cases store with
      | nil =>
          constructor
          · intro accepted; cases accepted
          · intro typed; have length := typed.length_eq; cases length
      | cons value values =>
          simp only [storeValid, Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨⟨payload, tag⟩, tail⟩
            have rest := ih.mp tail
            have allowed := Core.Ty.isCellPayload_sound payload
            refine ⟨congrArg Nat.succ rest.length_eq, ?_⟩
            intro location elementType found
            cases location with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                subst elementType
                exact ⟨value, rfl, allowed, payload_tag_hasType allowed tag⟩
            | succ index => exact rest.lookup found
          · intro typed
            obtain ⟨head, found, payload, headTyped⟩ := typed.lookup (location := 0) rfl
            have same : head = value := (Option.some.inj found).symm
            subst head
            refine ⟨⟨Core.Ty.isCellPayload_complete payload, headTyped.type_eq⟩, ih.mpr ?_⟩
            refine ⟨Nat.succ.inj typed.length_eq, ?_⟩
            intro index elementType foundType
            exact typed.lookup (location := index + 1) foundType

/-- Exact runtime premises for these original typed arguments and this whole
store. The validator does not establish source preparation or structural typing. -/
theorem validateRuntimeInputs_iff {world : Core.StoreTyping}
    {arguments : List TypedRuntimeArgument} {store : Core.Store} :
    validateRuntimeInputs world arguments store = true ↔
      (∀ argument ∈ arguments, Core.RuntimeValueHasType world argument.value argument.type) ∧
        Core.StoreHasTypes world store := by
  simp only [validateRuntimeInputs, Bool.and_eq_true, List.all_eq_true, storeValid_iff]
  constructor
  · rintro ⟨checked, stored⟩
    exact ⟨fun argument member => (valueReferencesValid_iff argument.valueTyped).mp (checked argument member), stored⟩
  · rintro ⟨typed, stored⟩
    exact ⟨fun argument member => (valueReferencesValid_iff argument.valueTyped).mpr (typed argument member), stored⟩

end Solcore.Frontend
