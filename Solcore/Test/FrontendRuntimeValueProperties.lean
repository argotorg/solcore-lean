import Solcore.Frontend.RuntimeValueProperties

/-! These are representation tests, not value typing or operational semantics.
Every old payload, code body, tag, capture and raw store slot is retained literally;
no runtime inhabitance, validity, world, allocation or host-support premise is used. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeValue
open Solcore Solcore.Frontend

theorem all_atomic_core_constructors_preserve_arbitrary_original_payloads
    (boolean : Bool) (word : Core.Word) (host : Core.HostFunction)
    (elementType : Core.Ty) (location : Core.Location) :
    RuntimeValue.ofCore .unit=.unit ∧
    RuntimeValue.ofCore (.bool boolean)=.bool boolean ∧
    RuntimeValue.ofCore (.word word)=.word word ∧
    RuntimeValue.ofCore (.hostFunction host)=.hostFunction host ∧
    RuntimeValue.ofCore (.cellRef elementType location)=.cellRef elementType location := by
  simp [RuntimeValue.ofCore]

theorem all_composite_core_constructors_preserve_sides_tags_and_payloads
    (left right payload : Core.Value) (otherSide : Core.Ty) (constructor : Core.ConstructorId) :
    RuntimeValue.ofCore (.pair left right)=.pair (RuntimeValue.ofCore left) (RuntimeValue.ofCore right) ∧
    RuntimeValue.ofCore (.inLeft otherSide payload)=.inLeft otherSide (RuntimeValue.ofCore payload) ∧
    RuntimeValue.ofCore (.inRight otherSide payload)=.inRight otherSide (RuntimeValue.ofCore payload) ∧
    RuntimeValue.ofCore (.constructed constructor payload)=.constructed constructor (RuntimeValue.ofCore payload) := by
  simp [RuntimeValue.ofCore]

theorem core_closure_code_types_and_every_ordered_capture_remain_literal
    (parameterType resultType : Core.Ty) (body : Core.Expr) (captured : Core.Environment) :
    RuntimeValue.ofCore (.closure parameterType resultType body captured)=
      .coreClosure parameterType resultType body (captured.map RuntimeValue.ofCore) ∧
    RuntimeValue.toCore? (.coreClosure parameterType resultType body (captured.map RuntimeValue.ofCore))=
      some (.closure parameterType resultType body captured) := by
  have literal : RuntimeValue.ofCore (.closure parameterType resultType body captured)=
      .coreClosure parameterType resultType body (captured.map RuntimeValue.ofCore) := by
    simp only [RuntimeValue.ofCore,List.attach_map_val]
  exact ⟨literal,literal ▸ RuntimeValue.toCore?_ofCore _⟩

theorem roundtrip_and_exact_image_need_no_semantic_premises (old : Core.Value) (value : RuntimeValue) :
    RuntimeValue.toCore? (RuntimeValue.ofCore old)=some old ∧
    (RuntimeValue.toCore? value=some old ↔ value=RuntimeValue.ofCore old) :=
  ⟨RuntimeValue.toCore?_ofCore old,RuntimeValue.toCore?_eq_some_iff⟩

private theorem listRoundtrip (values : List Core.Value) :
    (values.map RuntimeValue.ofCore).mapM RuntimeValue.toCore?=some values := by
  induction values with
  | nil => rfl
  | cons value tail ih =>
      simp only [List.map_cons,List.mapM_cons,RuntimeValue.toCore?_ofCore,ih,bind,Option.bind_some,pure]
private theorem listReflect (values : List RuntimeValue) (cores : List Core.Value)
    (projected : values.mapM RuntimeValue.toCore?=some cores) : values=cores.map RuntimeValue.ofCore := by
  induction values generalizing cores with
  | nil =>
      have same : []=cores := Option.some.inj projected
      subst cores; rfl
  | cons value tail ih =>
      simp only [List.mapM_cons,bind,Option.bind_eq_some_iff] at projected
      obtain ⟨core,valueProjected,rest,tailProjected,same⟩ := projected
      cases Option.some.inj same
      change value::tail=RuntimeValue.ofCore core::rest.map RuntimeValue.ofCore
      rw [RuntimeValue.toCore?_eq_some_iff.mp valueProjected,ih rest tailProjected]

theorem every_original_raw_store_roundtrips_with_order_and_length
    (store : Core.Store) :
    (store.map RuntimeValue.ofCore).mapM RuntimeValue.toCore?=some store ∧
    (store.map RuntimeValue.ofCore).length=store.length :=
  ⟨listRoundtrip store,List.length_map _⟩

theorem whole_ordered_list_projection_has_exactly_the_original_list_image
    (values : List RuntimeValue) (cores : List Core.Value) :
    values.mapM RuntimeValue.toCore?=some cores ↔ values=cores.map RuntimeValue.ofCore := by
  constructor
  · exact listReflect values cores
  · intro same; rw [same]; exact listRoundtrip cores

theorem successful_projection_cannot_drop_reorder_or_replace_actual_slots
    (values : List RuntimeValue) (cores : List Core.Value)
    (projected : values.mapM RuntimeValue.toCore?=some cores) :
    values.length=cores.length ∧ ∀ index : Nat,values[index]?=(cores[index]?).map RuntimeValue.ofCore := by
  rw [listReflect values cores projected]
  exact ⟨List.length_map _,fun index => List.getElem?_map⟩

theorem embedding_distinguishes_original_values_and_ordered_raw_stores
    (left right : Core.Value) (leftStore rightStore : Core.Store) :
    (RuntimeValue.ofCore left=RuntimeValue.ofCore right ↔ left=right) ∧
    (leftStore.map RuntimeValue.ofCore=rightStore.map RuntimeValue.ofCore ↔ leftStore=rightStore) := by
  constructor
  · exact ⟨fun equal => RuntimeValue.ofCore_injective equal,congrArg RuntimeValue.ofCore⟩
  · constructor
    · intro equal
      have projected := congrArg (List.mapM RuntimeValue.toCore?) equal
      simpa only [listRoundtrip,Option.some.injEq] using projected
    · intro equal; rw [equal]

theorem arbitrary_capture_prefix_and_suffix_preserve_the_selected_middle_value
    (a b : Core.Ty) (body : Core.Expr) (leading suffix : Core.Environment) (middle : Core.Value) :
    RuntimeValue.ofCore (.closure a b body (leading++middle::suffix))=
      .coreClosure a b body (leading.map RuntimeValue.ofCore++RuntimeValue.ofCore middle::suffix.map RuntimeValue.ofCore) ∧
    RuntimeValue.toCore? (.coreClosure a b body
      (leading.map RuntimeValue.ofCore++RuntimeValue.ofCore middle::suffix.map RuntimeValue.ofCore))=
      some (.closure a b body (leading++middle::suffix)) := by
  simpa only [List.map_append,List.map_cons] using
    core_closure_code_types_and_every_ordered_capture_remain_literal a b body (leading++middle::suffix)

private def coreTree (a b otherSide : Core.Ty) (body : Core.Expr) (constructor : Core.ConstructorId)
    (value : Core.Value) : Nat → Core.Value
  | 0 => value
  | n+1 => .pair (.closure a b body [coreTree a b otherSide body constructor value n,value])
      (.constructed constructor (.inLeft otherSide (coreTree a b otherSide body constructor value n)))
private def mixedTree (a b otherSide : Core.Ty) (body : Core.Expr) (constructor : Core.ConstructorId)
    (value : Core.Value) : Nat → RuntimeValue
  | 0 => RuntimeValue.ofCore value
  | n+1 => .pair (.coreClosure a b body [mixedTree a b otherSide body constructor value n,RuntimeValue.ofCore value])
      (.constructed constructor (.inLeft otherSide (mixedTree a b otherSide body constructor value n)))
private theorem treeLiteral (a b otherSide : Core.Ty) (body : Core.Expr) (constructor : Core.ConstructorId)
    (value : Core.Value) (n : Nat) :
    RuntimeValue.ofCore (coreTree a b otherSide body constructor value n)=mixedTree a b otherSide body constructor value n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [coreTree,mixedTree,RuntimeValue.ofCore,List.attach_map_val,List.map_cons,List.map_nil,ih]

theorem arbitrary_depth_literal_capture_trees_preserve_old_code_and_data
    (a b otherSide : Core.Ty) (body : Core.Expr) (constructor : Core.ConstructorId)
    (value : Core.Value) (depth : Nat) :
    RuntimeValue.ofCore (coreTree a b otherSide body constructor value depth)=mixedTree a b otherSide body constructor value depth ∧
    RuntimeValue.toCore? (mixedTree a b otherSide body constructor value depth)=
      some (coreTree a b otherSide body constructor value depth) :=
  ⟨treeLiteral a b otherSide body constructor value depth,
    (treeLiteral a b otherSide body constructor value depth) ▸ RuntimeValue.toCore?_ofCore _⟩

end Tests.FrontendRuntimeValue
