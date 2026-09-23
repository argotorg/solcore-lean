import Solcore.Core.LocalFragment
import Solcore.Core.Safety

/-! Independent Core pairs retain original child environments and exact costs.
Static nominal types and arbitrary data definitions never supply runtime values. -/
set_option autoImplicit false
namespace Tests.CoreLocalFragmentPair
open Solcore Solcore.Core

private def nested (index : Nat) : Expr :=
  .pair (.letE (.var index) (.pair (.var 0) (.var (index + 2)))) (.var index)
private theorem nestedLocal (index : Nat) : (nested index).LocalFragment := .pair (.letE .var (.pair .var .var)) .var
private theorem nestedEval (leading suffix : Environment) (left right : Value) (store : Store) :
    Evaluates (leading ++ left :: right :: suffix) store (nested leading.length) (.pair (.pair left right) left) store := by
  have first : (leading ++ left :: right :: suffix)[leading.length]? = some left := by simp
  have second : (left :: (leading ++ left :: right :: suffix))[leading.length + 2]? = some right := by simp
  exact .pair (.letE (.var first) (.pair (.var rfl) (.var second))) (.var first)
private theorem nestedPath (leading suffix : Environment) (left right : Value) (store : Store) :
    Steps 12 (State.initial (nested leading.length) (leading ++ left :: right :: suffix) store)
      (State.final (.pair (.pair left right) left) store) := by
  have first : (leading ++ left :: right :: suffix)[leading.length]? = some left := by simp
  have second : (left :: (leading ++ left :: right :: suffix))[leading.length + 2]? = some right := by simp
  exact .cons .enterPair (.cons .enterLet (.cons (.var first) (.cons .bindLet (.cons .enterPair
    (.cons (.var rfl) (.cons .enterPairRight (.cons (.var second) (.cons .applyPair
    (.cons .enterPairRight (.cons (.var first) (.cons .applyPair .refl)))))))))))
private theorem nestedTyped (leading suffix : Context) (left right : Ty) (definitions : DataEnvironment) :
    HasType (leading ++ left :: right :: suffix) (nested leading.length) (.product (.product left right) left) definitions :=
  .pair (.letE (.var (by simp)) (.pair (.var rfl) (.var (by simp)))) (.var (by simp))

theorem pair_cost_is_the_sum_of_actual_ordered_child_paths_plus_three
    (leading suffix : Environment) (inserted leftValue rightValue : Value) (initialStore middleStore finalStore : Store)
    (left right : Expr) (leftLocal : left.LocalFragment) (rightLocal : right.LocalFragment) (leftCost rightCost : Nat)
    (leftPath : ∀ continuation, Steps leftCost ⟨.eval left (leading ++ suffix), continuation, initialStore⟩ ⟨.ret leftValue, continuation, middleStore⟩)
    (rightPath : ∀ continuation, Steps rightCost ⟨.eval right (leading ++ suffix), continuation, middleStore⟩ ⟨.ret rightValue, continuation, finalStore⟩) :
    Steps (leftCost + rightCost + 3) (State.initial (.pair left right) (leading ++ suffix) initialStore)
      (State.final (.pair leftValue rightValue) finalStore) ∧
    ∀ continuation, Steps (leftCost + rightCost + 3)
      ⟨.eval ((Expr.pair left right).weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
      ⟨.ret (.pair leftValue rightValue), continuation, finalStore⟩ := by
  have path := Steps.cons .enterPair ((leftPath [.pairRight right (leading ++ suffix)]).trans
    (.cons .enterPairRight ((rightPath [.pairApply leftValue]).trans (.cons .applyPair .refl))))
  have exactPath : Steps (leftCost + rightCost + 3) (State.initial (.pair left right) (leading ++ suffix) initialStore)
      (State.final (.pair leftValue rightValue) finalStore) := by simpa [Nat.add_assoc, State.initial, State.final] using path
  exact ⟨exactPath, fun continuation => (Expr.LocalFragment.pair leftLocal rightLocal).steps_insert leading suffix inserted exactPath continuation⟩

theorem nested_pairs_and_lets_weaken_only_original_suffix_positions (cutoff : Nat) :
    (nested cutoff).weakenAt cutoff =
      .pair (.letE (.var (cutoff + 1)) (.pair (.var 0) (.var (cutoff + 3)))) (.var (cutoff + 1)) ∧
    ((nested cutoff).weakenAt cutoff).LocalFragment := by
  exact ⟨by simp [nested, Expr.weakenAt, Nat.add_assoc], (nestedLocal cutoff).weakenAt cutoff⟩

theorem retained_prefix_evaluation_insertion_reflects_the_same_final_store
    (leading suffix : Environment) (left right inserted : Value) (store final : Store) :
    Evaluates (leading ++ inserted :: left :: right :: suffix) store
      ((nested leading.length).weakenAt leading.length) (.pair (.pair left right) left) store ∧
    (Evaluates (leading ++ inserted :: left :: right :: suffix) store
      ((nested leading.length).weakenAt leading.length) (.pair (.pair left right) left) final ↔ final = store) := by
  have shifted := ((nestedLocal leading.length).evaluates_insert_iff leading (left :: right :: suffix) inserted).mpr
    (nestedEval leading suffix left right store)
  refine ⟨shifted, ?_⟩
  constructor
  · intro evaluation
    exact (evaluation_deterministic evaluation shifted).2
  · intro same; subst final; exact shifted

theorem twelve_is_shared_before_choosing_any_outer_continuation
    (leading suffix : Environment) (left right inserted : Value) (store : Store) :
    ∃ cost, cost = 12 ∧ ∀ continuation,
      Steps cost ⟨.eval (nested leading.length) (leading ++ left :: right :: suffix), continuation, store⟩
        ⟨.ret (.pair (.pair left right) left), continuation, store⟩ ∧
      Steps cost ⟨.eval ((nested leading.length).weakenAt leading.length) (leading ++ inserted :: left :: right :: suffix), continuation, store⟩
        ⟨.ret (.pair (.pair left right) left), continuation, store⟩ := by
  obtain ⟨cost, paths⟩ := (nestedLocal leading.length).insertion_paths leading (left :: right :: suffix) inserted (nestedEval leading suffix left right store)
  have same := ((nestedPath leading suffix left right store).final_unique (paths []).1).1
  exact ⟨cost, same.symm, paths⟩

theorem closed_paths_reflect_at_arbitrary_cuts_without_comparing_checkpoint_payloads
    (leading suffix : Environment) (left right inserted result : Value) (store final : Store) (cost : Nat) (continuation : List Frame) :
    Steps 12 ⟨.eval (nested leading.length) (leading ++ left :: right :: suffix), continuation, store⟩
      ⟨.ret (.pair (.pair left right) left), continuation, store⟩ ∧
    (Steps cost (State.initial ((nested leading.length).weakenAt leading.length) (leading ++ inserted :: left :: right :: suffix) store)
      (State.final result final) ↔
      Steps cost (State.initial (nested leading.length) (leading ++ left :: right :: suffix) store) (State.final result final)) := by
  have shifted := (nestedLocal leading.length).steps_insert leading (left :: right :: suffix) inserted
    (nestedPath leading suffix left right store) []
  exact ⟨(nestedLocal leading.length).steps_reflect_insert leading (left :: right :: suffix) inserted shifted continuation,
    (nestedLocal leading.length).steps_insert_iff leading (left :: right :: suffix) inserted⟩

theorem head_insertion_and_reflection_preserve_values_and_unexecuted_outer_frames
    (left right inserted : Value) (suffix : Environment) (store : Store) (continuation : List Frame) :
    Evaluates (inserted :: left :: right :: suffix) store ((nested 0).weakenAt 0) (.pair (.pair left right) left) store ∧
    Evaluates (left :: right :: suffix) store (nested 0) (.pair (.pair left right) left) store ∧
    (Evaluates (inserted :: left :: right :: suffix) store ((nested 0).weakenAt 0) (.pair (.pair left right) left) store ↔
      Evaluates (left :: right :: suffix) store (nested 0) (.pair (.pair left right) left) store) ∧
    Steps 12 ⟨.eval ((nested 0).weakenAt 0) (inserted :: left :: right :: suffix), continuation, store⟩ ⟨.ret (.pair (.pair left right) left), continuation, store⟩ ∧
    Steps 12 ⟨.eval (nested 0) (left :: right :: suffix), continuation, store⟩ ⟨.ret (.pair (.pair left right) left), continuation, store⟩ := by
  have evaluation := (nestedEval [] suffix left right store).weakenAt_zero_localFragment (nestedLocal 0) inserted
  have path := nestedPath [] suffix left right store
  have shifted := path.weakenAt_zero_localFragment (nestedLocal 0) inserted []
  exact ⟨evaluation, evaluation.reflect_weakenAt_zero_localFragment (nestedLocal 0),
    (nestedLocal 0).evaluates_weaken_zero_iff (left :: right :: suffix) inserted,
    path.weakenAt_zero_localFragment (nestedLocal 0) inserted continuation,
    shifted.reflect_weakenAt_zero_localFragment (nestedLocal 0) continuation⟩

theorem arbitrary_static_products_and_data_definitions_survive_retained_insertion
    (leading suffix : Context) (left right inserted : Ty) (definitions : DataEnvironment) :
    HasType (leading ++ inserted :: left :: right :: suffix) ((nested leading.length).weakenAt leading.length)
      (.product (.product left right) left) definitions ∧
    HasType (leading ++ left :: right :: suffix) (nested leading.length) (.product (.product left right) left) definitions ∧
    infer? (leading ++ inserted :: left :: right :: suffix) ((nested leading.length).weakenAt leading.length) definitions =
      some (.product (.product left right) left) := by
  have shifted := ((nestedLocal leading.length).hasType_insert_iff leading (left :: right :: suffix) inserted).mpr (nestedTyped leading suffix left right definitions)
  exact ⟨shifted, ((nestedLocal leading.length).hasType_insert_iff leading (left :: right :: suffix) inserted).mp shifted,
    ((nestedLocal leading.length).infer_insert leading (left :: right :: suffix) inserted definitions).trans
      (infer_complete (nestedTyped leading suffix left right definitions))⟩

theorem static_head_insertion_reflects_exact_types_and_full_inference
    (left right inserted : Ty) (suffix : Context) (definitions : DataEnvironment) :
    HasType (inserted :: left :: right :: suffix) ((nested 0).weakenAt 0) (.product (.product left right) left) definitions ∧
    HasType (left :: right :: suffix) (nested 0) (.product (.product left right) left) definitions ∧
    (HasType (inserted :: left :: right :: suffix) ((nested 0).weakenAt 0) (.product (.product left right) left) definitions ↔
      HasType (left :: right :: suffix) (nested 0) (.product (.product left right) left) definitions) ∧
    infer? (inserted :: left :: right :: suffix) ((nested 0).weakenAt 0) definitions = some (.product (.product left right) left) := by
  have shifted := (nestedTyped [] suffix left right definitions).weakenAt_zero_localFragment (nestedLocal 0) inserted
  exact ⟨shifted, shifted.reflect_weakenAt_zero_localFragment (nestedLocal 0),
    (nestedLocal 0).hasType_weaken_zero_iff (left :: right :: suffix) inserted,
    ((nestedLocal 0).infer_weaken_zero (left :: right :: suffix) inserted definitions).trans
      (infer_complete (nestedTyped [] suffix left right definitions))⟩

theorem nominal_component_types_do_not_provide_runtime_inhabitants (nominal : DataTypeId) (inserted : Ty) :
    infer? [inserted, .namedData nominal, .word] ((nested 0).weakenAt 0) [] =
      some (.product (.product (.namedData nominal) .word) (.namedData nominal)) ∧
    ¬ ∃ value, ValueHasType value (.namedData nominal) := by
  refine ⟨(static_head_insertion_reflects_exact_types_and_full_inference (.namedData nominal) .word inserted [] []).2.2.2, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?] at found

theorem opaque_closures_cells_and_constructed_values_are_only_paired
    (location : Location) (captured : Value) (constructor : ConstructorId) (payload : Value)
    (inserted : Value) (store : Store) (continuation : List Frame) :
    Steps 12 ⟨.eval ((nested 0).weakenAt 0)
      [inserted, .closure .word .bool (.var 99) [captured], .pair (.cellRef .word location) (.constructed constructor payload)], continuation, store⟩
      ⟨.ret (.pair (.pair (.closure .word .bool (.var 99) [captured]) (.pair (.cellRef .word location) (.constructed constructor payload)))
        (.closure .word .bool (.var 99) [captured])), continuation, store⟩ :=
  (nestedPath [] [] _ _ store).weakenAt_zero_localFragment (nestedLocal 0) inserted continuation

private def missing (index : Nat) : Expr := .pair .unit (.var index)
private theorem missingLocal (index : Nat) : (missing index).LocalFragment := .pair .unit .var
theorem missing_pair_children_remain_missing_after_insertion
    (leading suffix : Environment) (inserted : Value) (store : Store) :
    ¬ ∃ result final, Evaluates (leading ++ inserted :: suffix) store
      ((missing (leading.length + suffix.length)).weakenAt leading.length) result final := by
  rintro ⟨result, final, path⟩
  have original := ((missingLocal (leading.length + suffix.length)).evaluates_insert_iff leading suffix inserted).mp path
  cases original with
  | pair _ right =>
    cases right with
    | var found => simp only [← List.length_append] at found; simp at found
theorem missing_pair_inference_is_full_none_for_arbitrary_definitions
    (leading suffix : Context) (inserted : Ty) (definitions : DataEnvironment) :
    infer? (leading ++ inserted :: suffix) ((missing (leading.length + suffix.length)).weakenAt leading.length) definitions = none := by
  rw [(missingLocal (leading.length + suffix.length)).infer_insert leading suffix inserted definitions]
  cases accepted : infer? (leading ++ suffix) (missing (leading.length + suffix.length)) definitions with
  | none => rfl
  | some type =>
    have typed := infer_sound accepted
    cases typed with
    | pair _ right =>
      cases right with
      | var found => simp only [← List.length_append] at found; simp at found

private def wrong : Expr := .pair .unit (.unary .wordNot (.bool true))
private theorem wrongLocal : wrong.LocalFragment := .pair .unit (.unary .bool)
theorem structural_pair_membership_does_not_license_wrong_primitive_children
    (leading suffix : Environment) (inserted : Value) (store : Store) (context : Context) (insertedType : Ty) (definitions : DataEnvironment) :
    wrong.LocalFragment ∧ infer? (insertedType :: context) (wrong.weakenAt 0) definitions = none ∧
    ¬ ∃ result final, Evaluates (leading ++ inserted :: suffix) store (wrong.weakenAt leading.length) result final := by
  refine ⟨wrongLocal, (wrongLocal.infer_weaken_zero context insertedType definitions).trans (by rfl), ?_⟩
  rintro ⟨result, final, path⟩
  have original := (wrongLocal.evaluates_insert_iff leading suffix inserted).mp path
  cases original with
  | pair _ right =>
    cases right with
    | unary operand applied => cases operand; cases applied

end Tests.CoreLocalFragmentPair
