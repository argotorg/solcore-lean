import Solcore.Resolved.RenamingProperties
import Solcore.Resolved.ScopeExtensionProperties
import Solcore.Resolved.ScopeExtensionReflectionProperties
import Solcore.Core.ExactFuelProperties
import Solcore.Core.Safety

/-! Independent ordered products: duplicate identities, untyped actual values,
and arbitrary product types are separate from successful whole checking. -/
set_option autoImplicit false
namespace Tests.ResolvedPair
open Solcore Solcore.Resolved

private def owner : DeclarationId := ⟨⟨.main, ⟨[⟨"ResolvedPair", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : LocalId := ⟨owner, index⟩
private theorem different : ident 0 ≠ ident 1 := by decide
private def spine (id : LocalId) : Nat → Expr
  | 0 => .unit
  | n + 1 => .pair (.var id) (spine id n)
private def spineCore : Nat → Core.Expr
  | 0 => .unit
  | n + 1 => .pair (.var 0) (spineCore n)
private def spineType (type : Core.Ty) : Nat → Core.Ty
  | 0 => .unit
  | n + 1 => .product type (spineType type n)
private def spineValue (value : Core.Value) : Nat → Core.Value
  | 0 => .unit
  | n + 1 => .pair value (spineValue value n)
private theorem spineLower (id : LocalId) (scope : List LocalId) (n : Nat) :
    Lowers (id :: scope) (spine id n) (spineCore n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.var .head) ih
private theorem spineTyped (id : LocalId) (context : Context) (type : Core.Ty) (n : Nat) :
    HasType ((id, type) :: context) (spine id n) (spineType type n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.var .head) ih
private theorem spineScoped (id : LocalId) (scope : List LocalId) (n : Nat) :
    WellScoped (id :: scope) (spine id n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.var (by simp)) ih
private theorem spineEval (id : LocalId) (environment : Environment) (value : Core.Value) (store : Core.Store) (n : Nat) :
    Evaluates ((id, value) :: environment) store (spine id n) (spineValue value n) store := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.var .head) ih
private theorem spineCoreEval (environment : Core.Environment) (value : Core.Value) (store : Core.Store) (n : Nat) :
    Core.Evaluates (value :: environment) store (spineCore n) (spineValue value n) store := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.var rfl) ih
private theorem spinePath (environment : Core.Environment) (value : Core.Value) (store : Core.Store) (n : Nat) :
    ∀ continuation, Core.Steps (4 * n + 1) ⟨.eval (spineCore n) (value :: environment), continuation, store⟩
      ⟨.ret (spineValue value n), continuation, store⟩ := by
  induction n with
  | zero => intro continuation; exact .cons .unit .refl
  | succ n ih =>
      intro continuation
      have path := Core.Steps.cons .enterPair (.cons (.var (index := 0) rfl) (.cons .enterPairRight
        ((ih (.pairApply value :: continuation)).trans (.cons .applyPair .refl))))
      simpa [spineCore, spineValue, Nat.mul_add, Nat.add_assoc] using path

theorem arbitrary_depth_and_types_keep_duplicate_first_match_and_exact_core
    (id : LocalId) (type hiddenType : Core.Ty) (suffix : Context) (n : Nat) :
    WellScoped (id :: id :: LocalScope.ids suffix) (spine id n) ∧
    Lowers (id :: id :: LocalScope.ids suffix) (spine id n) (spineCore n) ∧
    (spine id n).lower? (id :: id :: LocalScope.ids suffix) = some (spineCore n) ∧
    HasType ((id, type) :: (id, hiddenType) :: suffix) (spine id n) (spineType type n) ∧
    infer? ((id, type) :: (id, hiddenType) :: suffix) (spine id n) = some (spineType type n) ∧
    (spineCore n).LocalFragment :=
  ⟨spineScoped id _ n, spineLower id _ n, (spineLower id _ n).complete,
    spineTyped id _ type n, infer_complete (spineTyped id _ type n), (spineLower id [] n).localFragment⟩

theorem exact_product_typing_reflects_without_requiring_actual_values
    (id : LocalId) (type : Core.Ty) (suffix : Context) (n : Nat) :
    Core.HasType (type :: LocalScope.values suffix) (spineCore n) (spineType type n) ∧
    (HasType ((id, type) :: suffix) (spine id n) (spineType type n) ↔
      Core.HasType (type :: LocalScope.values suffix) (spineCore n) (spineType type n)) ∧
    HasType ((id, type) :: suffix) (spine id n) (spineType type n) := by
  have independent : Core.HasType (type :: LocalScope.values suffix) (spineCore n) (spineType type n) := by
    induction n with
    | zero => exact .unit
    | succ n ih => exact .pair (.var rfl) ih
  have lowered := spineLower id (LocalScope.ids suffix) n
  exact ⟨lowered.preserves_type (context := (id, type) :: suffix) (spineTyped id suffix type n),
    lowered.typing_iff (context := (id, type) :: suffix),
    lowered.reflects_type (context := (id, type) :: suffix) independent⟩

theorem arbitrary_raw_values_retain_both_stores_and_bidirectional_core_correspondence
    (id : LocalId) (value hidden result : Core.Value) (suffix : Environment) (store final : Core.Store) (n : Nat) :
    Evaluates ((id, value) :: (id, hidden) :: suffix) store (spine id n) (spineValue value n) store ∧
    Core.Evaluates (value :: hidden :: LocalScope.values suffix) store (spineCore n) (spineValue value n) store ∧
    (Evaluates ((id, value) :: (id, hidden) :: suffix) store (spine id n) result final ↔
      Core.Evaluates (value :: hidden :: LocalScope.values suffix) store (spineCore n) result final) ∧
    (Evaluates ((id, value) :: (id, hidden) :: suffix) store (spine id n) result final →
      result = spineValue value n ∧ final = store) := by
  have lowered := spineLower id (id :: LocalScope.ids suffix) n
  have evaluation := spineEval id ((id, hidden) :: suffix) value store n
  refine ⟨Evaluates.ofCore lowered (spineCoreEval _ value store n), evaluation.toCore lowered,
    lowered.evaluates_iff (environment := (id, value) :: (id, hidden) :: suffix), ?_⟩
  intro other
  exact ⟨(evaluation_deterministic other evaluation).1, other.store_eq⟩

theorem independently_counted_pairs_cost_four_per_node_under_any_outer_frames
    (id : LocalId) (value hidden : Core.Value) (suffix : Environment) (store : Core.Store)
    (n fuel : Nat) (continuation : List Core.Frame) :
    Lowers (id :: id :: LocalScope.ids suffix) (spine id n) (spineCore n) ∧
    Core.Steps (4 * n + 1) ⟨.eval (spineCore n) (value :: hidden :: LocalScope.values suffix), continuation, store⟩
      ⟨.ret (spineValue value n), continuation, store⟩ ∧
    (Core.runStateful fuel (Core.State.initial (spineCore n) (value :: hidden :: LocalScope.values suffix) store) =
      .done (spineValue value n) store ↔ 4 * n + 1 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (Core.State.initial (spineCore n) (value :: hidden :: LocalScope.values suffix) store) =
      .outOfFuel checkpoint) ↔ fuel < 4 * n + 1) :=
  ⟨spineLower id _ n, spinePath _ value store n continuation,
    (spinePath _ value store n []).runStateful_done_iff, (spinePath _ value store n []).runStateful_outOfFuel_iff⟩

theorem nominal_products_can_check_without_any_runtime_inhabitant (nominal : Core.DataTypeId) (n : Nat) :
    infer? [(ident 0, .namedData nominal)] (spine (ident 0) (n + 1)) = some (spineType (.namedData nominal) (n + 1)) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨infer_complete (spineTyped (ident 0) [] (.namedData nominal) _), ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem opaque_cells_closures_and_constructor_payloads_are_not_executed
    (location : Core.Location) (constructor : Core.ConstructorId) (payload captured : Core.Value)
    (store : Core.Store) (n : Nat) :
    Evaluates [(ident 0, .pair (.cellRef .word location)
      (.pair (.closure .word .bool (.var 99) [captured]) (.constructed constructor payload))),
      (ident 0, captured)] store (spine (ident 0) n)
      (spineValue (.pair (.cellRef .word location)
        (.pair (.closure .word .bool (.var 99) [captured]) (.constructed constructor payload))) n) store :=
  spineEval _ _ _ _ _

private def source : Expr := .pair (.letE (ident 1) (.var (ident 0)) (.var (ident 1))) (.var (ident 1))
private def core : Core.Expr := .pair (.letE (.var 0) (.var 0)) (.var 1)
private def scope : List LocalId := [ident 0, ident 1]
private def environment (left right : Core.Value) : Environment := [(ident 0, left), (ident 1, right)]
private theorem lowered : Lowers scope source core := .pair (.letE (.var .head) (.var .head)) (.var (.tail different .head))
private theorem typed (left right : Core.Ty) : HasType [(ident 0, left), (ident 1, right)] source (.product left right) :=
  .pair (.letE (.var .head) (.var .head)) (.var (.tail different .head))
private theorem evaluated (left right : Core.Value) (store : Core.Store) :
    Evaluates (environment left right) store source (.pair left right) store :=
  .pair (.letE (.var .head) (.var .head)) (.var (.tail different .head))
private theorem nestedPath (left right : Core.Value) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 8 ⟨.eval core [left, right], continuation, store⟩ ⟨.ret (.pair left right), continuation, store⟩ :=
  .cons .enterPair (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl)
    (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))))

theorem a_left_local_shadow_never_changes_the_original_right_environment
    (left right : Core.Value) (leftType rightType : Core.Ty) (store : Core.Store) (continuation : List Core.Frame) :
    WellScoped scope source ∧ Lowers scope source core ∧ HasType [(ident 0, leftType), (ident 1, rightType)] source (.product leftType rightType) ∧
    Evaluates (environment left right) store source (.pair left right) store ∧
    Core.Steps 8 ⟨.eval core [left, right], continuation, store⟩ ⟨.ret (.pair left right), continuation, store⟩ :=
  ⟨lowered.wellScoped, lowered, typed _ _, evaluated _ _ _, nestedPath _ _ _ _⟩

theorem a_swapped_same_typed_core_is_not_an_exact_lowering (type : Core.Ty) :
    Core.HasType [type, type] (.pair (.var 1) (.letE (.var 0) (.var 0))) (.product type type) ∧
    ¬ Lowers scope source (.pair (.var 1) (.letE (.var 0) (.var 0))) := by
  refine ⟨.pair (.var rfl) (.letE (.var rfl) (.var rfl)), ?_⟩
  intro other
  have impossible := lowered.deterministic other
  cases impossible

theorem structural_maps_need_no_injectivity_but_semantic_transport_does
    (first second mapping : LocalId → LocalId) (injective : Function.Injective mapping)
    (left right : Core.Value) (leftType rightType : Core.Ty) (store : Core.Store) :
    (source.renameIds first).renameIds second = source.renameIds (second ∘ first) ∧
    source.renameIds id = source ∧
    (source.renameIds mapping).lower? (scope.map mapping) = some core ∧
    infer? (LocalScope.mapIds mapping [(ident 0, leftType), (ident 1, rightType)]) (source.renameIds mapping) = some (.product leftType rightType) ∧
    (Evaluates (LocalScope.mapIds mapping (environment left right)) store (source.renameIds mapping) (.pair left right) store ↔
      Evaluates (environment left right) store source (.pair left right) store) ∧
    Evaluates (LocalScope.mapIds mapping (environment left right)) store (source.renameIds mapping) (.pair left right) store :=
  ⟨source.renameIds_comp first second, source.renameIds_id,
    (Expr.lower?_renameIds mapping injective source scope).trans lowered.complete,
    (infer?_renameIds mapping injective _ source).trans (infer_complete (typed _ _)),
    evaluates_renameIds_iff mapping injective, (evaluates_renameIds_iff mapping injective).mpr (evaluated _ _ _)⟩

theorem collapsing_two_identities_really_changes_the_ordered_pair (store : Core.Store) :
    Evaluates (environment (.bool true) (.bool false)) store source (.pair (.bool true) (.bool false)) store ∧
    Evaluates (LocalScope.mapIds (fun _ => ident 0) (environment (.bool true) (.bool false))) store
      (source.renameIds (fun _ => ident 0)) (.pair (.bool true) (.bool true)) store ∧
    ¬ Evaluates (LocalScope.mapIds (fun _ => ident 0) (environment (.bool true) (.bool false))) store
      (source.renameIds (fun _ => ident 0)) (.pair (.bool true) (.bool false)) store := by
  have collapsed : Evaluates (LocalScope.mapIds (fun _ => ident 0) (environment (.bool true) (.bool false))) store
      (source.renameIds (fun _ => ident 0)) (.pair (.bool true) (.bool true)) store :=
    .pair (.letE (.var .head) (.var .head)) (.var .head)
  refine ⟨evaluated _ _ _, collapsed, ?_⟩
  intro other
  have impossible := (evaluation_deterministic other collapsed).1
  cases impossible

private def retained : Expr := .pair (.letE (ident 2) (.var (ident 0)) (.var (ident 2))) (.var (ident 2))
private def retainedCore : Core.Expr := .pair (.letE (.var 1) (.var 0)) (.var 0)
theorem suffix_freshness_allows_the_inserted_identity_in_the_prefix_and_inner_binder
    (kept bound inserted result : Core.Value) (store final : Core.Store) :
    Lowers [ident 2, ident 2, ident 0] retained (retainedCore.weakenAt 1) ∧
    Evaluates [(ident 2, kept), (ident 2, inserted), (ident 0, bound)] store retained (.pair bound kept) store ∧
    (Evaluates [(ident 2, kept), (ident 2, inserted), (ident 0, bound)] store retained result final ↔
      Evaluates [(ident 2, kept), (ident 0, bound)] store retained result final) := by
  have fresh : ident 2 ∉ [ident 0] := by decide
  have original : Lowers [ident 2, ident 0] retained retainedCore :=
    .pair (.letE (.var (.tail (by decide) .head)) (.var .head)) (.var .head)
  have evaluation : Evaluates [(ident 2, kept), (ident 0, bound)] store retained (.pair bound kept) store :=
    .pair (.letE (.var (.tail (by decide) .head)) (.var .head)) (.var .head)
  exact ⟨Lowers.insert_fresh (kept := [ident 2]) fresh original,
    evaluation.insert_fresh (leading := [(ident 2, kept)]) fresh,
    original.wellScoped.evaluates_insert_fresh_iff (leading := [(ident 2, kept)])
      (suffix := [(ident 0, bound)]) fresh⟩

theorem fresh_head_insertion_preserves_static_and_actual_profiles_separately
    (id newId : LocalId) (different : newId ≠ id) (type insertedType : Core.Ty)
    (value inserted : Core.Value) (store : Core.Store) (n : Nat) :
    HasType [(newId, insertedType), (id, type)] (spine id n) (spineType type n) ∧
    (spine id n).lower? [newId, id] = ((spine id n).lower? [id]).map (fun core => core.weakenAt 0) ∧
    Evaluates [(newId, inserted), (id, value)] store (spine id n) (spineValue value n) store ∧
    (Evaluates [(newId, inserted), (id, value)] store (spine id n) (spineValue value n) store ↔
      Evaluates [(id, value)] store (spine id n) (spineValue value n) store) := by
  have fresh : newId ∉ [id] := by simp [different]
  exact ⟨(spineTyped id [] type n).weaken_fresh fresh insertedType,
    (spine id n).lower?_weaken_fresh (spineScoped id [] n) fresh,
    (spineEval id [] value store n).weaken_fresh fresh,
    (spineScoped id [] n).evaluates_weaken_fresh_iff (environment := [(id, value)]) fresh⟩

private def skipped : Expr := .pair (.var (ident 0)) (.ifE (.bool true) .unit (.var (ident 9)))
theorem raw_selected_pairs_can_succeed_while_whole_lowering_and_typing_fail
    (value : Core.Value) (store : Core.Store) (type : Core.Ty) :
    Evaluates [(ident 0, value)] store skipped (.pair value .unit) store ∧
    skipped.lower? [ident 0] = none ∧ infer? [(ident 0, type)] skipped = none ∧
    ¬ WellScoped [ident 0] skipped := by
  have missing : skipped.lower? [ident 0] = none := by decide
  exact ⟨.pair (.var .head) (.ifTrue .bool .unit), missing,
    by simp [infer?, LocalScope.ids, missing], Expr.lower?_eq_none_iff_not_wellScoped.mp missing⟩

theorem original_scoping_is_necessary_to_reflect_a_newly_enabled_pair
    (value : Core.Value) (store : Core.Store) :
    Evaluates [(ident 2, value)] store (.pair .unit (.var (ident 2))) (.pair .unit value) store ∧
    ¬ ∃ result final, Evaluates [] store (.pair .unit (.var (ident 2))) result final := by
  refine ⟨.pair .unit (.var .head), ?_⟩
  rintro ⟨result, final, evaluation⟩
  cases evaluation with
  | pair _ right => cases right with | var found => cases found

end Tests.ResolvedPair
