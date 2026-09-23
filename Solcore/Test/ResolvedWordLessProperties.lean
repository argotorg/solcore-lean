import Solcore.Resolved.Renaming
import Solcore.Resolved.Scope
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Frontend.LocalFunctionApplication

/-! Independent consumers use only the two original named operands. Positional
Core bindings introduce no LocalIds, even with duplicate identities, nested
shadowing, or comparison of one named value with itself. -/

set_option autoImplicit false

namespace Tests.ResolvedWordLess

open Solcore Solcore.Resolved

private def owner : DeclarationId := ⟨⟨.main, ⟨[⟨"IdentityFreeLess", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : LocalId := ⟨owner, index⟩
private def scope : List LocalId := [ident 0, ident 1]
private def context : Context := [(ident 0, .word), (ident 1, .word)]
private def environment (left right : Core.Word) : Environment := [(ident 0, .word left), (ident 1, .word right)]
private def source : Expr := .wordLt (.var (ident 0)) (.var (ident 1))
private def core : Core.Expr := .letE (.var 0) (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1)))
private theorem different : ident 0 ≠ ident 1 := by decide
private theorem fresh : ident 2 ∉ scope := by decide
private theorem scopeValid : WellScoped scope source := .wordLt (.var (by decide)) (.var (by decide))
private theorem lowered : Lowers scope source core := by
  simpa [source, core, Core.Expr.wordLt_expansion, Core.Expr.weakenAt] using
    (Lowers.wordLt (Lowers.var .head) (Lowers.var (.tail different .head)) :
      Lowers scope source ((Core.Expr.var 0).wordLt (.var 1)))
private theorem typed : HasType context source .bool := .wordLt (.var .head) (.var (.tail different .head))
private theorem evaluated (left right : Core.Word) (store : Core.Store) :
    Evaluates (environment left right) store source (.bool (decide (left < right))) store :=
  .wordLt (.var .head) (.var (.tail different .head))
private theorem coreEvaluated (left right : Core.Word) (store : Core.Store) :
    Core.Evaluates [.word left, .word right] store core (.bool (decide (left < right))) store :=
  .letE (.var rfl) (.letE (.var rfl) (.binary (.var rfl) (.var rfl) rfl))

theorem exact_lowering_keeps_both_original_positions_without_named_temporaries :
    source = .wordLt (.var (ident 0)) (.var (ident 1)) ∧ WellScoped scope source ∧
    Lowers scope source core ∧ source.lower? scope = some core ∧ core.LocalFragment ∧
    HasType context source .bool ∧ infer? context source = some .bool :=
  ⟨rfl, scopeValid, lowered, lowered.complete, lowered.localFragment, typed, infer_complete typed⟩

theorem independent_type_correspondence_preserves_and_reflects_bool :
    Core.HasType [.word, .word] core .bool ∧
    (HasType context source .bool ↔ Core.HasType [.word, .word] core .bool) ∧
    HasType context source .bool := by
  have independent : Core.HasType [.word, .word] core .bool :=
    .letE (.var rfl) (.letE (.var rfl) (.binary (.var rfl) (.var rfl)))
  exact ⟨lowered.preserves_type (context := context) typed,
    lowered.typing_iff (context := context), lowered.reflects_type (context := context) independent⟩

theorem arbitrary_actual_words_and_nonempty_stores_have_bidirectional_core_correspondence
    (left right : Core.Word) (store : Core.Store) :
    Evaluates (environment left right) (.unit :: store) source (.bool (decide (left < right))) (.unit :: store) ∧
    Core.Evaluates [.word left, .word right] (.unit :: store) core
      (.bool (decide (left < right))) (.unit :: store) ∧
    (Evaluates (environment left right) (.unit :: store) source (.bool (decide (left < right))) (.unit :: store) ↔
      Core.Evaluates [.word left, .word right] (.unit :: store) core
        (.bool (decide (left < right))) (.unit :: store)) :=
  ⟨Evaluates.ofCore lowered (coreEvaluated left right (.unit :: store)),
    (evaluated left right (.unit :: store)).toCore lowered,
    lowered.evaluates_iff (environment := environment left right)⟩

theorem equal_strict_and_reversed_unsigned_words_use_boolean_results
    (left right : Core.Word) (ordered : left < right) (store : Core.Store) :
    Evaluates (environment left left) store source (.bool false) store ∧
    Evaluates (environment left right) store source (.bool true) store ∧
    Evaluates (environment right left) store source (.bool false) store := by
  have reversed : ¬right < left := Nat.not_lt.mpr (Nat.le_of_lt ordered)
  exact ⟨by simpa using evaluated left left store, by simpa [ordered] using evaluated left right store,
    by simpa [reversed] using evaluated right left store⟩

theorem every_evaluation_recovers_the_unique_value_and_original_store
    (left right : Core.Word) (store finalStore : Core.Store) (value : Core.Value)
    (evaluation : Evaluates (environment left right) store source value finalStore) :
    value = .bool (decide (left < right)) ∧ finalStore = store :=
  ⟨(evaluation_deterministic evaluation (evaluated left right store)).1, evaluation.store_eq⟩

private def nestedRight : Expr := .letE (ident 0) (.var (ident 1))
  (.letE (ident 0) (.var (ident 0)) (.var (ident 0)))
private def nestedSource : Expr := .wordLt (.var (ident 0)) nestedRight
private def nestedCore : Core.Expr := .letE (.var 0)
  (.letE (.letE (.var 2) (.letE (.var 0) (.var 0))) (.binary .wordGt (.var 0) (.var 1)))

theorem repeated_inner_binders_shadow_an_outer_operand_without_capturing_it
    (left right : Core.Word) (store : Core.Store) :
    WellScoped scope nestedSource ∧ Lowers scope nestedSource nestedCore ∧
    HasType context nestedSource .bool ∧
    Evaluates (environment left right) store nestedSource (.bool (decide (left < right))) store := by
  have rightLowered : Lowers scope nestedRight (.letE (.var 1) (.letE (.var 0) (.var 0))) :=
    .letE (.var (.tail different .head)) (.letE (.var .head) (.var .head))
  have rightTyped : HasType context nestedRight .word :=
    .letE (.var (.tail different .head)) (.letE (.var .head) (.var .head))
  have rightEvaluated : Evaluates (environment left right) store nestedRight (.word right) store :=
    .letE (.var (.tail different .head)) (.letE (.var .head) (.var .head))
  refine ⟨.wordLt (.var (by decide)) (.letE (.var (by decide))
    (.letE (.var (by simp)) (.var (by simp)))), ?_, .wordLt (.var .head) rightTyped,
    .wordLt (.var .head) rightEvaluated⟩
  simpa [scope, nestedSource, nestedCore, Core.Expr.wordLt_expansion, Core.Expr.weakenAt] using
    Lowers.wordLt (Lowers.var .head) rightLowered

theorem duplicate_scope_entries_keep_nearest_lookup_in_both_original_operands
    (left hidden right : Core.Word) (store : Core.Store) :
    Lowers [ident 0, ident 0, ident 1] source
      ((Core.Expr.var 0).wordLt (.var 2)) ∧
    HasType [(ident 0, .word), (ident 0, .bool), (ident 1, .word)] source .bool ∧
    Evaluates [(ident 0, .word left), (ident 0, .word hidden), (ident 1, .word right)] store
      source (.bool (decide (left < right))) store :=
  ⟨.wordLt (.var .head) (.var (.tail different (.tail different .head))),
    .wordLt (.var .head) (.var (.tail different (.tail different .head))),
    .wordLt (.var .head) (.var (.tail different (.tail different .head)))⟩

theorem comparison_of_one_identity_with_itself_needs_no_freshness_or_distinctness
    (word hidden : Core.Word) (store : Core.Store) :
    WellScoped [ident 0, ident 0] (.wordLt (.var (ident 0)) (.var (ident 0))) ∧
    Lowers [ident 0, ident 0] (.wordLt (.var (ident 0)) (.var (ident 0)))
      ((Core.Expr.var 0).wordLt (.var 0)) ∧
    Evaluates [(ident 0, .word word), (ident 0, .word hidden)] store
      (.wordLt (.var (ident 0)) (.var (ident 0))) (.bool false) store := by
  refine ⟨.wordLt (.var (by simp)) (.var (by simp)), .wordLt (.var .head) (.var .head), ?_⟩
  simpa using (Evaluates.wordLt (.var .head) (.var .head) :
    Evaluates [(ident 0, .word word), (ident 0, .word hidden)] store
      (.wordLt (.var (ident 0)) (.var (ident 0))) (.bool (decide (word < word))) store)

theorem structural_renaming_laws_allow_arbitrary_even_collapsing_maps
    (first second : LocalId → LocalId) :
    source.renameIds first = .wordLt (.var (first (ident 0))) (.var (first (ident 1))) ∧
    source.renameIds id = source ∧
    (source.renameIds first).renameIds second = source.renameIds (second ∘ first) ∧
    source.renameIds (fun _ => ident 0) = .wordLt (.var (ident 0)) (.var (ident 0)) :=
  ⟨rfl, source.renameIds_id, source.renameIds_comp first second, rfl⟩

theorem injective_semantic_renaming_keeps_exact_core_type_and_ordered_evaluation
    (mapping : LocalId → LocalId) (injective : Function.Injective mapping)
    (left right : Core.Word) (store : Core.Store) :
    (source.renameIds mapping).lower? (scope.map mapping) = some core ∧
    HasType (LocalScope.mapIds mapping context) (source.renameIds mapping) .bool ∧
    Evaluates (LocalScope.mapIds mapping (environment left right)) store (source.renameIds mapping)
      (.bool (decide (left < right))) store :=
  ⟨(Expr.lower?_renameIds mapping injective source scope).trans lowered.complete,
    (typing_renameIds_iff mapping injective).mpr typed,
    (evaluates_renameIds_iff mapping injective).mpr (evaluated left right store)⟩

theorem fresh_outer_insertion_preserves_lowering_typing_and_reflects_evaluation
    (inserted : Core.Value) (insertedType : Core.Ty) (left right : Core.Word)
    (store finalStore : Core.Store) (value : Core.Value) :
    Lowers (ident 2 :: scope) source (core.weakenAt 0) ∧
    HasType ((ident 2, insertedType) :: context) source .bool ∧
    Evaluates ((ident 2, inserted) :: environment left right) store source (.bool (decide (left < right))) store ∧
    (Evaluates ((ident 2, inserted) :: environment left right) store source value finalStore ↔
      Evaluates (environment left right) store source value finalStore) :=
  ⟨lowered.weaken_fresh fresh, typed.weaken_fresh fresh insertedType,
    (evaluated left right store).weaken_fresh fresh,
    scopeValid.evaluates_weaken_fresh_iff (environment := environment left right) fresh⟩

theorem actual_lowered_operand_paths_cost_eleven_with_the_outer_continuation_retained
    (left right : Core.Word) (store : Core.Store) (continuation : List Core.Frame) :
    Lowers scope source core ∧ Core.Steps 11
      ⟨.eval core [.word left, .word right], continuation, store⟩
      ⟨.ret (.bool (decide (left < right))), continuation, store⟩ := by
  have leftPath : ∀ frames, Core.Steps 1 ⟨.eval (.var 0) [.word left, .word right], frames, store⟩
      ⟨.ret (.word left), frames, store⟩ := fun _ => .cons (.var rfl) .refl
  have rightPath : ∀ frames, Core.Steps 1 ⟨.eval (.var 1) [.word left, .word right], frames, store⟩
      ⟨.ret (.word right), frames, store⟩ := fun _ => .cons (.var rfl) .refl
  refine ⟨lowered, ?_⟩
  simpa [core, Core.Expr.wordLt_expansion, Core.Expr.weakenAt] using
    Frontend.CostStepComposition.wordLt_of_local_right leftPath rightPath .var continuation

end Tests.ResolvedWordLess
