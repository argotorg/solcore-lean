import Solcore.Resolved.RenamingProperties
import Solcore.Resolved.ScopeExtensionProperties
import Solcore.Resolved.ScopeExtensionReflectionProperties

/-! Raw ordered comparison evaluates only selected conditional branches. Whole
scope and typing checks remain stricter, and positional Core temporaries cannot
repair a missing named reference. Semantic renaming still needs injectivity. -/

set_option autoImplicit false

namespace Tests.ResolvedWordLessBoundary

open Solcore Solcore.Resolved

private def owner : DeclarationId := ⟨⟨.main, ⟨[⟨"LessBoundary", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : LocalId := ⟨owner, index⟩
private def one : Core.Word := Core.Word.ofNatModulo 1
private def scope : List LocalId := [ident 0, ident 1]
private def context : Context := [(ident 0, .word), (ident 1, .word)]
private def environment : Environment := [(ident 0, .word .zero), (ident 1, .word one)]
private theorem different : ident 0 ≠ ident 1 := by decide
private theorem fresh : ident 2 ∉ scope := by decide
private theorem ordered : decide (Core.Word.zero < one) = true := by decide

private def skippedMissing : Expr := .wordLt (.word .zero)
  (.ifE (.bool true) (.word one) (.var (ident 2)))
private def skippedBad : Expr := .wordLt (.word .zero)
  (.ifE (.bool true) (.word one) (.bool false))
private def skippedBadCore : Core.Expr := (Core.Expr.word .zero).wordLt
  (.ifE (.bool true) (.word one) (.bool false))
private def missingRight : Expr := .wordLt (.word .zero) (.var (ident 2))

private theorem missingRejected : skippedMissing.lower? scope = none := by decide
private theorem missingNotScoped : ¬WellScoped scope skippedMissing :=
  Expr.lower?_eq_none_iff_not_wellScoped.mp missingRejected
private theorem missingNotTyped (type : Core.Ty) : ¬HasType context skippedMissing type :=
  fun typing => missingNotScoped typing.wellScoped
private theorem missingEvaluated (store : Core.Store) :
    Evaluates environment store skippedMissing (.bool true) store := by
  simpa only [skippedMissing, ordered] using (Evaluates.wordLt .word (.ifTrue .bool .word) :
    Evaluates environment store skippedMissing (.bool (decide (Core.Word.zero < one))) store)
private theorem badLowered : Lowers scope skippedBad skippedBadCore :=
  .wordLt .word (.ifE .bool .word .bool)
private theorem badNotTyped (type : Core.Ty) : ¬HasType context skippedBad type := by
  intro typing
  cases typing with
  | wordLt _ right => cases right with
    | ifE _ _ wrong => cases wrong
private theorem badEvaluated (store : Core.Store) :
    Evaluates environment store skippedBad (.bool true) store := by
  simpa only [skippedBad, ordered] using (Evaluates.wordLt .word (.ifTrue .bool .word) :
    Evaluates environment store skippedBad (.bool (decide (Core.Word.zero < one))) store)
private theorem inferNone {expr : Expr} (rejected : ∀ type, ¬HasType context expr type) :
    infer? context expr = none := by
  cases inferred : infer? context expr with
  | none => rfl
  | some type => exact False.elim (rejected type (infer_sound inferred))

theorem skipped_unresolved_branch_allows_raw_success_but_rejects_whole_lowering_and_typing
    (store : Core.Store) :
    Evaluates environment store skippedMissing (.bool true) store ∧
    skippedMissing.lower? scope = none ∧ ¬WellScoped scope skippedMissing ∧
    (∀ type, ¬HasType context skippedMissing type) ∧ infer? context skippedMissing = none :=
  ⟨missingEvaluated store, missingRejected, missingNotScoped, missingNotTyped,
    inferNone missingNotTyped⟩

theorem raw_success_without_whole_scope_still_has_unique_value_and_unchanged_store
    (store finalStore : Core.Store) (value : Core.Value)
    (evaluation : Evaluates environment store skippedMissing value finalStore) :
    value = .bool true ∧ finalStore = store :=
  ⟨(evaluation_deterministic evaluation (missingEvaluated store)).1, evaluation.store_eq⟩

theorem skipped_wrong_type_lowers_and_runs_but_has_no_resolved_type
    (store : Core.Store) :
    Lowers scope skippedBad skippedBadCore ∧ skippedBad.lower? scope = some skippedBadCore ∧
    WellScoped scope skippedBad ∧ Evaluates environment store skippedBad (.bool true) store ∧
    Core.Evaluates [.word .zero, .word one] store skippedBadCore (.bool true) store ∧
    (∀ type, ¬HasType context skippedBad type) ∧ infer? context skippedBad = none :=
  ⟨badLowered, badLowered.complete, badLowered.wellScoped, badEvaluated store,
    (badEvaluated store).toCore badLowered, badNotTyped, inferNone badNotTyped⟩

private theorem noMissingEvaluation (store : Core.Store) :
    ¬∃ value finalStore, Evaluates environment store missingRight value finalStore := by
  rintro ⟨value, finalStore, evaluation⟩
  cases evaluation with
  | wordLt _ right => cases right with
    | var found =>
        have lookup := LocalScope.lookup?_iff.mpr found
        have absent : LocalScope.lookup? environment (ident 2) = none := by decide
        rw [absent] at lookup
        cases lookup

theorem positional_temporaries_do_not_enable_an_originally_missing_right_reference
    (store : Core.Store) :
    missingRight.lower? scope = none ∧ ¬WellScoped scope missingRight ∧
    (¬∃ value finalStore, Evaluates environment store missingRight value finalStore) := by
  have absent : missingRight.lower? scope = none := by decide
  exact ⟨absent, Expr.lower?_eq_none_iff_not_wellScoped.mp absent, noMissingEvaluation store⟩

theorem explicitly_inserting_the_missing_identity_cannot_be_reflected_without_original_scope
    (store : Core.Store) :
    ident 2 ∉ LocalScope.ids environment ∧
    Lowers (ident 2 :: scope) missingRight ((Core.Expr.word .zero).wordLt (.var 0)) ∧
    Evaluates ((ident 2, .word one) :: environment) store missingRight (.bool true) store ∧
    (¬∃ value finalStore, Evaluates environment store missingRight value finalStore) := by
  refine ⟨fresh, .wordLt .word (.var .head), ?_, noMissingEvaluation store⟩
  simpa only [missingRight, ordered] using (Evaluates.wordLt .word (.var .head) :
    Evaluates ((ident 2, .word one) :: environment) store missingRight
      (.bool (decide (Core.Word.zero < one))) store)

private def source : Expr := .wordLt (.var (ident 0)) (.var (ident 1))
private def merge : LocalId → LocalId := fun _ => ident 0
private theorem sourceEvaluated (store : Core.Store) :
    Evaluates environment store source (.bool true) store := by
  simpa only [source, ordered] using (Evaluates.wordLt (.var .head) (.var (.tail different .head)) :
    Evaluates environment store source (.bool (decide (Core.Word.zero < one))) store)
private theorem mergedEvaluated (store : Core.Store) :
    Evaluates (LocalScope.mapIds merge environment) store (source.renameIds merge) (.bool false) store := by
  simpa [source, Expr.renameIds] using (Evaluates.wordLt (.var .head) (.var .head) :
    Evaluates (LocalScope.mapIds merge environment) store (source.renameIds merge)
      (.bool (decide (Core.Word.zero < Core.Word.zero))) store)

theorem noninjective_renaming_obeys_structural_composition_but_changes_nearest_lookup_semantics
    (after : LocalId → LocalId) (store : Core.Store) :
    ¬Function.Injective merge ∧
    (source.renameIds merge).renameIds after = source.renameIds (after ∘ merge) ∧
    LocalScope.mapIds merge environment = [(ident 0, .word .zero), (ident 0, .word one)] ∧
    Lowers scope source ((Core.Expr.var 0).wordLt (.var 1)) ∧
    Lowers (scope.map merge) (source.renameIds merge) ((Core.Expr.var 0).wordLt (.var 0)) ∧
    Evaluates environment store source (.bool true) store ∧
    Evaluates (LocalScope.mapIds merge environment) store (source.renameIds merge) (.bool false) store ∧
    ¬Evaluates (LocalScope.mapIds merge environment) store (source.renameIds merge) (.bool true) store := by
  refine ⟨fun injective => different (injective rfl), source.renameIds_comp merge after, rfl,
    .wordLt (.var .head) (.var (.tail different .head)), .wordLt (.var .head) (.var .head),
    sourceEvaluated store, mergedEvaluated store, ?_⟩
  intro wrong
  have impossible := (evaluation_deterministic wrong (mergedEvaluated store)).1
  cases impossible

theorem fresh_insertion_and_reflection_through_word_less_need_scope_but_not_typing
    (inserted : Core.Value) (store finalStore : Core.Store) (value : Core.Value) :
    (∀ type, ¬HasType context skippedBad type) ∧
    Lowers (ident 2 :: scope) skippedBad (skippedBadCore.weakenAt 0) ∧
    Evaluates ((ident 2, inserted) :: environment) store skippedBad (.bool true) store ∧
    (Evaluates ((ident 2, inserted) :: environment) store skippedBad value finalStore ↔
      Evaluates environment store skippedBad value finalStore) :=
  ⟨badNotTyped, badLowered.weaken_fresh fresh, (badEvaluated store).weaken_fresh fresh,
    badLowered.wellScoped.evaluates_weaken_fresh_iff (environment := environment) fresh⟩

theorem injective_renaming_preserves_raw_success_even_when_whole_lowering_fails
    (mapping : LocalId → LocalId) (injective : Function.Injective mapping) (store : Core.Store) :
    (skippedMissing.renameIds mapping).lower? (scope.map mapping) = none ∧
    Evaluates (LocalScope.mapIds mapping environment) store (skippedMissing.renameIds mapping)
      (.bool true) store :=
  ⟨(Expr.lower?_renameIds mapping injective skippedMissing scope).trans missingRejected,
    (evaluates_renameIds_iff mapping injective).mpr (missingEvaluated store)⟩

end Tests.ResolvedWordLessBoundary
