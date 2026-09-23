import Solcore.Resolved.WordLessWithIds
import Solcore.Resolved.Renaming

/-! Explicit comparison temporaries are hygienic under precise premises. These
consumers do not add canonical source operators or infer freshness from names. -/

set_option autoImplicit false

namespace Tests.ResolvedWordLessWithIds

open Solcore Solcore.Resolved

private def owner : DeclarationId := ⟨⟨.main, ⟨[⟨"ExplicitLess", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : LocalId := ⟨owner, index⟩
private def scope : List LocalId := [ident 0, ident 1]
private def context : Context := [(ident 0, .word), (ident 1, .word)]
private def environment (left right : Core.Word) : Environment := [(ident 0, .word left), (ident 1, .word right)]
private def source : Expr := .wordLtWithIds (ident 2) (ident 0) (.var (ident 0)) (.var (ident 1))
private def core : Core.Expr := .letE (.var 0) (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1)))
private theorem distinctOuter : ident 0 ≠ ident 1 := by decide
private theorem distinctTemps : ident 0 ≠ ident 2 := by decide
private theorem fresh : ident 2 ∉ scope := by decide
private theorem leftEvaluation (left right : Core.Word) (store : Core.Store) :
    Evaluates (environment left right) store (.var (ident 0)) (.word left) store := .var .head
private theorem rightEvaluation (left right : Core.Word) (store : Core.Store) :
    Evaluates (environment left right) store (.var (ident 1)) (.word right) store := .var (.tail distinctOuter .head)
private theorem lowered : Lowers scope source core := by
  simpa [scope, source, Core.Expr.wordLt_expansion, Core.Expr.weakenAt, core] using
    (Lowers.var .head).wordLtWithIds (Lowers.var (.tail distinctOuter .head)) fresh distinctTemps
private theorem typed : HasType context source .bool :=
  (HasType.var .head).wordLtWithIds (HasType.var (.tail distinctOuter .head)) fresh distinctTemps
private theorem evaluated (left right : Core.Word) (store : Core.Store) :
    Evaluates (environment left right) store source (.bool (decide (left < right))) store :=
  (leftEvaluation left right store).wordLtWithIds (rightEvaluation left right store) fresh distinctTemps
private theorem rightScoped : WellScoped scope (.var (ident 1)) := .var (by decide)

theorem second_temporary_may_reuse_an_outer_id_with_exact_nested_core
    (left right : Core.Word) (store : Core.Store) :
    ident 0 ∈ scope ∧ Lowers scope source core ∧ HasType context source .bool ∧
    source.lower? scope = some core ∧ infer? context source = some .bool ∧
    Evaluates (environment left right) (.unit :: store) source (.bool (decide (left < right))) (.unit :: store) ∧
    Core.Evaluates [.word left, .word right] (.unit :: store) core
      (.bool (decide (left < right))) (.unit :: store) := by
  refine ⟨by decide, lowered, typed, ?_,
    infer_wordLtWithIds (infer_complete (HasType.var .head))
      (infer_complete (HasType.var (.tail distinctOuter .head))) fresh distinctTemps,
    evaluated left right (.unit :: store), (evaluated left right (.unit :: store)).toCore lowered⟩
  simpa [scope, source, Core.Expr.wordLt_expansion, Core.Expr.weakenAt, core] using
    Expr.lower?_wordLtWithIds (Lowers.var .head).complete
      (Lowers.var (.tail distinctOuter .head)).complete fresh distinctTemps

theorem reflection_recovers_original_ordered_children_and_intermediate_store
    (left right : Core.Word) (initialStore finalStore : Core.Store) (value : Core.Value)
    (evaluation : Evaluates (environment left right) initialStore source value finalStore) :
    (∃ leftWord rightWord middleStore,
      Evaluates (environment left right) initialStore (.var (ident 0)) (.word leftWord) middleStore ∧
      Evaluates (environment left right) middleStore (.var (ident 1)) (.word rightWord) finalStore ∧
      value = .bool (decide (leftWord < rightWord))) ∧
    (Evaluates (environment left right) initialStore source value finalStore ↔
      ∃ leftWord rightWord middleStore,
        Evaluates (environment left right) initialStore (.var (ident 0)) (.word leftWord) middleStore ∧
        Evaluates (environment left right) middleStore (.var (ident 1)) (.word rightWord) finalStore ∧
        value = .bool (decide (leftWord < rightWord))) :=
  ⟨evaluation.wordLtWithIds_inv rightScoped fresh distinctTemps,
    wordLtWithIds_evaluates_iff rightScoped fresh distinctTemps⟩

theorem equality_and_both_unsigned_directions_use_the_original_values
    (left right : Core.Word) (strict : left < right) (store : Core.Store) :
    Evaluates (environment left left) store source (.bool false) store ∧
    Evaluates (environment left right) store source (.bool true) store ∧
    Evaluates (environment right left) store source (.bool false) store := by
  have reverse : ¬right < left := Nat.not_lt.mpr (Nat.le_of_lt strict)
  exact ⟨by simpa using evaluated left left store, by simpa [strict] using evaluated left right store,
    by simpa [reverse] using evaluated right left store⟩

theorem injective_explicit_identity_changes_keep_the_same_core_and_meaning
    (mapping : LocalId → LocalId) (injective : Function.Injective mapping)
    (left right : Core.Word) (store : Core.Store) :
    source.renameIds mapping = Expr.wordLtWithIds (mapping (ident 2)) (mapping (ident 0))
      (.var (mapping (ident 0))) (.var (mapping (ident 1))) ∧
    (Expr.wordLtWithIds (mapping (ident 2)) (mapping (ident 0))
      (.var (mapping (ident 0))) (.var (mapping (ident 1)))).lower? (scope.map mapping) = some core ∧
    Evaluates (LocalScope.mapIds mapping (environment left right)) store
      (Expr.wordLtWithIds (mapping (ident 2)) (mapping (ident 0))
        (.var (mapping (ident 0))) (.var (mapping (ident 1)))) (.bool (decide (left < right))) store := by
  refine ⟨Expr.renameIds_wordLtWithIds _ _ _ _ _, ?_, ?_⟩
  · simpa only [source, Expr.renameIds_wordLtWithIds, Expr.renameIds] using
      (Expr.lower?_renameIds mapping injective source scope).trans lowered.complete
  · simpa only [source, Expr.renameIds_wordLtWithIds, Expr.renameIds] using
      (evaluates_renameIds_iff mapping injective).mpr (evaluated left right store)

private def shadowedRight : Expr := .letE (ident 2) (.var (ident 1)) (.var (ident 2))
private def shadowedSource := Expr.wordLtWithIds (ident 2) (ident 0) (.var (ident 0)) shadowedRight
private def shadowedCore : Core.Expr :=
  .letE (.var 0) (.letE (.letE (.var 2) (.var 0)) (.binary .wordGt (.var 0) (.var 1)))

theorem inner_operand_binders_can_shadow_the_first_temporary
    (left right : Core.Word) (store : Core.Store) :
    WellScoped scope shadowedRight ∧ Lowers scope shadowedSource shadowedCore ∧
    HasType context shadowedSource .bool ∧
    Evaluates (environment left right) store shadowedSource (.bool (decide (left < right))) store := by
  have rightLowered : Lowers scope shadowedRight (.letE (.var 1) (.var 0)) :=
    .letE (.var (.tail distinctOuter .head)) (.var .head)
  have rightTyped : HasType context shadowedRight .word :=
    .letE (.var (.tail distinctOuter .head)) (.var .head)
  have rightEvaluated : Evaluates (environment left right) store shadowedRight (.word right) store :=
    .letE (rightEvaluation left right store) (.var .head)
  refine ⟨.letE rightScoped (.var (by simp)), ?_,
    (HasType.var .head).wordLtWithIds rightTyped fresh distinctTemps,
    (leftEvaluation left right store).wordLtWithIds rightEvaluated fresh distinctTemps⟩
  simpa [scope, shadowedSource, Core.Expr.wordLt_expansion, Core.Expr.weakenAt, shadowedCore] using
    (Lowers.var .head).wordLtWithIds rightLowered fresh distinctTemps

private def one : Core.Word := Core.Word.ofNatModulo 1
private def zeroOne : Environment := environment .zero one
private theorem zeroOneEvaluatesTrue (store : Core.Store) :
    Evaluates zeroOne store source (.bool true) store := by
  have ordered : decide (Core.Word.zero < one) = true := by decide
  simpa only [zeroOne, ordered] using evaluated .zero one store

theorem equal_temporary_ids_compare_the_right_value_with_itself
    (store : Core.Store) :
    Evaluates zeroOne store source (.bool true) store ∧
    Evaluates zeroOne store (Expr.wordLtWithIds (ident 2) (ident 2)
      (.var (ident 0)) (.var (ident 1))) (.bool false) store := by
  refine ⟨zeroOneEvaluatesTrue store, ?_⟩
  exact .letE (leftEvaluation .zero one store)
    (.letE (.var (.tail (by decide) (.tail distinctOuter .head)))
      (.binary (.var .head) (.var .head) rfl))

theorem a_capturing_first_temporary_changes_an_existing_right_reference
    (store : Core.Store) :
    Evaluates zeroOne store (.var (ident 1)) (.word one) store ∧
    Evaluates ((ident 1, .word .zero) :: zeroOne) store (.var (ident 1)) (.word .zero) store ∧
    Evaluates zeroOne store (Expr.wordLtWithIds (ident 1) (ident 2)
      (.var (ident 0)) (.var (ident 1))) (.bool false) store ∧
    Evaluates zeroOne store source (.bool true) store := by
  refine ⟨rightEvaluation .zero one store, .var .head, ?_, ?_⟩
  · exact .letE (leftEvaluation .zero one store)
      (.letE (.var .head) (.binary (.var .head) (.var (.tail (by decide) .head)) rfl))
  · exact zeroOneEvaluatesTrue store

theorem newly_enabled_missing_right_reference_explains_the_reflection_scope_premise
    (store : Core.Store) :
    ident 2 ∉ LocalScope.ids zeroOne ∧ ident 3 ≠ ident 2 ∧
    Evaluates zeroOne store (Expr.wordLtWithIds (ident 2) (ident 3)
      (.word .zero) (.var (ident 2))) (.bool false) store ∧
    ¬∃ value finalStore, Evaluates zeroOne store (.var (ident 2)) value finalStore := by
  refine ⟨fresh, by decide, ?_, ?_⟩
  · exact .letE .word (.letE (.var .head)
      (.binary (.var .head) (.var (.tail (by decide) .head)) rfl))
  · rintro ⟨value, finalStore, evaluation⟩
    cases evaluation with
    | var found =>
      have lookup := LocalScope.lookup?_iff.mpr found
      have absent : LocalScope.lookup? zeroOne (ident 2) = none := by decide
      rw [absent] at lookup
      cases lookup

end Tests.ResolvedWordLessWithIds
