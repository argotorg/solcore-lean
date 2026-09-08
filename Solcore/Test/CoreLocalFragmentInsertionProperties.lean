import Solcore.Core.LocalFragmentInsertionProperties
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Resolved.WordLessWithIds

/-! Exact values and stores survive insertion for the independent local syntax
fragment. Existing closures and references are opaque returned values, not calls
or allocations, and retained binder indices remain distinct from shifted inputs. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentInsertion

open Solcore Solcore.Core

private def arithmetic (cutoff : Nat) : Expr :=
  .unary .wordNot (.binary .wordSub (.var cutoff) (.var (cutoff + 1)))
private theorem arithmeticLocal (cutoff : Nat) : Expr.LocalFragment (arithmetic cutoff) :=
  .unary (.binary .var .var)
private theorem arithmeticEvaluates (leading suffix : Environment) (left right : Word) (store : Store) :
    Evaluates (leading ++ .word left :: .word right :: suffix) store (arithmetic leading.length)
      (.word (left.sub right).bitNot) store := by
  have leftFound : (leading ++ .word left :: .word right :: suffix)[leading.length]? = some (.word left) := by
    simp
  have rightFound : (leading ++ .word left :: .word right :: suffix)[leading.length + 1]? = some (.word right) := by
    simp
  exact .unary (.binary (.var leftFound) (.var rightFound) rfl) rfl

private def nested : Expr := .letE (.var 1) (.letE (.var 0) (.var 2))
private def nestedShifted : Expr := .letE (.var 2) (.letE (.var 0) (.var 2))
private theorem nestedLocal : Expr.LocalFragment nested := .letE .var (.letE .var .var)
private theorem nestedEvaluates (retained bound : Value) (suffix : Environment) (store : Store) :
    Evaluates (retained :: bound :: suffix) store nested retained store :=
  .letE (.var rfl) (.letE (.var rfl) (.var rfl))

private def conditional (choice : Bool) : Expr := .ifE (.bool choice) (.var 0) (.var 1)
private theorem conditionalLocal (choice : Bool) : Expr.LocalFragment (conditional choice) := .ifE .bool .var .var
private theorem conditionalEvaluates (choice : Bool) (left right : Value) (suffix : Environment) (store : Store) :
    Evaluates (left :: right :: suffix) store (conditional choice) (if choice then left else right) store := by
  cases choice
  · exact .ifFalse .bool (.var rfl)
  · exact .ifTrue .bool (.var rfl)

private def skippedBadOperand : Expr := .ifE (.bool true) (.var 0) (.binary .wordSub (.bool true) .unit)
private theorem skippedLocal : Expr.LocalFragment skippedBadOperand := .ifE .bool .var (.binary .bool .unit)
private theorem skippedEvaluates (value : Value) (suffix : Environment) (store : Store) :
    Evaluates (value :: suffix) store skippedBadOperand value store := .ifTrue .bool (.var rfl)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"LocalInsertion", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def named : Resolved.Expr := .wordLtWithIds (ident 2) (ident 0) (.var (ident 0)) (.var (ident 1))
private def ordered : Expr := .letE (.var 0) (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1)))
private theorem orderedLowered : Resolved.Lowers [ident 0, ident 1] named ordered := by
  have lowerLeft : Resolved.Lowers [ident 0, ident 1] (.var (ident 0)) (.var 0) := .var .head
  have lowerRight : Resolved.Lowers [ident 0, ident 1] (.var (ident 1)) (.var 1) := .var (.tail (by decide) .head)
  simpa [named, ordered, Expr.wordLt_expansion, Expr.weakenAt] using
    lowerLeft.wordLtWithIds (leftId := ident 2) (rightId := ident 0) lowerRight (by decide) (by decide)
private theorem orderedEvaluates (left right : Word) (store : Store) :
    Evaluates [.word left, .word right] store ordered (.bool (decide (left < right))) store :=
  .letE (.var rfl) (.letE (.var rfl) (.binary (.var rfl) (.var rfl) rfl))

theorem all_three_constant_forms_keep_values_under_arbitrary_retained_prefixes
    (leading suffix : Environment) (inserted : Value) (choice : Bool) (word : Word) (store : Store) :
    Evaluates (leading ++ inserted :: suffix) store .unit .unit store ∧
    Evaluates (leading ++ inserted :: suffix) store (.bool choice) (.bool choice) store ∧
    Evaluates (leading ++ inserted :: suffix) store (.word word) (.word word) store := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Expr.weakenAt] using (Expr.LocalFragment.unit.evaluates_insert_iff leading suffix inserted).mpr
      (show Evaluates (leading ++ suffix) store .unit .unit store from .unit)
  · simpa only [Expr.weakenAt] using (Expr.LocalFragment.bool.evaluates_insert_iff leading suffix inserted).mpr
      (show Evaluates (leading ++ suffix) store (.bool choice) (.bool choice) store from .bool)
  · simpa only [Expr.weakenAt] using (Expr.LocalFragment.word.evaluates_insert_iff leading suffix inserted).mpr
      (show Evaluates (leading ++ suffix) store (.word word) (.word word) store from .word)

theorem arbitrary_suffix_values_are_shifted_past_insertion_at_any_prefix_length
    (leading suffix : Environment) (value inserted : Value) (store : Store) :
    Evaluates (leading ++ value :: suffix) store (.var leading.length) value store ∧
    Evaluates (leading ++ inserted :: value :: suffix) store (.var (leading.length + 1)) value store ∧
    (Expr.var leading.length).LocalFragment ∧
    ((Expr.var leading.length).weakenAt leading.length).LocalFragment := by
  have original : Evaluates (leading ++ value :: suffix) store (.var leading.length) value store := .var (by simp)
  have fragment : (Expr.var leading.length).LocalFragment := .var
  have shifted := (fragment.evaluates_insert_iff leading (value :: suffix) inserted).mpr original
  refine ⟨original, ?_, fragment, fragment.weakenAt leading.length⟩
  simpa only [Expr.weakenAt, Nat.le_refl, ↓reduceIte] using shifted

theorem arbitrary_return_values_have_exact_empty_prefix_preservation_and_reflection
    (environment : Environment) (value inserted : Value) (store : Store) :
    Evaluates (inserted :: value :: environment) store (.var 1) value store ∧
    Evaluates (value :: environment) store (.var 0) value store ∧
    (Evaluates (inserted :: value :: environment) store (.var 1) value store ↔
      Evaluates (value :: environment) store (.var 0) value store) := by
  have original : Evaluates (value :: environment) store (.var 0) value store := .var rfl
  have shifted := original.weakenAt_zero_localFragment .var inserted
  refine ⟨?_, shifted.reflect_weakenAt_zero_localFragment .var, ?_⟩
  · simpa [Expr.weakenAt] using shifted
  · simpa [Expr.weakenAt] using (Expr.LocalFragment.var (index := 0)).evaluates_weaken_zero_iff
      (value :: environment) inserted (initialStore := store) (finalStore := store) (value := value)

theorem existing_cells_and_closures_are_returned_opaquely_without_allocation_or_capture
    (inserted : Value) (environment captured : Environment) (store : Store) (body : Expr) :
    Evaluates (inserted :: .cellRef .word 40 :: environment) [] (.var 1) (.cellRef .word 40) [] ∧
    Evaluates (inserted :: .closure .word .bool body captured :: environment) store (.var 1)
      (.closure .word .bool body captured) store :=
  ⟨(arbitrary_return_values_have_exact_empty_prefix_preservation_and_reflection
      environment (.cellRef .word 40) inserted []).1,
    (arbitrary_return_values_have_exact_empty_prefix_preservation_and_reflection
      environment (.closure .word .bool body captured) inserted store).1⟩

theorem unary_and_binary_primitives_preserve_ordered_words_at_arbitrary_cutoffs
    (leading suffix : Environment) (left right : Word) (inserted : Value) (store : Store) :
    (arithmetic leading.length).LocalFragment ∧
    Evaluates (leading ++ .word left :: .word right :: suffix) store (arithmetic leading.length)
      (.word (left.sub right).bitNot) store ∧
    Evaluates (leading ++ inserted :: .word left :: .word right :: suffix) store
      ((arithmetic leading.length).weakenAt leading.length) (.word (left.sub right).bitNot) store :=
  ⟨arithmeticLocal leading.length, arithmeticEvaluates leading suffix left right store,
    ((arithmeticLocal leading.length).evaluates_insert_iff leading (.word left :: .word right :: suffix) inserted).mpr
      (arithmeticEvaluates leading suffix left right store)⟩

theorem nested_lets_retain_bound_indices_while_shifting_the_original_suffix
    (retained bound inserted : Value) (suffix : Environment) (store : Store) :
    nested.weakenAt 1 = nestedShifted ∧ nestedShifted.LocalFragment ∧
    Evaluates (retained :: bound :: suffix) store nested retained store ∧
    Evaluates (retained :: inserted :: bound :: suffix) store nestedShifted retained store := by
  have same : nested.weakenAt 1 = nestedShifted := by simp [nested, nestedShifted, Expr.weakenAt]
  refine ⟨same, same ▸ nestedLocal.weakenAt 1, nestedEvaluates retained bound suffix store, ?_⟩
  have shifted := (nestedLocal.evaluates_insert_iff [retained] (bound :: suffix) inserted).mpr
    (nestedEvaluates retained bound suffix store)
  simpa only [List.length_cons, List.length_nil, same, List.cons_append, List.nil_append] using shifted

theorem both_conditional_paths_preserve_the_selected_actual_value
    (choice : Bool) (left right inserted : Value) (suffix : Environment) (store : Store) :
    (conditional choice).LocalFragment ∧
    Evaluates (left :: right :: suffix) store (conditional choice) (if choice then left else right) store ∧
    Evaluates (inserted :: left :: right :: suffix) store ((conditional choice).weakenAt 0)
      (if choice then left else right) store :=
  ⟨conditionalLocal choice, conditionalEvaluates choice left right suffix store,
    (conditionalEvaluates choice left right suffix store).weakenAt_zero_localFragment (conditionalLocal choice) inserted⟩

theorem whole_fragment_membership_does_not_require_the_skipped_primitive_to_typecheck
    (value inserted : Value) (suffix : Environment) (store : Store) :
    skippedBadOperand.LocalFragment ∧
    Evaluates (value :: suffix) store skippedBadOperand value store ∧
    Evaluates (inserted :: value :: suffix) store (skippedBadOperand.weakenAt 0) value store :=
  ⟨skippedLocal, skippedEvaluates value suffix store,
    (skippedEvaluates value suffix store).weakenAt_zero_localFragment skippedLocal inserted⟩

theorem resolved_ordered_comparison_lowers_into_the_independent_core_fragment
    (left right : Word) (inserted : Value) (store : Store) :
    Resolved.Lowers [ident 0, ident 1] named ordered ∧ ordered.LocalFragment ∧
    (ordered.weakenAt 0).LocalFragment ∧
    Evaluates [.word left, .word right] (.unit :: store) ordered (.bool (decide (left < right))) (.unit :: store) ∧
    Evaluates [inserted, .word left, .word right] (.unit :: store) (ordered.weakenAt 0)
      (.bool (decide (left < right))) (.unit :: store) :=
  ⟨orderedLowered, orderedLowered.localFragment, orderedLowered.localFragment.weakenAt 0,
    orderedEvaluates left right (.unit :: store),
    (orderedEvaluates left right (.unit :: store)).weakenAt_zero_localFragment orderedLowered.localFragment inserted⟩

end Tests.CoreLocalFragmentInsertion
