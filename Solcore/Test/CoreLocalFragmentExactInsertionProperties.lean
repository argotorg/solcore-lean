import Solcore.Core.LocalFragment
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Resolved.WordLessWithIds

/-! Independent transition chains fix numeric costs before insertion. The same
outer continuation is retained without executing its frames, and runtime values
and stores need no typing, freshness, or allocation premises. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentExactInsertion

open Solcore Solcore.Core

private def arithmetic (cutoff : Nat) : Expr :=
  .unary .wordNot (.binary .wordSub (.var cutoff) (.var (cutoff + 1)))
private theorem arithmeticLocal (cutoff : Nat) : (arithmetic cutoff).LocalFragment := .unary (.binary .var .var)
private theorem arithmeticEvaluates (leading suffix : Environment) (left right : Word) (store : Store) :
    Evaluates (leading ++ .word left :: .word right :: suffix) store (arithmetic leading.length)
      (.word (left.sub right).bitNot) store := by
  have first : (leading ++ .word left :: .word right :: suffix)[leading.length]? = some (.word left) := by simp
  have second : (leading ++ .word left :: .word right :: suffix)[leading.length + 1]? = some (.word right) := by simp
  exact .unary (.binary (.var first) (.var second) rfl) rfl
private theorem arithmeticPath (leading suffix : Environment) (left right : Word) (store : Store) :
    Steps 7 (State.initial (arithmetic leading.length) (leading ++ .word left :: .word right :: suffix) store)
      (State.final (.word (left.sub right).bitNot) store) := by
  have first : (leading ++ .word left :: .word right :: suffix)[leading.length]? = some (.word left) := by simp
  have second : (leading ++ .word left :: .word right :: suffix)[leading.length + 1]? = some (.word right) := by simp
  exact .cons .enterUnary (.cons .enterBinary (.cons (.var first) (.cons .enterBinaryRight
    (.cons (.var second) (.cons (.applyBinary (result := .word (left.sub right)) rfl) (.cons (.applyUnary rfl) .refl))))))

private def nested : Expr := .letE (.var 1) (.letE (.var 0) (.var 2))
private theorem nestedLocal : nested.LocalFragment := .letE .var (.letE .var .var)
private theorem nestedPath (retained bound : Value) (suffix : Environment) (store : Store) :
    Steps 7 (State.initial nested (retained :: bound :: suffix) store) (State.final retained store) :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet
    (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))))))

private def conditional (choice : Bool) (left right : Word) : Expr :=
  .ifE (.bool choice) (.binary .wordMul (.word left) (.word right)) (.var 0)
private theorem conditionalLocal (choice : Bool) (left right : Word) : (conditional choice left right).LocalFragment :=
  .ifE .bool (.binary .word .word) .var
private theorem conditionalPath (choice : Bool) (left right : Word) (value : Value) (suffix : Environment) (store : Store) :
    Steps (if choice then 8 else 4) (State.initial (conditional choice left right) (value :: suffix) store)
      (State.final (if choice then .word (left.mul right) else value) store) := by
  cases choice
  · exact .cons .enterIf (.cons .bool (.cons .chooseFalse (.cons (.var rfl) .refl)))
  · exact .cons .enterIf (.cons .bool (.cons .chooseTrue (.cons .enterBinary
      (.cons .word (.cons .enterBinaryRight (.cons .word (.cons (.applyBinary rfl) .refl)))))))

private def skipped : Expr := .ifE (.bool true) (.var 0) (.binary .wordSub (.bool true) .unit)
private theorem skippedLocal : skipped.LocalFragment := .ifE .bool .var (.binary .bool .unit)
private theorem skippedPath (value : Value) (suffix : Environment) (store : Store) :
    Steps 4 (State.initial skipped (value :: suffix) store) (State.final value store) :=
  .cons .enterIf (.cons .bool (.cons .chooseTrue (.cons (.var rfl) .refl)))

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ExactInsertion", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def named : Resolved.Expr := .wordLtWithIds (ident 2) (ident 0) (.var (ident 0)) (.var (ident 1))
private def ordered : Expr := .letE (.var 0) (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1)))
private theorem orderedLowered : Resolved.Lowers [ident 0, ident 1] named ordered := by
  have left : Resolved.Lowers [ident 0, ident 1] (.var (ident 0)) (.var 0) := .var .head
  have right : Resolved.Lowers [ident 0, ident 1] (.var (ident 1)) (.var 1) := .var (.tail (by decide) .head)
  simpa [named, ordered, Expr.wordLt_expansion, Expr.weakenAt] using
    left.wordLtWithIds (leftId := ident 2) (rightId := ident 0) right (by decide) (by decide)
private theorem orderedPath (left right : Word) (store : Store) :
    Steps 11 (State.initial ordered [.word left, .word right] store)
      (State.final (.bool (decide (left < right))) store) :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl)
    (.cons .bindLet (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight
      (.cons (.var rfl) (.cons (.applyBinary rfl) .refl))))))))))

theorem unit_bool_and_word_constants_cost_one_under_any_retained_prefix
    (leading suffix : Environment) (inserted : Value) (choice : Bool) (word : Word)
    (store : Store) (continuation : List Frame) :
    Steps 1 ⟨.eval .unit (leading ++ inserted :: suffix), continuation, store⟩ ⟨.ret .unit, continuation, store⟩ ∧
    Steps 1 ⟨.eval (.bool choice) (leading ++ inserted :: suffix), continuation, store⟩
      ⟨.ret (.bool choice), continuation, store⟩ ∧
    Steps 1 ⟨.eval (.word word) (leading ++ inserted :: suffix), continuation, store⟩
      ⟨.ret (.word word), continuation, store⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Expr.weakenAt] using Expr.LocalFragment.unit.steps_insert leading suffix inserted
      (show Steps 1 (State.initial .unit (leading ++ suffix) store) (State.final .unit store) from .cons .unit .refl) continuation
  · simpa only [Expr.weakenAt] using Expr.LocalFragment.bool.steps_insert leading suffix inserted
      (show Steps 1 (State.initial (.bool choice) (leading ++ suffix) store) (State.final (.bool choice) store)
        from .cons .bool .refl) continuation
  · simpa only [Expr.weakenAt] using Expr.LocalFragment.word.steps_insert leading suffix inserted
      (show Steps 1 (State.initial (.word word) (leading ++ suffix) store) (State.final (.word word) store)
        from .cons .word .refl) continuation

theorem arbitrary_return_values_keep_one_step_and_exact_closed_path_reflection
    (leading suffix : Environment) (value inserted : Value) (store : Store) (continuation : List Frame) :
    Steps 1 ⟨.eval ((Expr.var leading.length).weakenAt leading.length) (leading ++ inserted :: value :: suffix),
      continuation, store⟩ ⟨.ret value, continuation, store⟩ ∧
    Steps 1 ⟨.eval (.var leading.length) (leading ++ value :: suffix), continuation, store⟩
      ⟨.ret value, continuation, store⟩ ∧
    (Steps 1 (State.initial ((Expr.var leading.length).weakenAt leading.length) (leading ++ inserted :: value :: suffix) store)
      (State.final value store) ↔
      Steps 1 (State.initial (.var leading.length) (leading ++ value :: suffix) store) (State.final value store)) := by
  have fragment : (Expr.var leading.length).LocalFragment := .var
  have original : Steps 1 (State.initial (.var leading.length) (leading ++ value :: suffix) store) (State.final value store) :=
    .cons (.var (by simp)) .refl
  have shifted := fragment.steps_insert leading (value :: suffix) inserted original []
  exact ⟨fragment.steps_insert leading (value :: suffix) inserted original continuation,
    fragment.steps_reflect_insert leading (value :: suffix) inserted shifted continuation,
    fragment.steps_insert_iff leading (value :: suffix) inserted⟩

theorem paired_unary_binary_paths_choose_seven_before_the_arbitrary_continuation
    (leading suffix : Environment) (left right : Word) (inserted : Value) (store : Store) :
    ∃ cost, cost = 7 ∧ ∀ continuation,
      Steps cost ⟨.eval (arithmetic leading.length) (leading ++ .word left :: .word right :: suffix), continuation, store⟩
        ⟨.ret (.word (left.sub right).bitNot), continuation, store⟩ ∧
      Steps cost ⟨.eval ((arithmetic leading.length).weakenAt leading.length)
          (leading ++ inserted :: .word left :: .word right :: suffix), continuation, store⟩
        ⟨.ret (.word (left.sub right).bitNot), continuation, store⟩ := by
  obtain ⟨cost, paths⟩ := (arithmeticLocal leading.length).insertion_paths leading
    (.word left :: .word right :: suffix) inserted (arithmeticEvaluates leading suffix left right store)
  have exactCost := ((arithmeticPath leading suffix left right store).final_unique (paths []).1).1
  exact ⟨cost, exactCost.symm, paths⟩

theorem nested_lets_keep_seven_steps_at_nonzero_insertion_depth
    (retained bound inserted : Value) (suffix : Environment) (store : Store) (continuation : List Frame) :
    Steps 7 ⟨.eval (nested.weakenAt 1) (retained :: inserted :: bound :: suffix), continuation, store⟩
      ⟨.ret retained, continuation, store⟩ ∧
    Steps 7 ⟨.eval nested (retained :: bound :: suffix), continuation, store⟩ ⟨.ret retained, continuation, store⟩ := by
  have shifted := nestedLocal.steps_insert [retained] (bound :: suffix) inserted (nestedPath retained bound suffix store) []
  exact ⟨nestedLocal.steps_insert [retained] (bound :: suffix) inserted (nestedPath retained bound suffix store) continuation,
    nestedLocal.steps_reflect_insert [retained] (bound :: suffix) inserted shifted continuation⟩

theorem both_conditional_paths_preserve_their_distinct_exact_costs
    (choice : Bool) (left right : Word) (value inserted : Value) (suffix : Environment)
    (store : Store) (continuation : List Frame) :
    Steps (if choice then 8 else 4)
      ⟨.eval ((conditional choice left right).weakenAt 0) (inserted :: value :: suffix), continuation, store⟩
      ⟨.ret (if choice then .word (left.mul right) else value), continuation, store⟩ ∧
    Steps (if choice then 8 else 4)
      ⟨.eval (conditional choice left right) (value :: suffix), continuation, store⟩
      ⟨.ret (if choice then .word (left.mul right) else value), continuation, store⟩ := by
  have original := conditionalPath choice left right value suffix store
  have shifted := original.weakenAt_zero_localFragment (conditionalLocal choice left right) inserted []
  exact ⟨original.weakenAt_zero_localFragment (conditionalLocal choice left right) inserted continuation,
    shifted.reflect_weakenAt_zero_localFragment (conditionalLocal choice left right) continuation⟩

theorem shifted_and_original_closed_runs_have_identical_exact_fuel_thresholds
    (choice : Bool) (left right : Word) (value inserted : Value) (suffix : Environment) (store : Store) (fuel : Nat) :
    (runStateful fuel (State.initial ((conditional choice left right).weakenAt 0) (inserted :: value :: suffix) store) =
      .done (if choice then .word (left.mul right) else value) store ↔ (if choice then 8 else 4) ≤ fuel) ∧
    ((∃ checkpoint, runStateful fuel
      (State.initial ((conditional choice left right).weakenAt 0) (inserted :: value :: suffix) store) = .outOfFuel checkpoint) ↔
      fuel < (if choice then 8 else 4)) ∧
    (runStateful fuel (State.initial (conditional choice left right) (value :: suffix) store) =
      .done (if choice then .word (left.mul right) else value) store ↔ (if choice then 8 else 4) ≤ fuel) := by
  have paths := both_conditional_paths_preserve_their_distinct_exact_costs choice left right value inserted suffix store []
  exact ⟨paths.1.runStateful_done_iff, paths.1.runStateful_outOfFuel_iff, paths.2.runStateful_done_iff⟩

theorem skipped_local_bad_type_adds_no_cost_and_outer_frames_remain_unexecuted
    (value inserted : Value) (suffix : Environment) (store : Store) :
    skipped.LocalFragment ∧ Steps 4
      ⟨.eval (skipped.weakenAt 0) (inserted :: value :: suffix), [.unaryApply .wordNot], store⟩
      ⟨.ret value, [.unaryApply .wordNot], store⟩ :=
  ⟨skippedLocal, (skippedPath value suffix store).weakenAt_zero_localFragment skippedLocal inserted [.unaryApply .wordNot]⟩

theorem lowered_ordered_comparison_preserves_eleven_steps_on_nonempty_stores
    (left right : Word) (inserted : Value) (store : Store) (continuation : List Frame) :
    Resolved.Lowers [ident 0, ident 1] named ordered ∧ ordered.LocalFragment ∧
    Steps 11 (State.initial ordered [.word left, .word right] (.unit :: store))
      (State.final (.bool (decide (left < right))) (.unit :: store)) ∧
    Steps 11 ⟨.eval (ordered.weakenAt 0) [inserted, .word left, .word right], continuation, .unit :: store⟩
      ⟨.ret (.bool (decide (left < right))), continuation, .unit :: store⟩ :=
  ⟨orderedLowered, orderedLowered.localFragment, orderedPath left right (.unit :: store),
    (orderedPath left right (.unit :: store)).weakenAt_zero_localFragment orderedLowered.localFragment inserted continuation⟩

end Tests.CoreLocalFragmentExactInsertion
