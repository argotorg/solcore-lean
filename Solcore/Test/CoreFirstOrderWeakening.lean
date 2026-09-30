import Solcore.Core.FirstOrderWeakening

/-! Inserting an initializer's temporary value after a fresh lexical binder
preserves the old binder order and the exact finite first-order result. -/

set_option autoImplicit false

namespace Tests.CoreFirstOrderWeakening

open Solcore.Core

private def number : Word := Word.ofNatModulo 7
private def body : Expr := .pair (.var 0) (.var 1)
private def environment : Environment := [.word number, .bool true]
private def context : Context := [.word, .bool]
private def result : Value := .pair (.word number) (.bool true)

private theorem evaluation : Evaluates environment [] body result [] :=
  .pair (.var rfl) (.var rfl)

private theorem typed : HasType context body (.product .word .bool) :=
  .pair (.var rfl) (.var rfl)

private theorem environmentTyped : RuntimeEnvironmentHasTypes [] environment context :=
  .cons .word (.cons .bool .nil)

private theorem emptyStore : StoreHasTypes [] [] := {
  length_eq := rfl
  lookup := by intro location type found; simp at found
}

example : Evaluates [.word number, .unit, .bool true] [] (body.weakenAt 1) result [] :=
  evaluation.weakenAt_cellPayload typed (.product .word .bool)
    environmentTyped (.nil []) emptyStore 1 .unit

example : (body.weakenAt 1) = .pair (.var 0) (.var 2) := by
  simp [body, Expr.weakenAt]

example : runStateful 20
    (.initial (body.weakenAt 1) [.word number, .unit, .bool true] []) = .done result [] := by
  simp [body, Expr.weakenAt, result]
  rfl

end Tests.CoreFirstOrderWeakening
