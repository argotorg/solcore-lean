import Solcore.Core.LocalControl
import Solcore.Core.ExactFuelProperties

/-! Control sums retain condition effects, early returns, failures and the
heap shared with scoped blocks. Every completion here has an actual finite run. -/

set_option autoImplicit false

namespace Tests.CoreLocalControl

open Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def reason : Word := word 31

example {environment : Environment} {store : Store} (next : Expr) :
    Evaluates environment store
      (LocalControl.sequence .word (LocalControl.returned (literal 7)) next)
      (.inRight .word (.inRight .unit (scalar 7))) store :=
  LocalControl.sequence_returned .word (LocalControl.returned_evaluates .word)

private def conditionalProgram (select : Bool) : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 3))
    (LocalControl.finish .word
      (LocalControl.conditional .word
        (LanguageResult.success (.letE (.storeCell (.var 0) (literal 11)) (.bool select)))
        (LocalControl.returned (.loadCell (.var 0)))
        (LocalControl.returned
          (.letE (.storeCell (.var 0) (literal 17)) (.loadCell (.var 1)))))
      (LanguageResult.failure .word (.word reason)))
}

example (select : Bool) : (conditionalProgram select).check = true := by
  cases select <;> simp [conditionalProgram, LocalControl.finish, LocalControl.conditional, LocalControl.returned,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  all_goals decide

example : (conditionalProgram true).runStateful 100 =
    .done (.inRight .word (scalar 11)) [scalar 11] := by
  simp [conditionalProgram, LocalControl.finish, LocalControl.conditional, LocalControl.returned,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  rfl

example : (conditionalProgram false).runStateful 100 =
    .done (.inRight .word (scalar 17)) [scalar 17] := by
  simp [conditionalProgram, LocalControl.finish, LocalControl.conditional, LocalControl.returned,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  rfl

private def conditionFailureProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 3))
    (LocalControl.finish .word
      (LocalControl.sequence .word
        (LocalControl.conditional .word
          (LanguageResult.failure .bool
            (.letE (.storeCell (.var 0) (literal 11)) (.word reason)))
          (LocalControl.returned (.letE (.storeCell (.var 0) (literal 99)) (literal 7)))
          (LocalControl.returned (.letE (.storeCell (.var 0) (literal 98)) (literal 8))))
        (LocalControl.returned (.letE (.storeCell (.var 0) (literal 97)) (literal 9))))
      (LanguageResult.failure .word (.word reason)))
}

example : conditionFailureProgram.check = true := by
  simp [conditionFailureProgram, LocalControl.finish, LocalControl.sequence, LocalControl.conditional,
    LocalControl.returned, LanguageResult.bind, LanguageResult.failure, LanguageResult.success,
    Expr.weakenAt, literal]
  decide

/-- Condition failure keeps its write and skips both branches and the tail. -/
example : conditionFailureProgram.runStateful 100 =
    .done (.inLeft .word (.word reason)) [scalar 11] := by
  simp [conditionFailureProgram, LocalControl.finish, LocalControl.sequence, LocalControl.conditional,
    LocalControl.returned, LanguageResult.bind, LanguageResult.failure, LanguageResult.success,
    Expr.weakenAt, literal]
  rfl

private def scopedFallthroughProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 3))
    (LocalControl.finish .word
      (LocalControl.sequence .word
        (LocalSequence.letInitialized (LocalControl.controlType .word) .word
          (LanguageResult.success (literal 7))
          (LocalSequence.discard (LocalControl.controlType .word)
            (OptionalCell.write (.var 0) (literal 9))
            (.letE (.storeCell (.var 1) (literal 11)) (LocalControl.fallthrough .word))))
        (LocalControl.returned (.loadCell (.var 0))))
      (LanguageResult.failure .word (.word reason)))
}

example : scopedFallthroughProgram.check = true := by
  simp [scopedFallthroughProgram, LocalControl.finish, LocalControl.sequence, LocalControl.returned,
    LocalControl.fallthrough, LocalSequence.letInitialized, LocalSequence.discard,
    OptionalCell.allocateInitialized, OptionalCell.write, LanguageResult.bind,
    LanguageResult.failure, LanguageResult.success, Expr.weakenAt, literal]
  decide

/-- The block's local reference stays out of the outer lexical environment;
its allocation and writes remain in the shared heap. The tail reads the outer
counter, rather than the block's optional cell. -/
example : scopedFallthroughProgram.runStateful 150 =
    .done (.inRight .word (scalar 11)) [scalar 11, .inRight .unit (scalar 9)] := by
  simp [scopedFallthroughProgram, LocalControl.finish, LocalControl.sequence, LocalControl.returned,
    LocalControl.fallthrough, LocalSequence.letInitialized, LocalSequence.discard,
    OptionalCell.allocateInitialized, OptionalCell.write, LanguageResult.bind,
    LanguageResult.failure, LanguageResult.success, Expr.weakenAt, literal]
  rfl

private def earlyReturnProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 3))
    (LocalControl.finish .word
      (LocalControl.sequence .word
        (LocalSequence.letInitialized (LocalControl.controlType .word) .word
          (LanguageResult.success (literal 7))
          (LocalControl.conditional .word (LanguageResult.success (.bool true))
            (LocalControl.returnValue .word (OptionalCell.read .word (.var 0) reason))
            (LocalControl.fallthrough .word)))
        (LocalControl.returned (.letE (.storeCell (.var 0) (literal 99)) (.loadCell (.var 1)))))
      (LanguageResult.failure .word (.word reason)))
}

private theorem earlyReturn_checked : earlyReturnProgram.check = true := by
  simp [earlyReturnProgram, LocalControl.finish, LocalControl.sequence, LocalControl.conditional,
    LocalControl.returnValue, LocalControl.returned, LocalControl.fallthrough,
    LocalSequence.letInitialized, OptionalCell.allocateInitialized, OptionalCell.read,
    LanguageResult.bind, LanguageResult.failure, LanguageResult.success, Expr.weakenAt, literal]
  decide

private theorem earlyReturn_completed : earlyReturnProgram.runStateful 150 =
    .done (.inRight .word (scalar 7)) [scalar 3, .inRight .unit (scalar 7)] := by
  simp [earlyReturnProgram, LocalControl.finish, LocalControl.sequence, LocalControl.conditional,
    LocalControl.returnValue, LocalControl.returned, LocalControl.fallthrough,
    LocalSequence.letInitialized, OptionalCell.allocateInitialized, OptionalCell.read,
    LanguageResult.bind, LanguageResult.failure, LanguageResult.success, Expr.weakenAt, literal]
  rfl

/-- A successful Unit fallthrough is chosen explicitly at the function boundary. -/
example : Evaluates [] []
    (LocalControl.finish .unit (LocalControl.fallthrough .unit) (LanguageResult.success .unit))
    (.inRight .word .unit) [] := by
  apply LocalControl.finish_fallthrough .unit (LocalControl.fallthrough_evaluates _ _ _)
  simp [LanguageResult.success, Expr.weakenAt]
  exact .inRight .unit

/-- A missing-return fallback is a normal language failure, rather than an
internal machine fault, and it executes after the block's preceding effects. -/
example : Evaluates [.cellRef .word 0] [scalar 3]
    (LocalControl.finish .word
      (.letE (.storeCell (.var 0) (literal 11)) (LocalControl.fallthrough .word))
      (LanguageResult.failure .word
        (.letE (.storeCell (.var 0) (literal 17)) (.word reason))))
    (.inLeft .word (.word reason)) [scalar 17] := by
  apply LocalControl.finish_fallthrough .word
  · exact .letE (.storeCell (.var rfl) rfl .word rfl)
      (LocalControl.fallthrough_evaluates _ _ _)
  · simp [LanguageResult.failure, Expr.weakenAt, literal]
    exact .inLeft (.letE (.storeCell (.var rfl) rfl .word rfl) .word)

example (fuel : Nat) : (earlyReturnProgram.runStateful fuel).HasType earlyReturnProgram.resultType :=
  Program.checked_runStateful_has_type earlyReturn_checked fuel

example (fuel additional : Nat) (checkpoint : State)
    (exhausted : earlyReturnProgram.runStateful fuel = .outOfFuel checkpoint) :
    runStateful additional checkpoint = earlyReturnProgram.runStateful (fuel + additional) :=
  runStateful_resume exhausted additional

example : ∃ required, ∀ fuel, required ≤ fuel → earlyReturnProgram.runStateful fuel =
    .done (.inRight .word (scalar 7)) [scalar 3, .inRight .unit (scalar 7)] :=
  evaluation_runStateful_complete_with_sufficient_fuel
    (runStateful_evaluation_sound earlyReturn_completed)

end Tests.CoreLocalControl
