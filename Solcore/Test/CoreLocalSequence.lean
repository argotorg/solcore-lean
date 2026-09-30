import Solcore.Core.LocalSequence
import Solcore.Core.ExactFuelProperties

/-! Local statement helpers retain evaluation order, failure effects, lexical
cell references and actual fuel checkpoints. -/

set_option autoImplicit false

namespace Tests.CoreLocalSequence

open Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def reason : Word := word 21

example : Evaluates [] []
    (LocalSequence.letUninitialized .word (OptionalCell.read .word (.var 0) reason))
    (.inLeft .word (.word reason)) [.inLeft .word .unit] :=
  LocalSequence.letUninitialized_evaluates .word
    (OptionalCell.read_failure reason (.var rfl) rfl)

/-- A payload inserted at index one leaves the lexical reference at index zero. -/
example : Evaluates [] []
    (LocalSequence.letInitialized .word .word (LanguageResult.success (literal 7))
      (OptionalCell.read .word (.var 0) reason))
    (.inRight .word (scalar 7)) [.inRight .unit (scalar 7)] := by
  apply LocalSequence.letInitialized_success .word .word (.inRight .word)
  simpa [OptionalCell.read, LanguageResult.success, LanguageResult.failure, Expr.weakenAt, scalar, literal] using
    (OptionalCell.read_success (type := .word) (reference := .var 0) reason
      (environment := [.cellRef (OptionalCell.cellType .word) 0, scalar 7])
      (referenceStore := [.inRight .unit (scalar 7)]) (.var rfl) rfl)

private def assignmentProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := LocalSequence.letUninitialized .word
    (LocalSequence.assign .word (.var 0) (LanguageResult.success (literal 7))
      (LocalSequence.discard .word (OptionalCell.write (.var 0) (literal 9))
        (OptionalCell.read .word (.var 0) reason)))
}

private theorem assignment_checked : assignmentProgram.check = true := by
  simp [assignmentProgram, LocalSequence.letUninitialized, LocalSequence.assign,
    LocalSequence.discard, OptionalCell.allocate, OptionalCell.write, OptionalCell.read,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt,
    literal]
  decide

private theorem assignment_completed : assignmentProgram.runStateful 128 =
    .done (.inRight .word (scalar 9)) [.inRight .unit (scalar 9)] := by
  simp [assignmentProgram, LocalSequence.letUninitialized, LocalSequence.assign,
    LocalSequence.discard, OptionalCell.allocate, OptionalCell.write, OptionalCell.read,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt,
    literal]
  rfl

/-- Capture the reference first: its effect changes the counter read by the RHS.
The RHS and continuation still share the same original optional cell. -/
private def capturedReferenceProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := LocalSequence.letUninitialized .word
    (.letE (.newCell .word (literal 3))
      (LocalSequence.assign .word
        (.letE (.storeCell (.var 0) (literal 11)) (.var 2))
        (LanguageResult.success (.loadCell (.var 0)))
        (OptionalCell.read .word (.var 1) reason)))
}

example : capturedReferenceProgram.check = true := by
  simp [capturedReferenceProgram, LocalSequence.letUninitialized, LocalSequence.assign,
    OptionalCell.allocate, OptionalCell.read, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.weakenAt, literal]
  decide

example : capturedReferenceProgram.runStateful 128 =
    .done (.inRight .word (scalar 11)) [.inRight .unit (scalar 11), scalar 11] := by
  simp [capturedReferenceProgram, LocalSequence.letUninitialized, LocalSequence.assign,
    OptionalCell.allocate, OptionalCell.read, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.weakenAt, literal]
  rfl

/-- Reference and RHS effects are retained on RHS failure. Neither the target
write nor the continuation's counter mutation takes place. -/
private def rhsFailureProgram : Program := {
  resultType := LanguageResult.resultType .unit
  body := LocalSequence.letUninitialized .word
    (.letE (.newCell .word (literal 3))
      (LocalSequence.assign .unit
        (.letE (.storeCell (.var 0) (literal 11)) (.var 2))
        (LanguageResult.failure .word
          (.letE (.storeCell (.var 0) (literal 17)) (.word reason)))
        (LanguageResult.success (.storeCell (.var 0) (literal 99)))))
}

private theorem rhsFailure_checked : rhsFailureProgram.check = true := by
  simp [rhsFailureProgram, LocalSequence.letUninitialized, LocalSequence.assign,
    OptionalCell.allocate, LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Expr.weakenAt, literal]
  decide

private theorem rhsFailure_completed : rhsFailureProgram.runStateful 128 =
    .done (.inLeft .unit (.word reason)) [.inLeft .word .unit, scalar 17] := by
  simp [rhsFailureProgram, LocalSequence.letUninitialized, LocalSequence.assign,
    OptionalCell.allocate, LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Expr.weakenAt, literal]
  rfl

/-- Initializer effects finish before the new local cell is allocated. The body
uses its new lexical reference and the existing counter reference. -/
private def initializedEffectsProgram : Program := {
  resultType := LanguageResult.resultType (.product .word .word)
  body := .letE (.newCell .word (literal 3))
    (LocalSequence.letInitialized (.product .word .word) .word
      (LanguageResult.success (.letE (.storeCell (.var 0) (literal 11)) (literal 7)))
      (LocalSequence.pair .word .word
        (OptionalCell.read .word (.var 0) reason)
        (LanguageResult.success (.loadCell (.var 1)))))
}

example : initializedEffectsProgram.check = true := by
  simp [initializedEffectsProgram, LocalSequence.letInitialized, LocalSequence.pair,
    OptionalCell.allocateInitialized, OptionalCell.read, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  decide

example : initializedEffectsProgram.runStateful 128 =
    .done (.inRight .word (.pair (scalar 7) (scalar 11)))
      [scalar 11, .inRight .unit (scalar 7)] := by
  simp [initializedEffectsProgram, LocalSequence.letInitialized, LocalSequence.pair,
    OptionalCell.allocateInitialized, OptionalCell.read, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  rfl

private def initializerFailureProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := LocalSequence.letInitialized .word .word
    (LanguageResult.failure .word (.letE (.newCell .word (literal 23)) (.word reason)))
    (LanguageResult.success (literal 99))
}

example : initializerFailureProgram.check = true := by
  simp [initializerFailureProgram, LocalSequence.letInitialized,
    OptionalCell.allocateInitialized, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.weakenAt, literal]
  decide

/-- A failed initializer keeps its preceding allocation and skips allocation
of the optional binding itself. -/
example : initializerFailureProgram.runStateful 64 =
    .done (.inLeft .word (.word reason)) [scalar 23] := by
  simp [initializerFailureProgram, LocalSequence.letInitialized,
    OptionalCell.allocateInitialized, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.weakenAt, literal]
  rfl

private def discardFailureProgram : Program := {
  resultType := LanguageResult.resultType (.cell .word)
  body := LocalSequence.discard (.cell .word) (LanguageResult.failure .unit (.word reason))
    (LanguageResult.success (.newCell .word (literal 7)))
}

example : discardFailureProgram.check = true := by
  simp [discardFailureProgram, LocalSequence.discard, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  decide

example : discardFailureProgram.runStateful 64 =
    .done (.inLeft (.cell .word) (.word reason)) [] := by
  simp [discardFailureProgram, LocalSequence.discard, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  rfl

private def pairProgram : Program := {
  resultType := LanguageResult.resultType (.product .word .word)
  body := .letE (.newCell .word (literal 0))
    (LocalSequence.pair .word .word
      (LanguageResult.success
        (.letE (.storeCell (.var 0) (literal 11)) (.loadCell (.var 1))))
      (LanguageResult.success
        (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (literal 1)))
          (.loadCell (.var 1)))))
}

example : pairProgram.check = true := by
  simp [pairProgram, LocalSequence.pair, LanguageResult.bind, LanguageResult.success,
    Expr.weakenAt, literal]
  decide

/-- The right element observes the left element's mutation of the same counter. -/
example : pairProgram.runStateful 128 =
    .done (.inRight .word (.pair (scalar 11) (scalar 12))) [scalar 12] := by
  simp [pairProgram, LocalSequence.pair, LanguageResult.bind, LanguageResult.success,
    Expr.weakenAt, literal]
  rfl

private def pairFailureProgram : Program := {
  resultType := LanguageResult.resultType (.product .word .word)
  body := .letE (.newCell .word (literal 0))
    (LocalSequence.pair .word .word
      (LanguageResult.success (.letE (.storeCell (.var 0) (literal 11)) (literal 7)))
      (LanguageResult.failure .word (.letE (.storeCell (.var 0) (literal 12)) (.word reason))))
}

example : pairFailureProgram.check = true := by
  simp [pairFailureProgram, LocalSequence.pair, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.weakenAt, literal]
  decide

example : pairFailureProgram.runStateful 128 =
    .done (.inLeft (.product .word .word) (.word reason)) [scalar 12] := by
  simp [pairFailureProgram, LocalSequence.pair, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.weakenAt, literal]
  rfl

example (fuel : Nat) :
    (assignmentProgram.runStateful fuel).HasType (LanguageResult.resultType .word) :=
  Program.checked_runStateful_has_type assignment_checked fuel

/-- RHS failure is a typed completion; its genuine intermediate checkpoints
retain both typing and the same run on resume. -/
example (fuel additional : Nat) (checkpoint : State)
    (exhausted : rhsFailureProgram.runStateful fuel = .outOfFuel checkpoint) :
    (runStateful additional checkpoint).HasType (LanguageResult.resultType .unit) ∧
    runStateful additional checkpoint = rhsFailureProgram.runStateful (fuel + additional) :=
  well_typed_runStateful_resume_has_type
    (initial_state_has_type (Program.check_full_sound rhsFailure_checked).bodyHasType)
    exhausted additional

example : ∃ required world,
    RuntimeStoreHasTypes world [.inLeft .word .unit, scalar 17] ∧
    RuntimeValueHasType world (.inLeft .unit (.word reason)) (LanguageResult.resultType .unit) ∧
    ∀ fuel, required ≤ fuel → rhsFailureProgram.runStateful fuel =
      .done (.inLeft .unit (.word reason)) [.inLeft .word .unit, scalar 17] := by
  have evaluation := runStateful_evaluation_sound rhsFailure_completed
  obtain ⟨world, _, stored, typed⟩ := evaluation_preserves_type evaluation
    (Program.check_full_sound rhsFailure_checked).bodyHasType .nil (.nil [])
  obtain ⟨required, completes⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨required, world, stored, typed, completes⟩

end Tests.CoreLocalSequence
