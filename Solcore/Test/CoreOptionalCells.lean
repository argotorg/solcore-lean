import Solcore.Core.OptionalCell
import Solcore.Core.BoundedSafety
import Solcore.Core.ExactFuelProperties

/-! Optional cells return ordinary language failures for uninitialized reads.
The same representation handles aliases, closures and shared references. -/

set_option autoImplicit false

namespace Tests.CoreOptionalCells

open Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def reason : Word := word 21

private def freshProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := OptionalCell.read .word (OptionalCell.allocate .word) reason
}

private theorem fresh_checked : freshProgram.check = true := by decide

/-- The new cell contains a marker rather than an arbitrary Word. Its read
finishes with a language failure, and preserves that marker in the heap. -/
private theorem fresh_evaluates :
    Evaluates [] [] freshProgram.body (.inLeft .word (.word reason))
      [.inLeft .word .unit] :=
  OptionalCell.read_failure reason (OptionalCell.allocate_evaluates .word [] []) rfl

example : freshProgram.runStateful 12 =
    .done (.inLeft .word (.word reason)) [.inLeft .word .unit] := by rfl

example : ∃ checkpoint, freshProgram.runStateful 11 = .outOfFuel checkpoint :=
  ⟨_, rfl⟩

example (fuel : Nat) :
    (freshProgram.runStateful fuel).HasType (LanguageResult.resultType .word) :=
  Program.checked_runStateful_has_type fresh_checked fuel

private def initializedProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := OptionalCell.read .word
    (OptionalCell.allocateInitialized .word (literal 9)) reason
}

example : initializedProgram.check = true := by decide

example : Evaluates [] [] initializedProgram.body (.inRight .word (scalar 9))
    [.inRight .unit (scalar 9)] :=
  OptionalCell.read_success reason (OptionalCell.allocateInitialized_evaluates .word) rfl

example : initializedProgram.runStateful 12 =
    .done (.inRight .word (scalar 9)) [.inRight .unit (scalar 9)] := by rfl

/-- Write through an alias, then read through the original handle. -/
private def aliasProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (OptionalCell.allocate .word)
    (.letE (.var 0)
      (LanguageResult.bind .word (OptionalCell.write (.var 0) (literal 7))
        (OptionalCell.read .word (.var 2) reason)))
}

private theorem alias_checked : aliasProgram.check = true := by decide

private theorem alias_completed : aliasProgram.runStateful 64 =
    .done (.inRight .word (scalar 7)) [.inRight .unit (scalar 7)] := by rfl

example : ∃ world,
    RuntimeStoreHasTypes world [.inRight .unit (scalar 7)] ∧
    RuntimeValueHasType world (.inRight .word (scalar 7))
      (LanguageResult.resultType .word) :=
  Program.checked_runStateful_preserves_result_type alias_checked alias_completed

/-- If the read fails, the bind never evaluates its continuation's mutation. -/
private def shortCircuitProgram : Program := {
  resultType := LanguageResult.resultType .unit
  body := .letE (OptionalCell.allocate .word)
    (.letE (.newCell .word (literal 99))
      (LanguageResult.bind .unit (OptionalCell.read .word (.var 1) reason)
        (LanguageResult.success (.storeCell (.var 1) (literal 100)))))
}

private theorem shortCircuit_checked : shortCircuitProgram.check = true := by decide

private theorem shortCircuit_evaluates :
    Evaluates [] [] shortCircuitProgram.body (.inLeft .unit (.word reason))
      [.inLeft .word .unit, scalar 99] := by
  exact .letE (OptionalCell.allocate_evaluates .word [] [])
    (.letE (.newCell .word)
      (LanguageResult.bind_failure .unit
        (OptionalCell.read_failure reason (.var rfl) rfl)))

example : shortCircuitProgram.runStateful 64 =
    .done (.inLeft .unit (.word reason)) [.inLeft .word .unit, scalar 99] := by rfl

private def functionType : Ty := .function .word .word

/-- Captures are optional alias, original optional reference, and shared counter. -/
private def functionBody : Expr :=
  .letE (.storeCell (.var 3) (.var 0)) (.loadCell (.var 4))

/-- An uninitialized function binding requires no dummy closure. Installing a
closure preserves its two aliases and its shared mutable counter. -/
private def functionProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 3))
    (.letE (OptionalCell.allocate functionType)
      (.letE (.var 0)
        (LanguageResult.bind .word
          (OptionalCell.write (.var 0) (.lambda .word .word functionBody))
          (LanguageResult.bind .word
            (OptionalCell.read functionType (.var 2) reason)
            (LanguageResult.success (.apply (.var 0) (literal 7)))))))
}

private def installedClosure : Value :=
  .closure .word .word functionBody
    [.cellRef (OptionalCell.cellType functionType) 1,
     .cellRef (OptionalCell.cellType functionType) 1, .cellRef .word 0]

private def functionStore : Store :=
  [scalar 7, .inRight .unit installedClosure]

private theorem function_checked : functionProgram.check = true := by decide

set_option maxRecDepth 2048 in
private theorem function_completed : functionProgram.runStateful 128 =
    .done (.inRight .word (scalar 7)) functionStore := by rfl

/-- The optional function's captures include its own cell, and remain valid
after the captured counter is mutated through that same shared store. -/
example : RuntimeStoreHasTypes [.word, OptionalCell.cellType functionType] functionStore := by
  obtain ⟨world, stored, _⟩ :=
    Program.checked_runStateful_preserves_result_type function_checked function_completed
  have exactWorld : world = [.word, OptionalCell.cellType functionType] := by
    simpa only [functionStore, List.map_cons, List.map_nil, Value.type,
      scalar, installedClosure, OptionalCell.cellType, functionType] using stored.world_eq
  change RuntimeStoreHasTypes world functionStore at stored
  simpa only [exactWorld] using stored

/-- The ordinary checked-machine guarantee applies to every suspension and
its resumed run, including the eventual language failure. -/
example (fuel additional : Nat) (checkpoint : State)
    (exhausted : shortCircuitProgram.runStateful fuel = .outOfFuel checkpoint) :
    StateHasType checkpoint (LanguageResult.resultType .unit) ∧
    (runStateful additional checkpoint).HasType (LanguageResult.resultType .unit) ∧
    runStateful additional checkpoint = shortCircuitProgram.runStateful (fuel + additional) := by
  have typed := initial_state_has_type
    (Program.check_full_sound shortCircuit_checked).bodyHasType
  have checkpointTyped := well_typed_runStateful_preserves_checkpoint_type typed exhausted
  exact ⟨checkpointTyped, well_typed_runStateful_resume_has_type typed exhausted additional⟩

example : ∃ required world,
    RuntimeStoreHasTypes world [.inLeft .word .unit, scalar 99] ∧
    RuntimeValueHasType world (.inLeft .unit (.word reason)) (LanguageResult.resultType .unit) ∧
    ∀ fuel, required ≤ fuel → shortCircuitProgram.runStateful fuel =
      .done (.inLeft .unit (.word reason)) [.inLeft .word .unit, scalar 99] := by
  obtain ⟨world, _, stored, typed⟩ := evaluation_preserves_type shortCircuit_evaluates
    (Program.check_full_sound shortCircuit_checked).bodyHasType .nil (.nil [])
  obtain ⟨required, completes⟩ :=
    evaluation_runStateful_complete_with_sufficient_fuel shortCircuit_evaluates
  exact ⟨required, world, stored, typed, completes⟩

/-- Nominal declarations are supported by the same allocation/read typing rule. -/
example {definitions : DataEnvironment} {context : Context} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) (reason : Word) :
    HasType context (OptionalCell.read type (OptionalCell.allocate type) reason)
      (LanguageResult.resultType type) definitions :=
  OptionalCell.read_hasType reason wellFormed (OptionalCell.allocate_hasType wellFormed)

end Tests.CoreOptionalCells
