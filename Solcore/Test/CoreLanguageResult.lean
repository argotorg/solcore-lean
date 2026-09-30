import Solcore.Core.LanguageResult
import Solcore.Core.BoundedSafety

set_option autoImplicit false

namespace Tests.CoreLanguageResult

open Solcore.Core
open Solcore.Core.LanguageResult

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)

/-- Failure keeps the first update and bypasses the continuation's update. The
input success type is bool; the output success type is word. -/
private def failedProgram : Program := {
  resultType := resultType .word
  body :=
    .letE (.newCell .word (literal 0)) <|
    bind .word
      (.letE (.storeCell (.var 0) (literal 1)) (failure .bool (literal 41)))
      (.letE (.storeCell (.var 1) (literal 99)) (success (.loadCell (.var 2))))
}

/-- The successful continuation sees the computation's store and its payload.
The true branch changes 1 to 3; neither ignoring ordering nor ignoring the
payload can produce the expected result. -/
private def succeededProgram : Program := {
  resultType := resultType .word
  body :=
    .letE (.newCell .word (literal 0)) <|
    bind .word
      (.letE (.storeCell (.var 0) (literal 1)) (success (.bool true)))
      (.ifE (.var 0)
        (.letE
          (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (literal 2)))
          (success (.loadCell (.var 2))))
        (failure .word (literal 42)))
}

/-- Reference-valued success must preserve the referenced store location. -/
private def referenceProgram : Program := {
  resultType := resultType (.cell .word)
  body := success (.newCell .word (literal 7))
}

private theorem failedProgram_checked : failedProgram.check = true := by decide
private theorem succeededProgram_checked : succeededProgram.check = true := by decide
private theorem referenceProgram_checked : referenceProgram.check = true := by decide

private theorem failure_completed :
    failedProgram.runStateful 80 = .done (.inLeft .word (scalar 41)) [scalar 1] := by rfl

private theorem success_completed :
    succeededProgram.runStateful 80 = .done (.inRight .word (scalar 3)) [scalar 3] := by rfl

private theorem reference_completed :
    referenceProgram.runStateful 8 = .done (.inRight .word (.cellRef .word 0)) [scalar 7] := by
  rfl

example : Evaluates [] [] failedProgram.body (.inLeft .word (scalar 41)) [scalar 1] :=
  runStateful_evaluation_sound failure_completed

example : Evaluates [] [] succeededProgram.body (.inRight .word (scalar 3)) [scalar 3] :=
  runStateful_evaluation_sound success_completed

/-- The skipped continuation need not even have a finite evaluation. -/
example (body : Expr) :
    Evaluates [] [] (bind .word (failure .bool (literal 41)) body)
      (.inLeft .word (scalar 41)) [] :=
  bind_failure .word (failure_evaluates .bool .word)

/-- The result is a failure value, while all finite machine runs remain safe. -/
example (fuel : Nat) :
    (failedProgram.runStateful fuel).HasType (resultType .word) :=
  Program.checked_runStateful_has_type failedProgram_checked fuel

example :
    ∃ world outcome, RuntimeStoreHasTypes world [scalar 1] ∧
      decode? (.inLeft .word (scalar 41)) = some outcome ∧
      outcome.RuntimeHasType world .word :=
  checked_completion_decodes failedProgram_checked rfl failure_completed

example :
    ∃ world outcome, RuntimeStoreHasTypes world [scalar 3] ∧
      decode? (.inRight .word (scalar 3)) = some outcome ∧
      outcome.RuntimeHasType world .word :=
  checked_completion_decodes succeededProgram_checked rfl success_completed

example :
    ∃ world outcome, RuntimeStoreHasTypes world [scalar 7] ∧
      decode? (.inRight .word (.cellRef .word 0)) = some outcome ∧
      outcome.RuntimeHasType world (.cell .word) :=
  checked_completion_decodes referenceProgram_checked rfl reference_completed

example :
    (decode (definitions := []) (.inRight .word (.cellRef .word 0))
      (.inRight .cellRef)).RuntimeHasType
      [.word] (.cell .word) :=
  decode_runtime_hasType (.inRight (.cellRef rfl))

example : decode? (.inLeft .word .unit) = none := rfl
example : decode? (.inRight .bool (scalar 3)) = none := rfl
example : decode? (scalar 41) = none := rfl

example : LanguageResult.run failedProgram 80 = .failed (word 41) [scalar 1] := rfl
example : LanguageResult.run succeededProgram 80 = .succeeded (scalar 3) [scalar 3] := rfl
example : LanguageResult.run failedProgram 0 = .outOfFuel (.initial failedProgram.body) := rfl

example : observeResult (.done .unit []) = .invalidCarrier .unit [] := rfl
example : observeResult (.fault (.unboundVariable 0) (.initial (.var 0))) =
    .internalFault (.unboundVariable 0) (.initial (.var 0)) := rfl

example (fuel : Nat) :
    (LanguageResult.run failedProgram fuel).HasType .word :=
  checked_run_hasType failedProgram_checked rfl fuel

example (fuel : Nat) (value : Value) (store : Store) :
    LanguageResult.run failedProgram fuel ≠ .invalidCarrier value store :=
  checked_run_ne_invalidCarrier failedProgram_checked rfl

example (fuel : Nat) (error : MachineFault) (state : State) :
    LanguageResult.run failedProgram fuel ≠ .internalFault error state :=
  checked_run_ne_internalFault failedProgram_checked rfl

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def run : IO Unit := do
  assertTrue (failedProgram.check && succeededProgram.check && referenceProgram.check)
    "language result programs must pass the ordinary Core checker"
  assertTrue (failedProgram.runStateful 80 == .done (.inLeft .word (scalar 41)) [scalar 1])
    "failure must preserve earlier effects and skip continuation effects"
  assertTrue (succeededProgram.runStateful 80 == .done (.inRight .word (scalar 3)) [scalar 3])
    "success must pass the payload and updated store to the continuation"
  assertTrue (referenceProgram.runStateful 8 ==
      .done (.inRight .word (.cellRef .word 0)) [scalar 7])
    "success must retain cell identity in its payload"
  assertTrue (decode? (.inLeft .word (scalar 41)) == some (.failed (word 41)))
    "completed failure must decode as a language failure reason"
  assertTrue (decode? (.inRight .word (scalar 3)) == some (.succeeded (scalar 3)))
    "completed success must decode its original payload"
  assertTrue ((decode? (.inLeft .word .unit)).isNone &&
      (decode? (.inRight .bool (scalar 3))).isNone && (decode? (scalar 41)).isNone)
    "malformed carriers must not decode as success or language failure"
  assertTrue (LanguageResult.run failedProgram 80 == .failed (word 41) [scalar 1])
    "the observation facade must preserve language failure and its final store"
  assertTrue (LanguageResult.run succeededProgram 80 == .succeeded (scalar 3) [scalar 3])
    "the observation facade must preserve successful payloads and their final store"
  assertTrue (LanguageResult.run failedProgram 0 == .outOfFuel (.initial failedProgram.body))
    "the observation facade must retain the exact exhaustion checkpoint"
  assertTrue (observeResult (.done .unit []) == .invalidCarrier .unit [])
    "a malformed completion must remain distinct from language failure"
  assertTrue (observeResult (.fault (.unboundVariable 0) (.initial (.var 0))) ==
      .internalFault (.unboundVariable 0) (.initial (.var 0)))
    "the observation facade must retain the internal fault and its state"

end Tests.CoreLanguageResult
