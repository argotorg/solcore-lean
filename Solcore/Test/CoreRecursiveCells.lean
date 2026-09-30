import Solcore.Core.BoundedSafety
import Solcore.Core.ExactFuelProperties

/-! Terminating recursion through ordinary closure cells. The observations
include results, shared mutation counts, returned references, and exact stores. -/

set_option autoImplicit false

namespace Tests.CoreRecursiveCells

open Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)

private def sumFunctionType : Ty := .function .word .word

/-- Entry environment: argument, self reference, shared counter reference.
The sequencing let shifts all three positions before the recursive branch. -/
private def sumBody : Expr :=
  .letE
    (.storeCell (.var 2) (.binary .wordAdd (.loadCell (.var 2)) (literal 1)))
    (.ifE (.binary .wordEq (.var 1) (literal 0))
      (literal 0)
      (.binary .wordAdd (.var 1)
        (.apply (.loadCell (.var 2)) (.binary .wordSub (.var 1) (literal 1)))))

private def sumObservationType : Ty :=
  .product .word (.product .word
    (.product .word (.product (.cell sumFunctionType) (.cell .word))))

/-- Invoke the input function twice. Its two calls and all recursive calls
share the same captured cells. The client returns both cell handles as well. -/
private def callSumTwice : Expr :=
  .lambda sumFunctionType sumObservationType
    (.letE (.apply (.var 0) (literal 3))
      (.letE (.apply (.var 1) (literal 2))
        (.pair (.var 1)
          (.pair (.var 0)
            (.pair (.loadCell (.var 5)) (.pair (.var 4) (.var 5)))))))

private def sumProgram : Program := {
  resultType := sumObservationType
  body :=
    .letE (.newCell .word (literal 0))
      (.letE (.newCell sumFunctionType (.lambda .word .word (literal 0)))
        (.letE (.storeCell (.var 0) (.lambda .word .word sumBody))
          (.apply callSumTwice (.loadCell (.var 1)))))
}

private theorem sumProgram_checked : sumProgram.check = true := by decide

private def sumClosure : Value :=
  .closure .word .word sumBody [.cellRef sumFunctionType 1, .cellRef .word 0]

private def sumObservation : Value :=
  .pair (scalar 6) (.pair (scalar 3)
    (.pair (scalar 7) (.pair (.cellRef sumFunctionType 1) (.cellRef .word 0))))

private def sumStore : Store := [scalar 7, sumClosure]

private def parityFunctionType : Ty := .function .word .bool

/-- Entry environment: argument, odd reference, even reference, shared count. -/
private def evenBody : Expr :=
  .letE
    (.storeCell (.var 3) (.binary .wordAdd (.loadCell (.var 3)) (literal 1)))
    (.ifE (.binary .wordEq (.var 1) (literal 0))
      (.bool true)
      (.apply (.loadCell (.var 2)) (.binary .wordSub (.var 1) (literal 1))))

/-- The prior installation contributes a captured unit before both references. -/
private def oddBody : Expr :=
  .letE
    (.storeCell (.var 4) (.binary .wordAdd (.loadCell (.var 4)) (literal 1)))
    (.ifE (.binary .wordEq (.var 1) (literal 0))
      (.bool false)
      (.apply (.loadCell (.var 4)) (.binary .wordSub (.var 1) (literal 1))))

private def parityObservationType : Ty :=
  .product .bool (.product .bool (.product .word
    (.product (.cell parityFunctionType) (.product (.cell parityFunctionType) (.cell .word)))))

private def parityProgram : Program := {
  resultType := parityObservationType
  body :=
    .letE (.newCell .word (literal 0)) <|
    .letE (.newCell parityFunctionType (.lambda .word .bool (.bool false))) <|
    .letE (.newCell parityFunctionType (.lambda .word .bool (.bool false))) <|
    .letE (.storeCell (.var 1) (.lambda .word .bool evenBody)) <|
    .letE (.storeCell (.var 1) (.lambda .word .bool oddBody)) <|
    .letE (.apply (.loadCell (.var 3)) (literal 4)) <|
    .letE (.apply (.loadCell (.var 3)) (literal 3)) <|
    .pair (.var 1) (.pair (.var 0) (.pair (.loadCell (.var 6))
      (.pair (.var 5) (.pair (.var 4) (.var 6)))))
}

private theorem parityProgram_checked : parityProgram.check = true := by decide

private def evenClosure : Value :=
  .closure .word .bool evenBody
    [.cellRef parityFunctionType 2, .cellRef parityFunctionType 1, .cellRef .word 0]

private def oddClosure : Value :=
  .closure .word .bool oddBody
    [.unit, .cellRef parityFunctionType 2, .cellRef parityFunctionType 1, .cellRef .word 0]

private def parityObservation : Value :=
  .pair (.bool true) (.pair (.bool true) (.pair (scalar 9)
    (.pair (.cellRef parityFunctionType 1)
      (.pair (.cellRef parityFunctionType 2) (.cellRef .word 0)))))

private def parityStore : Store := [scalar 9, evenClosure, oddClosure]

/-! These bounds count actual machine transitions. In particular, admission is
checked separately from the finite execution evidence below. -/

set_option maxRecDepth 4096 in
private theorem sum_completed :
    sumProgram.runStateful 274 = .done sumObservation sumStore := by rfl

set_option maxRecDepth 4096 in
private theorem sum_predecessor_exhausted :
    ∃ checkpoint, sumProgram.runStateful 273 = .outOfFuel checkpoint := by
  exact ⟨_, rfl⟩

set_option maxRecDepth 4096 in
private theorem parity_completed :
    parityProgram.runStateful 329 = .done parityObservation parityStore := by rfl

set_option maxRecDepth 4096 in
private theorem parity_predecessor_exhausted :
    ∃ checkpoint, parityProgram.runStateful 328 = .outOfFuel checkpoint := by
  exact ⟨_, rfl⟩

private theorem exact_steps_of_boundary
    {start : State} {cost : Nat} {value : Value} {store : Store}
    (completed : runStateful (cost + 1) start = .done value store)
    (exhausted : ∃ checkpoint, runStateful cost start = .outOfFuel checkpoint) :
    Steps (cost + 1) start (State.final value store) := by
  obtain ⟨actual, enough, path⟩ := runStateful_sound completed
  have lower : cost < actual := path.runStateful_outOfFuel_iff.mp exhausted
  have exactCost : actual = cost + 1 := by omega
  simpa only [exactCost] using path

private theorem sum_steps :
    Steps 274 (State.initial sumProgram.body) (State.final sumObservation sumStore) :=
  exact_steps_of_boundary sum_completed sum_predecessor_exhausted

private theorem parity_steps :
    Steps 329 (State.initial parityProgram.body)
      (State.final parityObservation parityStore) :=
  exact_steps_of_boundary parity_completed parity_predecessor_exhausted

private theorem sum_exact_fuel (fuel : Nat) :
    sumProgram.runStateful fuel = .done sumObservation sumStore ↔ 274 ≤ fuel :=
  sum_steps.runStateful_done_iff

private theorem parity_exact_fuel (fuel : Nat) :
    parityProgram.runStateful fuel = .done parityObservation parityStore ↔ 329 ≤ fuel :=
  parity_steps.runStateful_done_iff

private theorem sum_evaluates :
    Evaluates [] [] sumProgram.body sumObservation sumStore :=
  runStateful_evaluation_sound sum_completed

private theorem parity_evaluates :
    Evaluates [] [] parityProgram.body parityObservation parityStore :=
  runStateful_evaluation_sound parity_completed

/-- The runtime world types both the self reference in the closure and the
returned handle without recursively unfolding the store. -/
private theorem sum_result_typed :
    RuntimeStoreHasTypes [.word, sumFunctionType] sumStore ∧
      RuntimeValueHasType [.word, sumFunctionType] sumObservation sumObservationType := by
  obtain ⟨world, stored, typed⟩ :=
    Program.checked_runStateful_preserves_result_type sumProgram_checked sum_completed
  have sameWorld : world = [.word, sumFunctionType] := stored.world_eq
  subst world
  exact ⟨stored, typed⟩

/-- Both closure cells contain references to the same two function locations
and the same counter, including references forming a cycle. -/
private theorem parity_result_typed :
    RuntimeStoreHasTypes [.word, parityFunctionType, parityFunctionType] parityStore ∧
      RuntimeValueHasType [.word, parityFunctionType, parityFunctionType]
        parityObservation parityObservationType := by
  obtain ⟨world, stored, typed⟩ :=
    Program.checked_runStateful_preserves_result_type parityProgram_checked parity_completed
  have sameWorld : world = [.word, parityFunctionType, parityFunctionType] := stored.world_eq
  subst world
  exact ⟨stored, typed⟩

/-- Resume the actual pre-completion checkpoint, retaining its cyclic heap. -/
private theorem sum_resume_typed :
    ∃ checkpoint,
      sumProgram.runStateful 273 = .outOfFuel checkpoint ∧
      StateHasType checkpoint sumObservationType ∧
      runStateful 1 checkpoint = .done sumObservation sumStore ∧
      (runStateful 1 checkpoint).HasType sumObservationType := by
  obtain ⟨checkpoint, exhausted⟩ := sum_predecessor_exhausted
  have initialTyped := initial_state_has_type
    (Program.check_full_sound sumProgram_checked).bodyHasType
  have checkpointTyped := well_typed_runStateful_preserves_checkpoint_type
    initialTyped exhausted
  obtain ⟨resumedTyped, resumed⟩ := well_typed_runStateful_resume_has_type
    initialTyped exhausted 1
  exact ⟨checkpoint, exhausted, checkpointTyped, resumed.trans sum_completed, resumedTyped⟩

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def checkExecution (label : String) (program : Program)
    (cost : Nat) (expected : Value) (expectedStore : Store) : IO Unit := do
  assertTrue program.check s!"{label}: the recursive program must pass the checker"
  assertTrue (program.runStateful cost == .done expected expectedStore)
    s!"{label}: results, mutation count, shared references, and closure captures must agree"
  match program.runStateful (cost - 1) with
  | .outOfFuel checkpoint =>
      assertTrue (runStateful 1 checkpoint == .done expected expectedStore)
        s!"{label}: one more transition must complete from the retained checkpoint"
  | _ => throw (IO.userError s!"{label}: the preceding fuel bound must exhaust")

/-- Cover self recursion passed as a function argument and called twice, mutual
recursion, shared mutation, cyclic stores, exact fuel, and resumption. -/
def run : IO Unit := do
  checkExecution "self recursion" sumProgram 274 sumObservation sumStore
  checkExecution "mutual recursion" parityProgram 329 parityObservation parityStore

end Tests.CoreRecursiveCells
