import Solcore.Core.Machine

set_option autoImplicit false

namespace Solcore.Core

theorem advance_next_iff {state next : State} :
    advance state = .next next ↔ Transition state next := by
  constructor
  · intro advanced
    rcases state with ⟨control, continuation, store⟩
    cases control with
    | eval expr environment =>
        cases expr with
        | unit =>
            simp [advance] at advanced
            cases advanced
            exact .unit
        | bool value =>
            simp [advance] at advanced
            cases advanced
            exact .bool
        | word value =>
            simp [advance] at advanced
            cases advanced
            exact .word
        | pair left right =>
            simp [advance] at advanced
            cases advanced
            exact .enterPair
        | first operand =>
            simp [advance] at advanced
            cases advanced
            exact .enterFirst
        | second operand =>
            simp [advance] at advanced
            cases advanced
            exact .enterSecond
        | inLeft rightType payload =>
            simp [advance] at advanced
            cases advanced
            exact .enterInLeft
        | inRight leftType payload =>
            simp [advance] at advanced
            cases advanced
            exact .enterInRight
        | caseE scrutinee leftBranch rightBranch =>
            simp [advance] at advanced
            cases advanced
            exact .enterCase
        | newCell elementType initializer =>
            simp [advance] at advanced
            cases advanced
            exact .enterNewCell
        | loadCell reference =>
            simp [advance] at advanced
            cases advanced
            exact .enterLoadCell
        | storeCell reference valueExpr =>
            simp [advance] at advanced
            cases advanced
            exact .enterStoreCell
        | construct constructor payload =>
            simp [advance] at advanced
            cases advanced
            exact .enterConstruct
        | matchData dataType resultType scrutinee branches =>
            simp [advance] at advanced
            cases advanced
            exact .enterMatchData
        | lambda parameterType resultType body =>
            simp [advance] at advanced
            cases advanced
            exact .lambda
        | apply function argument =>
            simp [advance] at advanced
            cases advanced
            exact .enterApply
        | var index =>
            cases lookup : environment[index]? with
            | none => simp [advance, lookup] at advanced
            | some value =>
                simp [advance, lookup] at advanced
                cases advanced
                exact .var lookup
        | unary op operand =>
            simp [advance] at advanced
            cases advanced
            exact .enterUnary
        | binary op left right =>
            simp [advance] at advanced
            cases advanced
            exact .enterBinary
        | letE value body =>
            simp [advance] at advanced
            cases advanced
            exact .enterLet
        | ifE condition thenBranch elseBranch =>
            simp [advance] at advanced
            cases advanced
            exact .enterIf
    | ret value =>
        cases continuation with
        | nil => simp [advance] at advanced
        | cons frame continuation =>
            cases frame with
            | unaryApply op =>
                cases applied : op.apply value with
                | none => simp [advance, applied] at advanced
                | some result =>
                    simp [advance, applied] at advanced
                    cases advanced
                    exact .applyUnary applied
            | binaryRight op right environment =>
                simp [advance] at advanced
                cases advanced
                exact .enterBinaryRight
            | binaryApply op leftValue =>
                cases applied : op.apply leftValue value with
                | none => simp [advance, applied] at advanced
                | some result =>
                    simp [advance, applied] at advanced
                    cases advanced
                    exact .applyBinary applied
            | ternarySecond op second third environment =>
                simp [advance] at advanced
                cases advanced
                exact .enterTernarySecond
            | ternaryThird op firstValue third environment =>
                simp [advance] at advanced
                cases advanced
                exact .enterTernaryThird
            | ternaryApply op firstValue secondValue =>
                cases applied : op.apply firstValue secondValue value with
                | none => simp [advance, applied] at advanced
                | some result =>
                    simp [advance, applied] at advanced
                    cases advanced
                    exact .applyTernary applied
            | pairRight right environment =>
                simp [advance] at advanced
                cases advanced
                exact .enterPairRight
            | pairApply leftValue =>
                simp [advance] at advanced
                cases advanced
                exact .applyPair
            | firstApply =>
                cases value with
                | unit | bool | word | inLeft | inRight | closure | cellRef |
                    constructed =>
                    simp [advance] at advanced
                | pair leftValue rightValue =>
                    simp [advance] at advanced
                    cases advanced
                    exact .applyFirst
            | secondApply =>
                cases value with
                | unit | bool | word | inLeft | inRight | closure | cellRef |
                    constructed =>
                    simp [advance] at advanced
                | pair leftValue rightValue =>
                    simp [advance] at advanced
                    cases advanced
                    exact .applySecond
            | inLeftApply rightType =>
                simp [advance] at advanced
                cases advanced
                exact .applyInLeft
            | inRightApply leftType =>
                simp [advance] at advanced
                cases advanced
                exact .applyInRight
            | caseBranches leftBranch rightBranch environment =>
                cases value with
                | unit | bool | word | pair | closure | cellRef | constructed =>
                    simp [advance] at advanced
                | inLeft rightType payload =>
                    simp [advance] at advanced
                    cases advanced
                    exact .chooseLeft
                | inRight leftType payload =>
                    simp [advance] at advanced
                    cases advanced
                    exact .chooseRight
            | newCellApply elementType =>
                simp [advance] at advanced
                cases advanced
                exact .applyNewCell
            | loadCellApply =>
                cases value with
                | unit | bool | word | pair | closure | inLeft | inRight |
                    constructed =>
                    simp [advance] at advanced
                | cellRef elementType location =>
                    cases lookup : store.read? location with
                    | none => simp [advance, lookup] at advanced
                    | some loaded =>
                        simp [advance, lookup] at advanced
                        cases advanced
                        exact .applyLoadCell lookup
            | storeCellValue valueExpr environment =>
                cases value with
                | unit | bool | word | pair | closure | inLeft | inRight |
                    constructed =>
                    simp [advance] at advanced
                | cellRef elementType location =>
                    cases lookup : store.read? location with
                    | none => simp [advance, lookup] at advanced
                    | some oldValue =>
                        simp [advance, lookup] at advanced
                        cases advanced
                        exact .beginStoreCellValue lookup
            | storeCellApply elementType location =>
                cases written : store.write? location value with
                | none => simp [advance, written] at advanced
                | some updatedStore =>
                    simp [advance, written] at advanced
                    cases advanced
                    exact .applyStoreCell written
            | constructApply constructor =>
                simp [advance] at advanced
                cases advanced
                exact .applyConstruct
            | matchDataApply dataType branches environment =>
                cases value with
                | unit | bool | word | pair | closure | inLeft | inRight | cellRef =>
                    simp [advance] at advanced
                | constructed constructor payload =>
                    by_cases sameOwner : constructor.owner = dataType
                    · cases branchLookup : branches[constructor.index]? with
                      | none =>
                          simp [advance, sameOwner, branchLookup] at advanced
                      | some branch =>
                          simp [advance, sameOwner, branchLookup] at advanced
                          cases advanced
                          exact .chooseData sameOwner branchLookup
                    · simp [advance, sameOwner] at advanced
            | applyArgument argument callerEnvironment =>
                cases value with
                | unit | bool | word | pair | inLeft | inRight | cellRef |
                    constructed =>
                    simp [advance] at advanced
                | closure parameterType resultType body capturedEnvironment =>
                    simp [advance] at advanced
                    cases advanced
                    exact .beginArgument
            | applyClosure parameterType resultType body capturedEnvironment =>
                simp [advance] at advanced
                cases advanced
                exact .invokeClosure
            | letBody body environment =>
                simp [advance] at advanced
                cases advanced
                exact .bindLet
            | ifBranches thenBranch elseBranch environment =>
                cases value with
                | unit | word | pair | inLeft | inRight | closure | cellRef |
                    constructed =>
                    simp [advance] at advanced
                | bool decision =>
                    cases decision with
                    | false =>
                        simp [advance] at advanced
                        cases advanced
                        exact .chooseFalse
                    | true =>
                        simp [advance] at advanced
                        cases advanced
                        exact .chooseTrue
  · intro transition
    cases transition <;> simp [advance, *]

theorem advance_done_iff {state : State} {value : Value} :
    advance state = .done value ↔
      ∃ store, state = State.final value store := by
  constructor
  · intro advanced
    rcases state with ⟨control, continuation, store⟩
    cases control with
    | eval expr environment =>
        cases expr with
        | unit | bool | word | pair | first | second | inLeft | inRight | caseE |
            newCell | loadCell | storeCell | construct | matchData | lambda |
            apply | unary | binary | letE | ifE =>
            simp [advance] at advanced
        | var index =>
            cases lookup : environment[index]? <;> simp [advance, lookup] at advanced
    | ret returned =>
        cases continuation with
        | nil =>
            simp [advance] at advanced
            cases advanced
            exact ⟨store, rfl⟩
        | cons frame continuation =>
            cases frame with
            | unaryApply op =>
                cases applied : op.apply returned <;>
                  simp [advance, applied] at advanced
            | binaryRight op right environment =>
                simp [advance] at advanced
            | binaryApply op leftValue =>
                cases applied : op.apply leftValue returned <;>
                  simp [advance, applied] at advanced
            | ternarySecond op second third environment =>
                simp [advance] at advanced
            | ternaryThird op firstValue third environment =>
                simp [advance] at advanced
            | ternaryApply op firstValue secondValue =>
                cases applied : op.apply firstValue secondValue returned <;>
                  simp [advance, applied] at advanced
            | pairRight right environment => simp [advance] at advanced
            | pairApply leftValue => simp [advance] at advanced
            | firstApply =>
                cases returned <;> simp [advance] at advanced
            | secondApply =>
                cases returned <;> simp [advance] at advanced
            | inLeftApply rightType => simp [advance] at advanced
            | inRightApply leftType => simp [advance] at advanced
            | caseBranches leftBranch rightBranch environment =>
                cases returned <;> simp [advance] at advanced
            | newCellApply elementType => simp [advance] at advanced
            | loadCellApply =>
                cases returned with
                | unit | bool | word | pair | closure | inLeft | inRight |
                    constructed =>
                    simp [advance] at advanced
                | cellRef elementType location =>
                    cases lookup : store.read? location <;>
                      simp [advance, lookup] at advanced
            | storeCellValue valueExpr environment =>
                cases returned with
                | unit | bool | word | pair | closure | inLeft | inRight |
                    constructed =>
                    simp [advance] at advanced
                | cellRef elementType location =>
                    cases lookup : store.read? location <;>
                      simp [advance, lookup] at advanced
            | storeCellApply elementType location =>
                cases written : store.write? location returned <;>
                  simp [advance, written] at advanced
            | constructApply constructor =>
                simp [advance] at advanced
            | matchDataApply dataType branches environment =>
                cases returned with
                | unit | bool | word | pair | closure | inLeft | inRight | cellRef =>
                    simp [advance] at advanced
                | constructed constructor payload =>
                    by_cases sameOwner : constructor.owner = dataType
                    · cases branchLookup : branches[constructor.index]? <;>
                        simp [advance, sameOwner, branchLookup] at advanced
                    · simp [advance, sameOwner] at advanced
            | applyArgument argument callerEnvironment =>
                cases returned <;> simp [advance] at advanced
            | applyClosure parameterType resultType body capturedEnvironment =>
                simp [advance] at advanced
            | letBody body environment => simp [advance] at advanced
            | ifBranches thenBranch elseBranch environment =>
                cases returned with
                | unit | word | pair | inLeft | inRight | closure | cellRef |
                    constructed =>
                    simp [advance] at advanced
                | bool decision =>
                    cases decision <;> simp [advance] at advanced
  · rintro ⟨store, rfl⟩
    simp [advance, State.final]

theorem transition_deterministic
    {state left right : State}
    (leftStep : Transition state left)
    (rightStep : Transition state right) :
    left = right := by
  rw [← advance_next_iff] at leftStep rightStep
  rw [leftStep] at rightStep
  cases rightStep
  rfl

theorem runStateful_sound
    {fuel : Nat} {state : State} {value : Value} {finalStore : Store}
    (result : runStateful fuel state = .done value finalStore) :
    ∃ steps,
      steps ≤ fuel ∧
      Steps steps state (State.final value finalStore) := by
  induction fuel generalizing state value with
  | zero =>
      cases advanced : advance state with
      | next next =>
          rw [runStateful, advanced] at result
          contradiction
      | fault error =>
          rw [runStateful, advanced] at result
          contradiction
      | done returned =>
          obtain ⟨store, rfl⟩ := advance_done_iff.mp advanced
          rw [runStateful, advanced] at result
          cases result
          exact ⟨0, Nat.zero_le 0, .refl⟩
  | succ fuel fuelIH =>
      cases advanced : advance state with
      | fault error =>
          rw [runStateful, advanced] at result
          contradiction
      | done returned =>
          obtain ⟨store, rfl⟩ := advance_done_iff.mp advanced
          rw [runStateful, advanced] at result
          cases result
          exact ⟨0, Nat.zero_le _, .refl⟩
      | next next =>
          have tailResult :
              runStateful fuel next = .done value finalStore := by
            rw [runStateful, advanced] at result
            exact result
          obtain ⟨steps, bounded, path⟩ := fuelIH tailResult
          exact ⟨steps + 1, Nat.succ_le_succ bounded,
            .cons (advance_next_iff.mp advanced) path⟩

theorem runStateful_fault_sound
    {fuel : Nat} {state faultState : State} {error : MachineFault}
    (result : runStateful fuel state = .fault error faultState) :
    ∃ steps,
      steps ≤ fuel ∧
      Steps steps state faultState ∧
      advance faultState = .fault error := by
  induction fuel generalizing state error faultState with
  | zero =>
      cases advanced : advance state with
      | next next =>
          rw [runStateful, advanced] at result
          contradiction
      | done value =>
          rw [runStateful, advanced] at result
          contradiction
      | fault actualError =>
          rw [runStateful, advanced] at result
          cases result
          exact ⟨0, Nat.zero_le 0, .refl, advanced⟩
  | succ fuel fuelIH =>
      cases advanced : advance state with
      | done value =>
          rw [runStateful, advanced] at result
          contradiction
      | fault actualError =>
          rw [runStateful, advanced] at result
          cases result
          exact ⟨0, Nat.zero_le _, .refl, advanced⟩
      | next next =>
          have tailResult :
              runStateful fuel next = .fault error faultState := by
            rw [runStateful, advanced] at result
            exact result
          obtain ⟨steps, bounded, path, terminal⟩ := fuelIH tailResult
          exact ⟨steps + 1, Nat.succ_le_succ bounded,
            .cons (advance_next_iff.mp advanced) path, terminal⟩

theorem runStateful_outOfFuel_sound
    {fuel : Nat} {state suspendedState : State}
    (result : runStateful fuel state = .outOfFuel suspendedState) :
    Steps fuel state suspendedState ∧
      ∃ next, advance suspendedState = .next next := by
  induction fuel generalizing state suspendedState with
  | zero =>
      cases advanced : advance state with
      | done value =>
          rw [runStateful, advanced] at result
          contradiction
      | fault error =>
          rw [runStateful, advanced] at result
          contradiction
      | next next =>
          rw [runStateful, advanced] at result
          cases result
          exact ⟨.refl, next, advanced⟩
  | succ fuel fuelIH =>
      cases advanced : advance state with
      | done value =>
          rw [runStateful, advanced] at result
          contradiction
      | fault error =>
          rw [runStateful, advanced] at result
          contradiction
      | next next =>
          have tailResult :
              runStateful fuel next = .outOfFuel suspendedState := by
            rw [runStateful, advanced] at result
            exact result
          obtain ⟨path, finalNext, pending⟩ := fuelIH tailResult
          exact ⟨.cons (advance_next_iff.mp advanced) path,
            finalNext, pending⟩

theorem runStateful_complete_of_steps
    {steps fuel : Nat} {state finish : State} {value : Value}
    (path : Steps steps state finish)
    (terminal : advance finish = .done value)
    (enough : steps ≤ fuel) :
    runStateful fuel state = .done value finish.store := by
  induction path generalizing fuel value with
  | refl =>
      rw [runStateful, terminal]
  | cons transition tail tailIH =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have advanced := advance_next_iff.mpr transition
          rw [runStateful, advanced]
          exact tailIH terminal (Nat.le_of_succ_le_succ enough)

theorem runStateful_complete_with_fuel
    {steps fuel : Nat} {state : State} {value : Value} {finalStore : Store}
    (path : Steps steps state (State.final value finalStore))
    (enough : steps ≤ fuel) :
    runStateful fuel state = .done value finalStore :=
  runStateful_complete_of_steps path (by simp [advance, State.final]) enough

theorem runStateful_fault_complete_of_steps
    {steps fuel : Nat} {state faultState : State} {error : MachineFault}
    (path : Steps steps state faultState)
    (terminal : advance faultState = .fault error)
    (enough : steps ≤ fuel) :
    runStateful fuel state = .fault error faultState := by
  induction path generalizing fuel error with
  | refl =>
      rw [runStateful, terminal]
  | cons transition tail tailIH =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have advanced := advance_next_iff.mpr transition
          rw [runStateful, advanced]
          exact tailIH terminal (Nat.le_of_succ_le_succ enough)

theorem runStateful_outOfFuel_complete
    {fuel : Nat} {state suspendedState next : State}
    (path : Steps fuel state suspendedState)
    (pending : advance suspendedState = .next next) :
    runStateful fuel state = .outOfFuel suspendedState := by
  induction path with
  | refl =>
      rw [runStateful, pending]
  | cons transition tail tailIH =>
      have advanced := advance_next_iff.mpr transition
      rw [runStateful, advanced]
      exact tailIH pending

theorem run_sound
    {fuel : Nat} {state : State} {value : Value}
    (result : run fuel state = .done value) :
    ∃ finalStore steps,
      steps ≤ fuel ∧
      Steps steps state (State.final value finalStore) := by
  cases stateful : runStateful fuel state with
  | done returned finalStore =>
      rw [run, stateful] at result
      cases result
      obtain ⟨steps, bounded, path⟩ := runStateful_sound stateful
      exact ⟨finalStore, steps, bounded, path⟩
  | outOfFuel suspendedState =>
      simp [run, stateful, StatefulRunResult.erase] at result
  | fault error faultState =>
      simp [run, stateful, StatefulRunResult.erase] at result

theorem run_complete_of_steps
    {steps fuel : Nat} {state finish : State} {value : Value}
    (path : Steps steps state finish)
    (terminal : advance finish = .done value)
    (enough : steps ≤ fuel) :
    run fuel state = .done value := by
  simp [run, runStateful_complete_of_steps path terminal enough,
    StatefulRunResult.erase]

theorem run_complete_with_fuel
    {steps fuel : Nat} {state : State} {value : Value} {finalStore : Store}
    (path : Steps steps state (State.final value finalStore))
    (enough : steps ≤ fuel) :
    run fuel state = .done value :=
  run_complete_of_steps path (by simp [advance, State.final]) enough

end Solcore.Core
