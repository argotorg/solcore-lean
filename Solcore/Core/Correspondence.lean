import Solcore.Core.MachineProperties

set_option autoImplicit false

namespace Solcore.Core

theorem Steps.trans
    {leftSteps rightSteps : Nat} {start middle finish : State}
    (left : Steps leftSteps start middle)
    (right : Steps rightSteps middle finish) :
    Steps (leftSteps + rightSteps) start finish := by
  induction left with
  | refl => simpa using right
  | cons transition tail tailIH =>
      have combined := tailIH right
      have prefixed := Steps.cons transition combined
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using prefixed

theorem Evaluates.toStepsWithContinuation
    {environment : Environment} {expr : Expr} {value : Value}
    (evaluation : Evaluates environment expr value)
    (continuation : List Frame) :
    ∃ steps,
      Steps steps
        ⟨.eval expr environment, continuation⟩
        ⟨.ret value, continuation⟩ := by
  induction evaluation generalizing continuation with
  | unit =>
      exact ⟨1, .cons .unit .refl⟩
  | bool =>
      exact ⟨1, .cons .bool .refl⟩
  | word =>
      exact ⟨1, .cons .word .refl⟩
  | @pair environment left right leftValue rightValue
      leftEvaluation rightEvaluation leftIH rightIH =>
      obtain ⟨leftSteps, leftPath⟩ :=
        leftIH (.pairRight right environment :: continuation)
      obtain ⟨rightSteps, rightPath⟩ :=
        rightIH (.pairApply leftValue :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.pair left right) environment, continuation⟩
          ⟨.eval left environment,
            .pairRight right environment :: continuation⟩ :=
        .cons
          (@Transition.enterPair environment left right continuation)
          .refl
      let rightEntryPath : Steps 1
          ⟨.ret leftValue, .pairRight right environment :: continuation⟩
          ⟨.eval right environment, .pairApply leftValue :: continuation⟩ :=
        .cons
          (@Transition.enterPairRight environment right leftValue continuation)
          .refl
      let applyPath : Steps 1
          ⟨.ret rightValue, .pairApply leftValue :: continuation⟩
          ⟨.ret (.pair leftValue rightValue), continuation⟩ :=
        .cons
          (@Transition.applyPair leftValue rightValue continuation)
          .refl
      exact ⟨_,
        enterPath.trans
          (leftPath.trans
            (rightEntryPath.trans
              (rightPath.trans applyPath)))⟩
  | @first environment operand leftValue rightValue
      operandEvaluation operandIH =>
      obtain ⟨operandSteps, operandPath⟩ :=
        operandIH (.firstApply :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.first operand) environment, continuation⟩
          ⟨.eval operand environment, .firstApply :: continuation⟩ :=
        .cons
          (@Transition.enterFirst environment operand continuation)
          .refl
      let applyPath : Steps 1
          ⟨.ret (.pair leftValue rightValue), .firstApply :: continuation⟩
          ⟨.ret leftValue, continuation⟩ :=
        .cons
          (@Transition.applyFirst leftValue rightValue continuation)
          .refl
      exact ⟨_, enterPath.trans (operandPath.trans applyPath)⟩
  | @second environment operand leftValue rightValue
      operandEvaluation operandIH =>
      obtain ⟨operandSteps, operandPath⟩ :=
        operandIH (.secondApply :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.second operand) environment, continuation⟩
          ⟨.eval operand environment, .secondApply :: continuation⟩ :=
        .cons
          (@Transition.enterSecond environment operand continuation)
          .refl
      let applyPath : Steps 1
          ⟨.ret (.pair leftValue rightValue), .secondApply :: continuation⟩
          ⟨.ret rightValue, continuation⟩ :=
        .cons
          (@Transition.applySecond leftValue rightValue continuation)
          .refl
      exact ⟨_, enterPath.trans (operandPath.trans applyPath)⟩
  | var lookup =>
      exact ⟨1, .cons (.var lookup) .refl⟩
  | @unary environment op operand operandValue result
      operandEvaluation applied operandIH =>
      obtain ⟨operandSteps, operandPath⟩ :=
        operandIH (.unaryApply op :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.unary op operand) environment, continuation⟩
          ⟨.eval operand environment, .unaryApply op :: continuation⟩ :=
        .cons
          (@Transition.enterUnary environment op operand continuation)
          .refl
      let applyPath : Steps 1
          ⟨.ret operandValue, .unaryApply op :: continuation⟩
          ⟨.ret result, continuation⟩ :=
        .cons
          (@Transition.applyUnary op operandValue result continuation applied)
          .refl
      exact ⟨_, enterPath.trans (operandPath.trans applyPath)⟩
  | @binary environment op left right leftValue rightValue result
      leftEvaluation rightEvaluation applied leftIH rightIH =>
      obtain ⟨leftSteps, leftPath⟩ :=
        leftIH (.binaryRight op right environment :: continuation)
      obtain ⟨rightSteps, rightPath⟩ :=
        rightIH (.binaryApply op leftValue :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.binary op left right) environment, continuation⟩
          ⟨.eval left environment,
            .binaryRight op right environment :: continuation⟩ :=
        .cons
          (@Transition.enterBinary environment op left right continuation)
          .refl
      let rightEntryPath : Steps 1
          ⟨.ret leftValue, .binaryRight op right environment :: continuation⟩
          ⟨.eval right environment, .binaryApply op leftValue :: continuation⟩ :=
        .cons
          (@Transition.enterBinaryRight environment op right leftValue continuation)
          .refl
      let applyPath : Steps 1
          ⟨.ret rightValue, .binaryApply op leftValue :: continuation⟩
          ⟨.ret result, continuation⟩ :=
        .cons
          (@Transition.applyBinary op leftValue rightValue result continuation applied)
          .refl
      exact ⟨_,
        enterPath.trans
          (leftPath.trans
            (rightEntryPath.trans
              (rightPath.trans applyPath)))⟩
  | @letE environment bound body boundValue result
      boundEvaluation bodyEvaluation boundIH bodyIH =>
      obtain ⟨boundSteps, boundPath⟩ :=
        boundIH (.letBody body environment :: continuation)
      obtain ⟨bodySteps, bodyPath⟩ := bodyIH continuation
      let enterPath : Steps 1
          ⟨.eval (.letE bound body) environment, continuation⟩
          ⟨.eval bound environment, .letBody body environment :: continuation⟩ :=
        .cons (@Transition.enterLet environment bound body continuation) .refl
      let bindPath : Steps 1
          ⟨.ret boundValue, .letBody body environment :: continuation⟩
          ⟨.eval body (boundValue :: environment), continuation⟩ :=
        .cons (@Transition.bindLet environment boundValue body continuation) .refl
      exact ⟨_,
        enterPath.trans (boundPath.trans (bindPath.trans bodyPath))⟩
  | @ifTrue environment condition thenBranch elseBranch result
      conditionEvaluation branchEvaluation conditionIH branchIH =>
      obtain ⟨conditionSteps, conditionPath⟩ :=
        conditionIH (.ifBranches thenBranch elseBranch environment :: continuation)
      obtain ⟨branchSteps, branchPath⟩ := branchIH continuation
      let enterPath : Steps 1
          ⟨.eval (.ifE condition thenBranch elseBranch) environment, continuation⟩
          ⟨.eval condition environment,
            .ifBranches thenBranch elseBranch environment :: continuation⟩ :=
        .cons
          (@Transition.enterIf environment condition thenBranch elseBranch continuation)
          .refl
      let choosePath : Steps 1
          ⟨.ret (.bool true),
            .ifBranches thenBranch elseBranch environment :: continuation⟩
          ⟨.eval thenBranch environment, continuation⟩ :=
        .cons
          (@Transition.chooseTrue environment thenBranch elseBranch continuation)
          .refl
      exact ⟨_,
        enterPath.trans (conditionPath.trans (choosePath.trans branchPath))⟩
  | @ifFalse environment condition thenBranch elseBranch result
      conditionEvaluation branchEvaluation conditionIH branchIH =>
      obtain ⟨conditionSteps, conditionPath⟩ :=
        conditionIH (.ifBranches thenBranch elseBranch environment :: continuation)
      obtain ⟨branchSteps, branchPath⟩ := branchIH continuation
      let enterPath : Steps 1
          ⟨.eval (.ifE condition thenBranch elseBranch) environment, continuation⟩
          ⟨.eval condition environment,
            .ifBranches thenBranch elseBranch environment :: continuation⟩ :=
        .cons
          (@Transition.enterIf environment condition thenBranch elseBranch continuation)
          .refl
      let choosePath : Steps 1
          ⟨.ret (.bool false),
            .ifBranches thenBranch elseBranch environment :: continuation⟩
          ⟨.eval elseBranch environment, continuation⟩ :=
        .cons
          (@Transition.chooseFalse environment thenBranch elseBranch continuation)
          .refl
      exact ⟨_,
        enterPath.trans (conditionPath.trans (choosePath.trans branchPath))⟩

theorem Evaluates.toSteps
    {environment : Environment} {expr : Expr} {value : Value}
    (evaluation : Evaluates environment expr value) :
    ∃ steps,
      Steps steps (State.initial expr environment) (State.final value) := by
  simpa [State.initial, State.final] using
    evaluation.toStepsWithContinuation []

inductive Continues : List Frame → Value → Value → Prop where
  | done {value : Value} :
      Continues [] value value
  | unaryApply
      {op : UnaryOp} {continuation : List Frame}
      {operand result finalValue : Value} :
      op.apply operand = some result →
      Continues continuation result finalValue →
      Continues (.unaryApply op :: continuation) operand finalValue
  | binaryRight
      {op : BinaryOp} {right : Expr} {environment : Environment}
      {continuation : List Frame} {leftValue rightValue result finalValue : Value} :
      Evaluates environment right rightValue →
      op.apply leftValue rightValue = some result →
      Continues continuation result finalValue →
      Continues
        (.binaryRight op right environment :: continuation)
        leftValue
        finalValue
  | binaryApply
      {op : BinaryOp} {leftValue rightValue result finalValue : Value}
      {continuation : List Frame} :
      op.apply leftValue rightValue = some result →
      Continues continuation result finalValue →
      Continues
        (.binaryApply op leftValue :: continuation)
        rightValue
        finalValue
  | pairRight
      {right : Expr} {environment : Environment}
      {continuation : List Frame}
      {leftValue rightValue finalValue : Value} :
      Evaluates environment right rightValue →
      Continues continuation (.pair leftValue rightValue) finalValue →
      Continues
        (.pairRight right environment :: continuation)
        leftValue
        finalValue
  | pairApply
      {leftValue rightValue finalValue : Value}
      {continuation : List Frame} :
      Continues continuation (.pair leftValue rightValue) finalValue →
      Continues
        (.pairApply leftValue :: continuation)
        rightValue
        finalValue
  | firstApply
      {leftValue rightValue finalValue : Value}
      {continuation : List Frame} :
      Continues continuation leftValue finalValue →
      Continues
        (.firstApply :: continuation)
        (.pair leftValue rightValue)
        finalValue
  | secondApply
      {leftValue rightValue finalValue : Value}
      {continuation : List Frame} :
      Continues continuation rightValue finalValue →
      Continues
        (.secondApply :: continuation)
        (.pair leftValue rightValue)
        finalValue
  | letBody
      {body : Expr} {environment : Environment} {continuation : List Frame}
      {boundValue result finalValue : Value} :
      Evaluates (boundValue :: environment) body result →
      Continues continuation result finalValue →
      Continues (.letBody body environment :: continuation) boundValue finalValue
  | ifTrue
      {thenBranch elseBranch : Expr} {environment : Environment}
      {continuation : List Frame} {result finalValue : Value} :
      Evaluates environment thenBranch result →
      Continues continuation result finalValue →
      Continues
        (.ifBranches thenBranch elseBranch environment :: continuation)
        (.bool true)
        finalValue
  | ifFalse
      {thenBranch elseBranch : Expr} {environment : Environment}
      {continuation : List Frame} {result finalValue : Value} :
      Evaluates environment elseBranch result →
      Continues continuation result finalValue →
      Continues
        (.ifBranches thenBranch elseBranch environment :: continuation)
        (.bool false)
        finalValue

inductive StateDenotes : State → Value → Prop where
  | eval
      {expr : Expr} {environment : Environment} {continuation : List Frame}
      {value finalValue : Value} :
      Evaluates environment expr value →
      Continues continuation value finalValue →
      StateDenotes ⟨.eval expr environment, continuation⟩ finalValue
  | ret
      {value finalValue : Value} {continuation : List Frame} :
      Continues continuation value finalValue →
      StateDenotes ⟨.ret value, continuation⟩ finalValue

theorem transition_reflects_denotation
    {state next : State} {value : Value}
    (transition : Transition state next)
    (denotes : StateDenotes next value) :
    StateDenotes state value := by
  cases transition with
  | unit =>
      cases denotes with
      | ret continuation => exact .eval .unit continuation
  | bool =>
      cases denotes with
      | ret continuation => exact .eval .bool continuation
  | word =>
      cases denotes with
      | ret continuation => exact .eval .word continuation
  | enterPair =>
      cases denotes with
      | eval leftEvaluation continuation =>
          cases continuation with
          | pairRight rightEvaluation rest =>
              exact .eval (.pair leftEvaluation rightEvaluation) rest
  | enterPairRight =>
      cases denotes with
      | eval rightEvaluation continuation =>
          cases continuation with
          | pairApply rest =>
              exact .ret (.pairRight rightEvaluation rest)
  | applyPair =>
      cases denotes with
      | ret continuation =>
          exact .ret (.pairApply continuation)
  | enterFirst =>
      cases denotes with
      | eval operandEvaluation continuation =>
          cases continuation with
          | firstApply rest =>
              exact .eval (.first operandEvaluation) rest
  | applyFirst =>
      cases denotes with
      | ret continuation =>
          exact .ret (.firstApply continuation)
  | enterSecond =>
      cases denotes with
      | eval operandEvaluation continuation =>
          cases continuation with
          | secondApply rest =>
              exact .eval (.second operandEvaluation) rest
  | applySecond =>
      cases denotes with
      | ret continuation =>
          exact .ret (.secondApply continuation)
  | var lookup =>
      cases denotes with
      | ret continuation => exact .eval (.var lookup) continuation
  | enterUnary =>
      cases denotes with
      | eval operandEvaluation continuation =>
          cases continuation with
          | unaryApply applied rest =>
              exact .eval (.unary operandEvaluation applied) rest
  | applyUnary applied =>
      cases denotes with
      | ret continuation =>
          exact .ret (.unaryApply applied continuation)
  | enterBinary =>
      cases denotes with
      | eval leftEvaluation continuation =>
          cases continuation with
          | binaryRight rightEvaluation applied rest =>
              exact .eval (.binary leftEvaluation rightEvaluation applied) rest
  | enterBinaryRight =>
      cases denotes with
      | eval rightEvaluation continuation =>
          cases continuation with
          | binaryApply applied rest =>
              exact .ret (.binaryRight rightEvaluation applied rest)
  | applyBinary applied =>
      cases denotes with
      | ret continuation =>
          exact .ret (.binaryApply applied continuation)
  | enterLet =>
      cases denotes with
      | eval boundEvaluation continuation =>
          cases continuation with
          | letBody bodyEvaluation rest =>
              exact .eval (.letE boundEvaluation bodyEvaluation) rest
  | bindLet =>
      cases denotes with
      | eval bodyEvaluation continuation =>
          exact .ret (.letBody bodyEvaluation continuation)
  | enterIf =>
      cases denotes with
      | eval conditionEvaluation continuation =>
          cases continuation with
          | ifTrue branchEvaluation rest =>
              exact .eval (.ifTrue conditionEvaluation branchEvaluation) rest
          | ifFalse branchEvaluation rest =>
              exact .eval (.ifFalse conditionEvaluation branchEvaluation) rest
  | chooseTrue =>
      cases denotes with
      | eval branchEvaluation continuation =>
          exact .ret (.ifTrue branchEvaluation continuation)
  | chooseFalse =>
      cases denotes with
      | eval branchEvaluation continuation =>
          exact .ret (.ifFalse branchEvaluation continuation)

theorem steps_reflect_denotation
    {steps : Nat} {start finish : State} {value : Value}
    (path : Steps steps start finish)
    (denotes : StateDenotes finish value) :
    StateDenotes start value := by
  induction path with
  | refl => exact denotes
  | cons transition tail tailIH =>
      exact transition_reflects_denotation transition (tailIH denotes)

theorem steps_from_initial_sound
    {steps : Nat} {environment : Environment} {expr : Expr} {value : Value}
    (path : Steps steps (State.initial expr environment) (State.final value)) :
    Evaluates environment expr value := by
  have finalDenotes : StateDenotes (State.final value) value :=
    .ret .done
  have initialDenotes := steps_reflect_denotation path finalDenotes
  cases initialDenotes with
  | eval evaluation continuation =>
      cases continuation
      exact evaluation

theorem run_evaluation_sound
    {fuel : Nat} {environment : Environment} {expr : Expr} {value : Value}
    (result : run fuel (State.initial expr environment) = .done value) :
    Evaluates environment expr value := by
  obtain ⟨steps, _, path⟩ := run_sound result
  exact steps_from_initial_sound path

theorem evaluation_run_complete
    {environment : Environment} {expr : Expr} {value : Value}
    (evaluation : Evaluates environment expr value) :
    ∃ fuel, run fuel (State.initial expr environment) = .done value := by
  obtain ⟨steps, path⟩ := evaluation.toSteps
  exact ⟨steps, run_complete_with_fuel path (Nat.le_refl steps)⟩

theorem evaluation_run_complete_with_sufficient_fuel
    {environment : Environment} {expr : Expr} {value : Value}
    (evaluation : Evaluates environment expr value) :
    ∃ required,
      ∀ fuel, required ≤ fuel →
        run fuel (State.initial expr environment) = .done value := by
  obtain ⟨steps, path⟩ := evaluation.toSteps
  exact ⟨steps, fun fuel enough => run_complete_with_fuel path enough⟩

end Solcore.Core
