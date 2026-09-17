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
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore)
    (continuation : List Frame) :
    ∃ steps,
      Steps steps
        ⟨.eval expr environment, continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ := by
  induction evaluation generalizing continuation with
  | unit =>
      exact ⟨1, .cons .unit .refl⟩
  | bool =>
      exact ⟨1, .cons .bool .refl⟩
  | word =>
      exact ⟨1, .cons .word .refl⟩
  | @pair environment initialStore middleStore finalStore left right
      leftValue rightValue leftEvaluation rightEvaluation leftIH rightIH =>
      obtain ⟨leftSteps, leftPath⟩ :=
        leftIH (.pairRight right environment :: continuation)
      obtain ⟨rightSteps, rightPath⟩ :=
        rightIH (.pairApply leftValue :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.pair left right) environment, continuation, initialStore⟩
          ⟨.eval left environment,
            .pairRight right environment :: continuation, initialStore⟩ :=
        .cons .enterPair .refl
      let rightEntryPath : Steps 1
          ⟨.ret leftValue,
            .pairRight right environment :: continuation, middleStore⟩
          ⟨.eval right environment,
            .pairApply leftValue :: continuation, middleStore⟩ :=
        .cons .enterPairRight .refl
      let applyPath : Steps 1
          ⟨.ret rightValue, .pairApply leftValue :: continuation, finalStore⟩
          ⟨.ret (.pair leftValue rightValue), continuation, finalStore⟩ :=
        .cons .applyPair .refl
      exact ⟨_,
        enterPath.trans
          (leftPath.trans
            (rightEntryPath.trans
              (rightPath.trans applyPath)))⟩
  | @first environment initialStore finalStore operand leftValue rightValue
      operandEvaluation operandIH =>
      obtain ⟨operandSteps, operandPath⟩ :=
        operandIH (.firstApply :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.first operand) environment, continuation, initialStore⟩
          ⟨.eval operand environment, .firstApply :: continuation, initialStore⟩ :=
        .cons .enterFirst .refl
      let applyPath : Steps 1
          ⟨.ret (.pair leftValue rightValue), .firstApply :: continuation, finalStore⟩
          ⟨.ret leftValue, continuation, finalStore⟩ :=
        .cons .applyFirst .refl
      exact ⟨_, enterPath.trans (operandPath.trans applyPath)⟩
  | @second environment initialStore finalStore operand leftValue rightValue
      operandEvaluation operandIH =>
      obtain ⟨operandSteps, operandPath⟩ :=
        operandIH (.secondApply :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.second operand) environment, continuation, initialStore⟩
          ⟨.eval operand environment, .secondApply :: continuation, initialStore⟩ :=
        .cons .enterSecond .refl
      let applyPath : Steps 1
          ⟨.ret (.pair leftValue rightValue), .secondApply :: continuation, finalStore⟩
          ⟨.ret rightValue, continuation, finalStore⟩ :=
        .cons .applySecond .refl
      exact ⟨_, enterPath.trans (operandPath.trans applyPath)⟩
  | @inLeft environment initialStore finalStore rightType payload payloadValue
      payloadEvaluation payloadIH =>
      obtain ⟨payloadSteps, payloadPath⟩ :=
        payloadIH (.inLeftApply rightType :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.inLeft rightType payload) environment, continuation, initialStore⟩
          ⟨.eval payload environment,
            .inLeftApply rightType :: continuation, initialStore⟩ :=
        .cons .enterInLeft .refl
      let applyPath : Steps 1
          ⟨.ret payloadValue, .inLeftApply rightType :: continuation, finalStore⟩
          ⟨.ret (.inLeft rightType payloadValue), continuation, finalStore⟩ :=
        .cons .applyInLeft .refl
      exact ⟨_, enterPath.trans (payloadPath.trans applyPath)⟩
  | @inRight environment initialStore finalStore leftType payload payloadValue
      payloadEvaluation payloadIH =>
      obtain ⟨payloadSteps, payloadPath⟩ :=
        payloadIH (.inRightApply leftType :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.inRight leftType payload) environment, continuation, initialStore⟩
          ⟨.eval payload environment,
            .inRightApply leftType :: continuation, initialStore⟩ :=
        .cons .enterInRight .refl
      let applyPath : Steps 1
          ⟨.ret payloadValue, .inRightApply leftType :: continuation, finalStore⟩
          ⟨.ret (.inRight leftType payloadValue), continuation, finalStore⟩ :=
        .cons .applyInRight .refl
      exact ⟨_, enterPath.trans (payloadPath.trans applyPath)⟩
  | @caseLeft environment initialStore branchStore finalStore scrutinee
      leftBranch rightBranch rightType payload result scrutineeEvaluation
      branchEvaluation scrutineeIH branchIH =>
      obtain ⟨scrutineeSteps, scrutineePath⟩ :=
        scrutineeIH
          (.caseBranches leftBranch rightBranch environment :: continuation)
      obtain ⟨branchSteps, branchPath⟩ := branchIH continuation
      let enterPath : Steps 1
          ⟨.eval (.caseE scrutinee leftBranch rightBranch) environment,
            continuation, initialStore⟩
          ⟨.eval scrutinee environment,
            .caseBranches leftBranch rightBranch environment :: continuation,
            initialStore⟩ :=
        .cons .enterCase .refl
      let choosePath : Steps 1
          ⟨.ret (.inLeft rightType payload),
            .caseBranches leftBranch rightBranch environment :: continuation,
            branchStore⟩
          ⟨.eval leftBranch (payload :: environment), continuation, branchStore⟩ :=
        .cons .chooseLeft .refl
      exact ⟨_,
        enterPath.trans
          (scrutineePath.trans (choosePath.trans branchPath))⟩
  | @caseRight environment initialStore branchStore finalStore scrutinee
      leftBranch rightBranch leftType payload result scrutineeEvaluation
      branchEvaluation scrutineeIH branchIH =>
      obtain ⟨scrutineeSteps, scrutineePath⟩ :=
        scrutineeIH
          (.caseBranches leftBranch rightBranch environment :: continuation)
      obtain ⟨branchSteps, branchPath⟩ := branchIH continuation
      let enterPath : Steps 1
          ⟨.eval (.caseE scrutinee leftBranch rightBranch) environment,
            continuation, initialStore⟩
          ⟨.eval scrutinee environment,
            .caseBranches leftBranch rightBranch environment :: continuation,
            initialStore⟩ :=
        .cons .enterCase .refl
      let choosePath : Steps 1
          ⟨.ret (.inRight leftType payload),
            .caseBranches leftBranch rightBranch environment :: continuation,
            branchStore⟩
          ⟨.eval rightBranch (payload :: environment), continuation, branchStore⟩ :=
        .cons .chooseRight .refl
      exact ⟨_,
        enterPath.trans
          (scrutineePath.trans (choosePath.trans branchPath))⟩
  | @lambda environment store parameterType resultType body =>
      exact ⟨1, .cons .lambda .refl⟩
  | @apply environment capturedEnvironment initialStore argumentStore bodyStore
      finalStore function argument body parameterType resultType argumentValue result
      functionEvaluation argumentEvaluation bodyEvaluation functionIH argumentIH
      bodyIH =>
      obtain ⟨functionSteps, functionPath⟩ :=
        functionIH (.applyArgument argument environment :: continuation)
      obtain ⟨argumentSteps, argumentPath⟩ :=
        argumentIH
          (.applyClosure parameterType resultType body capturedEnvironment ::
            continuation)
      obtain ⟨bodySteps, bodyPath⟩ := bodyIH continuation
      let enterPath : Steps 1
          ⟨.eval (.apply function argument) environment, continuation, initialStore⟩
          ⟨.eval function environment,
            .applyArgument argument environment :: continuation, initialStore⟩ :=
        .cons .enterApply .refl
      let beginArgumentPath : Steps 1
          ⟨.ret (.closure parameterType resultType body capturedEnvironment),
            .applyArgument argument environment :: continuation, argumentStore⟩
          ⟨.eval argument environment,
            .applyClosure parameterType resultType body capturedEnvironment ::
              continuation,
            argumentStore⟩ :=
        .cons .beginArgument .refl
      let invokePath : Steps 1
          ⟨.ret argumentValue,
            .applyClosure parameterType resultType body capturedEnvironment ::
              continuation,
            bodyStore⟩
          ⟨.eval body (argumentValue :: capturedEnvironment), continuation,
            bodyStore⟩ :=
        .cons .invokeClosure .refl
      exact ⟨_,
        enterPath.trans
          (functionPath.trans
            (beginArgumentPath.trans
              (argumentPath.trans
                (invokePath.trans bodyPath))))⟩
  | @var environment store index value lookup =>
      exact ⟨1, .cons (.var lookup) .refl⟩
  | @newCell environment initialStore initializedStore elementType initializer
      initialValue initializerEvaluation initializerIH =>
      obtain ⟨initializerSteps, initializerPath⟩ :=
        initializerIH (.newCellApply elementType :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.newCell elementType initializer) environment, continuation,
            initialStore⟩
          ⟨.eval initializer environment,
            .newCellApply elementType :: continuation, initialStore⟩ :=
        .cons .enterNewCell .refl
      let applyPath : Steps 1
          ⟨.ret initialValue, .newCellApply elementType :: continuation,
            initializedStore⟩
          ⟨.ret
              (.cellRef elementType (initializedStore.allocate initialValue).2),
            continuation, (initializedStore.allocate initialValue).1⟩ :=
        .cons .applyNewCell .refl
      refine ⟨1 + (initializerSteps + 1), ?_⟩
      simpa [Store.allocate] using
        enterPath.trans (initializerPath.trans applyPath)
  | @loadCell environment initialStore referenceStore reference elementType location
      value referenceEvaluation read referenceIH =>
      obtain ⟨referenceSteps, referencePath⟩ :=
        referenceIH (.loadCellApply :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.loadCell reference) environment, continuation, initialStore⟩
          ⟨.eval reference environment, .loadCellApply :: continuation,
            initialStore⟩ :=
        .cons .enterLoadCell .refl
      let applyPath : Steps 1
          ⟨.ret (.cellRef elementType location), .loadCellApply :: continuation,
            referenceStore⟩
          ⟨.ret value, continuation, referenceStore⟩ :=
        .cons (.applyLoadCell read) .refl
      exact ⟨_, enterPath.trans (referencePath.trans applyPath)⟩
  | @storeCell environment initialStore referenceStore valueStore finalStore
      reference valueExpr elementType location oldValue newValue
      referenceEvaluation read valueEvaluation written referenceIH valueIH =>
      obtain ⟨referenceSteps, referencePath⟩ :=
        referenceIH (.storeCellValue valueExpr environment :: continuation)
      obtain ⟨valueSteps, valuePath⟩ :=
        valueIH (.storeCellApply elementType location :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.storeCell reference valueExpr) environment, continuation,
            initialStore⟩
          ⟨.eval reference environment,
            .storeCellValue valueExpr environment :: continuation, initialStore⟩ :=
        .cons .enterStoreCell .refl
      let beginValuePath : Steps 1
          ⟨.ret (.cellRef elementType location),
            .storeCellValue valueExpr environment :: continuation, referenceStore⟩
          ⟨.eval valueExpr environment,
            .storeCellApply elementType location :: continuation, referenceStore⟩ :=
        .cons (.beginStoreCellValue read) .refl
      let applyPath : Steps 1
          ⟨.ret newValue, .storeCellApply elementType location :: continuation,
            valueStore⟩
          ⟨.ret .unit, continuation, finalStore⟩ :=
        .cons (.applyStoreCell written) .refl
      exact ⟨_,
        enterPath.trans
          (referencePath.trans
            (beginValuePath.trans
              (valuePath.trans applyPath)))⟩
  | @construct environment initialStore finalStore constructor payload payloadValue
      payloadEvaluation payloadIH =>
      obtain ⟨payloadSteps, payloadPath⟩ :=
        payloadIH (.constructApply constructor :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.construct constructor payload) environment, continuation,
            initialStore⟩
          ⟨.eval payload environment,
            .constructApply constructor :: continuation, initialStore⟩ :=
        .cons .enterConstruct .refl
      let applyPath : Steps 1
          ⟨.ret payloadValue, .constructApply constructor :: continuation,
            finalStore⟩
          ⟨.ret (.constructed constructor payloadValue), continuation, finalStore⟩ :=
        .cons .applyConstruct .refl
      exact ⟨_, enterPath.trans (payloadPath.trans applyPath)⟩
  | @matchData environment initialStore branchStore finalStore dataType resultType
      scrutinee branch branches constructor payload result scrutineeEvaluation
      sameOwner branchLookup branchEvaluation scrutineeIH branchIH =>
      obtain ⟨scrutineeSteps, scrutineePath⟩ :=
        scrutineeIH
          (.matchDataApply dataType branches environment :: continuation)
      obtain ⟨branchSteps, branchPath⟩ := branchIH continuation
      let enterPath : Steps 1
          ⟨.eval (.matchData dataType resultType scrutinee branches) environment,
            continuation, initialStore⟩
          ⟨.eval scrutinee environment,
            .matchDataApply dataType branches environment :: continuation,
            initialStore⟩ :=
        .cons .enterMatchData .refl
      let choosePath : Steps 1
          ⟨.ret (.constructed constructor payload),
            .matchDataApply dataType branches environment :: continuation,
            branchStore⟩
          ⟨.eval branch (payload :: environment), continuation, branchStore⟩ :=
        .cons (.chooseData sameOwner branchLookup) .refl
      exact ⟨_,
        enterPath.trans
          (scrutineePath.trans (choosePath.trans branchPath))⟩
  | @unary environment initialStore finalStore op operand operandValue result
      operandEvaluation applied operandIH =>
      obtain ⟨operandSteps, operandPath⟩ :=
        operandIH (.unaryApply op :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.unary op operand) environment, continuation, initialStore⟩
          ⟨.eval operand environment, .unaryApply op :: continuation,
            initialStore⟩ :=
        .cons .enterUnary .refl
      let applyPath : Steps 1
          ⟨.ret operandValue, .unaryApply op :: continuation, finalStore⟩
          ⟨.ret result, continuation, finalStore⟩ :=
        .cons (.applyUnary applied) .refl
      exact ⟨_, enterPath.trans (operandPath.trans applyPath)⟩
  | @binary environment initialStore rightStore finalStore op left right
      leftValue rightValue result leftEvaluation rightEvaluation applied leftIH
      rightIH =>
      obtain ⟨leftSteps, leftPath⟩ :=
        leftIH (.binaryRight op right environment :: continuation)
      obtain ⟨rightSteps, rightPath⟩ :=
        rightIH (.binaryApply op leftValue :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.binary op left right) environment, continuation, initialStore⟩
          ⟨.eval left environment,
            .binaryRight op right environment :: continuation, initialStore⟩ :=
        .cons .enterBinary .refl
      let rightEntryPath : Steps 1
          ⟨.ret leftValue,
            .binaryRight op right environment :: continuation, rightStore⟩
          ⟨.eval right environment,
            .binaryApply op leftValue :: continuation, rightStore⟩ :=
        .cons .enterBinaryRight .refl
      let applyPath : Steps 1
          ⟨.ret rightValue, .binaryApply op leftValue :: continuation, finalStore⟩
          ⟨.ret result, continuation, finalStore⟩ :=
        .cons (.applyBinary applied) .refl
      exact ⟨_,
        enterPath.trans
          (leftPath.trans
            (rightEntryPath.trans
              (rightPath.trans applyPath)))⟩
  | @ternary environment initialStore secondStore thirdStore finalStore op
      firstExpr secondExpr thirdExpr firstValue secondValue thirdValue result
      firstEvaluation secondEvaluation thirdEvaluation applied firstIH secondIH
      thirdIH =>
      obtain ⟨firstSteps, firstPath⟩ :=
        firstIH
          (.ternarySecond op secondExpr thirdExpr environment :: continuation)
      obtain ⟨secondSteps, secondPath⟩ :=
        secondIH
          (.ternaryThird op firstValue thirdExpr environment :: continuation)
      obtain ⟨thirdSteps, thirdPath⟩ :=
        thirdIH (.ternaryApply op firstValue secondValue :: continuation)
      let enterPath : Steps 1
          ⟨.eval (.ternary op firstExpr secondExpr thirdExpr) environment,
            continuation, initialStore⟩
          ⟨.eval firstExpr environment,
            .ternarySecond op secondExpr thirdExpr environment :: continuation,
            initialStore⟩ :=
        .cons .enterTernary .refl
      let secondEntryPath : Steps 1
          ⟨.ret firstValue,
            .ternarySecond op secondExpr thirdExpr environment :: continuation,
            secondStore⟩
          ⟨.eval secondExpr environment,
            .ternaryThird op firstValue thirdExpr environment :: continuation,
            secondStore⟩ :=
        .cons .enterTernarySecond .refl
      let thirdEntryPath : Steps 1
          ⟨.ret secondValue,
            .ternaryThird op firstValue thirdExpr environment :: continuation,
            thirdStore⟩
          ⟨.eval thirdExpr environment,
            .ternaryApply op firstValue secondValue :: continuation, thirdStore⟩ :=
        .cons .enterTernaryThird .refl
      let applyPath : Steps 1
          ⟨.ret thirdValue,
            .ternaryApply op firstValue secondValue :: continuation, finalStore⟩
          ⟨.ret result, continuation, finalStore⟩ :=
        .cons (.applyTernary applied) .refl
      exact ⟨_,
        enterPath.trans
          (firstPath.trans
            (secondEntryPath.trans
              (secondPath.trans
                (thirdEntryPath.trans
                  (thirdPath.trans applyPath)))))⟩
  | @letE environment initialStore bodyStore finalStore valueExpr body boundValue
      result valueEvaluation bodyEvaluation valueIH bodyIH =>
      obtain ⟨valueSteps, valuePath⟩ :=
        valueIH (.letBody body environment :: continuation)
      obtain ⟨bodySteps, bodyPath⟩ := bodyIH continuation
      let enterPath : Steps 1
          ⟨.eval (.letE valueExpr body) environment, continuation, initialStore⟩
          ⟨.eval valueExpr environment,
            .letBody body environment :: continuation, initialStore⟩ :=
        .cons .enterLet .refl
      let bindPath : Steps 1
          ⟨.ret boundValue, .letBody body environment :: continuation, bodyStore⟩
          ⟨.eval body (boundValue :: environment), continuation, bodyStore⟩ :=
        .cons .bindLet .refl
      exact ⟨_, enterPath.trans (valuePath.trans (bindPath.trans bodyPath))⟩
  | @ifTrue environment initialStore branchStore finalStore condition thenBranch
      elseBranch result conditionEvaluation branchEvaluation conditionIH branchIH =>
      obtain ⟨conditionSteps, conditionPath⟩ :=
        conditionIH (.ifBranches thenBranch elseBranch environment :: continuation)
      obtain ⟨branchSteps, branchPath⟩ := branchIH continuation
      let enterPath : Steps 1
          ⟨.eval (.ifE condition thenBranch elseBranch) environment, continuation,
            initialStore⟩
          ⟨.eval condition environment,
            .ifBranches thenBranch elseBranch environment :: continuation,
            initialStore⟩ :=
        .cons .enterIf .refl
      let choosePath : Steps 1
          ⟨.ret (.bool true),
            .ifBranches thenBranch elseBranch environment :: continuation,
            branchStore⟩
          ⟨.eval thenBranch environment, continuation, branchStore⟩ :=
        .cons .chooseTrue .refl
      exact ⟨_,
        enterPath.trans
          (conditionPath.trans (choosePath.trans branchPath))⟩
  | @ifFalse environment initialStore branchStore finalStore condition thenBranch
      elseBranch result conditionEvaluation branchEvaluation conditionIH branchIH =>
      obtain ⟨conditionSteps, conditionPath⟩ :=
        conditionIH (.ifBranches thenBranch elseBranch environment :: continuation)
      obtain ⟨branchSteps, branchPath⟩ := branchIH continuation
      let enterPath : Steps 1
          ⟨.eval (.ifE condition thenBranch elseBranch) environment, continuation,
            initialStore⟩
          ⟨.eval condition environment,
            .ifBranches thenBranch elseBranch environment :: continuation,
            initialStore⟩ :=
        .cons .enterIf .refl
      let choosePath : Steps 1
          ⟨.ret (.bool false),
            .ifBranches thenBranch elseBranch environment :: continuation,
            branchStore⟩
          ⟨.eval elseBranch environment, continuation, branchStore⟩ :=
        .cons .chooseFalse .refl
      exact ⟨_,
        enterPath.trans
          (conditionPath.trans (choosePath.trans branchPath))⟩

theorem Evaluates.toSteps
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ steps,
      Steps steps
        (State.initial expr environment initialStore)
        (State.final value finalStore) := by
  simpa [State.initial, State.final] using
    evaluation.toStepsWithContinuation []

/-!
`Continues continuation currentValue currentStore finalValue finalStore` means
that returning `currentValue` with `currentStore` into `continuation` finishes
with `finalValue` and `finalStore`. Keeping each value adjacent to the store in
which it is current prevents frames from accidentally reusing an earlier
store.
-/
inductive Continues :
    List Frame → Value → Store → Value → Store → Prop where
  | done {value : Value} {store : Store} :
      Continues [] value store value store
  | unaryApply
      {op : UnaryOp} {continuation : List Frame}
      {store finalStore : Store} {operand result finalValue : Value} :
      op.apply operand = some result →
      Continues continuation result store finalValue finalStore →
      Continues (.unaryApply op :: continuation) operand store finalValue finalStore
  | binaryRight
      {op : BinaryOp} {right : Expr} {environment : Environment}
      {continuation : List Frame} {initialStore rightStore finalStore : Store}
      {leftValue rightValue result finalValue : Value} :
      Evaluates environment initialStore right rightValue rightStore →
      op.apply leftValue rightValue = some result →
      Continues continuation result rightStore finalValue finalStore →
      Continues
        (.binaryRight op right environment :: continuation)
        leftValue initialStore finalValue finalStore
  | binaryApply
      {op : BinaryOp} {leftValue rightValue result finalValue : Value}
      {continuation : List Frame} {store finalStore : Store} :
      op.apply leftValue rightValue = some result →
      Continues continuation result store finalValue finalStore →
      Continues
        (.binaryApply op leftValue :: continuation)
        rightValue store finalValue finalStore
  | ternarySecond
      {op : TernaryOp} {second third : Expr} {environment : Environment}
      {continuation : List Frame}
      {initialStore secondStore thirdStore finalStore : Store}
      {firstValue secondValue thirdValue result finalValue : Value} :
      Evaluates environment initialStore second secondValue secondStore →
      Evaluates environment secondStore third thirdValue thirdStore →
      op.apply firstValue secondValue thirdValue = some result →
      Continues continuation result thirdStore finalValue finalStore →
      Continues (.ternarySecond op second third environment :: continuation)
        firstValue initialStore finalValue finalStore
  | ternaryThird
      {op : TernaryOp} {firstValue secondValue thirdValue result finalValue : Value}
      {third : Expr} {environment : Environment} {continuation : List Frame}
      {initialStore thirdStore finalStore : Store} :
      Evaluates environment initialStore third thirdValue thirdStore →
      op.apply firstValue secondValue thirdValue = some result →
      Continues continuation result thirdStore finalValue finalStore →
      Continues (.ternaryThird op firstValue third environment :: continuation)
        secondValue initialStore finalValue finalStore
  | ternaryApply
      {op : TernaryOp} {firstValue secondValue thirdValue result finalValue : Value}
      {continuation : List Frame} {store finalStore : Store} :
      op.apply firstValue secondValue thirdValue = some result →
      Continues continuation result store finalValue finalStore →
      Continues (.ternaryApply op firstValue secondValue :: continuation)
        thirdValue store finalValue finalStore
  | pairRight
      {right : Expr} {environment : Environment}
      {continuation : List Frame} {initialStore rightStore finalStore : Store}
      {leftValue rightValue finalValue : Value} :
      Evaluates environment initialStore right rightValue rightStore →
      Continues continuation (.pair leftValue rightValue) rightStore
        finalValue finalStore →
      Continues
        (.pairRight right environment :: continuation)
        leftValue initialStore finalValue finalStore
  | pairApply
      {leftValue rightValue finalValue : Value}
      {continuation : List Frame} {store finalStore : Store} :
      Continues continuation (.pair leftValue rightValue) store
        finalValue finalStore →
      Continues
        (.pairApply leftValue :: continuation)
        rightValue store finalValue finalStore
  | firstApply
      {leftValue rightValue finalValue : Value}
      {continuation : List Frame} {store finalStore : Store} :
      Continues continuation leftValue store finalValue finalStore →
      Continues
        (.firstApply :: continuation)
        (.pair leftValue rightValue) store finalValue finalStore
  | secondApply
      {leftValue rightValue finalValue : Value}
      {continuation : List Frame} {store finalStore : Store} :
      Continues continuation rightValue store finalValue finalStore →
      Continues
        (.secondApply :: continuation)
        (.pair leftValue rightValue) store finalValue finalStore
  | inLeftApply
      {rightType : Ty} {payload finalValue : Value}
      {continuation : List Frame} {store finalStore : Store} :
      Continues continuation (.inLeft rightType payload) store
        finalValue finalStore →
      Continues
        (.inLeftApply rightType :: continuation)
        payload store finalValue finalStore
  | inRightApply
      {leftType : Ty} {payload finalValue : Value}
      {continuation : List Frame} {store finalStore : Store} :
      Continues continuation (.inRight leftType payload) store
        finalValue finalStore →
      Continues
        (.inRightApply leftType :: continuation)
        payload store finalValue finalStore
  | caseLeft
      {leftBranch rightBranch : Expr} {environment : Environment}
      {rightType : Ty} {payload result finalValue : Value}
      {continuation : List Frame} {initialStore branchStore finalStore : Store} :
      Evaluates (payload :: environment) initialStore leftBranch result branchStore →
      Continues continuation result branchStore finalValue finalStore →
      Continues
        (.caseBranches leftBranch rightBranch environment :: continuation)
        (.inLeft rightType payload) initialStore finalValue finalStore
  | caseRight
      {leftBranch rightBranch : Expr} {environment : Environment}
      {leftType : Ty} {payload result finalValue : Value}
      {continuation : List Frame} {initialStore branchStore finalStore : Store} :
      Evaluates (payload :: environment) initialStore rightBranch result branchStore →
      Continues continuation result branchStore finalValue finalStore →
      Continues
        (.caseBranches leftBranch rightBranch environment :: continuation)
        (.inRight leftType payload) initialStore finalValue finalStore
  | newCellApply
      {elementType : Ty} {initialValue finalValue : Value}
      {continuation : List Frame} {store finalStore : Store} :
      Continues continuation
        (.cellRef elementType (store.allocate initialValue).2)
        (store.allocate initialValue).1 finalValue finalStore →
      Continues
        (.newCellApply elementType :: continuation)
        initialValue store finalValue finalStore
  | loadCellApply
      {elementType : Ty} {location : Location} {loaded finalValue : Value}
      {continuation : List Frame} {store finalStore : Store} :
      store.read? location = some loaded →
      Continues continuation loaded store finalValue finalStore →
      Continues
        (.loadCellApply :: continuation)
        (.cellRef elementType location) store finalValue finalStore
  | storeCellValue
      {valueExpr : Expr} {environment : Environment}
      {elementType : Ty} {location : Location}
      {oldValue newValue finalValue : Value}
      {continuation : List Frame}
      {referenceStore valueStore updatedStore finalStore : Store} :
      referenceStore.read? location = some oldValue →
      Evaluates environment referenceStore valueExpr newValue valueStore →
      valueStore.write? location newValue = some updatedStore →
      Continues continuation .unit updatedStore finalValue finalStore →
      Continues
        (.storeCellValue valueExpr environment :: continuation)
        (.cellRef elementType location) referenceStore finalValue finalStore
  | storeCellApply
      {elementType : Ty} {location : Location} {value finalValue : Value}
      {continuation : List Frame} {store updatedStore finalStore : Store} :
      store.write? location value = some updatedStore →
      Continues continuation .unit updatedStore finalValue finalStore →
      Continues
        (.storeCellApply elementType location :: continuation)
        value store finalValue finalStore
  | constructApply
      {constructor : ConstructorId} {payload finalValue : Value}
      {continuation : List Frame} {store finalStore : Store} :
      Continues continuation (.constructed constructor payload) store
        finalValue finalStore →
      Continues
        (.constructApply constructor :: continuation)
        payload store finalValue finalStore
  | matchDataApply
      {dataType : DataTypeId} {branches : List Expr}
      {environment : Environment} {constructor : ConstructorId}
      {payload result finalValue : Value} {branch : Expr}
      {continuation : List Frame} {initialStore branchStore finalStore : Store} :
      constructor.owner = dataType →
      branches[constructor.index]? = some branch →
      Evaluates (payload :: environment) initialStore branch result branchStore →
      Continues continuation result branchStore finalValue finalStore →
      Continues
        (.matchDataApply dataType branches environment :: continuation)
        (.constructed constructor payload) initialStore finalValue finalStore
  | applyArgument
      {argument : Expr} {callerEnvironment capturedEnvironment : Environment}
      {parameterType resultType : Ty} {body : Expr}
      {continuation : List Frame}
      {initialStore argumentStore bodyStore finalStore : Store}
      {argumentValue result finalValue : Value} :
      Evaluates callerEnvironment initialStore argument argumentValue argumentStore →
      Evaluates (argumentValue :: capturedEnvironment) argumentStore body result
        bodyStore →
      Continues continuation result bodyStore finalValue finalStore →
      Continues
        (.applyArgument argument callerEnvironment :: continuation)
        (.closure parameterType resultType body capturedEnvironment)
        initialStore finalValue finalStore
  | applyClosure
      {capturedEnvironment : Environment} {parameterType resultType : Ty}
      {body : Expr} {continuation : List Frame}
      {initialStore bodyStore finalStore : Store}
      {argumentValue result finalValue : Value} :
      Evaluates (argumentValue :: capturedEnvironment) initialStore body result
        bodyStore →
      Continues continuation result bodyStore finalValue finalStore →
      Continues
        (.applyClosure parameterType resultType body capturedEnvironment ::
          continuation)
        argumentValue initialStore finalValue finalStore
  | letBody
      {body : Expr} {environment : Environment} {continuation : List Frame}
      {initialStore bodyStore finalStore : Store}
      {boundValue result finalValue : Value} :
      Evaluates (boundValue :: environment) initialStore body result bodyStore →
      Continues continuation result bodyStore finalValue finalStore →
      Continues
        (.letBody body environment :: continuation)
        boundValue initialStore finalValue finalStore
  | ifTrue
      {thenBranch elseBranch : Expr} {environment : Environment}
      {continuation : List Frame} {initialStore branchStore finalStore : Store}
      {result finalValue : Value} :
      Evaluates environment initialStore thenBranch result branchStore →
      Continues continuation result branchStore finalValue finalStore →
      Continues
        (.ifBranches thenBranch elseBranch environment :: continuation)
        (.bool true) initialStore finalValue finalStore
  | ifFalse
      {thenBranch elseBranch : Expr} {environment : Environment}
      {continuation : List Frame} {initialStore branchStore finalStore : Store}
      {result finalValue : Value} :
      Evaluates environment initialStore elseBranch result branchStore →
      Continues continuation result branchStore finalValue finalStore →
      Continues
        (.ifBranches thenBranch elseBranch environment :: continuation)
        (.bool false) initialStore finalValue finalStore

/-!
`StateDenotes state finalValue finalStore` gives the successful big-step
outcome represented by a machine state. The state's own store is the input;
the two explicit indices are the terminal value and terminal store.
-/
inductive StateDenotes : State → Value → Store → Prop where
  | eval
      {expr : Expr} {environment : Environment} {continuation : List Frame}
      {initialStore expressionStore finalStore : Store}
      {value finalValue : Value} :
      Evaluates environment initialStore expr value expressionStore →
      Continues continuation value expressionStore finalValue finalStore →
      StateDenotes
        ⟨.eval expr environment, continuation, initialStore⟩
        finalValue finalStore
  | ret
      {value finalValue : Value} {continuation : List Frame}
      {store finalStore : Store} :
      Continues continuation value store finalValue finalStore →
      StateDenotes ⟨.ret value, continuation, store⟩ finalValue finalStore

theorem transition_reflects_denotation
    {state next : State} {finalValue : Value} {finalStore : Store}
    (transition : Transition state next)
    (denotes : StateDenotes next finalValue finalStore) :
    StateDenotes state finalValue finalStore := by
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
  | enterInLeft =>
      cases denotes with
      | eval payloadEvaluation continuation =>
          cases continuation with
          | inLeftApply rest =>
              exact .eval (.inLeft payloadEvaluation) rest
  | applyInLeft =>
      cases denotes with
      | ret continuation =>
          exact .ret (.inLeftApply continuation)
  | enterInRight =>
      cases denotes with
      | eval payloadEvaluation continuation =>
          cases continuation with
          | inRightApply rest =>
              exact .eval (.inRight payloadEvaluation) rest
  | applyInRight =>
      cases denotes with
      | ret continuation =>
          exact .ret (.inRightApply continuation)
  | enterCase =>
      cases denotes with
      | eval scrutineeEvaluation continuation =>
          cases continuation with
          | caseLeft branchEvaluation rest =>
              exact .eval (.caseLeft scrutineeEvaluation branchEvaluation) rest
          | caseRight branchEvaluation rest =>
              exact .eval (.caseRight scrutineeEvaluation branchEvaluation) rest
  | chooseLeft =>
      cases denotes with
      | eval branchEvaluation continuation =>
          exact .ret (.caseLeft branchEvaluation continuation)
  | chooseRight =>
      cases denotes with
      | eval branchEvaluation continuation =>
          exact .ret (.caseRight branchEvaluation continuation)
  | enterNewCell =>
      cases denotes with
      | eval initializerEvaluation continuation =>
          cases continuation with
          | newCellApply rest =>
              exact .eval (.newCell initializerEvaluation) rest
  | applyNewCell =>
      cases denotes with
      | ret continuation =>
          exact .ret (.newCellApply continuation)
  | enterLoadCell =>
      cases denotes with
      | eval referenceEvaluation continuation =>
          cases continuation with
          | loadCellApply read rest =>
              exact .eval (.loadCell referenceEvaluation read) rest
  | applyLoadCell read =>
      cases denotes with
      | ret continuation =>
          exact .ret (.loadCellApply read continuation)
  | enterStoreCell =>
      cases denotes with
      | eval referenceEvaluation continuation =>
          cases continuation with
          | storeCellValue read valueEvaluation written rest =>
              exact .eval
                (.storeCell referenceEvaluation read valueEvaluation written)
                rest
  | beginStoreCellValue read =>
      cases denotes with
      | eval valueEvaluation continuation =>
          cases continuation with
          | storeCellApply written rest =>
              exact .ret
                (.storeCellValue read valueEvaluation written rest)
  | applyStoreCell written =>
      cases denotes with
      | ret continuation =>
          exact .ret (.storeCellApply written continuation)
  | enterConstruct =>
      cases denotes with
      | eval payloadEvaluation continuation =>
          cases continuation with
          | constructApply rest =>
              exact .eval (.construct payloadEvaluation) rest
  | applyConstruct =>
      cases denotes with
      | ret continuation =>
          exact .ret (.constructApply continuation)
  | enterMatchData =>
      cases denotes with
      | eval scrutineeEvaluation continuation =>
          cases continuation with
          | matchDataApply sameOwner branchLookup branchEvaluation rest =>
              exact .eval
                (.matchData scrutineeEvaluation sameOwner branchLookup
                  branchEvaluation)
                rest
  | chooseData sameOwner branchLookup =>
      cases denotes with
      | eval branchEvaluation continuation =>
          exact .ret
            (.matchDataApply sameOwner branchLookup branchEvaluation continuation)
  | lambda =>
      cases denotes with
      | ret continuation => exact .eval .lambda continuation
  | enterApply =>
      cases denotes with
      | eval functionEvaluation continuation =>
          cases continuation with
          | applyArgument argumentEvaluation bodyEvaluation rest =>
              exact .eval
                (.apply functionEvaluation argumentEvaluation bodyEvaluation)
                rest
  | beginArgument =>
      cases denotes with
      | eval argumentEvaluation continuation =>
          cases continuation with
          | applyClosure bodyEvaluation rest =>
              exact .ret
                (.applyArgument argumentEvaluation bodyEvaluation rest)
  | invokeClosure =>
      cases denotes with
      | eval bodyEvaluation continuation =>
          exact .ret (.applyClosure bodyEvaluation continuation)
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
  | enterTernary =>
      cases denotes with
      | eval firstEvaluation continuation =>
          cases continuation with
          | ternarySecond secondEvaluation thirdEvaluation applied rest =>
              exact .eval
                (.ternary firstEvaluation secondEvaluation thirdEvaluation
                  applied)
                rest
  | enterTernarySecond =>
      cases denotes with
      | eval secondEvaluation continuation =>
          cases continuation with
          | ternaryThird thirdEvaluation applied rest =>
              exact .ret (.ternarySecond secondEvaluation thirdEvaluation applied rest)
  | enterTernaryThird =>
      cases denotes with
      | eval thirdEvaluation continuation =>
          cases continuation with
          | ternaryApply applied rest =>
              exact .ret (.ternaryThird thirdEvaluation applied rest)
  | applyTernary applied =>
      cases denotes with
      | ret continuation =>
          exact .ret (.ternaryApply applied continuation)
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
    {steps : Nat} {start finish : State}
    {finalValue : Value} {finalStore : Store}
    (path : Steps steps start finish)
    (denotes : StateDenotes finish finalValue finalStore) :
    StateDenotes start finalValue finalStore := by
  induction path with
  | refl => exact denotes
  | cons transition tail tailIH =>
      exact transition_reflects_denotation transition (tailIH denotes)

theorem steps_from_initial_sound
    {steps : Nat} {environment : Environment}
    {initialStore finalStore : Store} {expr : Expr} {value : Value}
    (path :
      Steps steps
        (State.initial expr environment initialStore)
        (State.final value finalStore)) :
    Evaluates environment initialStore expr value finalStore := by
  have finalDenotes :
      StateDenotes (State.final value finalStore) value finalStore :=
    .ret .done
  have initialDenotes := steps_reflect_denotation path finalDenotes
  cases initialDenotes with
  | eval evaluation continuation =>
      cases continuation
      exact evaluation

set_option doc.verso true in
/-- A completed run from an initial state gives a declarative {lean}`Evaluates`
derivation with exactly the same value and final store.

The inputs are the expression, environment, initial local store, and fuel.
There is no separate typing premise: a completed raw run still obeys the
dynamic rules. Exhausted and faulted runs are outside this conclusion.
-/
theorem runStateful_evaluation_sound
    {fuel : Nat} {environment : Environment}
    {initialStore finalStore : Store} {expr : Expr} {value : Value}
    (result :
      runStateful fuel (State.initial expr environment initialStore) =
        .done value finalStore) :
    Evaluates environment initialStore expr value finalStore := by
  obtain ⟨steps, _, path⟩ := runStateful_sound result
  exact steps_from_initial_sound path

theorem run_stateful_evaluation_sound
    {fuel : Nat} {environment : Environment}
    {initialStore finalStore : Store} {expr : Expr} {value : Value}
    (result :
      runStateful fuel (State.initial expr environment initialStore) =
        .done value finalStore) :
    Evaluates environment initialStore expr value finalStore :=
  runStateful_evaluation_sound result

theorem evaluation_runStateful_complete
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ fuel,
      runStateful fuel (State.initial expr environment initialStore) =
        .done value finalStore := by
  obtain ⟨steps, path⟩ := evaluation.toSteps
  exact ⟨steps, runStateful_complete_with_fuel path (Nat.le_refl steps)⟩

theorem evaluation_run_stateful_complete
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ fuel,
      runStateful fuel (State.initial expr environment initialStore) =
        .done value finalStore :=
  evaluation_runStateful_complete evaluation

set_option doc.verso true in
/-- Given a declarative {lean}`Evaluates` derivation, there is a fuel threshold
such that every budget at least that large returns its value and final store.

The evaluation derivation is a premise. This theorem does not infer termination
from an exhausted run, or promise success for every supplied budget.
-/
theorem evaluation_runStateful_complete_with_sufficient_fuel
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ required,
      ∀ fuel,
        required ≤ fuel →
        runStateful fuel (State.initial expr environment initialStore) =
          .done value finalStore := by
  obtain ⟨steps, path⟩ := evaluation.toSteps
  exact ⟨steps, fun fuel enough =>
    runStateful_complete_with_fuel path enough⟩

theorem evaluation_run_stateful_complete_with_sufficient_fuel
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ required,
      ∀ fuel,
        required ≤ fuel →
        runStateful fuel (State.initial expr environment initialStore) =
          .done value finalStore :=
  evaluation_runStateful_complete_with_sufficient_fuel evaluation

theorem run_evaluation_sound
    {fuel : Nat} {environment : Environment} {initialStore : Store}
    {expr : Expr} {value : Value}
    (result : run fuel (State.initial expr environment initialStore) = .done value) :
    ∃ finalStore,
      Evaluates environment initialStore expr value finalStore := by
  obtain ⟨finalStore, steps, _, path⟩ := run_sound result
  exact ⟨finalStore, steps_from_initial_sound path⟩

theorem evaluation_run_complete
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ fuel,
      run fuel (State.initial expr environment initialStore) = .done value := by
  obtain ⟨steps, path⟩ := evaluation.toSteps
  exact ⟨steps, run_complete_with_fuel path (Nat.le_refl steps)⟩

theorem evaluation_run_complete_with_sufficient_fuel
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∃ required,
      ∀ fuel,
        required ≤ fuel →
        run fuel (State.initial expr environment initialStore) = .done value := by
  obtain ⟨steps, path⟩ := evaluation.toSteps
  exact ⟨steps, fun fuel enough => run_complete_with_fuel path enough⟩

end Solcore.Core
