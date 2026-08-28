import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

inductive Control where
  | eval (expr : Expr) (environment : Environment)
  | ret (value : Value)
  deriving Repr, BEq, DecidableEq

inductive Frame where
  | unaryApply (op : UnaryOp)
  | binaryRight (op : BinaryOp) (right : Expr) (environment : Environment)
  | binaryApply (op : BinaryOp) (leftValue : Value)
  | ternarySecond
      (op : TernaryOp) (second third : Expr) (environment : Environment)
  | ternaryThird
      (op : TernaryOp) (firstValue : Value) (third : Expr)
      (environment : Environment)
  | ternaryApply (op : TernaryOp) (firstValue secondValue : Value)
  | pairRight (right : Expr) (environment : Environment)
  | pairApply (leftValue : Value)
  | firstApply
  | secondApply
  | inLeftApply (rightType : Ty)
  | inRightApply (leftType : Ty)
  | caseBranches
      (leftBranch rightBranch : Expr)
      (environment : Environment)
  | newCellApply (elementType : Ty)
  | loadCellApply
  | storeCellValue (valueExpr : Expr) (environment : Environment)
  | storeCellApply (elementType : Ty) (location : Location)
  | constructApply (constructor : ConstructorId)
  | matchDataApply
      (dataType : DataTypeId)
      (branches : List Expr)
      (environment : Environment)
  | applyArgument (argument : Expr) (environment : Environment)
  | applyClosure
      (parameterType resultType : Ty)
      (body : Expr)
      (environment : Environment)
  | letBody (body : Expr) (environment : Environment)
  | ifBranches (thenBranch : Expr) (elseBranch : Expr) (environment : Environment)
  deriving Repr, BEq, DecidableEq

structure State where
  control : Control
  continuation : List Frame
  store : Store
  deriving Repr, BEq, DecidableEq

def State.initial
    (expr : Expr)
    (environment : Environment := [])
    (store : Store := []) : State := {
  control := .eval expr environment
  continuation := []
  store
}

def State.final (value : Value) (store : Store := []) : State := {
  control := .ret value
  continuation := []
  store
}

inductive Transition : State → State → Prop where
  | unit
      {environment : Environment} {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval .unit environment, continuation, store⟩
        ⟨.ret .unit, continuation, store⟩
  | bool
      {environment : Environment} {value : Bool} {continuation : List Frame}
      {store : Store} :
      Transition
        ⟨.eval (.bool value) environment, continuation, store⟩
        ⟨.ret (.bool value), continuation, store⟩
  | word
      {environment : Environment} {value : Word} {continuation : List Frame}
      {store : Store} :
      Transition
        ⟨.eval (.word value) environment, continuation, store⟩
        ⟨.ret (.word value), continuation, store⟩
  | enterPair
      {environment : Environment} {left right : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.pair left right) environment, continuation, store⟩
        ⟨.eval left environment,
          .pairRight right environment :: continuation, store⟩
  | enterPairRight
      {environment : Environment} {right : Expr}
      {leftValue : Value} {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret leftValue, .pairRight right environment :: continuation, store⟩
        ⟨.eval right environment, .pairApply leftValue :: continuation, store⟩
  | applyPair
      {leftValue rightValue : Value} {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret rightValue, .pairApply leftValue :: continuation, store⟩
        ⟨.ret (.pair leftValue rightValue), continuation, store⟩
  | enterFirst
      {environment : Environment} {operand : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.first operand) environment, continuation, store⟩
        ⟨.eval operand environment, .firstApply :: continuation, store⟩
  | applyFirst
      {leftValue rightValue : Value} {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret (.pair leftValue rightValue), .firstApply :: continuation, store⟩
        ⟨.ret leftValue, continuation, store⟩
  | enterSecond
      {environment : Environment} {operand : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.second operand) environment, continuation, store⟩
        ⟨.eval operand environment, .secondApply :: continuation, store⟩
  | applySecond
      {leftValue rightValue : Value} {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret (.pair leftValue rightValue), .secondApply :: continuation, store⟩
        ⟨.ret rightValue, continuation, store⟩
  | enterInLeft
      {environment : Environment} {rightType : Ty} {payload : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.inLeft rightType payload) environment, continuation, store⟩
        ⟨.eval payload environment, .inLeftApply rightType :: continuation, store⟩
  | applyInLeft
      {rightType : Ty} {payload : Value} {continuation : List Frame}
      {store : Store} :
      Transition
        ⟨.ret payload, .inLeftApply rightType :: continuation, store⟩
        ⟨.ret (.inLeft rightType payload), continuation, store⟩
  | enterInRight
      {environment : Environment} {leftType : Ty} {payload : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.inRight leftType payload) environment, continuation, store⟩
        ⟨.eval payload environment, .inRightApply leftType :: continuation, store⟩
  | applyInRight
      {leftType : Ty} {payload : Value} {continuation : List Frame}
      {store : Store} :
      Transition
        ⟨.ret payload, .inRightApply leftType :: continuation, store⟩
        ⟨.ret (.inRight leftType payload), continuation, store⟩
  | enterCase
      {environment : Environment} {scrutinee leftBranch rightBranch : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.caseE scrutinee leftBranch rightBranch) environment,
          continuation, store⟩
        ⟨.eval scrutinee environment,
          .caseBranches leftBranch rightBranch environment :: continuation, store⟩
  | chooseLeft
      {environment : Environment} {leftBranch rightBranch : Expr}
      {rightType : Ty} {payload : Value} {continuation : List Frame}
      {store : Store} :
      Transition
        ⟨.ret (.inLeft rightType payload),
          .caseBranches leftBranch rightBranch environment :: continuation, store⟩
        ⟨.eval leftBranch (payload :: environment), continuation, store⟩
  | chooseRight
      {environment : Environment} {leftBranch rightBranch : Expr}
      {leftType : Ty} {payload : Value} {continuation : List Frame}
      {store : Store} :
      Transition
        ⟨.ret (.inRight leftType payload),
          .caseBranches leftBranch rightBranch environment :: continuation, store⟩
        ⟨.eval rightBranch (payload :: environment), continuation, store⟩
  | enterNewCell
      {environment : Environment} {elementType : Ty} {initializer : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.newCell elementType initializer) environment, continuation, store⟩
        ⟨.eval initializer environment,
          .newCellApply elementType :: continuation, store⟩
  | applyNewCell
      {elementType : Ty} {initialValue : Value}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret initialValue, .newCellApply elementType :: continuation, store⟩
        ⟨.ret (.cellRef elementType (store.allocate initialValue).2), continuation,
          (store.allocate initialValue).1⟩
  | enterLoadCell
      {environment : Environment} {reference : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.loadCell reference) environment, continuation, store⟩
        ⟨.eval reference environment, .loadCellApply :: continuation, store⟩
  | applyLoadCell
      {elementType : Ty} {location : Location} {value : Value}
      {continuation : List Frame} {store : Store} :
      store.read? location = some value →
      Transition
        ⟨.ret (.cellRef elementType location), .loadCellApply :: continuation, store⟩
        ⟨.ret value, continuation, store⟩
  | enterStoreCell
      {environment : Environment} {reference valueExpr : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.storeCell reference valueExpr) environment, continuation, store⟩
        ⟨.eval reference environment,
          .storeCellValue valueExpr environment :: continuation, store⟩
  | beginStoreCellValue
      {environment : Environment} {valueExpr : Expr}
      {elementType : Ty} {location : Location} {oldValue : Value}
      {continuation : List Frame} {store : Store} :
      store.read? location = some oldValue →
      Transition
        ⟨.ret (.cellRef elementType location),
          .storeCellValue valueExpr environment :: continuation, store⟩
        ⟨.eval valueExpr environment,
          .storeCellApply elementType location :: continuation, store⟩
  | applyStoreCell
      {elementType : Ty} {location : Location} {value : Value}
      {continuation : List Frame} {store updatedStore : Store} :
      store.write? location value = some updatedStore →
      Transition
        ⟨.ret value, .storeCellApply elementType location :: continuation, store⟩
        ⟨.ret .unit, continuation, updatedStore⟩
  | enterConstruct
      {environment : Environment} {constructor : ConstructorId} {payload : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.construct constructor payload) environment, continuation, store⟩
        ⟨.eval payload environment,
          .constructApply constructor :: continuation, store⟩
  | applyConstruct
      {constructor : ConstructorId} {payload : Value}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret payload, .constructApply constructor :: continuation, store⟩
        ⟨.ret (.constructed constructor payload), continuation, store⟩
  | enterMatchData
      {environment : Environment} {dataType : DataTypeId} {resultType : Ty}
      {scrutinee : Expr} {branches : List Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.matchData dataType resultType scrutinee branches) environment,
          continuation, store⟩
        ⟨.eval scrutinee environment,
          .matchDataApply dataType branches environment :: continuation, store⟩
  | chooseData
      {environment : Environment} {dataType : DataTypeId}
      {branches : List Expr} {constructor : ConstructorId}
      {payload : Value} {branch : Expr}
      {continuation : List Frame} {store : Store} :
      constructor.owner = dataType →
      branches[constructor.index]? = some branch →
      Transition
        ⟨.ret (.constructed constructor payload),
          .matchDataApply dataType branches environment :: continuation, store⟩
        ⟨.eval branch (payload :: environment), continuation, store⟩
  | lambda
      {environment : Environment} {parameterType resultType : Ty}
      {body : Expr} {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.lambda parameterType resultType body) environment, continuation, store⟩
        ⟨.ret (.closure parameterType resultType body environment), continuation, store⟩
  | enterApply
      {environment : Environment} {function argument : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.apply function argument) environment, continuation, store⟩
        ⟨.eval function environment,
          .applyArgument argument environment :: continuation, store⟩
  | beginArgument
      {callerEnvironment capturedEnvironment : Environment}
      {parameterType resultType : Ty} {body argument : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret (.closure parameterType resultType body capturedEnvironment),
          .applyArgument argument callerEnvironment :: continuation, store⟩
        ⟨.eval argument callerEnvironment,
          .applyClosure parameterType resultType body capturedEnvironment :: continuation,
          store⟩
  | invokeClosure
      {capturedEnvironment : Environment}
      {parameterType resultType : Ty} {body : Expr}
      {argumentValue : Value} {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret argumentValue,
          .applyClosure parameterType resultType body capturedEnvironment :: continuation,
          store⟩
        ⟨.eval body (argumentValue :: capturedEnvironment), continuation, store⟩
  | var
      {environment : Environment} {index : Nat} {value : Value}
      {continuation : List Frame} {store : Store} :
      environment[index]? = some value →
      Transition
        ⟨.eval (.var index) environment, continuation, store⟩
        ⟨.ret value, continuation, store⟩
  | enterUnary
      {environment : Environment} {op : UnaryOp} {operand : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.unary op operand) environment, continuation, store⟩
        ⟨.eval operand environment, .unaryApply op :: continuation, store⟩
  | applyUnary
      {op : UnaryOp} {operand result : Value} {continuation : List Frame}
      {store : Store} :
      op.apply operand = some result →
      Transition
        ⟨.ret operand, .unaryApply op :: continuation, store⟩
        ⟨.ret result, continuation, store⟩
  | enterBinary
      {environment : Environment} {op : BinaryOp} {left right : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.binary op left right) environment, continuation, store⟩
        ⟨.eval left environment,
          .binaryRight op right environment :: continuation, store⟩
  | enterBinaryRight
      {environment : Environment} {op : BinaryOp} {right : Expr}
      {leftValue : Value} {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret leftValue, .binaryRight op right environment :: continuation, store⟩
        ⟨.eval right environment, .binaryApply op leftValue :: continuation, store⟩
  | applyBinary
      {op : BinaryOp} {leftValue rightValue result : Value}
      {continuation : List Frame} {store : Store} :
      op.apply leftValue rightValue = some result →
      Transition
        ⟨.ret rightValue, .binaryApply op leftValue :: continuation, store⟩
        ⟨.ret result, continuation, store⟩
  | enterTernary
      {environment : Environment} {op : TernaryOp} {first second third : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.ternary op first second third) environment, continuation, store⟩
        ⟨.eval first environment,
          .ternarySecond op second third environment :: continuation, store⟩
  | enterTernarySecond
      {environment : Environment} {op : TernaryOp} {second third : Expr}
      {firstValue : Value} {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret firstValue,
          .ternarySecond op second third environment :: continuation, store⟩
        ⟨.eval second environment,
          .ternaryThird op firstValue third environment :: continuation, store⟩
  | enterTernaryThird
      {environment : Environment} {op : TernaryOp} {third : Expr}
      {firstValue secondValue : Value} {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret secondValue,
          .ternaryThird op firstValue third environment :: continuation, store⟩
        ⟨.eval third environment,
          .ternaryApply op firstValue secondValue :: continuation, store⟩
  | applyTernary
      {op : TernaryOp} {firstValue secondValue thirdValue result : Value}
      {continuation : List Frame} {store : Store} :
      op.apply firstValue secondValue thirdValue = some result →
      Transition
        ⟨.ret thirdValue,
          .ternaryApply op firstValue secondValue :: continuation, store⟩
        ⟨.ret result, continuation, store⟩
  | enterLet
      {environment : Environment} {value body : Expr} {continuation : List Frame}
      {store : Store} :
      Transition
        ⟨.eval (.letE value body) environment, continuation, store⟩
        ⟨.eval value environment, .letBody body environment :: continuation, store⟩
  | bindLet
      {environment : Environment} {value : Value} {body : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret value, .letBody body environment :: continuation, store⟩
        ⟨.eval body (value :: environment), continuation, store⟩
  | enterIf
      {environment : Environment} {condition thenBranch elseBranch : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.eval (.ifE condition thenBranch elseBranch) environment,
          continuation, store⟩
        ⟨.eval condition environment,
          .ifBranches thenBranch elseBranch environment :: continuation, store⟩
  | chooseTrue
      {environment : Environment} {thenBranch elseBranch : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret (.bool true),
          .ifBranches thenBranch elseBranch environment :: continuation, store⟩
        ⟨.eval thenBranch environment, continuation, store⟩
  | chooseFalse
      {environment : Environment} {thenBranch elseBranch : Expr}
      {continuation : List Frame} {store : Store} :
      Transition
        ⟨.ret (.bool false),
          .ifBranches thenBranch elseBranch environment :: continuation, store⟩
        ⟨.eval elseBranch environment, continuation, store⟩

inductive MachineFault where
  | unboundVariable (index : Nat)
  | expectedBool (actual : Value)
  | expectedProduct (actual : Value)
  | expectedSum (actual : Value)
  | expectedFunction (actual : Value)
  | unhandledHostFunction (function : HostFunction)
  | expectedCell (actual : Value)
  | invalidCellLocation (location : Location)
  | expectedNamedData (actual : Value)
  | namedDataTypeMismatch (expected actual : DataTypeId)
  | invalidConstructorBranch (constructor : ConstructorId)
  | invalidUnaryOperand (op : UnaryOp) (actual : Value)
  | invalidBinaryOperands (op : BinaryOp) (left right : Value)
  | invalidTernaryOperands
      (op : TernaryOp) (first second third : Value)
  deriving Repr, BEq, DecidableEq

inductive AdvanceResult where
  | next (state : State)
  | done (value : Value)
  | fault (error : MachineFault)
  deriving Repr, BEq, DecidableEq

def advance (state : State) : AdvanceResult :=
  match state.control with
  | .eval expr environment =>
      match expr with
      | .unit => .next ⟨.ret .unit, state.continuation, state.store⟩
      | .bool value =>
          .next ⟨.ret (.bool value), state.continuation, state.store⟩
      | .word value =>
          .next ⟨.ret (.word value), state.continuation, state.store⟩
      | .pair left right =>
          .next ⟨.eval left environment,
            .pairRight right environment :: state.continuation, state.store⟩
      | .first operand =>
          .next ⟨.eval operand environment, .firstApply :: state.continuation,
            state.store⟩
      | .second operand =>
          .next ⟨.eval operand environment, .secondApply :: state.continuation,
            state.store⟩
      | .inLeft rightType payload =>
          .next ⟨.eval payload environment,
            .inLeftApply rightType :: state.continuation, state.store⟩
      | .inRight leftType payload =>
          .next ⟨.eval payload environment,
            .inRightApply leftType :: state.continuation, state.store⟩
      | .caseE scrutinee leftBranch rightBranch =>
          .next ⟨.eval scrutinee environment,
            .caseBranches leftBranch rightBranch environment :: state.continuation,
            state.store⟩
      | .newCell elementType initializer =>
          .next ⟨.eval initializer environment,
            .newCellApply elementType :: state.continuation, state.store⟩
      | .loadCell reference =>
          .next ⟨.eval reference environment,
            .loadCellApply :: state.continuation, state.store⟩
      | .storeCell reference valueExpr =>
          .next ⟨.eval reference environment,
            .storeCellValue valueExpr environment :: state.continuation, state.store⟩
      | .construct constructor payload =>
          .next ⟨.eval payload environment,
            .constructApply constructor :: state.continuation, state.store⟩
      | .matchData dataType _ scrutinee branches =>
          .next ⟨.eval scrutinee environment,
            .matchDataApply dataType branches environment :: state.continuation,
            state.store⟩
      | .lambda parameterType resultType body =>
          .next ⟨.ret (.closure parameterType resultType body environment),
            state.continuation, state.store⟩
      | .apply function argument =>
          .next ⟨.eval function environment,
            .applyArgument argument environment :: state.continuation, state.store⟩
      | .var index =>
          match environment[index]? with
          | some value => .next ⟨.ret value, state.continuation, state.store⟩
          | none => .fault (.unboundVariable index)
      | .unary op operand =>
          .next ⟨.eval operand environment, .unaryApply op :: state.continuation,
            state.store⟩
      | .binary op left right =>
          .next ⟨.eval left environment,
            .binaryRight op right environment :: state.continuation, state.store⟩
      | .ternary op firstExpr secondExpr thirdExpr =>
          .next ⟨.eval firstExpr environment,
            .ternarySecond op secondExpr thirdExpr environment :: state.continuation,
            state.store⟩
      | .letE value body =>
          .next ⟨.eval value environment,
            .letBody body environment :: state.continuation, state.store⟩
      | .ifE condition thenBranch elseBranch =>
          .next ⟨.eval condition environment,
            .ifBranches thenBranch elseBranch environment :: state.continuation,
            state.store⟩
  | .ret value =>
      match state.continuation with
      | [] => .done value
      | .unaryApply op :: continuation =>
          match op.apply value with
          | some result => .next ⟨.ret result, continuation, state.store⟩
          | none => .fault (.invalidUnaryOperand op value)
      | .binaryRight op right environment :: continuation =>
          .next ⟨.eval right environment, .binaryApply op value :: continuation,
            state.store⟩
      | .binaryApply op leftValue :: continuation =>
          match op.apply leftValue value with
          | some result => .next ⟨.ret result, continuation, state.store⟩
          | none => .fault (.invalidBinaryOperands op leftValue value)
      | .ternarySecond op second third environment :: continuation =>
          .next ⟨.eval second environment,
            .ternaryThird op value third environment :: continuation, state.store⟩
      | .ternaryThird op firstValue third environment :: continuation =>
          .next ⟨.eval third environment,
            .ternaryApply op firstValue value :: continuation, state.store⟩
      | .ternaryApply op firstValue secondValue :: continuation =>
          match op.apply firstValue secondValue value with
          | some result => .next ⟨.ret result, continuation, state.store⟩
          | none =>
              .fault (.invalidTernaryOperands op firstValue secondValue value)
      | .pairRight right environment :: continuation =>
          .next ⟨.eval right environment, .pairApply value :: continuation,
            state.store⟩
      | .pairApply leftValue :: continuation =>
          .next ⟨.ret (.pair leftValue value), continuation, state.store⟩
      | .firstApply :: continuation =>
          match value with
          | .pair leftValue _ =>
              .next ⟨.ret leftValue, continuation, state.store⟩
          | actual => .fault (.expectedProduct actual)
      | .secondApply :: continuation =>
          match value with
          | .pair _ rightValue =>
              .next ⟨.ret rightValue, continuation, state.store⟩
          | actual => .fault (.expectedProduct actual)
      | .inLeftApply rightType :: continuation =>
          .next ⟨.ret (.inLeft rightType value), continuation, state.store⟩
      | .inRightApply leftType :: continuation =>
          .next ⟨.ret (.inRight leftType value), continuation, state.store⟩
      | .caseBranches leftBranch rightBranch environment :: continuation =>
          match value with
          | .inLeft _ payload =>
              .next ⟨.eval leftBranch (payload :: environment), continuation,
                state.store⟩
          | .inRight _ payload =>
              .next ⟨.eval rightBranch (payload :: environment), continuation,
                state.store⟩
          | actual => .fault (.expectedSum actual)
      | .newCellApply elementType :: continuation =>
          let allocated := state.store.allocate value
          .next ⟨.ret (.cellRef elementType allocated.2), continuation, allocated.1⟩
      | .loadCellApply :: continuation =>
          match value with
          | .cellRef _ location =>
              match state.store.read? location with
              | some loaded => .next ⟨.ret loaded, continuation, state.store⟩
              | none => .fault (.invalidCellLocation location)
          | actual => .fault (.expectedCell actual)
      | .storeCellValue valueExpr environment :: continuation =>
          match value with
          | .cellRef elementType location =>
              match state.store.read? location with
              | some _ =>
                  .next ⟨.eval valueExpr environment,
                    .storeCellApply elementType location :: continuation, state.store⟩
              | none => .fault (.invalidCellLocation location)
          | actual => .fault (.expectedCell actual)
      | .storeCellApply _ location :: continuation =>
          match state.store.write? location value with
          | some updatedStore => .next ⟨.ret .unit, continuation, updatedStore⟩
          | none => .fault (.invalidCellLocation location)
      | .constructApply constructor :: continuation =>
          .next ⟨.ret (.constructed constructor value), continuation, state.store⟩
      | .matchDataApply dataType branches environment :: continuation =>
          match value with
          | .constructed constructor payload =>
              if constructor.owner = dataType then
                match branches[constructor.index]? with
                | some branch =>
                    .next ⟨.eval branch (payload :: environment), continuation,
                      state.store⟩
                | none => .fault (.invalidConstructorBranch constructor)
              else
                .fault (.namedDataTypeMismatch dataType constructor.owner)
          | actual => .fault (.expectedNamedData actual)
      | .applyArgument argument callerEnvironment :: continuation =>
          match value with
          | .closure parameterType resultType body capturedEnvironment =>
              .next ⟨.eval argument callerEnvironment,
                .applyClosure parameterType resultType body capturedEnvironment ::
                  continuation,
                state.store⟩
          | .hostFunction function => .fault (.unhandledHostFunction function)
          | actual => .fault (.expectedFunction actual)
      | .applyClosure _ _ body capturedEnvironment :: continuation =>
          .next ⟨.eval body (value :: capturedEnvironment), continuation, state.store⟩
      | .letBody body environment :: continuation =>
          .next ⟨.eval body (value :: environment), continuation, state.store⟩
      | .ifBranches thenBranch elseBranch environment :: continuation =>
          match value with
          | .bool true =>
              .next ⟨.eval thenBranch environment, continuation, state.store⟩
          | .bool false =>
              .next ⟨.eval elseBranch environment, continuation, state.store⟩
          | actual => .fault (.expectedBool actual)

inductive Steps : Nat → State → State → Prop where
  | refl {state : State} : Steps 0 state state
  | cons
      {steps : Nat} {start next finish : State} :
      Transition start next →
      Steps steps next finish →
      Steps (steps + 1) start finish

inductive RunResult where
  | done (value : Value)
  | outOfFuel
  | fault (error : MachineFault)
  deriving Repr, BEq, DecidableEq

inductive StatefulRunResult where
  | done (value : Value) (store : Store)
  | outOfFuel (state : State)
  | fault (error : MachineFault) (state : State)
  deriving Repr, BEq, DecidableEq

def StatefulRunResult.erase : StatefulRunResult → RunResult
  | .done value _ => .done value
  | .outOfFuel _ => .outOfFuel
  | .fault error _ => .fault error

def runStateful : Nat → State → StatefulRunResult
  | fuel, state =>
      match advance state with
      | .done value => .done value state.store
      | .fault error => .fault error state
      | .next next =>
          match fuel with
          | 0 => .outOfFuel state
          | remaining + 1 => runStateful remaining next

def run (fuel : Nat) (state : State) : RunResult :=
  (runStateful fuel state).erase

def Program.runStateful (program : Program) (fuel : Nat) : StatefulRunResult :=
  Solcore.Core.runStateful fuel (State.initial program.body)

def Program.run (program : Program) (fuel : Nat) : RunResult :=
  Solcore.Core.run fuel (State.initial program.body)

end Solcore.Core
