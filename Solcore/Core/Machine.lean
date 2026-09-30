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
  | hostApply (function : HostFunction)
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
  | integer
      {environment : Environment} {value : Int} {continuation : List Frame}
      {store : Store} :
      Transition
        ⟨.eval (.integer value) environment, continuation, store⟩
        ⟨.ret (.integer value), continuation, store⟩
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
  | invalidHostArgument (function : HostFunction) (actual : Value)
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
      | .integer value =>
          .next ⟨.ret (.integer value), state.continuation, state.store⟩
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
      | .hostApply function :: _ =>
          .fault (.unhandledHostFunction function)
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

/-!
## Consolidated module: `Solcore.Core.MachineProperties`
-/

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
        | integer value =>
            simp [advance] at advanced
            cases advanced
            exact .integer
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
        | ternary op firstExpr secondExpr thirdExpr =>
            simp [advance] at advanced
            cases advanced
            exact .enterTernary
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
                | unit | bool | word | integer | hostFunction | inLeft | inRight | closure | cellRef |
                    constructed =>
                    simp [advance] at advanced
                | pair leftValue rightValue =>
                    simp [advance] at advanced
                    cases advanced
                    exact .applyFirst
            | secondApply =>
                cases value with
                | unit | bool | word | integer | hostFunction | inLeft | inRight | closure | cellRef |
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
                | unit | bool | word | integer | hostFunction | pair | closure | cellRef |
                    constructed =>
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
                | unit | bool | word | integer | hostFunction | pair | closure | inLeft | inRight |
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
                | unit | bool | word | integer | hostFunction | pair | closure | inLeft | inRight |
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
                | unit | bool | word | integer | hostFunction | pair | closure | inLeft | inRight |
                    cellRef =>
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
                | unit | bool | word | integer | hostFunction | pair | inLeft | inRight | cellRef |
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
            | hostApply function =>
                simp [advance] at advanced
            | letBody body environment =>
                simp [advance] at advanced
                cases advanced
                exact .bindLet
            | ifBranches thenBranch elseBranch environment =>
                cases value with
                | unit | word | integer | hostFunction | pair | inLeft | inRight | closure | cellRef |
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
        | unit | bool | word | integer | pair | first | second | inLeft | inRight | caseE |
            newCell | loadCell | storeCell | construct | matchData | lambda |
            apply | unary | binary | ternary | letE | ifE =>
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
                | unit | bool | word | integer | hostFunction | pair | closure | inLeft | inRight |
                    constructed =>
                    simp [advance] at advanced
                | cellRef elementType location =>
                    cases lookup : store.read? location <;>
                      simp [advance, lookup] at advanced
            | storeCellValue valueExpr environment =>
                cases returned with
                | unit | bool | word | integer | hostFunction | pair | closure | inLeft | inRight |
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
                | unit | bool | word | integer | hostFunction | pair | closure | inLeft | inRight |
                    cellRef =>
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
            | hostApply function => simp [advance] at advanced
            | letBody body environment => simp [advance] at advanced
            | ifBranches thenBranch elseBranch environment =>
                cases returned with
                | unit | word | integer | hostFunction | pair | inLeft | inRight | closure | cellRef |
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
