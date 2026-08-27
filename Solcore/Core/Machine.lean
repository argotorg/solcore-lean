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
  | pairRight (right : Expr) (environment : Environment)
  | pairApply (leftValue : Value)
  | firstApply
  | secondApply
  | inLeftApply (rightType : Ty)
  | inRightApply (leftType : Ty)
  | caseBranches
      (leftBranch rightBranch : Expr)
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
  deriving Repr, BEq, DecidableEq

def State.initial (expr : Expr) (environment : Environment := []) : State := {
  control := .eval expr environment
  continuation := []
}

def State.final (value : Value) : State := {
  control := .ret value
  continuation := []
}

inductive Transition : State → State → Prop where
  | unit {environment : Environment} {continuation : List Frame} :
      Transition
        ⟨.eval .unit environment, continuation⟩
        ⟨.ret .unit, continuation⟩
  | bool
      {environment : Environment} {value : Bool} {continuation : List Frame} :
      Transition
        ⟨.eval (.bool value) environment, continuation⟩
        ⟨.ret (.bool value), continuation⟩
  | word
      {environment : Environment} {value : Word} {continuation : List Frame} :
      Transition
        ⟨.eval (.word value) environment, continuation⟩
        ⟨.ret (.word value), continuation⟩
  | enterPair
      {environment : Environment} {left right : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.eval (.pair left right) environment, continuation⟩
        ⟨.eval left environment, .pairRight right environment :: continuation⟩
  | enterPairRight
      {environment : Environment} {right : Expr}
      {leftValue : Value} {continuation : List Frame} :
      Transition
        ⟨.ret leftValue, .pairRight right environment :: continuation⟩
        ⟨.eval right environment, .pairApply leftValue :: continuation⟩
  | applyPair
      {leftValue rightValue : Value} {continuation : List Frame} :
      Transition
        ⟨.ret rightValue, .pairApply leftValue :: continuation⟩
        ⟨.ret (.pair leftValue rightValue), continuation⟩
  | enterFirst
      {environment : Environment} {operand : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.eval (.first operand) environment, continuation⟩
        ⟨.eval operand environment, .firstApply :: continuation⟩
  | applyFirst
      {leftValue rightValue : Value} {continuation : List Frame} :
      Transition
        ⟨.ret (.pair leftValue rightValue), .firstApply :: continuation⟩
        ⟨.ret leftValue, continuation⟩
  | enterSecond
      {environment : Environment} {operand : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.eval (.second operand) environment, continuation⟩
        ⟨.eval operand environment, .secondApply :: continuation⟩
  | applySecond
      {leftValue rightValue : Value} {continuation : List Frame} :
      Transition
        ⟨.ret (.pair leftValue rightValue), .secondApply :: continuation⟩
        ⟨.ret rightValue, continuation⟩
  | enterInLeft
      {environment : Environment} {rightType : Ty} {payload : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.eval (.inLeft rightType payload) environment, continuation⟩
        ⟨.eval payload environment, .inLeftApply rightType :: continuation⟩
  | applyInLeft
      {rightType : Ty} {payload : Value} {continuation : List Frame} :
      Transition
        ⟨.ret payload, .inLeftApply rightType :: continuation⟩
        ⟨.ret (.inLeft rightType payload), continuation⟩
  | enterInRight
      {environment : Environment} {leftType : Ty} {payload : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.eval (.inRight leftType payload) environment, continuation⟩
        ⟨.eval payload environment, .inRightApply leftType :: continuation⟩
  | applyInRight
      {leftType : Ty} {payload : Value} {continuation : List Frame} :
      Transition
        ⟨.ret payload, .inRightApply leftType :: continuation⟩
        ⟨.ret (.inRight leftType payload), continuation⟩
  | enterCase
      {environment : Environment} {scrutinee leftBranch rightBranch : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.eval (.caseE scrutinee leftBranch rightBranch) environment, continuation⟩
        ⟨.eval scrutinee environment,
          .caseBranches leftBranch rightBranch environment :: continuation⟩
  | chooseLeft
      {environment : Environment} {leftBranch rightBranch : Expr}
      {rightType : Ty} {payload : Value} {continuation : List Frame} :
      Transition
        ⟨.ret (.inLeft rightType payload),
          .caseBranches leftBranch rightBranch environment :: continuation⟩
        ⟨.eval leftBranch (payload :: environment), continuation⟩
  | chooseRight
      {environment : Environment} {leftBranch rightBranch : Expr}
      {leftType : Ty} {payload : Value} {continuation : List Frame} :
      Transition
        ⟨.ret (.inRight leftType payload),
          .caseBranches leftBranch rightBranch environment :: continuation⟩
        ⟨.eval rightBranch (payload :: environment), continuation⟩
  | lambda
      {environment : Environment} {parameterType resultType : Ty}
      {body : Expr} {continuation : List Frame} :
      Transition
        ⟨.eval (.lambda parameterType resultType body) environment, continuation⟩
        ⟨.ret (.closure parameterType resultType body environment), continuation⟩
  | enterApply
      {environment : Environment} {function argument : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.eval (.apply function argument) environment, continuation⟩
        ⟨.eval function environment,
          .applyArgument argument environment :: continuation⟩
  | beginArgument
      {callerEnvironment capturedEnvironment : Environment}
      {parameterType resultType : Ty} {body argument : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.ret (.closure parameterType resultType body capturedEnvironment),
          .applyArgument argument callerEnvironment :: continuation⟩
        ⟨.eval argument callerEnvironment,
          .applyClosure parameterType resultType body capturedEnvironment :: continuation⟩
  | invokeClosure
      {capturedEnvironment : Environment}
      {parameterType resultType : Ty} {body : Expr}
      {argumentValue : Value} {continuation : List Frame} :
      Transition
        ⟨.ret argumentValue,
          .applyClosure parameterType resultType body capturedEnvironment :: continuation⟩
        ⟨.eval body (argumentValue :: capturedEnvironment), continuation⟩
  | var
      {environment : Environment} {index : Nat} {value : Value}
      {continuation : List Frame} :
      environment[index]? = some value →
      Transition
        ⟨.eval (.var index) environment, continuation⟩
        ⟨.ret value, continuation⟩
  | enterUnary
      {environment : Environment} {op : UnaryOp} {operand : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.eval (.unary op operand) environment, continuation⟩
        ⟨.eval operand environment, .unaryApply op :: continuation⟩
  | applyUnary
      {op : UnaryOp} {operand result : Value} {continuation : List Frame} :
      op.apply operand = some result →
      Transition
        ⟨.ret operand, .unaryApply op :: continuation⟩
        ⟨.ret result, continuation⟩
  | enterBinary
      {environment : Environment} {op : BinaryOp} {left right : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.eval (.binary op left right) environment, continuation⟩
        ⟨.eval left environment,
          .binaryRight op right environment :: continuation⟩
  | enterBinaryRight
      {environment : Environment} {op : BinaryOp} {right : Expr}
      {leftValue : Value} {continuation : List Frame} :
      Transition
        ⟨.ret leftValue, .binaryRight op right environment :: continuation⟩
        ⟨.eval right environment, .binaryApply op leftValue :: continuation⟩
  | applyBinary
      {op : BinaryOp} {leftValue rightValue result : Value}
      {continuation : List Frame} :
      op.apply leftValue rightValue = some result →
      Transition
        ⟨.ret rightValue, .binaryApply op leftValue :: continuation⟩
        ⟨.ret result, continuation⟩
  | enterLet
      {environment : Environment} {value body : Expr} {continuation : List Frame} :
      Transition
        ⟨.eval (.letE value body) environment, continuation⟩
        ⟨.eval value environment, .letBody body environment :: continuation⟩
  | bindLet
      {environment : Environment} {value : Value} {body : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.ret value, .letBody body environment :: continuation⟩
        ⟨.eval body (value :: environment), continuation⟩
  | enterIf
      {environment : Environment} {condition thenBranch elseBranch : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.eval (.ifE condition thenBranch elseBranch) environment, continuation⟩
        ⟨.eval condition environment,
          .ifBranches thenBranch elseBranch environment :: continuation⟩
  | chooseTrue
      {environment : Environment} {thenBranch elseBranch : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.ret (.bool true),
          .ifBranches thenBranch elseBranch environment :: continuation⟩
        ⟨.eval thenBranch environment, continuation⟩
  | chooseFalse
      {environment : Environment} {thenBranch elseBranch : Expr}
      {continuation : List Frame} :
      Transition
        ⟨.ret (.bool false),
          .ifBranches thenBranch elseBranch environment :: continuation⟩
        ⟨.eval elseBranch environment, continuation⟩

inductive MachineFault where
  | unboundVariable (index : Nat)
  | expectedBool (actual : Value)
  | expectedProduct (actual : Value)
  | expectedSum (actual : Value)
  | expectedFunction (actual : Value)
  | invalidUnaryOperand (op : UnaryOp) (actual : Value)
  | invalidBinaryOperands (op : BinaryOp) (left right : Value)
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
      | .unit => .next ⟨.ret .unit, state.continuation⟩
      | .bool value => .next ⟨.ret (.bool value), state.continuation⟩
      | .word value => .next ⟨.ret (.word value), state.continuation⟩
      | .pair left right =>
          .next ⟨.eval left environment,
            .pairRight right environment :: state.continuation⟩
      | .first operand =>
          .next ⟨.eval operand environment, .firstApply :: state.continuation⟩
      | .second operand =>
          .next ⟨.eval operand environment, .secondApply :: state.continuation⟩
      | .inLeft rightType payload =>
          .next ⟨.eval payload environment,
            .inLeftApply rightType :: state.continuation⟩
      | .inRight leftType payload =>
          .next ⟨.eval payload environment,
            .inRightApply leftType :: state.continuation⟩
      | .caseE scrutinee leftBranch rightBranch =>
          .next ⟨.eval scrutinee environment,
            .caseBranches leftBranch rightBranch environment :: state.continuation⟩
      | .lambda parameterType resultType body =>
          .next ⟨.ret (.closure parameterType resultType body environment),
            state.continuation⟩
      | .apply function argument =>
          .next ⟨.eval function environment,
            .applyArgument argument environment :: state.continuation⟩
      | .var index =>
          match environment[index]? with
          | some value => .next ⟨.ret value, state.continuation⟩
          | none => .fault (.unboundVariable index)
      | .unary op operand =>
          .next ⟨.eval operand environment, .unaryApply op :: state.continuation⟩
      | .binary op left right =>
          .next ⟨.eval left environment,
            .binaryRight op right environment :: state.continuation⟩
      | .letE value body =>
          .next ⟨.eval value environment,
            .letBody body environment :: state.continuation⟩
      | .ifE condition thenBranch elseBranch =>
          .next ⟨.eval condition environment,
            .ifBranches thenBranch elseBranch environment :: state.continuation⟩
  | .ret value =>
      match state.continuation with
      | [] => .done value
      | .unaryApply op :: continuation =>
          match op.apply value with
          | some result => .next ⟨.ret result, continuation⟩
          | none => .fault (.invalidUnaryOperand op value)
      | .binaryRight op right environment :: continuation =>
          .next ⟨.eval right environment, .binaryApply op value :: continuation⟩
      | .binaryApply op leftValue :: continuation =>
          match op.apply leftValue value with
          | some result => .next ⟨.ret result, continuation⟩
          | none => .fault (.invalidBinaryOperands op leftValue value)
      | .pairRight right environment :: continuation =>
          .next ⟨.eval right environment, .pairApply value :: continuation⟩
      | .pairApply leftValue :: continuation =>
          .next ⟨.ret (.pair leftValue value), continuation⟩
      | .firstApply :: continuation =>
          match value with
          | .pair leftValue _ => .next ⟨.ret leftValue, continuation⟩
          | actual => .fault (.expectedProduct actual)
      | .secondApply :: continuation =>
          match value with
          | .pair _ rightValue => .next ⟨.ret rightValue, continuation⟩
          | actual => .fault (.expectedProduct actual)
      | .inLeftApply rightType :: continuation =>
          .next ⟨.ret (.inLeft rightType value), continuation⟩
      | .inRightApply leftType :: continuation =>
          .next ⟨.ret (.inRight leftType value), continuation⟩
      | .caseBranches leftBranch rightBranch environment :: continuation =>
          match value with
          | .inLeft _ payload =>
              .next ⟨.eval leftBranch (payload :: environment), continuation⟩
          | .inRight _ payload =>
              .next ⟨.eval rightBranch (payload :: environment), continuation⟩
          | actual => .fault (.expectedSum actual)
      | .applyArgument argument callerEnvironment :: continuation =>
          match value with
          | .closure parameterType resultType body capturedEnvironment =>
              .next ⟨.eval argument callerEnvironment,
                .applyClosure parameterType resultType body capturedEnvironment ::
                  continuation⟩
          | actual => .fault (.expectedFunction actual)
      | .applyClosure _ _ body capturedEnvironment :: continuation =>
          .next ⟨.eval body (value :: capturedEnvironment), continuation⟩
      | .letBody body environment :: continuation =>
          .next ⟨.eval body (value :: environment), continuation⟩
      | .ifBranches thenBranch elseBranch environment :: continuation =>
          match value with
          | .bool true => .next ⟨.eval thenBranch environment, continuation⟩
          | .bool false => .next ⟨.eval elseBranch environment, continuation⟩
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

def run : Nat → State → RunResult
  | fuel, state =>
      match advance state with
      | .done value => .done value
      | .fault error => .fault error
      | .next next =>
          match fuel with
          | 0 => .outOfFuel
          | remaining + 1 => run remaining next

def Program.run (program : Program) (fuel : Nat) : RunResult :=
  Solcore.Core.run fuel (State.initial program.body)

end Solcore.Core
