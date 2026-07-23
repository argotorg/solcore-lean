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
