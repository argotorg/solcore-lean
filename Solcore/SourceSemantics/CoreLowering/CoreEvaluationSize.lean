import Solcore.Core.Eval

/-! A natural-number size certificate for the existing Core big-step relation.
The size counts rule nodes and strictly decreases at every premise. This is a
mathematical induction device; it adds neither an evaluator nor a machine rule.
Every existing finite evaluation has a size certificate, and erasing that
certificate recovers exactly the original relation. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CoreProof

open Core

inductive EvaluationSize : Nat → Environment → Store → Expr → Value → Store → Prop where
  | unit {environment : Environment} {store : Store} :
      EvaluationSize 1 environment store .unit .unit store
  | bool {environment : Environment} {store : Store} {value : Bool} :
      EvaluationSize 1 environment store (.bool value) (.bool value) store
  | word {environment : Environment} {store : Store} {value : Word} :
      EvaluationSize 1 environment store (.word value) (.word value) store
  | integer {environment : Environment} {store : Store} {value : Int} :
      EvaluationSize 1 environment store (.integer value) (.integer value) store
  | pair {cost1 cost2 : Nat}
      {environment : Environment} {initialStore middleStore finalStore : Store}
      {left right : Expr} {leftValue rightValue : Value} :
      EvaluationSize cost1 environment initialStore left leftValue middleStore →
      EvaluationSize cost2 environment middleStore right rightValue finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore (.pair left right)
        (.pair leftValue rightValue) finalStore
  | first {cost1 : Nat}
      {environment : Environment} {initialStore finalStore : Store}
      {operand : Expr} {leftValue rightValue : Value} :
      EvaluationSize cost1 environment initialStore operand
        (.pair leftValue rightValue) finalStore →
      EvaluationSize (cost1 + 1) environment initialStore (.first operand) leftValue finalStore
  | second {cost1 : Nat}
      {environment : Environment} {initialStore finalStore : Store}
      {operand : Expr} {leftValue rightValue : Value} :
      EvaluationSize cost1 environment initialStore operand
        (.pair leftValue rightValue) finalStore →
      EvaluationSize (cost1 + 1) environment initialStore (.second operand) rightValue finalStore
  | inLeft {cost1 : Nat}
      {environment : Environment} {initialStore finalStore : Store}
      {rightType : Ty} {payload : Expr} {payloadValue : Value} :
      EvaluationSize cost1 environment initialStore payload payloadValue finalStore →
      EvaluationSize (cost1 + 1) environment initialStore (.inLeft rightType payload)
        (.inLeft rightType payloadValue) finalStore
  | inRight {cost1 : Nat}
      {environment : Environment} {initialStore finalStore : Store}
      {leftType : Ty} {payload : Expr} {payloadValue : Value} :
      EvaluationSize cost1 environment initialStore payload payloadValue finalStore →
      EvaluationSize (cost1 + 1) environment initialStore (.inRight leftType payload)
        (.inRight leftType payloadValue) finalStore
  | caseLeft {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {scrutinee leftBranch rightBranch : Expr}
      {rightType : Ty} {payload result : Value} :
      EvaluationSize cost1 environment initialStore scrutinee
        (.inLeft rightType payload) branchStore →
      EvaluationSize cost2 (payload :: environment) branchStore leftBranch result finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore
        (.caseE scrutinee leftBranch rightBranch) result finalStore
  | caseRight {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {scrutinee leftBranch rightBranch : Expr}
      {leftType : Ty} {payload result : Value} :
      EvaluationSize cost1 environment initialStore scrutinee
        (.inRight leftType payload) branchStore →
      EvaluationSize cost2 (payload :: environment) branchStore rightBranch result finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore
        (.caseE scrutinee leftBranch rightBranch) result finalStore
  | lambda
      {environment : Environment} {store : Store}
      {parameterType resultType : Ty} {body : Expr} :
      EvaluationSize 1 environment store (.lambda parameterType resultType body)
        (.closure parameterType resultType body environment) store
  | apply {cost1 cost2 cost3 : Nat}
      {environment capturedEnvironment : Environment}
      {initialStore argumentStore bodyStore finalStore : Store}
      {function argument body : Expr} {parameterType resultType : Ty}
      {argumentValue result : Value} :
      EvaluationSize cost1 environment initialStore function
        (.closure parameterType resultType body capturedEnvironment)
        argumentStore →
      EvaluationSize cost2 environment argumentStore argument argumentValue bodyStore →
      EvaluationSize cost3 (argumentValue :: capturedEnvironment) bodyStore body result
        finalStore →
      EvaluationSize (cost1 + cost2 + cost3 + 1) environment initialStore (.apply function argument) result finalStore
  | var
      {environment : Environment} {store : Store}
      {index : Nat} {value : Value} :
      environment[index]? = some value →
      EvaluationSize 1 environment store (.var index) value store
  | newCell {cost1 : Nat}
      {environment : Environment} {initialStore initializedStore : Store}
      {elementType : Ty} {initializer : Expr} {initialValue : Value} :
      EvaluationSize cost1 environment initialStore initializer initialValue initializedStore →
      EvaluationSize (cost1 + 1) environment initialStore (.newCell elementType initializer)
        (.cellRef elementType initializedStore.length)
        (initializedStore ++ [initialValue])
  | loadCell {cost1 : Nat}
      {environment : Environment} {initialStore referenceStore : Store}
      {reference : Expr} {elementType : Ty} {location : Location}
      {value : Value} :
      EvaluationSize cost1 environment initialStore reference
        (.cellRef elementType location) referenceStore →
      Store.read? referenceStore location = some value →
      EvaluationSize (cost1 + 1) environment initialStore (.loadCell reference) value referenceStore
  | storeCell {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore referenceStore valueStore finalStore : Store}
      {reference value : Expr} {elementType : Ty} {location : Location}
      {oldValue newValue : Value} :
      EvaluationSize cost1 environment initialStore reference
        (.cellRef elementType location) referenceStore →
      Store.read? referenceStore location = some oldValue →
      EvaluationSize cost2 environment referenceStore value newValue valueStore →
      Store.write? valueStore location newValue = some finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore (.storeCell reference value) .unit finalStore
  | construct {cost1 : Nat}
      {environment : Environment} {initialStore finalStore : Store}
      {constructor : ConstructorId} {payload : Expr} {payloadValue : Value} :
      EvaluationSize cost1 environment initialStore payload payloadValue finalStore →
      EvaluationSize (cost1 + 1) environment initialStore (.construct constructor payload)
        (.constructed constructor payloadValue) finalStore
  | matchData {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {dataType : DataTypeId} {resultType : Ty}
      {scrutinee branch : Expr} {branches : List Expr}
      {constructor : ConstructorId} {payload result : Value} :
      EvaluationSize cost1 environment initialStore scrutinee
        (.constructed constructor payload) branchStore →
      constructor.owner = dataType →
      branches[constructor.index]? = some branch →
      EvaluationSize cost2 (payload :: environment) branchStore branch result finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore
        (.matchData dataType resultType scrutinee branches) result finalStore
  | unary {cost1 : Nat}
      {environment : Environment} {initialStore finalStore : Store}
      {op : UnaryOp} {operand : Expr} {operandValue result : Value} :
      EvaluationSize cost1 environment initialStore operand operandValue finalStore →
      op.apply operandValue = some result →
      EvaluationSize (cost1 + 1) environment initialStore (.unary op operand) result finalStore
  | binary {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore rightStore finalStore : Store}
      {op : BinaryOp} {left right : Expr}
      {leftValue rightValue result : Value} :
      EvaluationSize cost1 environment initialStore left leftValue rightStore →
      EvaluationSize cost2 environment rightStore right rightValue finalStore →
      op.apply leftValue rightValue = some result →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore (.binary op left right) result finalStore
  | ternary {cost1 cost2 cost3 : Nat}
      {environment : Environment}
      {initialStore secondStore thirdStore finalStore : Store}
      {op : TernaryOp} {first second third : Expr}
      {firstValue secondValue thirdValue result : Value} :
      EvaluationSize cost1 environment initialStore first firstValue secondStore →
      EvaluationSize cost2 environment secondStore second secondValue thirdStore →
      EvaluationSize cost3 environment thirdStore third thirdValue finalStore →
      op.apply firstValue secondValue thirdValue = some result →
      EvaluationSize (cost1 + cost2 + cost3 + 1) environment initialStore (.ternary op first second third)
        result finalStore
  | letE {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore bodyStore finalStore : Store}
      {value body : Expr} {boundValue result : Value} :
      EvaluationSize cost1 environment initialStore value boundValue bodyStore →
      EvaluationSize cost2 (boundValue :: environment) bodyStore body result finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore (.letE value body) result finalStore
  | ifTrue {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {condition thenBranch elseBranch : Expr} {result : Value} :
      EvaluationSize cost1 environment initialStore condition (.bool true) branchStore →
      EvaluationSize cost2 environment branchStore thenBranch result finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore
        (.ifE condition thenBranch elseBranch) result finalStore
  | ifFalse {cost1 cost2 : Nat}
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {condition thenBranch elseBranch : Expr} {result : Value} :
      EvaluationSize cost1 environment initialStore condition (.bool false) branchStore →
      EvaluationSize cost2 environment branchStore elseBranch result finalStore →
      EvaluationSize (cost1 + cost2 + 1) environment initialStore
        (.ifE condition thenBranch elseBranch) result finalStore


theorem EvaluationSize.sound
    {size : Nat} {environment : Environment} {before after : Store} {expression : Expr} {value : Value}
    (evaluation : EvaluationSize size environment before expression value after) :
    Evaluates environment before expression value after := by
  induction evaluation with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | pair _ _ left right => exact .pair left right
  | first _ operand => exact .first operand
  | second _ operand => exact .second operand
  | inLeft _ payload => exact .inLeft payload
  | inRight _ payload => exact .inRight payload
  | caseLeft _ _ scrutinee branch => exact .caseLeft scrutinee branch
  | caseRight _ _ scrutinee branch => exact .caseRight scrutinee branch
  | lambda => exact .lambda
  | apply _ _ _ function argument body => exact .apply function argument body
  | var found => exact .var found
  | newCell _ initializer => exact .newCell initializer
  | loadCell _ found reference => exact .loadCell reference found
  | storeCell _ read _ write reference value => exact .storeCell reference read value write
  | construct _ payload => exact .construct payload
  | matchData _ owned found _ scrutinee branch => exact .matchData scrutinee owned found branch
  | unary _ applied operand => exact .unary operand applied
  | binary _ _ applied left right => exact .binary left right applied
  | ternary _ _ _ applied first second third => exact .ternary first second third applied
  | letE _ _ value body => exact .letE value body
  | ifTrue _ _ condition branch => exact .ifTrue condition branch
  | ifFalse _ _ condition branch => exact .ifFalse condition branch

theorem evaluation_has_size
    {environment : Environment} {before after : Store} {expression : Expr} {value : Value}
    (evaluation : Evaluates environment before expression value after) :
    ∃ size, EvaluationSize size environment before expression value after := by
  induction evaluation with
  | unit => exact ⟨_, .unit⟩
  | bool => exact ⟨_, .bool⟩
  | word => exact ⟨_, .word⟩
  | integer => exact ⟨_, .integer⟩
  | pair _ _ left right =>
    obtain ⟨_, left⟩ := left; obtain ⟨_, right⟩ := right
    exact ⟨_, .pair left right⟩
  | first _ operand => obtain ⟨_, operand⟩ := operand; exact ⟨_, .first operand⟩
  | second _ operand => obtain ⟨_, operand⟩ := operand; exact ⟨_, .second operand⟩
  | inLeft _ payload => obtain ⟨_, payload⟩ := payload; exact ⟨_, .inLeft payload⟩
  | inRight _ payload => obtain ⟨_, payload⟩ := payload; exact ⟨_, .inRight payload⟩
  | caseLeft _ _ scrutinee branch =>
    obtain ⟨_, scrutinee⟩ := scrutinee; obtain ⟨_, branch⟩ := branch
    exact ⟨_, .caseLeft scrutinee branch⟩
  | caseRight _ _ scrutinee branch =>
    obtain ⟨_, scrutinee⟩ := scrutinee; obtain ⟨_, branch⟩ := branch
    exact ⟨_, .caseRight scrutinee branch⟩
  | lambda => exact ⟨_, .lambda⟩
  | apply _ _ _ function argument body =>
    obtain ⟨_, function⟩ := function; obtain ⟨_, argument⟩ := argument; obtain ⟨_, body⟩ := body
    exact ⟨_, .apply function argument body⟩
  | var found => exact ⟨_, .var found⟩
  | newCell _ initializer => obtain ⟨_, initializer⟩ := initializer; exact ⟨_, .newCell initializer⟩
  | loadCell _ found reference => obtain ⟨_, reference⟩ := reference; exact ⟨_, .loadCell reference found⟩
  | storeCell _ read _ write reference value =>
    obtain ⟨_, reference⟩ := reference; obtain ⟨_, value⟩ := value
    exact ⟨_, .storeCell reference read value write⟩
  | construct _ payload => obtain ⟨_, payload⟩ := payload; exact ⟨_, .construct payload⟩
  | matchData _ owned found _ scrutinee branch =>
    obtain ⟨_, scrutinee⟩ := scrutinee; obtain ⟨_, branch⟩ := branch
    exact ⟨_, .matchData scrutinee owned found branch⟩
  | unary _ applied operand => obtain ⟨_, operand⟩ := operand; exact ⟨_, .unary operand applied⟩
  | binary _ _ applied left right =>
    obtain ⟨_, left⟩ := left; obtain ⟨_, right⟩ := right
    exact ⟨_, .binary left right applied⟩
  | ternary _ _ _ applied first second third =>
    obtain ⟨_, first⟩ := first; obtain ⟨_, second⟩ := second; obtain ⟨_, third⟩ := third
    exact ⟨_, .ternary first second third applied⟩
  | letE _ _ value body =>
    obtain ⟨_, value⟩ := value; obtain ⟨_, body⟩ := body
    exact ⟨_, .letE value body⟩
  | ifTrue _ _ condition branch =>
    obtain ⟨_, condition⟩ := condition; obtain ⟨_, branch⟩ := branch
    exact ⟨_, .ifTrue condition branch⟩
  | ifFalse _ _ condition branch =>
    obtain ⟨_, condition⟩ := condition; obtain ⟨_, branch⟩ := branch
    exact ⟨_, .ifFalse condition branch⟩

theorem evaluation_iff_size
    {environment : Environment} {before after : Store} {expression : Expr} {value : Value} :
    Evaluates environment before expression value after ↔ ∃ size, EvaluationSize size environment before expression value after :=
  ⟨evaluation_has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem EvaluationSize.positive
    {size : Nat} {environment : Environment} {before after : Store} {expression : Expr} {value : Value}
    (evaluation : EvaluationSize size environment before expression value after) : 0 < size := by
  cases evaluation <;> omega

end Solcore.SourceSemantics.CoreLowering.CoreProof
