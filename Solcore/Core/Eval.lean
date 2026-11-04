import Solcore.Core.Syntax
import Solcore.Core.Typing

/-!
# Store and evaluation

`Store.allocate`, `Store.read?` and `Store.write?` are the store operations. `Evaluates` is the
big-step relation, which threads the store explicitly. The machine in `Machine` is proved equal to
it in `Correspondence`.
-/

section
-- leanmerge: from Solcore.Core.Store
set_option autoImplicit false

namespace Solcore.Core

namespace Store

def allocate (store : Store) (value : Value) : Store × Location :=
  (store ++ [value], store.length)

def read? (store : Store) (location : Location) : Option Value :=
  store[location]?

def write?
    (store : Store)
    (location : Location)
    (value : Value) : Option Store :=
  if location < store.length then
    some (store.set location value)
  else
    none

end Store

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.Eval
/-!
The big-step relation threads the local store explicitly. Environments remain
ordinary lexical values: closures capture cell references, not a store snapshot.
-/

set_option autoImplicit false

namespace Solcore.Core

inductive Evaluates : Environment → Store → Expr → Value → Store → Prop where
  | unit {environment : Environment} {store : Store} :
      Evaluates environment store .unit .unit store
  | bool {environment : Environment} {store : Store} {value : Bool} :
      Evaluates environment store (.bool value) (.bool value) store
  | word {environment : Environment} {store : Store} {value : Word} :
      Evaluates environment store (.word value) (.word value) store
  | integer {environment : Environment} {store : Store} {value : Int} :
      Evaluates environment store (.integer value) (.integer value) store
  | pair
      {environment : Environment} {initialStore middleStore finalStore : Store}
      {left right : Expr} {leftValue rightValue : Value} :
      Evaluates environment initialStore left leftValue middleStore →
      Evaluates environment middleStore right rightValue finalStore →
      Evaluates environment initialStore (.pair left right)
        (.pair leftValue rightValue) finalStore
  | first
      {environment : Environment} {initialStore finalStore : Store}
      {operand : Expr} {leftValue rightValue : Value} :
      Evaluates environment initialStore operand
        (.pair leftValue rightValue) finalStore →
      Evaluates environment initialStore (.first operand) leftValue finalStore
  | second
      {environment : Environment} {initialStore finalStore : Store}
      {operand : Expr} {leftValue rightValue : Value} :
      Evaluates environment initialStore operand
        (.pair leftValue rightValue) finalStore →
      Evaluates environment initialStore (.second operand) rightValue finalStore
  | inLeft
      {environment : Environment} {initialStore finalStore : Store}
      {rightType : Ty} {payload : Expr} {payloadValue : Value} :
      Evaluates environment initialStore payload payloadValue finalStore →
      Evaluates environment initialStore (.inLeft rightType payload)
        (.inLeft rightType payloadValue) finalStore
  | inRight
      {environment : Environment} {initialStore finalStore : Store}
      {leftType : Ty} {payload : Expr} {payloadValue : Value} :
      Evaluates environment initialStore payload payloadValue finalStore →
      Evaluates environment initialStore (.inRight leftType payload)
        (.inRight leftType payloadValue) finalStore
  | caseLeft
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {scrutinee leftBranch rightBranch : Expr}
      {rightType : Ty} {payload result : Value} :
      Evaluates environment initialStore scrutinee
        (.inLeft rightType payload) branchStore →
      Evaluates (payload :: environment) branchStore leftBranch result finalStore →
      Evaluates environment initialStore
        (.caseE scrutinee leftBranch rightBranch) result finalStore
  | caseRight
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {scrutinee leftBranch rightBranch : Expr}
      {leftType : Ty} {payload result : Value} :
      Evaluates environment initialStore scrutinee
        (.inRight leftType payload) branchStore →
      Evaluates (payload :: environment) branchStore rightBranch result finalStore →
      Evaluates environment initialStore
        (.caseE scrutinee leftBranch rightBranch) result finalStore
  | lambda
      {environment : Environment} {store : Store}
      {parameterType resultType : Ty} {body : Expr} :
      Evaluates environment store (.lambda parameterType resultType body)
        (.closure parameterType resultType body environment) store
  | apply
      {environment capturedEnvironment : Environment}
      {initialStore argumentStore bodyStore finalStore : Store}
      {function argument body : Expr} {parameterType resultType : Ty}
      {argumentValue result : Value} :
      Evaluates environment initialStore function
        (.closure parameterType resultType body capturedEnvironment)
        argumentStore →
      Evaluates environment argumentStore argument argumentValue bodyStore →
      Evaluates (argumentValue :: capturedEnvironment) bodyStore body result
        finalStore →
      Evaluates environment initialStore (.apply function argument) result finalStore
  | var
      {environment : Environment} {store : Store}
      {index : Nat} {value : Value} :
      environment[index]? = some value →
      Evaluates environment store (.var index) value store
  | newCell
      {environment : Environment} {initialStore initializedStore : Store}
      {elementType : Ty} {initializer : Expr} {initialValue : Value} :
      Evaluates environment initialStore initializer initialValue initializedStore →
      Evaluates environment initialStore (.newCell elementType initializer)
        (.cellRef elementType initializedStore.length)
        (initializedStore ++ [initialValue])
  | loadCell
      {environment : Environment} {initialStore referenceStore : Store}
      {reference : Expr} {elementType : Ty} {location : Location}
      {value : Value} :
      Evaluates environment initialStore reference
        (.cellRef elementType location) referenceStore →
      Store.read? referenceStore location = some value →
      Evaluates environment initialStore (.loadCell reference) value referenceStore
  | storeCell
      {environment : Environment}
      {initialStore referenceStore valueStore finalStore : Store}
      {reference value : Expr} {elementType : Ty} {location : Location}
      {oldValue newValue : Value} :
      Evaluates environment initialStore reference
        (.cellRef elementType location) referenceStore →
      Store.read? referenceStore location = some oldValue →
      Evaluates environment referenceStore value newValue valueStore →
      Store.write? valueStore location newValue = some finalStore →
      Evaluates environment initialStore (.storeCell reference value) .unit finalStore
  | construct
      {environment : Environment} {initialStore finalStore : Store}
      {constructor : ConstructorId} {payload : Expr} {payloadValue : Value} :
      Evaluates environment initialStore payload payloadValue finalStore →
      Evaluates environment initialStore (.construct constructor payload)
        (.constructed constructor payloadValue) finalStore
  | matchData
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {dataType : DataTypeId} {resultType : Ty}
      {scrutinee branch : Expr} {branches : List Expr}
      {constructor : ConstructorId} {payload result : Value} :
      Evaluates environment initialStore scrutinee
        (.constructed constructor payload) branchStore →
      constructor.owner = dataType →
      branches[constructor.index]? = some branch →
      Evaluates (payload :: environment) branchStore branch result finalStore →
      Evaluates environment initialStore
        (.matchData dataType resultType scrutinee branches) result finalStore
  | unary
      {environment : Environment} {initialStore finalStore : Store}
      {op : UnaryOp} {operand : Expr} {operandValue result : Value} :
      Evaluates environment initialStore operand operandValue finalStore →
      op.apply operandValue = some result →
      Evaluates environment initialStore (.unary op operand) result finalStore
  | binary
      {environment : Environment}
      {initialStore rightStore finalStore : Store}
      {op : BinaryOp} {left right : Expr}
      {leftValue rightValue result : Value} :
      Evaluates environment initialStore left leftValue rightStore →
      Evaluates environment rightStore right rightValue finalStore →
      op.apply leftValue rightValue = some result →
      Evaluates environment initialStore (.binary op left right) result finalStore
  | ternary
      {environment : Environment}
      {initialStore secondStore thirdStore finalStore : Store}
      {op : TernaryOp} {first second third : Expr}
      {firstValue secondValue thirdValue result : Value} :
      Evaluates environment initialStore first firstValue secondStore →
      Evaluates environment secondStore second secondValue thirdStore →
      Evaluates environment thirdStore third thirdValue finalStore →
      op.apply firstValue secondValue thirdValue = some result →
      Evaluates environment initialStore (.ternary op first second third)
        result finalStore
  | letE
      {environment : Environment}
      {initialStore bodyStore finalStore : Store}
      {value body : Expr} {boundValue result : Value} :
      Evaluates environment initialStore value boundValue bodyStore →
      Evaluates (boundValue :: environment) bodyStore body result finalStore →
      Evaluates environment initialStore (.letE value body) result finalStore
  | ifTrue
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {condition thenBranch elseBranch : Expr} {result : Value} :
      Evaluates environment initialStore condition (.bool true) branchStore →
      Evaluates environment branchStore thenBranch result finalStore →
      Evaluates environment initialStore
        (.ifE condition thenBranch elseBranch) result finalStore
  | ifFalse
      {environment : Environment}
      {initialStore branchStore finalStore : Store}
      {condition thenBranch elseBranch : Expr} {result : Value} :
      Evaluates environment initialStore condition (.bool false) branchStore →
      Evaluates environment branchStore elseBranch result finalStore →
      Evaluates environment initialStore
        (.ifE condition thenBranch elseBranch) result finalStore

end Solcore.Core
end
