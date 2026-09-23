import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.DirectWordBinary
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.Machine
import Solcore.Core.ExactFuelProperties
import Solcore.Frontend.LocalComputation
import Solcore.Core.Correspondence
import Solcore.Core.LocalFragment
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Frontend.LocalExpressionRenaming
import Solcore.Resolved.Renaming

/-! Recursive calls and groups with unary/Word binary operations, fixed ordered/negated
comparisons, conditionals, fixed lazy expressions and right-associated tuples.
Original children keep their scope; this does not change the older profiles. -/

set_option autoImplicit false

namespace Solcore.Frontend

def elaborateRecursiveLocalComputation? (table : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [argument]⟩⟩ => do
      let (functionCore, functionType) ← elaborateRecursiveLocalComputation? table context callee
      let (argumentCore, argumentType) ← elaborateRecursiveLocalComputation? table context argument
      match functionType with
      | .function parameterType resultType =>
          if argumentType = parameterType then
            some (.apply functionCore argumentCore, resultType)
          else none
      | _ => none
  | ⟨_, .group inner⟩ => elaborateRecursiveLocalComputation? table context inner
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ => do
      let (leftCore, leftType) ← elaborateRecursiveLocalComputation? table context left
      let (rightCore, rightType) ← elaborateRecursiveLocalComputation? table context right
      return (.pair leftCore rightCore, .product leftType rightType)
  | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ => do
      let (headCore, headType) ← elaborateRecursiveLocalComputation? table context first
      let (tailCore, tailType) ← elaborateRecursiveLocalComputation? table context
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩
      return (.pair headCore tailCore, .product headType tailType)
  | ⟨_, .unary ⟨_, .logicalNot⟩ operand⟩ => do
      let (operandCore, operandType) ← elaborateRecursiveLocalComputation? table context operand
      if operandType = .bool then some (.unary .boolNot operandCore, .bool) else none
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ => do
      let (operandCore, operandType) ← elaborateRecursiveLocalComputation? table context operand
      if operandType = .word then some (.unary .wordNot operandCore, .word) else none
  | ⟨_, .conditional condition _ thenBranch _ elseBranch⟩ => do
      let (conditionCore, conditionType) ← elaborateRecursiveLocalComputation? table context condition
      let (thenCore, thenType) ← elaborateRecursiveLocalComputation? table context thenBranch
      let (elseCore, elseType) ← elaborateRecursiveLocalComputation? table context elseBranch
      if conditionType = .bool ∧ elseType = thenType then
        some (.ifE conditionCore thenCore elseCore, thenType)
      else none
  | ⟨_, .binary left ⟨_, .logicalAnd⟩ right⟩ => do
      let (leftCore, leftType) ← elaborateRecursiveLocalComputation? table context left
      let (rightCore, rightType) ← elaborateRecursiveLocalComputation? table context right
      if leftType = .bool ∧ rightType = .bool then
        some (.ifE leftCore rightCore (.bool false), .bool)
      else none
  | ⟨_, .binary left ⟨_, .logicalOr⟩ right⟩ => do
      let (leftCore, leftType) ← elaborateRecursiveLocalComputation? table context left
      let (rightCore, rightType) ← elaborateRecursiveLocalComputation? table context right
      if leftType = .bool ∧ rightType = .bool then
        some (.ifE leftCore (.bool true) rightCore, .bool)
      else none
  | ⟨_, .binary left ⟨_, .notEqual⟩ right⟩ => do
      let (leftCore, leftType) ← elaborateRecursiveLocalComputation? table context left
      let (rightCore, rightType) ← elaborateRecursiveLocalComputation? table context right
      if leftType = .word ∧ rightType = .word then
        some (.unary .boolNot (.binary .wordEq leftCore rightCore), .bool)
      else none
  | ⟨_, .binary left ⟨_, .lessEqual⟩ right⟩ => do
      let (leftCore, leftType) ← elaborateRecursiveLocalComputation? table context left
      let (rightCore, rightType) ← elaborateRecursiveLocalComputation? table context right
      if leftType = .word ∧ rightType = .word then
        some (.unary .boolNot (.binary .wordGt leftCore rightCore), .bool)
      else none
  | ⟨_, .binary left ⟨_, .less⟩ right⟩ => do
      let (leftCore, leftType) ← elaborateRecursiveLocalComputation? table context left
      let (rightCore, rightType) ← elaborateRecursiveLocalComputation? table context right
      if leftType = .word ∧ rightType = .word then
        some (leftCore.wordLt rightCore, .bool)
      else none
  | ⟨_, .binary left ⟨_, .greaterEqual⟩ right⟩ => do
      let (leftCore, leftType) ← elaborateRecursiveLocalComputation? table context left
      let (rightCore, rightType) ← elaborateRecursiveLocalComputation? table context right
      if leftType = .word ∧ rightType = .word then
        some (.unary .boolNot (leftCore.wordLt rightCore), .bool)
      else none
  | ⟨_, .binary left ⟨_, sourceOp⟩ right⟩ =>
      match directWordBinary? sourceOp with
      | some op => do
          let (leftCore, leftType) ← elaborateRecursiveLocalComputation? table context left
          let (rightCore, rightType) ← elaborateRecursiveLocalComputation? table context right
          if leftType = op.leftType ∧ rightType = op.rightType then
            some (.binary op leftCore rightCore, op.resultType)
          else none
      | none => elaborateLocalExpression? table context source
  | _ => elaborateLocalExpression? table context source
termination_by sizeOf source

inductive RecursiveLocalComputationHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Ty → Prop where
  | pure {source : Syntax.Expr} {type : Core.Ty}
      (child : LocalExpressionHasType table context source type) :
      RecursiveLocalComputationHasType table context source type
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr} {type : Core.Ty}
      (child : RecursiveLocalComputationHasType table context inner type) :
      RecursiveLocalComputationHasType table context ⟨span, .group inner⟩ type
  | application {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {parameterType resultType : Core.Ty}
      (functionTyped : RecursiveLocalComputationHasType table context callee (.function parameterType resultType))
      (argumentTyped : RecursiveLocalComputationHasType table context argument parameterType) :
      RecursiveLocalComputationHasType table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ resultType

  | pair {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftType rightType : Core.Ty}
      (leftTyped : RecursiveLocalComputationHasType table context left leftType)
      (rightTyped : RecursiveLocalComputationHasType table context right rightType) :
      RecursiveLocalComputationHasType table context
        ⟨span, .tuple ⟨tupleSpan, [left, right]⟩⟩ (.product leftType rightType)
  | many {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr} {headType tailType : Core.Ty}
      (headTyped : RecursiveLocalComputationHasType table context first headType)
      (tailTyped : RecursiveLocalComputationHasType table context
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ tailType) :
      RecursiveLocalComputationHasType table context
        ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ (.product headType tailType)

  | binary {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
      (operator : DirectWordBinary sourceOp op)
      (leftTyped : RecursiveLocalComputationHasType table context left op.leftType)
      (rightTyped : RecursiveLocalComputationHasType table context right op.rightType) :
      RecursiveLocalComputationHasType table context
        ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ op.resultType

  | conditional {span question colon : Syntax.SourceSpan}
      {condition thenBranch elseBranch : Syntax.Expr} {type : Core.Ty}
      (conditionTyped : RecursiveLocalComputationHasType table context condition .bool)
      (thenTyped : RecursiveLocalComputationHasType table context thenBranch type)
      (elseTyped : RecursiveLocalComputationHasType table context elseBranch type) :
      RecursiveLocalComputationHasType table context
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ type

  | logicalNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (child : RecursiveLocalComputationHasType table context operand .bool) :
      RecursiveLocalComputationHasType table context
        ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ .bool
  | bitNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (child : RecursiveLocalComputationHasType table context operand .word) :
      RecursiveLocalComputationHasType table context
        ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ .word

  | logicalAnd {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : RecursiveLocalComputationHasType table context left .bool)
      (rightTyped : RecursiveLocalComputationHasType table context right .bool) :
      RecursiveLocalComputationHasType table context
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ .bool
  | logicalOr {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : RecursiveLocalComputationHasType table context left .bool)
      (rightTyped : RecursiveLocalComputationHasType table context right .bool) :
      RecursiveLocalComputationHasType table context
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ .bool

  | notEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : RecursiveLocalComputationHasType table context left .word)
      (rightTyped : RecursiveLocalComputationHasType table context right .word) :
      RecursiveLocalComputationHasType table context
        ⟨span, .binary left ⟨operatorSpan, .notEqual⟩ right⟩ .bool
  | lessEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : RecursiveLocalComputationHasType table context left .word)
      (rightTyped : RecursiveLocalComputationHasType table context right .word) :
      RecursiveLocalComputationHasType table context
        ⟨span, .binary left ⟨operatorSpan, .lessEqual⟩ right⟩ .bool

  | less {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : RecursiveLocalComputationHasType table context left .word)
      (rightTyped : RecursiveLocalComputationHasType table context right .word) :
      RecursiveLocalComputationHasType table context
        ⟨span, .binary left ⟨operatorSpan, .less⟩ right⟩ .bool
  | greaterEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : RecursiveLocalComputationHasType table context left .word)
      (rightTyped : RecursiveLocalComputationHasType table context right .word) :
      RecursiveLocalComputationHasType table context
        ⟨span, .binary left ⟨operatorSpan, .greaterEqual⟩ right⟩ .bool

inductive RecursiveLocalComputationElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | pure {source : Syntax.Expr} {resolved : Resolved.Expr} {core : Core.Expr} {type : Core.Ty}
      (resolution : ResolvesLocalExpression table source resolved)
      (lowered : Resolved.Lowers context.ids resolved core)
      (typing : Resolved.HasType context resolved type) :
      RecursiveLocalComputationElaborates table context source core type
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (child : RecursiveLocalComputationElaborates table context inner core type) :
      RecursiveLocalComputationElaborates table context ⟨span, .group inner⟩ core type
  | application {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {functionCore argumentCore : Core.Expr} {parameterType resultType : Core.Ty}
      (functionElaborated : RecursiveLocalComputationElaborates table context
        callee functionCore (.function parameterType resultType))
      (argumentElaborated : RecursiveLocalComputationElaborates table context argument argumentCore parameterType) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ (.apply functionCore argumentCore) resultType

  | pair {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
      (leftElaborated : RecursiveLocalComputationElaborates table context left leftCore leftType)
      (rightElaborated : RecursiveLocalComputationElaborates table context right rightCore rightType) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .tuple ⟨tupleSpan, [left, right]⟩⟩ (.pair leftCore rightCore) (.product leftType rightType)
  | many {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr} {headCore tailCore : Core.Expr} {headType tailType : Core.Ty}
      (headElaborated : RecursiveLocalComputationElaborates table context first headCore headType)
      (tailElaborated : RecursiveLocalComputationElaborates table context
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ tailCore tailType) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩
        (.pair headCore tailCore) (.product headType tailType)

  | binary {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} {leftCore rightCore : Core.Expr}
      (operator : DirectWordBinary sourceOp op)
      (leftElaborated : RecursiveLocalComputationElaborates table context left leftCore op.leftType)
      (rightElaborated : RecursiveLocalComputationElaborates table context right rightCore op.rightType) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ (.binary op leftCore rightCore) op.resultType

  | conditional {span question colon : Syntax.SourceSpan}
      {condition thenBranch elseBranch : Syntax.Expr}
      {conditionCore thenCore elseCore : Core.Expr} {type : Core.Ty}
      (conditionElaborated : RecursiveLocalComputationElaborates table context condition conditionCore .bool)
      (thenElaborated : RecursiveLocalComputationElaborates table context thenBranch thenCore type)
      (elseElaborated : RecursiveLocalComputationElaborates table context elseBranch elseCore type) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ (.ifE conditionCore thenCore elseCore) type

  | logicalNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr} {core : Core.Expr}
      (child : RecursiveLocalComputationElaborates table context operand core .bool) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ (.unary .boolNot core) .bool
  | bitNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr} {core : Core.Expr}
      (child : RecursiveLocalComputationElaborates table context operand core .word) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ (.unary .wordNot core) .word

  | logicalAnd {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftCore rightCore : Core.Expr}
      (leftElaborated : RecursiveLocalComputationElaborates table context left leftCore .bool)
      (rightElaborated : RecursiveLocalComputationElaborates table context right rightCore .bool) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ (.ifE leftCore rightCore (.bool false)) .bool
  | logicalOr {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftCore rightCore : Core.Expr}
      (leftElaborated : RecursiveLocalComputationElaborates table context left leftCore .bool)
      (rightElaborated : RecursiveLocalComputationElaborates table context right rightCore .bool) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ (.ifE leftCore (.bool true) rightCore) .bool

  | notEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftCore rightCore : Core.Expr}
      (leftElaborated : RecursiveLocalComputationElaborates table context left leftCore .word)
      (rightElaborated : RecursiveLocalComputationElaborates table context right rightCore .word) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .binary left ⟨operatorSpan, .notEqual⟩ right⟩
        (.unary .boolNot (.binary .wordEq leftCore rightCore)) .bool
  | lessEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftCore rightCore : Core.Expr}
      (leftElaborated : RecursiveLocalComputationElaborates table context left leftCore .word)
      (rightElaborated : RecursiveLocalComputationElaborates table context right rightCore .word) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .binary left ⟨operatorSpan, .lessEqual⟩ right⟩
        (.unary .boolNot (.binary .wordGt leftCore rightCore)) .bool

  | less {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftCore rightCore : Core.Expr}
      (leftElaborated : RecursiveLocalComputationElaborates table context left leftCore .word)
      (rightElaborated : RecursiveLocalComputationElaborates table context right rightCore .word) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .binary left ⟨operatorSpan, .less⟩ right⟩
        (leftCore.wordLt rightCore) .bool
  | greaterEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftCore rightCore : Core.Expr}
      (leftElaborated : RecursiveLocalComputationElaborates table context left leftCore .word)
      (rightElaborated : RecursiveLocalComputationElaborates table context right rightCore .word) :
      RecursiveLocalComputationElaborates table context
        ⟨span, .binary left ⟨operatorSpan, .greaterEqual⟩ right⟩
        (.unary .boolNot (leftCore.wordLt rightCore)) .bool

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationCost`
-/

/-! Independent exact costs retain original source children, actual closure paths
and stores. Ordered comparisons include both generated positional bindings.
Each ordered tuple pair adds three transitions, without a terminal Unit. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive RecursiveLocalComputationEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop where
  | pure {initialStore finalStore : Core.Store} {source : Syntax.Expr}
      {value : Core.Value} {cost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : RecursiveLocalComputationEvaluatesWithCost table environment initialStore inner value finalStore cost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .group inner⟩ value finalStore cost
  | application {initialStore argumentStore bodyStore finalStore : Core.Store}
      {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {parameterType resultType : Core.Ty} {body : Core.Expr}
      {captured : Core.Environment} {argumentValue result : Core.Value}
      {functionCost argumentCost bodyCost : Nat}
      (functionEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        callee (.closure parameterType resultType body captured) argumentStore functionCost)
      (argumentEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment argumentStore
        argument argumentValue bodyStore argumentCost)
      (bodyPath : Core.Steps bodyCost
        (Core.State.initial body (argumentValue :: captured) bodyStore)
        (Core.State.final result finalStore)) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore
        (functionCost + argumentCost + bodyCost + 3)

  | pair {initialStore middleStore finalStore : Core.Store}
      {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Value} {leftCost rightCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left leftValue middleStore leftCost)
      (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore right rightValue finalStore rightCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .tuple ⟨tupleSpan, [left, right]⟩⟩ (.pair leftValue rightValue) finalStore
        (leftCost + rightCost + 3)
  | many {initialStore middleStore finalStore : Core.Store}
      {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr} {headValue tailValue : Core.Value} {headCost tailCost : Nat}
      (headEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore first headValue middleStore headCost)
      (tailEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment middleStore
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ tailValue finalStore tailCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩
        (.pair headValue tailValue) finalStore (headCost + tailCost + 3)

  | binary {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} {leftValue rightValue result : Core.Value}
      {leftCost rightCost : Nat}
      (operator : DirectWordBinary sourceOp op)
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left leftValue middleStore leftCost)
      (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore right rightValue finalStore rightCost)
      (applied : op.apply leftValue rightValue = some result) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ result finalStore (leftCost + rightCost + 3)

  | ifTrue {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore condition (.bool true) middleStore conditionCost)
      (branchEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore thenBranch value finalStore branchCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore
        (conditionCost + branchCost + 2)
  | ifFalse {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore condition (.bool false) middleStore conditionCost)
      (branchEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore elseBranch value finalStore branchCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore
        (conditionCost + branchCost + 2)

  | logicalNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Bool} {childCost : Nat}
      (child : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore operand (.bool value) finalStore childCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ (.bool (!value)) finalStore (childCost + 2)
  | bitNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Core.Word} {childCost : Nat}
      (child : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore operand (.word value) finalStore childCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ (.word value.bitNot) finalStore (childCost + 2)

  | andTrue {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      {leftCost rightCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left (.bool true) middleStore leftCost)
      (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore right value finalStore rightCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ value finalStore (leftCost + rightCost + 2)
  | andFalse {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left (.bool false) finalStore leftCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ (.bool false) finalStore (leftCost + 3)
  | orTrue {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left (.bool true) finalStore leftCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ (.bool true) finalStore (leftCost + 3)
  | orFalse {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      {leftCost rightCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left (.bool false) middleStore leftCost)
      (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore right value finalStore rightCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ value finalStore (leftCost + rightCost + 2)

  | notEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .notEqual⟩ right⟩
        (.bool (!(leftValue == rightValue))) finalStore (leftCost + rightCost + 5)
  | lessEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .lessEqual⟩ right⟩
        (.bool (!(decide (leftValue > rightValue)))) finalStore (leftCost + rightCost + 5)

  | less {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .less⟩ right⟩
        (.bool (decide (leftValue < rightValue))) finalStore (leftCost + rightCost + 9)
  | greaterEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word} {leftCost rightCost : Nat}
      (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore left (.word leftValue) middleStore leftCost)
      (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
        middleStore right (.word rightValue) finalStore rightCost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .greaterEqual⟩ right⟩
        (.bool (!(decide (leftValue < rightValue)))) finalStore (leftCost + rightCost + 11)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationEvaluation`
-/

/-! Original calls retain actual bodies and captures. Strict binary children
thread their real stores left to right before applying the actual operator.
Conditionals evaluate the actual Bool guard and selected branch only.
Fixed lazy operators require an actual Bool left child; a selected right child
retains its actual value, while skipping evaluates one internal Bool literal.
Unary operations use the actual child payload and preserve its final store.
Fixed negated comparisons evaluate both actual Words before comparison and negation.
Ordered comparisons retain both original Words before swapping their saved positions.
Tuples retain arbitrary actual components in original order, with right-associated tails.
Grouping preserves the exact value, stores and cost of its child. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive RecursiveLocalComputationEvaluates
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop where
  | pure {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
      (child : LocalExpressionEvaluates table environment initialStore source value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore source value finalStore
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : RecursiveLocalComputationEvaluates table environment initialStore inner value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore ⟨span, .group inner⟩ value finalStore
  | application {initialStore argumentStore bodyStore finalStore : Core.Store}
      {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {parameterType resultType : Core.Ty} {body : Core.Expr}
      {captured : Core.Environment} {argumentValue result : Core.Value}
      (functionEvaluation : RecursiveLocalComputationEvaluates table environment initialStore
        callee (.closure parameterType resultType body captured) argumentStore)
      (argumentEvaluation : RecursiveLocalComputationEvaluates table environment argumentStore
        argument argumentValue bodyStore)
      (bodyEvaluation : Core.Evaluates (argumentValue :: captured) bodyStore body result finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore

  | pair {initialStore middleStore finalStore : Core.Store}
      {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Value}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left leftValue middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right rightValue finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .tuple ⟨tupleSpan, [left, right]⟩⟩ (.pair leftValue rightValue) finalStore
  | many {initialStore middleStore finalStore : Core.Store}
      {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr} {headValue tailValue : Core.Value}
      (headEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore first headValue middleStore)
      (tailEvaluation : RecursiveLocalComputationEvaluates table environment middleStore
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ tailValue finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩
        (.pair headValue tailValue) finalStore

  | binary {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} {leftValue rightValue result : Core.Value}
      (operator : DirectWordBinary sourceOp op)
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left leftValue middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right rightValue finalStore)
      (applied : op.apply leftValue rightValue = some result) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ result finalStore

  | ifTrue {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value}
      (conditionEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore condition (.bool true) middleStore)
      (branchEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore thenBranch value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore
  | ifFalse {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value}
      (conditionEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore condition (.bool false) middleStore)
      (branchEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore elseBranch value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore

  | logicalNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Bool}
      (child : RecursiveLocalComputationEvaluates table environment
        initialStore operand (.bool value) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ (.bool (!value)) finalStore
  | bitNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Core.Word}
      (child : RecursiveLocalComputationEvaluates table environment
        initialStore operand (.word value) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ (.word value.bitNot) finalStore

  | andTrue {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.bool true) middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ value finalStore
  | andFalse {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.bool false) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ (.bool false) finalStore
  | orTrue {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.bool true) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ (.bool true) finalStore
  | orFalse {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.bool false) middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ value finalStore

  | notEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.word leftValue) middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right (.word rightValue) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .notEqual⟩ right⟩
        (.bool (!(leftValue == rightValue))) finalStore
  | lessEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.word leftValue) middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right (.word rightValue) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .lessEqual⟩ right⟩
        (.bool (!(decide (leftValue > rightValue)))) finalStore

  | less {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.word leftValue) middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right (.word rightValue) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .less⟩ right⟩
        (.bool (decide (leftValue < rightValue))) finalStore
  | greaterEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : RecursiveLocalComputationEvaluates table environment
        initialStore left (.word leftValue) middleStore)
      (rightEvaluation : RecursiveLocalComputationEvaluates table environment
        middleStore right (.word rightValue) finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .binary left ⟨operatorSpan, .greaterEqual⟩ right⟩
        (.bool (!(decide (leftValue < rightValue)))) finalStore

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationDeterminismProperties`
-/

/-! Actual values, final stores and costs are jointly determined at every
original root, including pure overlap and skipped unsupported syntax. -/

set_option autoImplicit false

namespace Solcore.Frontend

-- The old pure relation has no root call, but may skip unsupported descendants.
-- Invert only the overlapping root; no global call-free premise is introduced.
private theorem agrees_with_pure {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {source : Syntax.Expr} {left right : Core.Value}
    {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (pureEvaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction evaluation generalizing right rightStore rightCost with
  | pure child => exact child.deterministic pureEvaluation
  | group _ ih =>
      cases pureEvaluation with
      | group child => exact ih child
  | application => cases pureEvaluation
  | pair _ _ leftIH rightIH | many _ _ leftIH rightIH =>
      cases pureEvaluation
      all_goals
        rename_i pureLeft pureRight
        obtain ⟨rfl, rfl, rfl⟩ := leftIH pureLeft
        obtain ⟨rfl, rfl, rfl⟩ := rightIH pureRight
        exact ⟨rfl, rfl, rfl⟩
  | binary operator _ _ applied leftIH rightIH =>
      cases operator <;> cases pureEvaluation
      all_goals
        rename_i pureLeft pureRight
        obtain ⟨rfl, rfl, rfl⟩ := leftIH pureLeft
        obtain ⟨rfl, rfl, rfl⟩ := rightIH pureRight
        cases applied
        exact ⟨rfl, rfl, rfl⟩
  | ifTrue _ _ conditionIH branchIH =>
      cases pureEvaluation with
      | ifTrue condition branch =>
          obtain ⟨_, rfl, rfl⟩ := conditionIH condition
          obtain ⟨rfl, rfl, rfl⟩ := branchIH branch
          exact ⟨rfl, rfl, rfl⟩
      | ifFalse condition _ => cases (conditionIH condition).1
  | ifFalse _ _ conditionIH branchIH =>
      cases pureEvaluation with
      | ifTrue condition _ => cases (conditionIH condition).1
      | ifFalse condition branch =>
          obtain ⟨_, rfl, rfl⟩ := conditionIH condition
          obtain ⟨rfl, rfl, rfl⟩ := branchIH branch
          exact ⟨rfl, rfl, rfl⟩

  | logicalNot _ ih =>
      cases pureEvaluation with
      | logicalNot child =>
          obtain ⟨sameValue, rfl, rfl⟩ := ih child
          cases sameValue
          exact ⟨rfl, rfl, rfl⟩
  | bitNot _ ih =>
      cases pureEvaluation with
      | bitNot child =>
          obtain ⟨sameValue, rfl, rfl⟩ := ih child
          cases sameValue
          exact ⟨rfl, rfl, rfl⟩
  | andTrue _ _ leftIH rightIH =>
      cases pureEvaluation with
      | andTrue left right =>
          obtain ⟨_, rfl, rfl⟩ := leftIH left
          obtain ⟨rfl, rfl, rfl⟩ := rightIH right
          exact ⟨rfl, rfl, rfl⟩
      | andFalse left => cases (leftIH left).1
  | andFalse _ ih =>
      cases pureEvaluation with
      | andTrue left _ => cases (ih left).1
      | andFalse left => obtain ⟨_, rfl, rfl⟩ := ih left; exact ⟨rfl, rfl, rfl⟩
  | orTrue _ ih =>
      cases pureEvaluation with
      | orTrue left => obtain ⟨_, rfl, rfl⟩ := ih left; exact ⟨rfl, rfl, rfl⟩
      | orFalse left _ => cases (ih left).1
  | orFalse _ _ leftIH rightIH =>
      cases pureEvaluation with
      | orTrue left => cases (leftIH left).1
      | orFalse left right =>
          obtain ⟨_, rfl, rfl⟩ := leftIH left
          obtain ⟨rfl, rfl, rfl⟩ := rightIH right
          exact ⟨rfl, rfl, rfl⟩

  | notEqual _ _ leftIH rightIH =>
      cases pureEvaluation with
      | notEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          cases sameLeft
          obtain ⟨sameRight, rfl, rfl⟩ := rightIH rightChild
          cases sameRight
          exact ⟨rfl, rfl, rfl⟩
  | lessEqual _ _ leftIH rightIH =>
      cases pureEvaluation with
      | lessEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          cases sameLeft
          obtain ⟨sameRight, rfl, rfl⟩ := rightIH rightChild
          cases sameRight
          exact ⟨rfl, rfl, rfl⟩

  | less _ _ leftIH rightIH =>
      cases pureEvaluation with
      | less leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          cases sameLeft
          obtain ⟨sameRight, rfl, rfl⟩ := rightIH rightChild
          cases sameRight
          exact ⟨rfl, rfl, rfl⟩
  | greaterEqual _ _ leftIH rightIH =>
      cases pureEvaluation with
      | greaterEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH leftChild
          cases sameLeft
          obtain ⟨sameRight, rfl, rfl⟩ := rightIH rightChild
          cases sameRight
          exact ⟨rfl, rfl, rfl⟩

/-- Successful recursive derivations determine the actual value, final store
and cost jointly, including overlapping pure derivations and selected branches. -/
theorem RecursiveLocalComputationEvaluatesWithCost.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (leftEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (rightEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction leftEvaluation generalizing right rightStore rightCost with
  | pure child =>
      obtain ⟨valueEq, storeEq, costEq⟩ := agrees_with_pure rightEvaluation child
      exact ⟨valueEq.symm, storeEq.symm, costEq.symm⟩
  | group child ih =>
      cases rightEvaluation with
      | pure other =>
          cases other with
          | group pureChild => exact agrees_with_pure child pureChild
      | group other => exact ih other
  | application _ _ bodyPath functionIH argumentIH =>
      cases rightEvaluation with
      | pure other => cases other
      | application otherFunction otherArgument otherPath =>
          obtain ⟨sameFunction, rfl, rfl⟩ := functionIH otherFunction
          cases sameFunction
          obtain ⟨rfl, rfl, rfl⟩ := argumentIH otherArgument
          obtain ⟨rfl, sameValue, sameStore⟩ := bodyPath.final_unique otherPath
          exact ⟨sameValue, sameStore, rfl⟩
  | pair leftChild rightChild leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.pair leftChild rightChild) other
      | pair otherLeft otherRight =>
          obtain ⟨rfl, rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, rfl, rfl⟩ := rightIH otherRight
          exact ⟨rfl, rfl, rfl⟩
  | many headChild tailChild headIH tailIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.many headChild tailChild) other
      | many otherHead otherTail =>
          obtain ⟨rfl, rfl, rfl⟩ := headIH otherHead
          obtain ⟨rfl, rfl, rfl⟩ := tailIH otherTail
          exact ⟨rfl, rfl, rfl⟩
  | binary operator leftChild rightChild applied leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.binary operator leftChild rightChild applied) other
      | binary otherOperator otherLeft otherRight otherApplied =>
          obtain ⟨rfl, rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, rfl, rfl⟩ := rightIH otherRight
          cases operator <;> cases otherOperator
          all_goals exact ⟨Option.some.inj (applied.symm.trans otherApplied), rfl, rfl⟩
      | andTrue _ _ | andFalse _ | orTrue _ | orFalse _ _ | notEqual _ _ | lessEqual _ _ | less _ _ | greaterEqual _ _ => cases operator
  | ifTrue condition branch conditionIH branchIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.ifTrue condition branch) other
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := conditionIH otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := branchIH otherBranch
          exact ⟨rfl, rfl, rfl⟩
      | ifFalse otherCondition _ => cases (conditionIH otherCondition).1
  | ifFalse condition branch conditionIH branchIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.ifFalse condition branch) other
      | ifTrue otherCondition _ => cases (conditionIH otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := conditionIH otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := branchIH otherBranch
          exact ⟨rfl, rfl, rfl⟩

  | logicalNot child ih =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.logicalNot child) other
      | logicalNot other =>
          obtain ⟨sameValue, rfl, rfl⟩ := ih other
          cases sameValue
          exact ⟨rfl, rfl, rfl⟩
  | bitNot child ih =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.bitNot child) other
      | bitNot other =>
          obtain ⟨sameValue, rfl, rfl⟩ := ih other
          cases sameValue
          exact ⟨rfl, rfl, rfl⟩
  | andTrue leftChild rightChild leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.andTrue leftChild rightChild) other
      | binary operator _ _ _ => cases operator
      | andTrue otherLeft otherRight =>
          obtain ⟨_, rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, rfl, rfl⟩ := rightIH otherRight
          exact ⟨rfl, rfl, rfl⟩
      | andFalse otherLeft => cases (leftIH otherLeft).1
  | andFalse left ih =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.andFalse left) other
      | binary operator _ _ _ => cases operator
      | andTrue otherLeft _ => cases (ih otherLeft).1
      | andFalse otherLeft => obtain ⟨_, rfl, rfl⟩ := ih otherLeft; exact ⟨rfl, rfl, rfl⟩
  | orTrue left ih =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.orTrue left) other
      | binary operator _ _ _ => cases operator
      | orTrue otherLeft => obtain ⟨_, rfl, rfl⟩ := ih otherLeft; exact ⟨rfl, rfl, rfl⟩
      | orFalse otherLeft _ => cases (ih otherLeft).1
  | orFalse leftChild rightChild leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.orFalse leftChild rightChild) other
      | binary operator _ _ _ => cases operator
      | orTrue otherLeft => cases (leftIH otherLeft).1
      | orFalse otherLeft otherRight =>
          obtain ⟨_, rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, rfl, rfl⟩ := rightIH otherRight
          exact ⟨rfl, rfl, rfl⟩

  | notEqual leftChild rightChild leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.notEqual leftChild rightChild) other
      | binary operator _ _ _ => cases operator
      | notEqual otherLeft otherRight =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH otherLeft
          cases sameLeft
          obtain ⟨sameRight, rfl, rfl⟩ := rightIH otherRight
          cases sameRight
          exact ⟨rfl, rfl, rfl⟩
  | lessEqual leftChild rightChild leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.lessEqual leftChild rightChild) other
      | binary operator _ _ _ => cases operator
      | lessEqual otherLeft otherRight =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH otherLeft
          cases sameLeft
          obtain ⟨sameRight, rfl, rfl⟩ := rightIH otherRight
          cases sameRight
          exact ⟨rfl, rfl, rfl⟩

  | less leftChild rightChild leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.less leftChild rightChild) other
      | binary operator _ _ _ => cases operator
      | less otherLeft otherRight =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH otherLeft
          cases sameLeft
          obtain ⟨sameRight, rfl, rfl⟩ := rightIH otherRight
          cases sameRight
          exact ⟨rfl, rfl, rfl⟩
  | greaterEqual leftChild rightChild leftIH rightIH =>
      cases rightEvaluation with
      | pure other => exact agrees_with_pure (.greaterEqual leftChild rightChild) other
      | binary operator _ _ _ => cases operator
      | greaterEqual otherLeft otherRight =>
          obtain ⟨sameLeft, rfl, rfl⟩ := leftIH otherLeft
          cases sameLeft
          obtain ⟨sameRight, rfl, rfl⟩ := rightIH otherRight
          cases sameRight
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties`
-/

/-! Old successes embed on the same original syntax and actual values, stores
and costs. No old endpoint or stronger pure runtime contract is changed. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationElaborates.toRecursiveLocalComputation
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type) :
    RecursiveLocalComputationElaborates table context source core type := by
  cases elaboration with
  | pure resolution lowered typing => exact .pure resolution lowered typing
  | application child =>
      cases child with
      | call functionResolution functionLowered functionTyped argumentResolution argumentLowered argumentTyped =>
          exact .application (.pure functionResolution functionLowered functionTyped)
            (.pure argumentResolution argumentLowered argumentTyped)

theorem LocalComputationEvaluatesWithCost.toRecursiveLocalComputation
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost) :
    RecursiveLocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost := by
  cases evaluation with
  | pure child => exact .pure child
  | application child =>
      cases child with
      | call functionEvaluation argumentEvaluation bodyPath =>
          exact .application (.pure functionEvaluation) (.pure argumentEvaluation) bodyPath

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationEvaluationProperties`
-/

/-! Raw success and exact cost agree across overlapping pure and recursive
groups, tuples, direct/ordered/negated comparisons, conditionals and fixed lazy operators.
Actual closures, arguments and stores are fixed by evaluation,
not by a checker, type tags or a global restriction on skipped source syntax. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem erase {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment
      initialStore source value finalStore cost) :
    RecursiveLocalComputationEvaluates table environment initialStore source value finalStore := by
  induction evaluation with
  | pure child => exact .pure child.erase
  | group _ ih => exact .group ih
  | application _ _ bodyPath functionIH argumentIH =>
      exact .application functionIH argumentIH (Core.steps_from_initial_sound bodyPath)
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | many _ _ headIH tailIH => exact .many headIH tailIH
  | binary operator _ _ applied leftIH rightIH =>
      exact .binary operator leftIH rightIH applied
  | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
  | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH
  | logicalNot _ ih => exact .logicalNot ih
  | bitNot _ ih => exact .bitNot ih
  | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
  | andFalse _ ih => exact .andFalse ih
  | orTrue _ ih => exact .orTrue ih
  | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
  | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
  | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
  | less _ _ leftIH rightIH => exact .less leftIH rightIH
  | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH

private theorem exists_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
    (evaluation : RecursiveLocalComputationEvaluates table environment
      initialStore source value finalStore) :
    ∃ cost, RecursiveLocalComputationEvaluatesWithCost table environment
      initialStore source value finalStore cost := by
  induction evaluation with
  | pure child =>
      obtain ⟨_, costed⟩ := child.exists_cost
      exact ⟨_, .pure costed⟩
  | group _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .group costed⟩
  | application _ _ bodyEvaluation functionIH argumentIH =>
      obtain ⟨_, functionCosted⟩ := functionIH
      obtain ⟨_, argumentCosted⟩ := argumentIH
      obtain ⟨_, bodyPath⟩ := bodyEvaluation.toSteps
      exact ⟨_, .application functionCosted argumentCosted bodyPath⟩
  | pair _ _ leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .pair leftCosted rightCosted⟩
  | many _ _ headIH tailIH =>
      obtain ⟨_, headCosted⟩ := headIH
      obtain ⟨_, tailCosted⟩ := tailIH
      exact ⟨_, .many headCosted tailCosted⟩
  | binary operator _ _ applied leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .binary operator leftCosted rightCosted applied⟩
  | ifTrue _ _ conditionIH branchIH =>
      obtain ⟨_, conditionCosted⟩ := conditionIH
      obtain ⟨_, branchCosted⟩ := branchIH
      exact ⟨_, .ifTrue conditionCosted branchCosted⟩
  | ifFalse _ _ conditionIH branchIH =>
      obtain ⟨_, conditionCosted⟩ := conditionIH
      obtain ⟨_, branchCosted⟩ := branchIH
      exact ⟨_, .ifFalse conditionCosted branchCosted⟩
  | logicalNot _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .logicalNot costed⟩
  | bitNot _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .bitNot costed⟩
  | andTrue _ _ leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .andTrue leftCosted rightCosted⟩
  | andFalse _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .andFalse costed⟩
  | orTrue _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .orTrue costed⟩
  | orFalse _ _ leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .orFalse leftCosted rightCosted⟩

  | notEqual _ _ leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .notEqual leftCosted rightCosted⟩
  | lessEqual _ _ leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .lessEqual leftCosted rightCosted⟩
  | less _ _ leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .less leftCosted rightCosted⟩
  | greaterEqual _ _ leftIH rightIH =>
      obtain ⟨_, leftCosted⟩ := leftIH
      obtain ⟨_, rightCosted⟩ := rightIH
      exact ⟨_, .greaterEqual leftCosted rightCosted⟩

theorem recursiveLocalComputationEvaluates_iff_exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} :
    RecursiveLocalComputationEvaluates table environment initialStore source value finalStore ↔
      ∃ cost, RecursiveLocalComputationEvaluatesWithCost table environment
        initialStore source value finalStore cost :=
  ⟨exists_cost, fun ⟨_, evaluation⟩ => erase evaluation⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationEvaluationRenamingProperties`
-/

/-! Raw identity relabeling keeps actual values, captured Core paths and all
stores/costs fixed. No checking, typing, scope alignment or runtime world is
required; neither successful evaluation nor its absence classifies faults. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem recursiveLocalComputationEvaluatesWithCost_mapIds_iff
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping environment) initialStore source value finalStore cost ↔
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost := by
  constructor
  · intro evaluation
    induction evaluation with
    | pure child => exact .pure ((localExpressionEvaluatesWithCost_mapIds_iff mapping injective).mp child)
    | group _ ih => exact .group ih
    | application _ _ bodyPath functionIH argumentIH => exact .application functionIH argumentIH bodyPath
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | binary operator _ _ applied leftIH rightIH => exact .binary operator leftIH rightIH applied
    | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
    | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
    | andFalse _ ih => exact .andFalse ih
    | orTrue _ ih => exact .orTrue ih
    | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
  · intro evaluation
    induction evaluation with
    | pure child => exact .pure ((localExpressionEvaluatesWithCost_mapIds_iff mapping injective).mpr child)
    | group _ ih => exact .group ih
    | application _ _ bodyPath functionIH argumentIH => exact .application functionIH argumentIH bodyPath
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | binary operator _ _ applied leftIH rightIH => exact .binary operator leftIH rightIH applied
    | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
    | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
    | andFalse _ ih => exact .andFalse ih
    | orTrue _ ih => exact .orTrue ih
    | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH

/-- Successful raw evaluation and its absence are both reflected. An actual
selected non-Bool lazy RHS remains allowed by these untyped raw rules. -/
theorem recursiveLocalComputationEvaluates_mapIds_iff
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    RecursiveLocalComputationEvaluates (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping environment) initialStore source value finalStore ↔
      RecursiveLocalComputationEvaluates table environment initialStore source value finalStore := by
  simp only [recursiveLocalComputationEvaluates_iff_exists_cost,
    recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationFragment`
-/

/-! Recursive applications, unary/strict binaries, pairs and conditionals/lets of pure callers.
Membership does not constrain actual returned closure bodies or captures;
the caller syntax itself has no lambda constructor. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive RecursiveLocalComputationFragment : Core.Expr → Prop where
  | pure {expr : Core.Expr} (child : expr.LocalFragment) : RecursiveLocalComputationFragment expr
  | application {function argument : Core.Expr}
      (callee : RecursiveLocalComputationFragment function)
      (operand : RecursiveLocalComputationFragment argument) :
      RecursiveLocalComputationFragment (.apply function argument)

  | pair {left right : Core.Expr}
      (leftChild : RecursiveLocalComputationFragment left)
      (rightChild : RecursiveLocalComputationFragment right) :
      RecursiveLocalComputationFragment (.pair left right)

  | binary {op : Core.BinaryOp} {left right : Core.Expr}
      (leftChild : RecursiveLocalComputationFragment left)
      (rightChild : RecursiveLocalComputationFragment right) :
      RecursiveLocalComputationFragment (.binary op left right)

  | ifE {condition thenBranch elseBranch : Core.Expr}
      (conditionChild : RecursiveLocalComputationFragment condition)
      (thenChild : RecursiveLocalComputationFragment thenBranch)
      (elseChild : RecursiveLocalComputationFragment elseBranch) :
      RecursiveLocalComputationFragment (.ifE condition thenBranch elseBranch)

  | unary {op : Core.UnaryOp} {operand : Core.Expr}
      (child : RecursiveLocalComputationFragment operand) :
      RecursiveLocalComputationFragment (.unary op operand)

  | letE {initializer body : Core.Expr}
      (initializerChild : RecursiveLocalComputationFragment initializer)
      (bodyChild : RecursiveLocalComputationFragment body) :
      RecursiveLocalComputationFragment (.letE initializer body)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths`
-/

/-! Each recursive caller pair shares one cost before every continuation.
An actual invoked body's closed path is chosen once and reused on both sides.
Let-body paths retain the same actual bound value before the caller prefix. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RecursiveLocalComputationFragment.insertion_paths
    {expr : Core.Expr} (fragment : RecursiveLocalComputationFragment expr)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value}
    (evaluation : Core.Evaluates (leading ++ suffix) initialStore expr value finalStore) :
    ∃ cost, ∀ continuation,
      Core.Steps cost
        ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ ∧
      Core.Steps cost
        ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ := by
  induction fragment generalizing leading initialStore finalStore value with
  | pure child => exact child.insertion_paths leading suffix inserted evaluation
  | application _ _ calleeIH operandIH =>
      cases evaluation with
      | apply functionEvaluation argumentEvaluation bodyEvaluation =>
          obtain ⟨functionCost, functionPaths⟩ := calleeIH leading functionEvaluation
          obtain ⟨argumentCost, argumentPaths⟩ := operandIH leading argumentEvaluation
          obtain ⟨bodyCost, bodyPath⟩ := bodyEvaluation.toSteps
          refine ⟨functionCost + argumentCost + bodyCost + 3, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.apply (functionPaths _).1 (argumentPaths _).1 bodyPath
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.apply (functionPaths _).2 (argumentPaths _).2 bodyPath
  | pair _ _ leftIH rightIH =>
      cases evaluation with
      | pair left right =>
          obtain ⟨leftCost, leftPaths⟩ := leftIH leading left
          obtain ⟨rightCost, rightPaths⟩ := rightIH leading right
          refine ⟨leftCost + rightCost + 3, fun continuation => ?_⟩
          constructor
          · have path := Core.Steps.cons (.enterPair (continuation := continuation))
              ((leftPaths _).1.trans (.cons .enterPairRight
                ((rightPaths _).1.trans (.cons .applyPair .refl))))
            simpa only [Nat.add_assoc] using path
          · simp only [Core.Expr.weakenAt]
            have path := Core.Steps.cons (.enterPair (continuation := continuation))
              ((leftPaths _).2.trans (.cons .enterPairRight
                ((rightPaths _).2.trans (.cons .applyPair .refl))))
            simpa only [Nat.add_assoc] using path
  | binary _ _ leftIH rightIH =>
      cases evaluation with
      | binary leftEvaluation rightEvaluation applied =>
          obtain ⟨leftCost, leftPaths⟩ := leftIH leading leftEvaluation
          obtain ⟨rightCost, rightPaths⟩ := rightIH leading rightEvaluation
          refine ⟨leftCost + rightCost + 3, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.binary (leftPaths _).1 (rightPaths _).1 applied
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.binary (leftPaths _).2 (rightPaths _).2 applied
  | ifE _ _ _ conditionIH thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch =>
          obtain ⟨conditionCost, conditionPaths⟩ := conditionIH leading condition
          obtain ⟨branchCost, branchPaths⟩ := thenIH leading branch
          refine ⟨conditionCost + branchCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.ifTrue (conditionPaths _).1 (branchPaths _).1
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.ifTrue (conditionPaths _).2 (branchPaths _).2
      | ifFalse condition branch =>
          obtain ⟨conditionCost, conditionPaths⟩ := conditionIH leading condition
          obtain ⟨branchCost, branchPaths⟩ := elseIH leading branch
          refine ⟨conditionCost + branchCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.ifFalse (conditionPaths _).1 (branchPaths _).1
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.ifFalse (conditionPaths _).2 (branchPaths _).2
  | unary _ childIH =>
      cases evaluation with
      | unary child applied =>
          obtain ⟨childCost, childPaths⟩ := childIH leading child
          refine ⟨childCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.unary (childPaths _).1 applied
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.unary (childPaths _).2 applied
  | letE _ _ initializerIH bodyIH =>
      cases evaluation with
      | @letE _ _ _ _ _ _ boundValue _ initializer body =>
          obtain ⟨initializerCost, initializerPaths⟩ := initializerIH leading initializer
          obtain ⟨bodyCost, bodyPaths⟩ := bodyIH (boundValue :: leading) body
          refine ⟨initializerCost + bodyCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.letE (initializerPaths _).1 (bodyPaths _).1
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.letE (initializerPaths _).2 (bodyPaths _).2

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties`
-/

/-! Inserting a caller slot preserves literal successful values and stores.
Recursive callees retain the same actual closure, captures and invoked body.
Each let retains its actual bound value ahead of the caller prefix. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RecursiveLocalComputationFragment.evaluates_insert_iff
    {expr : Core.Expr} (fragment : RecursiveLocalComputationFragment expr)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Evaluates (leading ++ inserted :: suffix) initialStore
      (expr.weakenAt leading.length) value finalStore ↔
      Core.Evaluates (leading ++ suffix) initialStore expr value finalStore := by
  induction fragment generalizing leading initialStore finalStore value with
  | pure child => exact child.evaluates_insert_iff leading suffix inserted
  | application _ _ calleeIH operandIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply ((calleeIH leading).mp functionEvaluation) ((operandIH leading).mp argumentEvaluation) bodyEvaluation
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply ((calleeIH leading).mpr functionEvaluation) ((operandIH leading).mpr argumentEvaluation) bodyEvaluation
  | pair _ _ leftIH rightIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | pair left right => exact .pair ((leftIH leading).mp left) ((rightIH leading).mp right)
      · intro evaluation
        cases evaluation with
        | pair left right => exact .pair ((leftIH leading).mpr left) ((rightIH leading).mpr right)
  | binary _ _ leftIH rightIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | binary leftEvaluation rightEvaluation applied =>
            exact .binary ((leftIH leading).mp leftEvaluation) ((rightIH leading).mp rightEvaluation) applied
      · intro evaluation
        cases evaluation with
        | binary leftEvaluation rightEvaluation applied =>
            exact .binary ((leftIH leading).mpr leftEvaluation) ((rightIH leading).mpr rightEvaluation) applied
  | ifE _ _ _ conditionIH thenIH elseIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue ((conditionIH leading).mp condition) ((thenIH leading).mp branch)
        | ifFalse condition branch => exact .ifFalse ((conditionIH leading).mp condition) ((elseIH leading).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue ((conditionIH leading).mpr condition) ((thenIH leading).mpr branch)
        | ifFalse condition branch => exact .ifFalse ((conditionIH leading).mpr condition) ((elseIH leading).mpr branch)
  | unary _ childIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | unary child applied => exact .unary ((childIH leading).mp child) applied
      · intro evaluation
        cases evaluation with
        | unary child applied => exact .unary ((childIH leading).mpr child) applied
  | letE _ _ initializerIH bodyIH =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | @letE _ _ _ _ _ _ boundValue _ initializer body =>
            exact .letE ((initializerIH leading).mp initializer) ((bodyIH (boundValue :: leading)).mp body)
      · intro evaluation
        cases evaluation with
        | @letE _ _ _ _ _ _ boundValue _ initializer body =>
            exact .letE ((initializerIH leading).mpr initializer) ((bodyIH (boundValue :: leading)).mpr body)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationFragmentProperties`
-/

/-! Recursive caller membership follows original elaboration and is stable
under positional weakening, without inspecting actual closure bodies. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RecursiveLocalComputationFragment.weakenAt {expr : Core.Expr}
    (fragment : RecursiveLocalComputationFragment expr) (cutoff : Nat) :
    RecursiveLocalComputationFragment (expr.weakenAt cutoff) := by
  induction fragment generalizing cutoff with
  | pure child => exact .pure (child.weakenAt cutoff)
  | application _ _ calleeIH operandIH =>
      simp only [Core.Expr.weakenAt]
      exact .application (calleeIH cutoff) (operandIH cutoff)
  | pair _ _ leftIH rightIH =>
      simp only [Core.Expr.weakenAt]
      exact .pair (leftIH cutoff) (rightIH cutoff)
  | binary _ _ leftIH rightIH =>
      simp only [Core.Expr.weakenAt]
      exact .binary (leftIH cutoff) (rightIH cutoff)
  | ifE _ _ _ conditionIH thenIH elseIH =>
      simp only [Core.Expr.weakenAt]
      exact .ifE (conditionIH cutoff) (thenIH cutoff) (elseIH cutoff)
  | unary _ childIH =>
      simp only [Core.Expr.weakenAt]
      exact .unary (childIH cutoff)
  | letE _ _ initializerIH bodyIH =>
      simp only [Core.Expr.weakenAt]
      exact .letE (initializerIH cutoff) (bodyIH (cutoff + 1))

theorem RecursiveLocalComputationElaborates.core_fragment
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type) :
    RecursiveLocalComputationFragment core := by
  induction elaboration with
  | pure _ lowered _ => exact .pure lowered.localFragment
  | group _ ih => exact ih
  | application _ _ calleeIH operandIH => exact .application calleeIH operandIH
  | pair _ _ leftIH rightIH | many _ _ leftIH rightIH => exact .pair leftIH rightIH
  | binary _ _ _ leftIH rightIH => exact .binary leftIH rightIH
  | conditional _ _ _ conditionIH thenIH elseIH => exact .ifE conditionIH thenIH elseIH
  | logicalNot _ childIH => exact .unary childIH
  | bitNot _ childIH => exact .unary childIH
  | logicalAnd _ _ leftIH rightIH => exact .ifE leftIH rightIH (.pure .bool)
  | logicalOr _ _ leftIH rightIH => exact .ifE leftIH (.pure .bool) rightIH
  | notEqual _ _ leftIH rightIH => exact .unary (.binary leftIH rightIH)
  | lessEqual _ _ leftIH rightIH => exact .unary (.binary leftIH rightIH)
  | less _ _ leftIH rightIH =>
      exact .letE leftIH (.letE (rightIH.weakenAt 0) (.pure (.binary .var .var)))
  | greaterEqual _ _ leftIH rightIH =>
      exact .unary (.letE leftIH (.letE (rightIH.weakenAt 0) (.pure (.binary .var .var))))

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationCostExecutionProperties`
-/

/-! Private original-root cost inversions reconcile overlapping pure derivations.
The existing continuation law preserves actual selected values, stores and costs.
Tuple pairs retain both actual components and the original head-to-tail store order. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem reflects_pure_cost {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost)
    {resolved : Resolved.Expr} (resolution : ResolvesLocalExpression table source resolved) :
    LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost := by
  induction evaluation generalizing resolved with
  | pure child => exact child
  | group _ ih =>
      cases resolution with
      | group child => exact .group (ih child)
  | application _ _ _ _ _ => cases resolution
  | pair _ _ leftIH rightIH =>
      cases resolution with
      | pair left right => exact .pair (leftIH left) (rightIH right)
  | many _ _ headIH tailIH =>
      cases resolution with
      | many head tail => exact .many (headIH head) (tailIH tail)
  | @binary initialStore middleStore finalStore span operatorSpan left right sourceOp op
      leftValue rightValue result leftCost rightCost operator _ _ applied leftIH rightIH =>
      cases operator <;> cases resolution
      all_goals
        rename_i leftResolution rightResolution
        cases leftValue <;> cases rightValue <;> cases applied
        first
        | exact .add (leftIH leftResolution) (rightIH rightResolution)
        | exact .subtract (leftIH leftResolution) (rightIH rightResolution)
        | exact .multiply (leftIH leftResolution) (rightIH rightResolution)
        | exact .divide (leftIH leftResolution) (rightIH rightResolution)
        | exact .modulo (leftIH leftResolution) (rightIH rightResolution)
        | exact .bitAnd (leftIH leftResolution) (rightIH rightResolution)
        | exact .bitOr (leftIH leftResolution) (rightIH rightResolution)
        | exact .bitXor (leftIH leftResolution) (rightIH rightResolution)
        | exact .greater (leftIH leftResolution) (rightIH rightResolution)
        | exact .equal (leftIH leftResolution) (rightIH rightResolution)
  | ifTrue _ _ conditionIH branchIH =>
      cases resolution with
      | conditional condition yes _ => exact .ifTrue (conditionIH condition) (branchIH yes)
  | ifFalse _ _ conditionIH branchIH =>
      cases resolution with
      | conditional condition _ no => exact .ifFalse (conditionIH condition) (branchIH no)

  | logicalNot _ ih =>
      cases resolution with
      | logicalNot child => exact .logicalNot (ih child)
  | bitNot _ ih =>
      cases resolution with
      | bitNot child => exact .bitNot (ih child)

  | andTrue _ _ leftIH rightIH =>
      cases resolution with
      | logicalAnd left right => exact .andTrue (leftIH left) (rightIH right)
  | andFalse _ leftIH =>
      cases resolution with
      | logicalAnd left _ => exact .andFalse (leftIH left)
  | orTrue _ leftIH =>
      cases resolution with
      | logicalOr left _ => exact .orTrue (leftIH left)
  | orFalse _ _ leftIH rightIH =>
      cases resolution with
      | logicalOr left right => exact .orFalse (leftIH left) (rightIH right)
  | notEqual _ _ leftIH rightIH =>
      cases resolution with
      | notEqual left right => exact .notEqual (leftIH left) (rightIH right)
  | lessEqual _ _ leftIH rightIH =>
      cases resolution with
      | lessEqual left right => exact .lessEqual (leftIH left) (rightIH right)

  | less _ _ leftIH rightIH =>
      cases resolution with
      | less left right => exact .less (leftIH left) (rightIH right)
  | greaterEqual _ _ leftIH rightIH =>
      cases resolution with
      | greaterEqual left right => exact .greaterEqual (leftIH left) (rightIH right)

private theorem pair_path {environment : Core.Environment}
    {initialStore middleStore finalStore : Core.Store} {left right : Core.Expr}
    {leftValue rightValue : Core.Value} {leftCost rightCost : Nat}
    {continuation : List Core.Frame}
    (leftPath : Core.Steps leftCost
      ⟨.eval left environment, .pairRight right environment :: continuation, initialStore⟩
      ⟨.ret leftValue, .pairRight right environment :: continuation, middleStore⟩)
    (rightPath : Core.Steps rightCost
      ⟨.eval right environment, .pairApply leftValue :: continuation, middleStore⟩
      ⟨.ret rightValue, .pairApply leftValue :: continuation, finalStore⟩) :
    Core.Steps (leftCost + rightCost + 3)
      ⟨.eval (.pair left right) environment, continuation, initialStore⟩
      ⟨.ret (.pair leftValue rightValue), continuation, finalStore⟩ := by
  have path := Core.Steps.cons .enterPair
    (leftPath.trans (.cons .enterPairRight (rightPath.trans (.cons .applyPair .refl))))
  simpa only [Nat.add_assoc] using path

private theorem ordered_path {environment : Core.Environment}
    {initialStore middleStore finalStore : Core.Store} {left right : Core.Expr}
    {leftWord rightWord : Core.Word} {leftCost rightCost : Nat}
    (rightFragment : RecursiveLocalComputationFragment right)
    (leftPath : ∀ continuation, Core.Steps leftCost
      ⟨.eval left environment, continuation, initialStore⟩
      ⟨.ret (.word leftWord), continuation, middleStore⟩)
    (rightPath : ∀ continuation, Core.Steps rightCost
      ⟨.eval right environment, continuation, middleStore⟩
      ⟨.ret (.word rightWord), continuation, finalStore⟩)
    (continuation : List Core.Frame) :
    Core.Steps (leftCost + rightCost + 9)
      ⟨.eval (left.wordLt right) environment, continuation, initialStore⟩
      ⟨.ret (.bool (decide (leftWord < rightWord))), continuation, finalStore⟩ := by
  obtain ⟨pairedCost, paired⟩ := rightFragment.insertion_paths [] environment (.word leftWord)
    (Core.steps_from_initial_sound (rightPath []))
  have sameCost : pairedCost = rightCost := ((paired []).1.final_unique (rightPath [])).1
  exact CostStepComposition.wordLt leftPath (fun k => sameCost ▸ (paired k).2) continuation

theorem RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : RecursiveLocalComputationEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type)
    (sameIds : environment.ids = context.ids) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  induction elaboration generalizing initialStore finalStore value cost continuation with
  | pure resolution lowered _ =>
      rw [← sameIds] at lowered
      exact (reflects_pure_cost evaluation resolution).toStepsWithContinuation resolution lowered continuation
  | group _ ih =>
      cases evaluation with
      | pure child => cases child with | group inner => exact ih (.pure inner) continuation
      | group child => exact ih child continuation
  | application _ _ functionIH argumentIH =>
      cases evaluation with
      | pure child => cases child
      | application functionEvaluation argumentEvaluation bodyPath =>
          exact CostStepComposition.apply (functionIH functionEvaluation _) (argumentIH argumentEvaluation _) bodyPath
  | pair _ _ leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | pair left right => exact pair_path (leftIH (.pure left) _) (rightIH (.pure right) _)
      | pair left right => exact pair_path (leftIH left _) (rightIH right _)
  | many _ _ headIH tailIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | many head tail => exact pair_path (headIH (.pure head) _) (tailIH (.pure tail) _)
      | many head tail => exact pair_path (headIH head _) (tailIH tail _)
  | binary operator _ _ leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases operator <;> cases child
          all_goals exact CostStepComposition.binary (leftIH (.pure ‹_›) _) (rightIH (.pure ‹_›) _) rfl
      | binary otherOperator left right applied =>
          cases operator <;> cases otherOperator
          all_goals exact CostStepComposition.binary (leftIH left _) (rightIH right _) applied
      | andTrue _ _ | andFalse _ | orTrue _ | orFalse _ _ | notEqual _ _ | lessEqual _ _ | less _ _ | greaterEqual _ _ => cases operator
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | ifTrue guard branch => exact CostStepComposition.ifTrue (conditionIH (.pure guard) _) (thenIH (.pure branch) _)
          | ifFalse guard branch => exact CostStepComposition.ifFalse (conditionIH (.pure guard) _) (elseIH (.pure branch) _)
      | ifTrue guard branch => exact CostStepComposition.ifTrue (conditionIH guard _) (thenIH branch _)
      | ifFalse guard branch => exact CostStepComposition.ifFalse (conditionIH guard _) (elseIH branch _)
  | logicalNot _ ih =>
      cases evaluation with
      | pure child => cases child with | logicalNot operand => exact CostStepComposition.unary (ih (.pure operand) _) rfl
      | logicalNot child => exact CostStepComposition.unary (ih child _) rfl
  | bitNot _ ih =>
      cases evaluation with
      | pure child => cases child with | bitNot operand => exact CostStepComposition.unary (ih (.pure operand) _) rfl
      | bitNot child => exact CostStepComposition.unary (ih child _) rfl
  | logicalAnd _ _ leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | andTrue left right => exact CostStepComposition.ifTrue (leftIH (.pure left) _) (rightIH (.pure right) _)
          | andFalse left => simpa only [Nat.add_assoc] using CostStepComposition.ifFalse (leftIH (.pure left) _) (.cons .bool .refl)
      | binary operator _ _ _ => cases operator
      | andTrue left right => exact CostStepComposition.ifTrue (leftIH left _) (rightIH right _)
      | andFalse left => simpa only [Nat.add_assoc] using CostStepComposition.ifFalse (leftIH left _) (.cons .bool .refl)
  | logicalOr _ _ leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | orTrue left => simpa only [Nat.add_assoc] using CostStepComposition.ifTrue (leftIH (.pure left) _) (.cons .bool .refl)
          | orFalse left right => exact CostStepComposition.ifFalse (leftIH (.pure left) _) (rightIH (.pure right) _)
      | binary operator _ _ _ => cases operator
      | orTrue left => simpa only [Nat.add_assoc] using CostStepComposition.ifTrue (leftIH left _) (.cons .bool .refl)
      | orFalse left right => exact CostStepComposition.ifFalse (leftIH left _) (rightIH right _)
  | notEqual _ _ leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | notEqual left right =>
              simpa only [Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
                (CostStepComposition.binary (op := .wordEq) (leftIH (.pure left) _) (rightIH (.pure right) _) rfl) rfl
      | binary operator _ _ _ => cases operator
      | notEqual left right =>
          simpa only [Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
            (CostStepComposition.binary (op := .wordEq) (leftIH left _) (rightIH right _) rfl) rfl
  | lessEqual _ _ leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | lessEqual left right =>
              simpa only [Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
                (CostStepComposition.binary (op := .wordGt) (leftIH (.pure left) _) (rightIH (.pure right) _) rfl) rfl
      | binary operator _ _ _ => cases operator
      | lessEqual left right =>
          simpa only [Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
            (CostStepComposition.binary (op := .wordGt) (leftIH left _) (rightIH right _) rfl) rfl
  | less _ rightElab leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | less left right => exact ordered_path rightElab.core_fragment (leftIH (.pure left)) (rightIH (.pure right)) continuation
      | binary operator _ _ _ => cases operator
      | less left right => exact ordered_path rightElab.core_fragment (leftIH left) (rightIH right) continuation
  | greaterEqual _ rightElab leftIH rightIH =>
      cases evaluation with
      | pure child =>
          cases child with
          | greaterEqual left right =>
              simpa only [Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
                (ordered_path rightElab.core_fragment (leftIH (.pure left)) (rightIH (.pure right)) _) rfl
      | binary operator _ _ _ => cases operator
      | greaterEqual left right =>
          simpa only [Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
            (ordered_path rightElab.core_fragment (leftIH left) (rightIH right) _) rfl

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationExecutionProperties`
-/

/-! Existing execution contracts retain original-source evidence.
Forward success uses the exact cost path; reverse success is independent induction.
Tuple inversion preserves arbitrary actual components and the intermediate store. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem ordered_inv {environment : Core.Environment}
    {initialStore finalStore : Core.Store} {left right : Core.Expr} {value : Core.Value}
    (evaluation : Core.Evaluates environment initialStore (left.wordLt right) value finalStore)
    (rightFragment : RecursiveLocalComputationFragment right) :
    ∃ leftWord rightWord middleStore,
      Core.Evaluates environment initialStore left (.word leftWord) middleStore ∧
      Core.Evaluates environment middleStore right (.word rightWord) finalStore ∧
      value = .bool (decide (leftWord < rightWord)) := by
  rw [Core.Expr.wordLt_expansion] at evaluation
  cases evaluation with
  | @letE _ _ _ _ _ _ boundLeft _ leftEvaluation bodyEvaluation =>
      cases bodyEvaluation with
      | @letE _ _ _ _ _ _ boundRight _ rightEvaluation comparison =>
          cases comparison with
          | @binary _ _ _ _ _ _ _ rightValue leftValue _ rightReference leftReference applied =>
              cases rightReference with
              | var foundRight =>
                  have rightEq : boundRight = rightValue := by simpa using foundRight
                  subst rightValue
                  cases leftReference with
                  | var foundLeft =>
                      have leftEq : boundLeft = leftValue := by simpa using foundLeft
                      subst leftValue
                      cases boundRight <;> cases boundLeft <;>
                        simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
                      case word.word rightWord leftWord =>
                        cases applied
                        exact ⟨leftWord, rightWord, _, leftEvaluation,
                          (rightFragment.evaluates_insert_iff [] environment (.word leftWord)).mp rightEvaluation, rfl⟩

theorem RecursiveLocalComputationElaborates.evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type)
    (sameIds : environment.ids = context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    RecursiveLocalComputationEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates environment.values initialStore core value finalStore := by
  constructor
  · intro evaluation
    obtain ⟨_, costed⟩ := recursiveLocalComputationEvaluates_iff_exists_cost.mp evaluation
    exact Core.steps_from_initial_sound (costed.toStepsWithContinuation elaboration sameIds [])
  · intro evaluation
    induction elaboration generalizing initialStore finalStore value with
    | pure resolution lowered _ =>
        rw [← sameIds] at lowered
        exact .pure ((resolution.core_evaluates_iff lowered).mpr evaluation)
    | group _ ih => exact .group (ih evaluation)
    | application _ _ functionIH argumentIH =>
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .application (functionIH functionEvaluation) (argumentIH argumentEvaluation) bodyEvaluation
    | pair _ _ leftIH rightIH =>
        cases evaluation with
        | pair left right => exact .pair (leftIH left) (rightIH right)
    | many _ _ headIH tailIH =>
        cases evaluation with
        | pair head tail => exact .many (headIH head) (tailIH tail)
    | binary operator _ _ leftIH rightIH =>
        cases evaluation with
        | binary leftChild rightChild applied => exact .binary operator (leftIH leftChild) (rightIH rightChild) applied
    | conditional _ _ _ conditionIH thenIH elseIH =>
        cases evaluation with
        | ifTrue guard branch => exact .ifTrue (conditionIH guard) (thenIH branch)
        | ifFalse guard branch => exact .ifFalse (conditionIH guard) (elseIH branch)
    | logicalNot _ ih =>
        cases evaluation with
        | @unary _ _ _ _ _ childValue _ child applied =>
            cases childValue <;> cases applied
            exact .logicalNot (ih child)
    | bitNot _ ih =>
        cases evaluation with
        | @unary _ _ _ _ _ childValue _ child applied =>
            cases childValue <;> cases applied
            exact .bitNot (ih child)
    | logicalAnd _ _ leftIH rightIH =>
        cases evaluation with
        | ifTrue left right => exact .andTrue (leftIH left) (rightIH right)
        | ifFalse left constant =>
            cases constant
            exact .andFalse (leftIH left)
    | logicalOr _ _ leftIH rightIH =>
        cases evaluation with
        | ifTrue left constant =>
            cases constant
            exact .orTrue (leftIH left)
        | ifFalse left right => exact .orFalse (leftIH left) (rightIH right)
    | notEqual _ _ leftIH rightIH =>
        cases evaluation with
        | unary comparison negated =>
            cases comparison with
            | @binary _ _ _ _ _ _ _ leftValue rightValue _ left right compared =>
                cases leftValue <;> cases rightValue <;> cases compared <;> cases negated
                exact .notEqual (leftIH left) (rightIH right)
    | lessEqual _ _ leftIH rightIH =>
        cases evaluation with
        | unary comparison negated =>
            cases comparison with
            | @binary _ _ _ _ _ _ _ leftValue rightValue _ left right compared =>
                cases leftValue <;> cases rightValue <;> cases compared <;> cases negated
                exact .lessEqual (leftIH left) (rightIH right)

    | less _ rightElab leftIH rightIH =>
        obtain ⟨_, _, _, left, right, rfl⟩ := ordered_inv evaluation rightElab.core_fragment
        exact .less (leftIH left) (rightIH right)
    | greaterEqual _ rightElab leftIH rightIH =>
        cases evaluation with
        | unary comparison negated =>
            obtain ⟨_, _, _, left, right, rfl⟩ := ordered_inv comparison rightElab.core_fragment
            cases negated
            exact .greaterEqual (leftIH left) (rightIH right)

theorem RecursiveLocalComputationElaborates.evaluatesWithCost_iff_steps
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type)
    (sameIds : environment.ids = context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    RecursiveLocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost ↔
      Core.Steps cost (.initial core environment.values initialStore) (.final value finalStore) := by
  constructor
  · intro evaluation
    exact evaluation.toStepsWithContinuation elaboration sameIds []
  · intro path
    have evaluation := (elaboration.evaluates_iff sameIds).mpr (Core.steps_from_initial_sound path)
    obtain ⟨actualCost, actual⟩ := recursiveLocalComputationEvaluates_iff_exists_cost.mp evaluation
    have sameCost := (path.final_unique (actual.toStepsWithContinuation elaboration sameIds [])).1
    exact sameCost.symm ▸ actual

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationTypingProperties`
-/

/-! Independent source typing and Core typing retain every written child,
including both children of the fixed short-circuit interpretation. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem recursiveLocalComputationHasType_iff_elaborates
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty} :
    RecursiveLocalComputationHasType table context source type ↔
      ∃ core, RecursiveLocalComputationElaborates table context source core type := by
  constructor
  · intro typing
    induction typing with
    | pure child =>
        obtain ⟨resolved, resolution, typed⟩ := child.resolves
        obtain ⟨core, lowered, _⟩ := typed.lowers
        exact ⟨core, .pure resolution lowered typed⟩
    | group _ ih =>
        obtain ⟨core, child⟩ := ih
        exact ⟨core, .group child⟩
    | application _ _ functionIH argumentIH =>
        obtain ⟨functionCore, functionElaborated⟩ := functionIH
        obtain ⟨argumentCore, argumentElaborated⟩ := argumentIH
        exact ⟨.apply functionCore argumentCore, .application functionElaborated argumentElaborated⟩
    | pair _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨.pair leftCore rightCore, .pair leftChild rightChild⟩
    | many _ _ headIH tailIH =>
        obtain ⟨headCore, headChild⟩ := headIH
        obtain ⟨tailCore, tailChild⟩ := tailIH
        exact ⟨.pair headCore tailCore, .many headChild tailChild⟩
    | binary operator _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftElaborated⟩ := leftIH
        obtain ⟨rightCore, rightElaborated⟩ := rightIH
        exact ⟨.binary _ leftCore rightCore, .binary operator leftElaborated rightElaborated⟩
    | conditional _ _ _ conditionIH thenIH elseIH =>
        obtain ⟨conditionCore, conditionElaborated⟩ := conditionIH
        obtain ⟨thenCore, thenElaborated⟩ := thenIH
        obtain ⟨elseCore, elseElaborated⟩ := elseIH
        exact ⟨.ifE conditionCore thenCore elseCore, .conditional conditionElaborated thenElaborated elseElaborated⟩
    | logicalNot _ ih =>
        obtain ⟨core, child⟩ := ih
        exact ⟨.unary .boolNot core, .logicalNot child⟩
    | bitNot _ ih =>
        obtain ⟨core, child⟩ := ih
        exact ⟨.unary .wordNot core, .bitNot child⟩
    | logicalAnd _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨.ifE leftCore rightCore (.bool false), .logicalAnd leftChild rightChild⟩
    | logicalOr _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨.ifE leftCore (.bool true) rightCore, .logicalOr leftChild rightChild⟩
    | notEqual _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨.unary .boolNot (.binary .wordEq leftCore rightCore), .notEqual leftChild rightChild⟩
    | lessEqual _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨.unary .boolNot (.binary .wordGt leftCore rightCore), .lessEqual leftChild rightChild⟩
    | less _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨leftCore.wordLt rightCore, .less leftChild rightChild⟩
    | greaterEqual _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftChild⟩ := leftIH
        obtain ⟨rightCore, rightChild⟩ := rightIH
        exact ⟨.unary .boolNot (leftCore.wordLt rightCore), .greaterEqual leftChild rightChild⟩
  · rintro ⟨core, elaboration⟩
    induction elaboration with
    | pure resolution _ typing => exact .pure (resolution.reflects_type typing)
    | group _ ih => exact .group ih
    | application _ _ functionIH argumentIH => exact .application functionIH argumentIH
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | binary operator _ _ leftIH rightIH => exact .binary operator leftIH rightIH
    | conditional _ _ _ conditionIH thenIH elseIH => exact .conditional conditionIH thenIH elseIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | logicalAnd _ _ leftIH rightIH => exact .logicalAnd leftIH rightIH
    | logicalOr _ _ leftIH rightIH => exact .logicalOr leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH

theorem RecursiveLocalComputationElaborates.core_hasType
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type) :
    Core.HasType context.values core type := by
  induction elaboration with
  | pure _ lowered typing => exact lowered.preserves_type typing
  | group _ ih => exact ih
  | application _ _ functionIH argumentIH => exact .apply functionIH argumentIH
  | pair _ _ leftIH rightIH | many _ _ leftIH rightIH => exact .pair leftIH rightIH
  | binary _ _ _ leftIH rightIH => exact .binary leftIH rightIH
  | conditional _ _ _ conditionIH thenIH elseIH => exact .ifE conditionIH thenIH elseIH
  | logicalNot _ ih | bitNot _ ih => exact .unary ih
  | logicalAnd _ _ leftIH rightIH => exact .ifE leftIH rightIH .bool
  | logicalOr _ _ leftIH rightIH => exact .ifE leftIH .bool rightIH
  | notEqual _ _ leftIH rightIH | lessEqual _ _ leftIH rightIH => exact .unary (.binary leftIH rightIH)
  | less _ _ leftIH rightIH => exact leftIH.wordLt rightIH
  | greaterEqual _ _ leftIH rightIH => exact .unary (leftIH.wordLt rightIH)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationProperties`
-/

/-! Exact static provenance for recursive calls, groups, tuples, operators and conditionals.
Pure overlap is reconciled internally without restricting source or callers. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem short_circuit_children {table : LocalNameTable} {context : Resolved.Context}
    {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty} (isOr : Bool) :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .binary left ⟨operatorSpan, if isOr then .logicalOr else .logicalAnd⟩ right⟩ = some (core, type) ↔
      ∃ leftCore rightCore,
        elaborateRecursiveLocalComputation? table context left = some (leftCore, .bool) ∧
        elaborateRecursiveLocalComputation? table context right = some (rightCore, .bool) ∧
        core = (if isOr then .ifE leftCore (.bool true) rightCore else .ifE leftCore rightCore (.bool false)) ∧
        type = .bool := by
  cases isOr <;>
    simp [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff,
      Prod.exists, and_assoc, and_left_comm, and_comm] <;> simp only [eq_comm]

private theorem unary_children {table : LocalNameTable} {context : Resolved.Context}
    {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
    {sourceOp : Syntax.UnaryOp} {op : Core.UnaryOp} {core : Core.Expr} {type : Core.Ty}
    (operator : sourceOp = .logicalNot ∧ op = .boolNot ∨ sourceOp = .bitNot ∧ op = .wordNot) :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .unary ⟨operatorSpan, sourceOp⟩ operand⟩ = some (core, type) ↔
      ∃ operandCore,
        elaborateRecursiveLocalComputation? table context operand = some (operandCore, op.operandType) ∧
        core = .unary op operandCore ∧ type = op.resultType := by
  rcases operator with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff,
      Prod.exists, and_left_comm, and_comm, Core.UnaryOp.operandType, Core.UnaryOp.resultType] <;> simp only [eq_comm]

private theorem binary_children {table : LocalNameTable} {context : Resolved.Context}
    {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
    {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} {core : Core.Expr} {type : Core.Ty}
    (ordered negated : Bool) (operator :
      (DirectWordBinary sourceOp op ∧ ordered = false ∧ negated = false) ∨
      (sourceOp = .notEqual ∧ op = .wordEq ∧ ordered = false ∧ negated = true) ∨
      (sourceOp = .lessEqual ∧ op = .wordGt ∧ ordered = false ∧ negated = true) ∨
      (sourceOp = .less ∧ op = .wordGt ∧ ordered = true ∧ negated = false) ∨
      (sourceOp = .greaterEqual ∧ op = .wordGt ∧ ordered = true ∧ negated = true)) :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ = some (core, type) ↔
      ∃ leftCore rightCore,
        elaborateRecursiveLocalComputation? table context left = some (leftCore, op.leftType) ∧
        elaborateRecursiveLocalComputation? table context right = some (rightCore, op.rightType) ∧
        core = (let body := if ordered then leftCore.wordLt rightCore else .binary op leftCore rightCore
          if negated then .unary .boolNot body else body) ∧
        type = op.resultType := by
  rcases operator with ⟨direct, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  all_goals try cases direct
  all_goals simp [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff,
      Prod.exists, and_assoc, and_left_comm, and_comm, directWordBinary?, Core.BinaryOp.leftType,
    Core.BinaryOp.rightType, Core.BinaryOp.resultType] <;> simp only [eq_comm]

private theorem conditional_children {table : LocalNameTable} {context : Resolved.Context}
    {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty} :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ = some (core, type) ↔
      ∃ conditionCore thenCore elseCore,
        elaborateRecursiveLocalComputation? table context condition = some (conditionCore, .bool) ∧
        elaborateRecursiveLocalComputation? table context thenBranch = some (thenCore, type) ∧
        elaborateRecursiveLocalComputation? table context elseBranch = some (elseCore, type) ∧
        core = .ifE conditionCore thenCore elseCore := by
  simp [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff,
      Prod.exists, and_assoc, and_left_comm, and_comm] <;> simp only [eq_comm]

private theorem pure_complete {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr} {core : Core.Expr} {type : Core.Ty}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers context.ids resolved core)
    (typing : Resolved.HasType context resolved type) :
    elaborateRecursiveLocalComputation? table context source = some (core, type) := by
  induction resolution generalizing core type with
  | group _ ih => simpa only [elaborateRecursiveLocalComputation?] using ih lowered typing
  | pair _ _ leftIH rightIH | many _ _ leftIH rightIH =>
      cases lowered with | pair leftLowered rightLowered =>
        cases typing with | pair leftTyped rightTyped =>
          rw [elaborateRecursiveLocalComputation?]
          simp only [leftIH leftLowered leftTyped, rightIH rightLowered rightTyped, bind, Option.bind_some, pure]
  | logicalNot _ ih | bitNot _ ih =>
      cases lowered with
      | unary childLowered =>
          cases typing with
          | unary childTyped => simp [elaborateRecursiveLocalComputation?, ih childLowered childTyped,
              Core.UnaryOp.operandType, Core.UnaryOp.resultType]
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases lowered with
      | ifE conditionLowered thenLowered elseLowered =>
          cases typing with
          | ifE conditionTyped thenTyped elseTyped =>
              exact conditional_children.mpr ⟨_, _, _, conditionIH conditionLowered conditionTyped,
                thenIH thenLowered thenTyped, elseIH elseLowered elseTyped, rfl⟩
  | logicalAnd _ _ leftIH rightIH =>
      cases lowered with
      | ifE leftLowered rightLowered constant =>
          cases constant; cases typing with
          | ifE leftTyped rightTyped constant =>
              cases constant
              exact (short_circuit_children false).mpr ⟨_, _, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped, rfl, rfl⟩
  | logicalOr _ _ leftIH rightIH =>
      cases lowered with
      | ifE leftLowered constant rightLowered =>
          cases constant; cases typing with
          | ifE leftTyped constant rightTyped =>
              cases constant
              exact (short_circuit_children true).mpr ⟨_, _, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped, rfl, rfl⟩
  | notEqual _ _ leftIH rightIH | lessEqual _ _ leftIH rightIH =>
      cases lowered with | unary comparisonLowered =>
        cases comparisonLowered with | binary leftLowered rightLowered =>
          cases typing with | unary comparisonTyped =>
            cases comparisonTyped with | binary leftTyped rightTyped =>
              simp [elaborateRecursiveLocalComputation?, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped,
                Core.BinaryOp.leftType, Core.BinaryOp.rightType, Core.UnaryOp.resultType]
  | less _ _ leftIH rightIH =>
      cases lowered with | wordLt leftLowered rightLowered =>
        cases typing with | wordLt leftTyped rightTyped =>
          simp [elaborateRecursiveLocalComputation?, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped]
  | greaterEqual _ _ leftIH rightIH =>
      cases lowered with | unary comparison =>
        cases comparison with | wordLt leftLowered rightLowered =>
          cases typing with | unary comparison =>
            cases comparison with | wordLt leftTyped rightTyped =>
              simp [elaborateRecursiveLocalComputation?, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped, Core.UnaryOp.resultType]
  | add _ _ leftIH rightIH | subtract _ _ leftIH rightIH
  | multiply _ _ leftIH rightIH | divide _ _ leftIH rightIH
  | modulo _ _ leftIH rightIH | greater _ _ leftIH rightIH | equal _ _ leftIH rightIH
  | bitAnd _ _ leftIH rightIH | bitOr _ _ leftIH rightIH | bitXor _ _ leftIH rightIH =>
      cases lowered with
      | binary leftLowered rightLowered =>
          cases typing with
          | binary leftTyped rightTyped =>
              rw [elaborateRecursiveLocalComputation?] <;>
                simp [directWordBinary?, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped]
  | _ =>
      rw [elaborateRecursiveLocalComputation?] <;> try simp
      exact elaborateLocalExpression?_complete (by constructor <;> assumption) lowered typing

private theorem application_children {table : LocalNameTable} {context : Resolved.Context}
    {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty} :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ = some (core, type) ↔
      ∃ functionCore argumentCore parameterType,
        elaborateRecursiveLocalComputation? table context callee =
          some (functionCore, .function parameterType type) ∧
        elaborateRecursiveLocalComputation? table context argument = some (argumentCore, parameterType) ∧
        core = .apply functionCore argumentCore := by
  simp only [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨functionCore, functionType⟩, functionAccepted,
      ⟨argumentCore, argumentType⟩, argumentAccepted, result⟩
    cases functionType <;> try cases result
    case function parameterType resultType =>
      dsimp only at result
      split at result
      next same => cases result; exact ⟨functionCore, argumentCore, parameterType, functionAccepted, same ▸ argumentAccepted, rfl⟩
      next => cases result
  · rintro ⟨functionCore, argumentCore, parameterType, functionAccepted, argumentAccepted, rfl⟩
    exact ⟨(functionCore, .function parameterType type), functionAccepted,
      (argumentCore, parameterType), argumentAccepted, by simp⟩

private theorem complete {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type) :
    elaborateRecursiveLocalComputation? table context source = some (core, type) := by
  induction elaboration with
  | pure resolution lowered typing =>
      exact pure_complete resolution lowered typing
  | group _ ih => simpa only [elaborateRecursiveLocalComputation?] using ih
  | pair _ _ leftIH rightIH | many _ _ leftIH rightIH =>
      rw [elaborateRecursiveLocalComputation?]
      simp only [leftIH, rightIH, bind, Option.bind_some, pure]
  | application _ _ functionIH argumentIH =>
      exact application_children.mpr ⟨_, _, _, functionIH, argumentIH, rfl⟩
  | binary operator _ _ leftIH rightIH =>
      exact (binary_children false false (.inl ⟨operator, rfl, rfl⟩)).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | conditional _ _ _ conditionIH thenIH elseIH =>
      exact conditional_children.mpr ⟨_, _, _, conditionIH, thenIH, elseIH, rfl⟩
  | logicalNot _ ih => exact (unary_children (Or.inl ⟨rfl, rfl⟩)).mpr ⟨_, ih, rfl, rfl⟩
  | bitNot _ ih => exact (unary_children (Or.inr ⟨rfl, rfl⟩)).mpr ⟨_, ih, rfl, rfl⟩
  | logicalAnd _ _ leftIH rightIH => exact (short_circuit_children false).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | logicalOr _ _ leftIH rightIH => exact (short_circuit_children true).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | notEqual _ _ leftIH rightIH => exact (binary_children false true (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | lessEqual _ _ leftIH rightIH => exact (binary_children false true (.inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩)))).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | less _ _ leftIH rightIH => exact (binary_children true false (.inr (.inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))))).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩
  | greaterEqual _ _ leftIH rightIH => exact (binary_children true true (.inr (.inr (.inr (.inr ⟨rfl, rfl, rfl, rfl⟩))))).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩

private theorem pure_sound {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type)) :
    RecursiveLocalComputationElaborates table context source core type := by
  obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound accepted
  exact .pure resolution lowered typing

private theorem sound {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateRecursiveLocalComputation? table context source = some (core, type)) :
    RecursiveLocalComputationElaborates table context source core type := by
  cases source with | mk span payload =>
    cases payload
    case group inner =>
      exact .group (sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted))
    case tuple elements =>
      cases elements with | mk tupleSpan elements =>
        cases elements with
        | nil => exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
        | cons first rest =>
            cases rest with
            | nil => exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
            | cons second rest =>
                cases rest with
                | nil =>
                    simp only [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff, pure] at accepted
                    obtain ⟨⟨leftCore, leftType⟩, leftAccepted, ⟨rightCore, rightType⟩, rightAccepted, same⟩ := accepted
                    cases same; exact .pair (sound leftAccepted) (sound rightAccepted)
                | cons third rest =>
                    rw [elaborateRecursiveLocalComputation?] at accepted
                    simp only [bind, Option.bind_eq_some_iff, pure] at accepted
                    obtain ⟨⟨headCore, headType⟩, headAccepted, ⟨tailCore, tailType⟩, tailAccepted, same⟩ := accepted
                    cases same; exact .many (sound headAccepted) (sound tailAccepted)
    case unary operator operand =>
      cases operator with | mk operatorSpan sourceOp =>
        cases sourceOp
        case logicalNot =>
          obtain ⟨childCore, child, rfl, rfl⟩ := (unary_children (Or.inl ⟨rfl, rfl⟩)).mp accepted
          exact .logicalNot (sound child)
        case bitNot =>
          obtain ⟨childCore, child, rfl, rfl⟩ := (unary_children (Or.inr ⟨rfl, rfl⟩)).mp accepted
          exact .bitNot (sound child)
    case conditional condition question thenBranch colon elseBranch =>
      obtain ⟨conditionCore, thenCore, elseCore, conditionAccepted, thenAccepted, elseAccepted, rfl⟩ :=
        conditional_children.mp accepted
      exact .conditional (sound conditionAccepted) (sound thenAccepted) (sound elseAccepted)
    case binary left operator right =>
      cases operator with | mk operatorSpan sourceOp =>
        cases mapped : directWordBinary? sourceOp with
        | some op =>
            have operator := directWordBinary?_iff.mp mapped
            obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ :=
              (binary_children false false (.inl ⟨operator, rfl, rfl⟩)).mp accepted
            exact .binary operator (sound leftAccepted) (sound rightAccepted)
        | none =>
            cases sourceOp <;> simp [directWordBinary?] at mapped
            case logicalAnd =>
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (short_circuit_children false).mp accepted
              exact .logicalAnd (sound leftAccepted) (sound rightAccepted)
            case logicalOr =>
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (short_circuit_children true).mp accepted
              exact .logicalOr (sound leftAccepted) (sound rightAccepted)
            case notEqual =>
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (binary_children false true (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))).mp accepted
              exact .notEqual (sound leftAccepted) (sound rightAccepted)
            case lessEqual =>
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (binary_children false true (.inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩)))).mp accepted
              exact .lessEqual (sound leftAccepted) (sound rightAccepted)
            case less =>
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (binary_children true false (.inr (.inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))))).mp accepted
              exact .less (sound leftAccepted) (sound rightAccepted)
            case greaterEqual =>
              obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ := (binary_children true true (.inr (.inr (.inr (.inr ⟨rfl, rfl, rfl, rfl⟩))))).mp accepted
              exact .greaterEqual (sound leftAccepted) (sound rightAccepted)
    case call callee arguments =>
      cases arguments with | mk argumentsSpan arguments =>
        cases arguments with
        | nil => exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
        | cons argument rest =>
            cases rest with
            | nil =>
                obtain ⟨functionCore, argumentCore, parameterType, functionAccepted, argumentAccepted, rfl⟩ :=
                  application_children.mp accepted
                exact .application (sound functionAccepted) (sound argumentAccepted)
            | cons _ _ => exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
    all_goals exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
termination_by sizeOf source

theorem elaborateRecursiveLocalComputation?_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateRecursiveLocalComputation? table context source = some (core, type) ↔
      RecursiveLocalComputationElaborates table context source core type :=
  ⟨sound, complete⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveLocalComputationRenamingProperties`
-/

/-! Simultaneous injective identity relabeling retains original recursive
source evidence and exact positional Core. No source binder is allocated here;
owner and binder-index changes need neither an inverse nor runtime values. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Reflect the original resolved child at pure leaves; recursive rules retain
their own evidence even when the source also belongs to the pure fragment. -/
theorem recursiveLocalComputationElaborates_mapIds_iff
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty} :
    RecursiveLocalComputationElaborates (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) source core type ↔
      RecursiveLocalComputationElaborates table context source core type := by
  constructor
  · intro elaboration
    induction elaboration with
    | pure resolution lowered typing =>
        obtain ⟨original, originalResolution, rfl⟩ :=
          (resolvesLocalExpression_mapIds_iff_exists mapping).mp resolution
        exact .pure originalResolution
          ((Resolved.lowers_renameIds_iff mapping injective).mp
            (by simpa only [Resolved.LocalScope.ids_mapIds] using lowered))
          ((Resolved.typing_renameIds_iff mapping injective).mp typing)
    | group _ ih => exact .group ih
    | application _ _ functionIH argumentIH => exact .application functionIH argumentIH
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | binary operator _ _ leftIH rightIH => exact .binary operator leftIH rightIH
    | conditional _ _ _ conditionIH thenIH elseIH => exact .conditional conditionIH thenIH elseIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | logicalAnd _ _ leftIH rightIH => exact .logicalAnd leftIH rightIH
    | logicalOr _ _ leftIH rightIH => exact .logicalOr leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
  · intro elaboration
    induction elaboration with
    | pure resolution lowered typing =>
        exact .pure (resolution.mapIds mapping)
          (by simpa only [Resolved.LocalScope.ids_mapIds] using
            (Resolved.lowers_renameIds_iff mapping injective).mpr lowered)
          ((Resolved.typing_renameIds_iff mapping injective).mpr typing)
    | group _ ih => exact .group ih
    | application _ _ functionIH argumentIH => exact .application functionIH argumentIH
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | binary operator _ _ leftIH rightIH => exact .binary operator leftIH rightIH
    | conditional _ _ _ conditionIH thenIH elseIH => exact .conditional conditionIH thenIH elseIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | logicalAnd _ _ leftIH rightIH => exact .logicalAnd leftIH rightIH
    | logicalOr _ _ leftIH rightIH => exact .logicalOr leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH

theorem recursiveLocalComputationHasType_mapIds_iff
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty} :
    RecursiveLocalComputationHasType (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) source type ↔
      RecursiveLocalComputationHasType table context source type := by
  simp only [recursiveLocalComputationHasType_iff_elaborates,
    recursiveLocalComputationElaborates_mapIds_iff mapping injective]

/-- Complete checking agrees, including rejected original children. Injectivity
does not require surjectivity, unique caller rows or an owner-only map. -/
theorem elaborateRecursiveLocalComputation?_mapIds
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (table : LocalNameTable) (context : Resolved.Context) (source : Syntax.Expr) :
    elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) source =
      elaborateRecursiveLocalComputation? table context source := by
  cases original : elaborateRecursiveLocalComputation? table context source with
  | none =>
      cases renamed : elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping table)
          (Resolved.LocalScope.mapIds mapping context) source with
      | none => rfl
      | some result =>
          rcases result with ⟨core, type⟩
          have accepted := elaborateRecursiveLocalComputation?_iff.mpr
            ((recursiveLocalComputationElaborates_mapIds_iff mapping injective).mp
              (elaborateRecursiveLocalComputation?_iff.mp renamed))
          rw [original] at accepted
          cases accepted
  | some result =>
      rcases result with ⟨core, type⟩
      exact elaborateRecursiveLocalComputation?_iff.mpr
        ((recursiveLocalComputationElaborates_mapIds_iff mapping injective).mpr
          (elaborateRecursiveLocalComputation?_iff.mp original))

end Solcore.Frontend
