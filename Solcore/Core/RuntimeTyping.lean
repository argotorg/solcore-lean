import Solcore.Core.Machine

/-!
# Typing of runtime states

The relations that `Safety` is stated over. `ValueHasType` and `EnvironmentHasTypes` type values
without a store. `WorldExtends`, `RuntimeValueHasType`, `RuntimeEnvironmentHasTypes`,
`RuntimeStoreHasTypes` and `StoreHasTypes` add a store typing that grows during a run.
`FrameHasType`, `ContinuationHasType` and `StateHasType` type the machine's states.
-/

set_option autoImplicit false

namespace Solcore.Core

/-! ## Structural value typing -/

mutual

  inductive ValueHasType :
      Value → Ty → (definitions : DataEnvironment := []) → Prop where
    | unit {definitions : DataEnvironment} : ValueHasType .unit .unit definitions
    | bool {definitions : DataEnvironment} {value : Bool} :
        ValueHasType (.bool value) .bool definitions
    | word {definitions : DataEnvironment} {value : Word} :
        ValueHasType (.word value) .word definitions
    | integer {definitions : DataEnvironment} {value : Int} :
        ValueHasType (.integer value) .integer definitions
    | pair
        {definitions : DataEnvironment}
        {left right : Value} {leftType rightType : Ty} :
        ValueHasType left leftType definitions →
        ValueHasType right rightType definitions →
        ValueHasType (.pair left right) (.product leftType rightType) definitions
    | inLeft
        {definitions : DataEnvironment}
        {payload : Value} {leftType rightType : Ty} :
        ValueHasType payload leftType definitions →
        ValueHasType (.inLeft rightType payload) (.sum leftType rightType)
          definitions
    | inRight
        {definitions : DataEnvironment}
        {payload : Value} {leftType rightType : Ty} :
        ValueHasType payload rightType definitions →
        ValueHasType (.inRight leftType payload) (.sum leftType rightType)
          definitions
    | closure
        {definitions : DataEnvironment}
        {parameterType resultType : Ty} {body : Expr}
        {environment : Environment} {context : Context} :
        EnvironmentHasTypes environment context definitions →
        HasType (parameterType :: context) body resultType definitions →
        ValueHasType
          (.closure parameterType resultType body environment)
          (.function parameterType resultType)
          definitions
    | cellRef
        {definitions : DataEnvironment} {elementType : Ty} {location : Location} :
        ValueHasType (.cellRef elementType location) (.cell elementType) definitions
    | constructed
        {definitions : DataEnvironment}
        {constructor : ConstructorId} {payload : Value} {payloadType : Ty} :
        definitions.lookupConstructorPayloadType? constructor = some payloadType →
        ValueHasType payload payloadType definitions →
        ValueHasType (.constructed constructor payload)
          (.namedData constructor.owner) definitions

  inductive EnvironmentHasTypes :
      Environment → Context → (definitions : DataEnvironment := []) → Prop where
    | nil {definitions : DataEnvironment} : EnvironmentHasTypes [] [] definitions
    | cons
        {definitions : DataEnvironment}
        {value : Value} {type : Ty}
        {environment : Environment} {context : Context} :
        ValueHasType value type definitions →
        EnvironmentHasTypes environment context definitions →
        EnvironmentHasTypes (value :: environment) (type :: context) definitions

end

/-! ## Worlds, runtime typing, and typed stores -/

def WorldExtends (initial future : StoreTyping) : Prop :=
  ∃ suffix, future = initial ++ suffix

mutual

  inductive RuntimeValueHasType
      (world : StoreTyping) :
      Value → Ty → (definitions : DataEnvironment := []) → Prop where
    | unit {definitions : DataEnvironment} :
        RuntimeValueHasType world .unit .unit definitions
    | bool {definitions : DataEnvironment} {value : Bool} :
        RuntimeValueHasType world (.bool value) .bool definitions
    | word {definitions : DataEnvironment} {value : Word} :
        RuntimeValueHasType world (.word value) .word definitions
    | integer {definitions : DataEnvironment} {value : Int} :
        RuntimeValueHasType world (.integer value) .integer definitions
    | pair
        {definitions : DataEnvironment}
        {left right : Value} {leftType rightType : Ty} :
        RuntimeValueHasType world left leftType definitions →
        RuntimeValueHasType world right rightType definitions →
        RuntimeValueHasType world (.pair left right) (.product leftType rightType)
          definitions
    | inLeft
        {definitions : DataEnvironment}
        {payload : Value} {leftType rightType : Ty} :
        RuntimeValueHasType world payload leftType definitions →
        RuntimeValueHasType world
          (.inLeft rightType payload) (.sum leftType rightType) definitions
    | inRight
        {definitions : DataEnvironment}
        {payload : Value} {leftType rightType : Ty} :
        RuntimeValueHasType world payload rightType definitions →
        RuntimeValueHasType world
          (.inRight leftType payload) (.sum leftType rightType) definitions
    | closure
        {definitions : DataEnvironment}
        {parameterType resultType : Ty} {body : Expr}
        {environment : Environment} {context : Context} :
        RuntimeEnvironmentHasTypes world environment context definitions →
        HasType (parameterType :: context) body resultType definitions →
        RuntimeValueHasType world
          (.closure parameterType resultType body environment)
          (.function parameterType resultType)
          definitions
    | cellRef
        {definitions : DataEnvironment}
        {elementType : Ty} {location : Location} :
        world[location]? = some elementType →
        RuntimeValueHasType world
          (.cellRef elementType location) (.cell elementType) definitions
    | constructed
        {definitions : DataEnvironment}
        {constructor : ConstructorId} {payload : Value} {payloadType : Ty} :
        definitions.lookupConstructorPayloadType? constructor = some payloadType →
        RuntimeValueHasType world payload payloadType definitions →
        RuntimeValueHasType world (.constructed constructor payload)
          (.namedData constructor.owner) definitions

  inductive RuntimeEnvironmentHasTypes
      (world : StoreTyping) :
      Environment → Context → (definitions : DataEnvironment := []) → Prop where
    | nil {definitions : DataEnvironment} :
        RuntimeEnvironmentHasTypes world [] [] definitions
    | cons
        {definitions : DataEnvironment}
        {value : Value} {type : Ty}
        {environment : Environment} {context : Context} :
        RuntimeValueHasType world value type definitions →
        RuntimeEnvironmentHasTypes world environment context definitions →
        RuntimeEnvironmentHasTypes world
          (value :: environment) (type :: context) definitions

end

/-- Every location is typed against the same world. References are checked by
world lookup rather than by recursively following the store. -/
structure RuntimeStoreHasTypes
    (world : StoreTyping) (store : Store)
    (definitions : DataEnvironment := []) : Prop where
  length_eq : world.length = store.length
  lookup :
    ∀ {location : Location} {elementType : Ty},
      world[location]? = some elementType →
      ∃ value,
        store.read? location = some value ∧
        RuntimeValueHasType world value elementType definitions

structure StoreHasTypes (world : StoreTyping) (store : Store) : Prop where
  length_eq : world.length = store.length
  lookup :
    ∀ {location : Location} {elementType : Ty},
      world[location]? = some elementType →
      ∃ value,
        store.read? location = some value ∧
        CellPayload elementType ∧
        ValueHasType value elementType

/-! ## Typed CEK states -/

inductive FrameHasType
    (world : StoreTyping) :
    Frame → Ty → Ty → (definitions : DataEnvironment := []) → Prop where
  | unaryApply {definitions : DataEnvironment} {op : UnaryOp} :
      FrameHasType world (.unaryApply op) op.operandType op.resultType definitions
  | binaryRight
      {definitions : DataEnvironment}
      {op : BinaryOp} {right : Expr} {environment : Environment}
      {context : Context} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context right op.rightType definitions →
      FrameHasType world (.binaryRight op right environment)
        op.leftType op.resultType definitions
  | binaryApply
      {definitions : DataEnvironment} {op : BinaryOp} {leftValue : Value} :
      RuntimeValueHasType world leftValue op.leftType definitions →
      FrameHasType world (.binaryApply op leftValue)
        op.rightType op.resultType definitions
  | ternarySecond
      {definitions : DataEnvironment} {op : TernaryOp}
      {second third : Expr} {environment : Environment} {context : Context} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context second op.secondType definitions →
      HasType context third op.thirdType definitions →
      FrameHasType world (.ternarySecond op second third environment)
        op.firstType op.resultType definitions
  | ternaryThird
      {definitions : DataEnvironment} {op : TernaryOp}
      {firstValue : Value} {third : Expr} {environment : Environment}
      {context : Context} :
      RuntimeValueHasType world firstValue op.firstType definitions →
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context third op.thirdType definitions →
      FrameHasType world (.ternaryThird op firstValue third environment)
        op.secondType op.resultType definitions
  | ternaryApply
      {definitions : DataEnvironment} {op : TernaryOp}
      {firstValue secondValue : Value} :
      RuntimeValueHasType world firstValue op.firstType definitions →
      RuntimeValueHasType world secondValue op.secondType definitions →
      FrameHasType world (.ternaryApply op firstValue secondValue)
        op.thirdType op.resultType definitions
  | pairRight
      {definitions : DataEnvironment}
      {right : Expr} {environment : Environment} {context : Context}
      {leftType rightType : Ty} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context right rightType definitions →
      FrameHasType world (.pairRight right environment)
        leftType (.product leftType rightType) definitions
  | pairApply
      {definitions : DataEnvironment}
      {leftValue : Value} {leftType rightType : Ty} :
      RuntimeValueHasType world leftValue leftType definitions →
      FrameHasType world (.pairApply leftValue)
        rightType (.product leftType rightType) definitions
  | firstApply {definitions : DataEnvironment} {leftType rightType : Ty} :
      FrameHasType world .firstApply (.product leftType rightType) leftType
        definitions
  | secondApply {definitions : DataEnvironment} {leftType rightType : Ty} :
      FrameHasType world .secondApply (.product leftType rightType) rightType
        definitions
  | inLeftApply
      {definitions : DataEnvironment} {leftType rightType : Ty} :
      FrameHasType world (.inLeftApply rightType)
        leftType (.sum leftType rightType) definitions
  | inRightApply
      {definitions : DataEnvironment} {leftType rightType : Ty} :
      FrameHasType world (.inRightApply leftType)
        rightType (.sum leftType rightType) definitions
  | caseBranches
      {definitions : DataEnvironment}
      {leftBranch rightBranch : Expr} {environment : Environment}
      {context : Context} {leftType rightType resultType : Ty} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType (leftType :: context) leftBranch resultType definitions →
      HasType (rightType :: context) rightBranch resultType definitions →
      FrameHasType world
        (.caseBranches leftBranch rightBranch environment)
        (.sum leftType rightType) resultType definitions
  | newCellApply {definitions : DataEnvironment} {elementType : Ty} :
      FrameHasType world (.newCellApply elementType)
        elementType (.cell elementType) definitions
  | loadCellApply {definitions : DataEnvironment} {elementType : Ty} :
      FrameHasType world .loadCellApply (.cell elementType) elementType definitions
  | storeCellValue
      {definitions : DataEnvironment}
      {valueExpr : Expr} {environment : Environment} {context : Context}
      {elementType : Ty} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context valueExpr elementType definitions →
      FrameHasType world (.storeCellValue valueExpr environment)
        (.cell elementType) .unit definitions
  | storeCellApply
      {definitions : DataEnvironment} {elementType : Ty} {location : Location} :
      world[location]? = some elementType →
      FrameHasType world (.storeCellApply elementType location)
        elementType .unit definitions
  | constructApply
      {definitions : DataEnvironment}
      {constructor : ConstructorId} {payloadType : Ty} :
      definitions.lookupConstructorPayloadType? constructor = some payloadType →
      FrameHasType world (.constructApply constructor) payloadType
        (.namedData constructor.owner) definitions
  | matchDataApply
      {definitions : DataEnvironment}
      {dataType : DataTypeId} {definition : DataDefinition}
      {branches : List Expr} {environment : Environment} {context : Context}
      {resultType : Ty} :
      definitions.lookupDataType? dataType = some definition →
      RuntimeEnvironmentHasTypes world environment context definitions →
      BranchesHaveType context resultType definition.constructorPayloadTypes
        branches definitions →
      FrameHasType world (.matchDataApply dataType branches environment)
        (.namedData dataType) resultType definitions
  | applyArgument
      {definitions : DataEnvironment}
      {argument : Expr} {environment : Environment} {context : Context}
      {parameterType resultType : Ty} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context argument parameterType definitions →
      FrameHasType world (.applyArgument argument environment)
        (.function parameterType resultType) resultType definitions
  | applyClosure
      {definitions : DataEnvironment}
      {parameterType resultType : Ty} {body : Expr}
      {environment : Environment} {context : Context} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType (parameterType :: context) body resultType definitions →
      FrameHasType world
        (.applyClosure parameterType resultType body environment)
        parameterType resultType definitions
  | letBody
      {definitions : DataEnvironment}
      {body : Expr} {environment : Environment} {context : Context}
      {inputType outputType : Ty} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType (inputType :: context) body outputType definitions →
      FrameHasType world (.letBody body environment) inputType outputType
        definitions
  | ifBranches
      {definitions : DataEnvironment}
      {thenBranch elseBranch : Expr} {environment : Environment}
      {context : Context} {outputType : Ty} :
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context thenBranch outputType definitions →
      HasType context elseBranch outputType definitions →
      FrameHasType world
        (.ifBranches thenBranch elseBranch environment) .bool outputType definitions

inductive ContinuationHasType
    (world : StoreTyping) :
    List Frame → Ty → Ty → (definitions : DataEnvironment := []) → Prop where
  | nil {definitions : DataEnvironment} {type : Ty} :
      ContinuationHasType world [] type type definitions
  | cons
      {definitions : DataEnvironment}
      {frame : Frame} {continuation : List Frame}
      {inputType middleType outputType : Ty} :
      FrameHasType world frame inputType middleType definitions →
      ContinuationHasType world continuation middleType outputType definitions →
      ContinuationHasType world (frame :: continuation) inputType outputType
        definitions

inductive StateHasType :
    State → Ty → (definitions : DataEnvironment := []) → Prop where
  | eval
      {definitions : DataEnvironment}
      {world : StoreTyping} {expr : Expr} {environment : Environment}
      {context : Context} {continuation : List Frame} {store : Store}
      {controlType resultType : Ty} :
      RuntimeStoreHasTypes world store definitions →
      RuntimeEnvironmentHasTypes world environment context definitions →
      HasType context expr controlType definitions →
      ContinuationHasType world continuation controlType resultType definitions →
      StateHasType
        ⟨.eval expr environment, continuation, store⟩ resultType definitions
  | ret
      {definitions : DataEnvironment}
      {world : StoreTyping} {value : Value} {continuation : List Frame}
      {store : Store} {controlType resultType : Ty} :
      RuntimeStoreHasTypes world store definitions →
      RuntimeValueHasType world value controlType definitions →
      ContinuationHasType world continuation controlType resultType definitions →
      StateHasType ⟨.ret value, continuation, store⟩ resultType definitions

end Solcore.Core
