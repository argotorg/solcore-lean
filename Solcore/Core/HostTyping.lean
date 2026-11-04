import Solcore.Core.RuntimeTyping
import Solcore.Core.Host
import Solcore.Core.HostMachine

/-!
# Typing with host capabilities

The relations of `RuntimeTyping` with host functions as values: `HostRuntimeValueHasType`,
`HostRuntimeEnvironmentHasTypes`, `HostStoreHasTypes`, `HostFrameHasType`,
`HostContinuationHasType`, `HostStateHasType` and `HostSuspensionHasType`.
-/

section
-- leanmerge: from Solcore.Core.Internal.HostValueTyping
/-! Runtime value typing extended additively with fixed host capabilities. -/

set_option autoImplicit false

namespace Solcore.Core

mutual

  /-- Store-aware value typing that additionally admits host functions. -/
  inductive HostRuntimeValueHasType
      (world : StoreTyping) :
      Value → Ty → (definitions : DataEnvironment := []) → Prop where
    | unit {definitions : DataEnvironment} :
        HostRuntimeValueHasType world .unit .unit definitions
    | bool {definitions : DataEnvironment} {value : Bool} :
        HostRuntimeValueHasType world (.bool value) .bool definitions
    | word {definitions : DataEnvironment} {value : Word} :
        HostRuntimeValueHasType world (.word value) .word definitions
    | integer {definitions : DataEnvironment} {value : Int} :
        HostRuntimeValueHasType world (.integer value) .integer definitions
    | hostFunction
        {definitions : DataEnvironment} {function : HostFunction} :
        HostRuntimeValueHasType world
          (.hostFunction function) function.functionType definitions
    | pair
        {definitions : DataEnvironment}
        {left right : Value} {leftType rightType : Ty} :
        HostRuntimeValueHasType world left leftType definitions →
        HostRuntimeValueHasType world right rightType definitions →
        HostRuntimeValueHasType world
          (.pair left right) (.product leftType rightType) definitions
    | inLeft
        {definitions : DataEnvironment}
        {payload : Value} {leftType rightType : Ty} :
        HostRuntimeValueHasType world payload leftType definitions →
        HostRuntimeValueHasType world
          (.inLeft rightType payload) (.sum leftType rightType) definitions
    | inRight
        {definitions : DataEnvironment}
        {payload : Value} {leftType rightType : Ty} :
        HostRuntimeValueHasType world payload rightType definitions →
        HostRuntimeValueHasType world
          (.inRight leftType payload) (.sum leftType rightType) definitions
    | closure
        {definitions : DataEnvironment}
        {parameterType resultType : Ty} {body : Expr}
        {environment : Environment} {context : Context} :
        HostRuntimeEnvironmentHasTypes world environment context definitions →
        HasType (parameterType :: context) body resultType definitions →
        HostRuntimeValueHasType world
          (.closure parameterType resultType body environment)
          (.function parameterType resultType) definitions
    | cellRef
        {definitions : DataEnvironment}
        {elementType : Ty} {location : Location} :
        world[location]? = some elementType →
        HostRuntimeValueHasType world
          (.cellRef elementType location) (.cell elementType) definitions
    | constructed
        {definitions : DataEnvironment}
        {constructor : ConstructorId} {payload : Value} {payloadType : Ty} :
        definitions.lookupConstructorPayloadType? constructor = some payloadType →
        HostRuntimeValueHasType world payload payloadType definitions →
        HostRuntimeValueHasType world
          (.constructed constructor payload) (.namedData constructor.owner)
          definitions

  /-- Positional typing for environments that may contain host functions. -/
  inductive HostRuntimeEnvironmentHasTypes
      (world : StoreTyping) :
      Environment → Context → (definitions : DataEnvironment := []) → Prop where
    | nil {definitions : DataEnvironment} :
        HostRuntimeEnvironmentHasTypes world [] [] definitions
    | cons
        {definitions : DataEnvironment}
        {value : Value} {type : Ty}
        {environment : Environment} {context : Context} :
        HostRuntimeValueHasType world value type definitions →
        HostRuntimeEnvironmentHasTypes world environment context definitions →
        HostRuntimeEnvironmentHasTypes world
          (value :: environment) (type :: context) definitions

end

/-- The Core-local store may hold closures that capture host capabilities.
Cell references are checked against the world without recursively following them,
so this relation also supports cycles through cells. -/
structure HostStoreHasTypes
    (world : StoreTyping) (store : Store)
    (definitions : DataEnvironment := []) : Prop where
  length_eq : world.length = store.length
  lookup :
    ∀ {location : Location} {elementType : Ty},
      world[location]? = some elementType →
      ∃ value,
        store.read? location = some value ∧
        HostRuntimeValueHasType world value elementType definitions

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.Internal.HostStateTyping
/-! Typing for CEK states that may carry fixed host capabilities. -/

set_option autoImplicit false

namespace Solcore.Core

inductive HostFrameHasType
    (world : StoreTyping) :
    Frame → Ty → Ty → (definitions : DataEnvironment := []) → Prop where
  | unaryApply {definitions : DataEnvironment} {op : UnaryOp} :
      HostFrameHasType world (.unaryApply op) op.operandType op.resultType definitions
  | binaryRight {definitions : DataEnvironment} {op : BinaryOp}
      {right : Expr} {environment : Environment} {context : Context} :
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType context right op.rightType definitions →
      HostFrameHasType world (.binaryRight op right environment)
        op.leftType op.resultType definitions
  | binaryApply {definitions : DataEnvironment} {op : BinaryOp} {left : Value} :
      HostRuntimeValueHasType world left op.leftType definitions →
      HostFrameHasType world (.binaryApply op left) op.rightType op.resultType definitions
  | ternarySecond {definitions : DataEnvironment} {op : TernaryOp}
      {second third : Expr} {environment : Environment} {context : Context} :
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType context second op.secondType definitions →
      HasType context third op.thirdType definitions →
      HostFrameHasType world (.ternarySecond op second third environment)
        op.firstType op.resultType definitions
  | ternaryThird {definitions : DataEnvironment} {op : TernaryOp}
      {first : Value} {third : Expr} {environment : Environment} {context : Context} :
      HostRuntimeValueHasType world first op.firstType definitions →
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType context third op.thirdType definitions →
      HostFrameHasType world (.ternaryThird op first third environment)
        op.secondType op.resultType definitions
  | ternaryApply {definitions : DataEnvironment} {op : TernaryOp}
      {first second : Value} :
      HostRuntimeValueHasType world first op.firstType definitions →
      HostRuntimeValueHasType world second op.secondType definitions →
      HostFrameHasType world (.ternaryApply op first second)
        op.thirdType op.resultType definitions
  | pairRight {definitions : DataEnvironment} {right : Expr}
      {environment : Environment} {context : Context} {leftType rightType : Ty} :
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType context right rightType definitions →
      HostFrameHasType world (.pairRight right environment) leftType
        (.product leftType rightType) definitions
  | pairApply {definitions : DataEnvironment} {left : Value} {leftType rightType : Ty} :
      HostRuntimeValueHasType world left leftType definitions →
      HostFrameHasType world (.pairApply left) rightType
        (.product leftType rightType) definitions
  | firstApply {definitions : DataEnvironment} {leftType rightType : Ty} :
      HostFrameHasType world .firstApply (.product leftType rightType) leftType definitions
  | secondApply {definitions : DataEnvironment} {leftType rightType : Ty} :
      HostFrameHasType world .secondApply (.product leftType rightType) rightType definitions
  | inLeftApply {definitions : DataEnvironment} {leftType rightType : Ty} :
      HostFrameHasType world (.inLeftApply rightType) leftType
        (.sum leftType rightType) definitions
  | inRightApply {definitions : DataEnvironment} {leftType rightType : Ty} :
      HostFrameHasType world (.inRightApply leftType) rightType
        (.sum leftType rightType) definitions
  | caseBranches {definitions : DataEnvironment} {leftBranch rightBranch : Expr}
      {environment : Environment} {context : Context}
      {leftType rightType resultType : Ty} :
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType (leftType :: context) leftBranch resultType definitions →
      HasType (rightType :: context) rightBranch resultType definitions →
      HostFrameHasType world (.caseBranches leftBranch rightBranch environment)
        (.sum leftType rightType) resultType definitions
  | newCellApply {definitions : DataEnvironment} {elementType : Ty} :
      HostFrameHasType world (.newCellApply elementType) elementType
        (.cell elementType) definitions
  | loadCellApply {definitions : DataEnvironment} {elementType : Ty} :
      HostFrameHasType world .loadCellApply (.cell elementType) elementType definitions
  | storeCellValue {definitions : DataEnvironment} {valueExpr : Expr}
      {environment : Environment} {context : Context} {elementType : Ty} :
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType context valueExpr elementType definitions →
      HostFrameHasType world (.storeCellValue valueExpr environment)
        (.cell elementType) .unit definitions
  | storeCellApply {definitions : DataEnvironment} {elementType : Ty}
      {location : Location} :
      world[location]? = some elementType →
      HostFrameHasType world (.storeCellApply elementType location)
        elementType .unit definitions
  | constructApply {definitions : DataEnvironment} {constructor : ConstructorId}
      {payloadType : Ty} :
      definitions.lookupConstructorPayloadType? constructor = some payloadType →
      HostFrameHasType world (.constructApply constructor) payloadType
        (.namedData constructor.owner) definitions
  | matchDataApply {definitions : DataEnvironment} {dataType : DataTypeId}
      {definition : DataDefinition} {branches : List Expr}
      {environment : Environment} {context : Context} {resultType : Ty} :
      definitions.lookupDataType? dataType = some definition →
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      BranchesHaveType context resultType definition.constructorPayloadTypes
        branches definitions →
      HostFrameHasType world (.matchDataApply dataType branches environment)
        (.namedData dataType) resultType definitions
  | applyArgument {definitions : DataEnvironment} {argument : Expr}
      {environment : Environment} {context : Context} {parameterType resultType : Ty} :
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType context argument parameterType definitions →
      HostFrameHasType world (.applyArgument argument environment)
        (.function parameterType resultType) resultType definitions
  | applyClosure {definitions : DataEnvironment} {parameterType resultType : Ty}
      {body : Expr} {environment : Environment} {context : Context} :
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType (parameterType :: context) body resultType definitions →
      HostFrameHasType world (.applyClosure parameterType resultType body environment)
        parameterType resultType definitions
  | hostApply {definitions : DataEnvironment} {function : HostFunction} :
      HostFrameHasType world (.hostApply function)
        function.parameterType function.resultType definitions
  | letBody {definitions : DataEnvironment} {body : Expr}
      {environment : Environment} {context : Context} {inputType outputType : Ty} :
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType (inputType :: context) body outputType definitions →
      HostFrameHasType world (.letBody body environment) inputType outputType definitions
  | ifBranches {definitions : DataEnvironment} {thenBranch elseBranch : Expr}
      {environment : Environment} {context : Context} {outputType : Ty} :
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType context thenBranch outputType definitions →
      HasType context elseBranch outputType definitions →
      HostFrameHasType world (.ifBranches thenBranch elseBranch environment)
        .bool outputType definitions

inductive HostContinuationHasType
    (world : StoreTyping) :
    List Frame → Ty → Ty → (definitions : DataEnvironment := []) → Prop where
  | nil {definitions : DataEnvironment} {type : Ty} :
      HostContinuationHasType world [] type type definitions
  | cons {definitions : DataEnvironment} {frame : Frame}
      {continuation : List Frame} {inputType middleType outputType : Ty} :
      HostFrameHasType world frame inputType middleType definitions →
      HostContinuationHasType world continuation middleType outputType definitions →
      HostContinuationHasType world (frame :: continuation)
        inputType outputType definitions

inductive HostStateHasType :
    State → Ty → (definitions : DataEnvironment := []) → Prop where
  | eval {definitions : DataEnvironment} {world : StoreTyping} {expr : Expr}
      {environment : Environment} {context : Context} {continuation : List Frame}
      {store : Store} {controlType resultType : Ty} :
      HostStoreHasTypes world store definitions →
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType context expr controlType definitions →
      HostContinuationHasType world continuation controlType resultType definitions →
      HostStateHasType ⟨.eval expr environment, continuation, store⟩ resultType definitions
  | ret {definitions : DataEnvironment} {world : StoreTyping} {value : Value}
      {continuation : List Frame} {store : Store} {controlType resultType : Ty} :
      HostStoreHasTypes world store definitions →
      HostRuntimeValueHasType world value controlType definitions →
      HostContinuationHasType world continuation controlType resultType definitions →
      HostStateHasType ⟨.ret value, continuation, store⟩ resultType definitions

/-- A suspended request preserves a typed store and expects its exact response type. -/
inductive HostSuspensionHasType :
    HostSuspension → Ty → (definitions : DataEnvironment := []) → Prop where
  | intro {definitions : DataEnvironment} {world : StoreTyping}
      {request : HostRequest} {continuation : List Frame} {store : Store}
      {resultType : Ty} :
      HostStoreHasTypes world store definitions →
      HostContinuationHasType world continuation request.responseType
        resultType definitions →
      HostSuspensionHasType ⟨request, continuation, store⟩ resultType definitions

end Solcore.Core
end
