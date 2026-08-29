import Solcore.Core.HostMachine
import Solcore.Core.HostSafety

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
      CellPayload elementType →
      HostFrameHasType world (.newCellApply elementType) elementType
        (.cell elementType) definitions
  | loadCellApply {definitions : DataEnvironment} {elementType : Ty} :
      CellPayload elementType →
      HostFrameHasType world .loadCellApply (.cell elementType) elementType definitions
  | storeCellValue {definitions : DataEnvironment} {valueExpr : Expr}
      {environment : Environment} {context : Context} {elementType : Ty} :
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType context valueExpr elementType definitions →
      CellPayload elementType →
      HostFrameHasType world (.storeCellValue valueExpr environment)
        (.cell elementType) .unit definitions
  | storeCellApply {definitions : DataEnvironment} {elementType : Ty}
      {location : Location} :
      world[location]? = some elementType → CellPayload elementType →
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

theorem HostFrameHasType.weaken {definitions : DataEnvironment}
    {initial future : StoreTyping} (extension : WorldExtends initial future)
    {frame : Frame} {inputType outputType : Ty}
    (typing : HostFrameHasType initial frame inputType outputType definitions) :
    HostFrameHasType future frame inputType outputType definitions := by
  cases typing with
  | unaryApply => exact .unaryApply
  | binaryRight env expr => exact .binaryRight (env.weaken extension) expr
  | binaryApply value => exact .binaryApply (value.weaken extension)
  | ternarySecond env second third => exact .ternarySecond (env.weaken extension) second third
  | ternaryThird first env third => exact .ternaryThird (first.weaken extension) (env.weaken extension) third
  | ternaryApply first second => exact .ternaryApply (first.weaken extension) (second.weaken extension)
  | pairRight env right => exact .pairRight (env.weaken extension) right
  | pairApply left => exact .pairApply (left.weaken extension)
  | firstApply => exact .firstApply
  | secondApply => exact .secondApply
  | inLeftApply => exact .inLeftApply
  | inRightApply => exact .inRightApply
  | caseBranches env left right => exact .caseBranches (env.weaken extension) left right
  | newCellApply payload => exact .newCellApply payload
  | loadCellApply payload => exact .loadCellApply payload
  | storeCellValue env value payload => exact .storeCellValue (env.weaken extension) value payload
  | storeCellApply found payload => exact .storeCellApply (extension.lookup found) payload
  | constructApply lookup => exact .constructApply lookup
  | matchDataApply lookup env branches => exact .matchDataApply lookup (env.weaken extension) branches
  | applyArgument env argument => exact .applyArgument (env.weaken extension) argument
  | applyClosure env body => exact .applyClosure (env.weaken extension) body
  | hostApply => exact .hostApply
  | letBody env body => exact .letBody (env.weaken extension) body
  | ifBranches env thenType elseType => exact .ifBranches (env.weaken extension) thenType elseType

theorem HostContinuationHasType.weaken {definitions : DataEnvironment}
    {initial future : StoreTyping} (extension : WorldExtends initial future)
    {continuation : List Frame} {inputType outputType : Ty}
    (typing : HostContinuationHasType initial continuation inputType outputType definitions) :
    HostContinuationHasType future continuation inputType outputType definitions := by
  induction typing with
  | nil => exact .nil
  | cons frame _ tail => exact .cons (frame.weaken extension) tail

inductive HostStateHasType :
    State → Ty → (definitions : DataEnvironment := []) → Prop where
  | eval {definitions : DataEnvironment} {world : StoreTyping} {expr : Expr}
      {environment : Environment} {context : Context} {continuation : List Frame}
      {store : Store} {controlType resultType : Ty} :
      StoreHasTypes world store →
      HostRuntimeEnvironmentHasTypes world environment context definitions →
      HasType context expr controlType definitions →
      HostContinuationHasType world continuation controlType resultType definitions →
      HostStateHasType ⟨.eval expr environment, continuation, store⟩ resultType definitions
  | ret {definitions : DataEnvironment} {world : StoreTyping} {value : Value}
      {continuation : List Frame} {store : Store} {controlType resultType : Ty} :
      StoreHasTypes world store →
      HostRuntimeValueHasType world value controlType definitions →
      HostContinuationHasType world continuation controlType resultType definitions →
      HostStateHasType ⟨.ret value, continuation, store⟩ resultType definitions

/-- A suspended request preserves a typed store and expects its exact response type. -/
inductive HostSuspensionHasType :
    HostSuspension → Ty → (definitions : DataEnvironment := []) → Prop where
  | intro {definitions : DataEnvironment} {world : StoreTyping}
      {request : HostRequest} {continuation : List Frame} {store : Store}
      {resultType : Ty} :
      StoreHasTypes world store →
      HostContinuationHasType world continuation request.responseType
        resultType definitions →
      HostSuspensionHasType ⟨request, continuation, store⟩ resultType definitions

theorem HostRequest.responseValue_hasType
    (request : HostRequest) (response : request.Response)
    (world : StoreTyping) (definitions : DataEnvironment := []) :
    HostRuntimeValueHasType world (request.responseValue response)
      request.responseType definitions := by
  cases request with
  | storageRead => exact .word
  | storageWrite => exact .unit
  | storageAddress => exact .word
  | codeAddress => exact .word
  | callValue => exact .word
  | callerAddress => exact .word

theorem HostSuspensionHasType.resume {definitions : DataEnvironment}
    {suspension : HostSuspension} {resultType : Ty}
    (typing : HostSuspensionHasType suspension resultType definitions)
    (response : suspension.request.Response) :
    HostStateHasType (suspension.resume response) resultType definitions := by
  cases typing with
  | intro storeTyping continuationTyping =>
      exact .ret storeTyping
        (HostRequest.responseValue_hasType _ response _ definitions)
        continuationTyping

end Solcore.Core
