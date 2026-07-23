import Solcore.Core.Check
import Solcore.Core.Machine
import Solcore.Core.Wire
import Solcore.Oracle.V2.Capabilities

set_option autoImplicit false

namespace Solcore.Oracle.V2

private def profileRef : ProfileRef := {
  id := m1aCoreProfile.id
  digest := m1aCoreProfileDigest
}

private def responseFor
    (request : Request)
    (verdict : Verdict) :
    Response := {
  schema := schemaVersion
  id := request.id
  spec := m1aLanguage.id
  profile := profileRef
  query := request.query.kind
  verdict
}

private def checkPathStepName : Core.CheckPathStep → String
  | .unaryOperand => "unaryOperand"
  | .binaryLeft => "binaryLeft"
  | .binaryRight => "binaryRight"
  | .letValue => "letValue"
  | .letBody => "letBody"
  | .ifCondition => "ifCondition"
  | .ifThen => "ifThen"
  | .ifElse => "ifElse"

private def checkErrorArguments : Core.CheckErrorData → Lean.Json
  | .unboundVariable index contextSize =>
      .mkObj [
        ("index", Lean.toJson index),
        ("contextSize", Lean.toJson contextSize)
      ]
  | .expectedBool actual =>
      .mkObj [("actual", Core.Wire.V1.encodeType actual)]
  | .primitiveOperandTypeMismatch expected actual =>
      .mkObj [
        ("expected", Core.Wire.V1.encodeType expected),
        ("actual", Core.Wire.V1.encodeType actual)
      ]
  | .branchTypeMismatch thenType elseType =>
      .mkObj [
        ("thenType", Core.Wire.V1.encodeType thenType),
        ("elseType", Core.Wire.V1.encodeType elseType)
      ]
  | .declaredResultTypeMismatch declaredType inferredType =>
      .mkObj [
        ("declaredType", Core.Wire.V1.encodeType declaredType),
        ("inferredType", Core.Wire.V1.encodeType inferredType)
      ]

private def diagnosticOfCheckError (error : Core.CheckError) : Diagnostic := {
  code := error.codeName
  phase := .coreChecking
  path := error.path.toArray.map checkPathStepName
  arguments := checkErrorArguments error.data
}

private def rejectedFor
    (request : Request)
    (error : Core.CheckError) :
    Response :=
  responseFor request (.rejected .coreChecking (diagnosticOfCheckError error) #[])

private def coreWirePointer (error : Core.Wire.V1.DecodeError) : String :=
  "/query/program" ++ error.path.toPointer

private def coreWireProtocolError
    (request : Request)
    (error : Core.Wire.V1.DecodeError) :
    ProtocolError := {
  id := some request.id
  code := "core.wire." ++ error.code.wireName
  path := coreWirePointer error
  arguments := error.arguments
  display := "invalid Semantic Core program"
}

private def decodeProgram
    (request : Request)
    (json : Lean.Json) :
    Except ProtocolError (Except Response Core.Program) :=
  let limits : Core.Wire.V1.DecodeLimits := {
    maxDepth := request.limits.inputDepth
    maxNodes := request.limits.inputNodes
  }
  match Core.Wire.V1.decodeProgramWith limits json with
  | .ok program => pure (.ok program.toCore)
  | .error error =>
      match error.code with
      | .depthLimitExceeded =>
          pure (.error (responseFor request (.inconclusive
            .coreDecoding .inputDepth request.limits.inputDepth none)))
      | .nodeLimitExceeded =>
          pure (.error (responseFor request (.inconclusive
            .coreDecoding .inputNodes request.limits.inputNodes none)))
      | _ => throw (coreWireProtocolError request error)

private def handleCheck (request : Request) (program : Core.Program) : Response :=
  match program.checkDetailed with
  | .error error => rejectedFor request error
  | .ok resultType =>
      responseFor request (.accepted .coreChecking {
        schema := checkResultSchema
        value := .mkObj [("resultType", Core.Wire.V1.encodeType resultType)]
      })

private def handleEval (request : Request) (program : Core.Program) : Response :=
  match program.checkDetailed with
  | .error error => rejectedFor request error
  | .ok _ =>
      match program.run request.limits.evaluationSteps with
      | .done value =>
          if value.type == program.resultType then
            responseFor request (.executed {
              schema := valueObservationSchema
              value := .mkObj [
                ("resultType", Core.Wire.V1.encodeType program.resultType),
                ("value", Core.Wire.V1.encodeValue value)
              ]
            })
          else
            responseFor request (.internalError
              (some .coreEvaluation)
              "typed-core-result-type-mismatch")
      | .outOfFuel =>
          responseFor request (.inconclusive
            .coreEvaluation
            .evaluationSteps
            request.limits.evaluationSteps
            (some request.limits.evaluationSteps))
      | .fault _ =>
          responseFor request (.internalError
            (some .coreEvaluation)
            "typed-core-machine-fault")

def handle (request : Request) : Except ProtocolError Response := do
  match request.validationErrors with
  | error :: _ =>
      throw {
        id := if request.id.isEmpty then none else some request.id
        code := "invalid-request"
        display := error
      }
  | [] =>
      let response ←
        match request.query.kind, request.query.program with
        | .capabilities, none =>
            pure (responseFor request (.accepted .protocol {
              schema := capabilitiesSchema
              value := Lean.toJson capabilityReport
            }))
        | .coreCheck, some json =>
            match ← decodeProgram request json with
            | .error response => pure response
            | .ok program => pure (handleCheck request program)
        | .coreEval, some json =>
            match ← decodeProgram request json with
            | .error response => pure response
            | .ok program => pure (handleEval request program)
        | _, _ =>
            throw {
              id := some request.id
              code := "invalid-request"
              display := "query/program invariant violated"
            }
      match response.validationErrors with
      | [] => pure response
      | _ =>
          pure (responseFor request (.internalError none "oracle-response-invariant"))

end Solcore.Oracle.V2
