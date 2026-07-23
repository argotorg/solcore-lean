import Solcore.Core.Check
import Solcore.Core.Machine
import Solcore.Core.Wire.V2
import Solcore.Oracle.V3.Capabilities

set_option autoImplicit false

namespace Solcore.Oracle.V3

private def profileRef : ProfileRef := {
  id := m1cCoreProfile.id
  digest := m1cCoreProfileDigest
}

private def responseFor
    (request : Request)
    (verdict : Verdict) :
    Response := {
  schema := schemaVersion
  id := request.id
  spec := m1cLanguage.id
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

private def encodeCoreType? (type : Core.Ty) : Option Lean.Json :=
  Core.Wire.V2.encodeType <$> Core.Wire.V2.Ty.ofCore? type

private def checkErrorArguments : Core.CheckErrorData → Option Lean.Json
  | .unboundVariable index contextSize =>
      some (.mkObj [
        ("index", Lean.toJson index),
        ("contextSize", Lean.toJson contextSize)
      ])
  | .expectedBool actual => do
      let actual ← encodeCoreType? actual
      pure (.mkObj [("actual", actual)])
  | .primitiveOperandTypeMismatch expected actual => do
      let expected ← encodeCoreType? expected
      let actual ← encodeCoreType? actual
      pure (.mkObj [
        ("expected", expected),
        ("actual", actual)
      ])
  | .branchTypeMismatch thenType elseType => do
      let thenType ← encodeCoreType? thenType
      let elseType ← encodeCoreType? elseType
      pure (.mkObj [
        ("thenType", thenType),
        ("elseType", elseType)
      ])
  | .declaredResultTypeMismatch declaredType inferredType => do
      let declaredType ← encodeCoreType? declaredType
      let inferredType ← encodeCoreType? inferredType
      pure (.mkObj [
        ("declaredType", declaredType),
        ("inferredType", inferredType)
      ])

private def diagnosticOfCheckError (error : Core.CheckError) : Option Diagnostic := do
  let arguments ← checkErrorArguments error.data
  pure {
    code := error.codeName
    phase := .coreChecking
    path := error.path.toArray.map checkPathStepName
    arguments
  }

private def rejectedFor
    (request : Request)
    (error : Core.CheckError) :
    Response :=
  match diagnosticOfCheckError error with
  | some diagnostic =>
      responseFor request (.rejected .coreChecking diagnostic #[])
  | none =>
      responseFor request (.internalError
        (some .coreChecking)
        "unsupported-core-type-in-diagnostic")

private def coreWirePointer (error : Core.Wire.V2.DecodeError) : String :=
  "/query/program" ++ error.path.toPointer

private def coreWireProtocolError
    (request : Request)
    (error : Core.Wire.V2.DecodeError) :
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
    Except ProtocolError (Except Response Core.Wire.V2.Program) :=
  let limits : Core.Wire.V2.DecodeLimits := {
    maxDepth := request.limits.inputDepth
    maxNodes := request.limits.inputNodes
  }
  match Core.Wire.V2.decodeProgramWith limits json with
  | .ok program => pure (.ok program)
  | .error error =>
      match error.code with
      | .depthLimitExceeded =>
          pure (.error (responseFor request (.inconclusive
            .coreDecoding .inputDepth request.limits.inputDepth none)))
      | .nodeLimitExceeded =>
          pure (.error (responseFor request (.inconclusive
            .coreDecoding .inputNodes request.limits.inputNodes none)))
      | _ => throw (coreWireProtocolError request error)

private def handleCheck
    (request : Request)
    (program : Core.Wire.V2.Program) :
    Response :=
  match program.toCore.checkDetailed with
  | .error error => rejectedFor request error
  | .ok _ =>
      responseFor request (.accepted .coreChecking {
        schema := checkResultSchema
        value := .mkObj [("resultType", Core.Wire.V2.encodeType program.resultType)]
      })

private def handleEval
    (request : Request)
    (program : Core.Wire.V2.Program) :
    Response :=
  let coreProgram := program.toCore
  match coreProgram.checkDetailed with
  | .error error => rejectedFor request error
  | .ok _ =>
      match coreProgram.run request.limits.evaluationSteps with
      | .done value =>
          if value.type == coreProgram.resultType then
            match Core.Wire.V2.Value.ofCore? value with
            | some wireValue =>
                responseFor request (.executed {
                  schema := valueObservationSchema
                  value := .mkObj [
                    ("resultType", Core.Wire.V2.encodeType program.resultType),
                    ("value", Core.Wire.V2.encodeValue wireValue)
                  ]
                })
            | none =>
                responseFor request (.internalError
                  (some .coreEvaluation)
                  "unsupported-core-value")
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

end Solcore.Oracle.V3
