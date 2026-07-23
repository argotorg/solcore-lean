import Solcore.Oracle.V2.Schema

set_option autoImplicit false

namespace Solcore.Oracle.V3

/-!
Oracle v3 retains the strict v2 envelope and verdict vocabulary. Its versioned
contract binds that vocabulary to the M1c profile and the Semantic Core v2 wire
language.
-/

def schemaVersion : String := "solcore-oracle/v3"

def capabilitiesSchema : String := "solcore-capabilities/v3"

def checkResultSchema : String := V2.checkResultSchema

def valueObservationSchema : String := V2.valueObservationSchema

abbrev QueryKind := V2.QueryKind

namespace QueryKind

def all : Array QueryKind := V2.QueryKind.all

end QueryKind

abbrev Phase := V2.Phase

abbrev Severity := V2.Severity

abbrev ResourceKind := V2.ResourceKind

abbrev VerdictKind := V2.VerdictKind

abbrev ProfileRef := V2.ProfileRef

abbrev CoreLimits := V2.CoreLimits

def CoreLimits.default : CoreLimits := V2.CoreLimits.default

abbrev Query := V2.Query

abbrev Request := V2.Request

abbrev ResultPayload := V2.ResultPayload

abbrev ObservationPayload := V2.ObservationPayload

abbrev Diagnostic := V2.Diagnostic

abbrev Verdict := V2.Verdict

abbrev Response := V2.Response

structure ProtocolError where
  kind : String := "protocolError"
  schema : String := schemaVersion
  id : Option String := none
  code : String
  path : String := ""
  arguments : Lean.Json := .null
  display : String
  deriving BEq, Lean.ToJson

abbrev DecodeError := V2.DecodeError

def decodeRequest (json : Lean.Json) : Except DecodeError Request :=
  V2.decodeRequest json

def Request.validationErrors (request : Request) : List String :=
  (if request.schema == schemaVersion then [] else ["unknown oracle schema"]) ++
  (if request.spec == Solcore.m1cLanguage.id then [] else ["unknown language specification"]) ++
  (if request.profile.id == Solcore.m1cCoreProfile.id then [] else ["unknown profile"]) ++
  (if request.profile.digest == Solcore.m1cCoreProfileDigest then
    []
  else
    ["profile digest mismatch"]) ++
  (if request.id.isEmpty then ["request id must not be empty"] else []) ++
  match request.query.kind, request.query.program with
  | .capabilities, none => []
  | .capabilities, some _ => ["capabilities query must not contain a program"]
  | .coreCheck, some _ | .coreEval, some _ => []
  | .coreCheck, none | .coreEval, none => ["Core query requires a program"]

def Response.validationErrors (response : Response) : List String :=
  let envelopeErrors :=
    (if response.schema == schemaVersion then [] else ["unknown oracle schema"]) ++
    (if response.id.isEmpty then ["response id must not be empty"] else []) ++
    (if response.spec == Solcore.m1cLanguage.id then [] else ["unknown language specification"]) ++
    (if response.profile.id == Solcore.m1cCoreProfile.id then [] else ["unknown profile"]) ++
    (if response.profile.digest == Solcore.m1cCoreProfileDigest then
      []
    else
      ["profile digest mismatch"])
  let verdictErrors :=
    match response.query, response.verdict with
    | .capabilities, .accepted .protocol result =>
        if result.schema == capabilitiesSchema then [] else ["capability result schema mismatch"]
    | .coreCheck, .accepted .coreChecking result =>
        if result.schema == checkResultSchema then [] else ["Core check result schema mismatch"]
    | .coreCheck, .rejected .coreChecking primary additional
    | .coreEval, .rejected .coreChecking primary additional =>
        if primary.phase == .coreChecking &&
            additional.all (fun diagnostic => diagnostic.phase == .coreChecking) then
          []
        else
          ["Core diagnostic phase mismatch"]
    | .coreCheck, .inconclusive .coreDecoding resource limit consumed
    | .coreEval, .inconclusive .coreDecoding resource limit consumed =>
        let resourceErrors :=
          if resource == .inputDepth || resource == .inputNodes then
            []
          else
            ["Core decoding uses an incompatible resource"]
        resourceErrors ++
        match consumed with
        | none => []
        | some value =>
            if value <= limit then [] else ["consumed resource exceeds declared limit"]
    | .coreEval, .inconclusive .coreEvaluation .evaluationSteps limit consumed =>
        match consumed with
        | none => []
        | some value =>
            if value <= limit then [] else ["consumed resource exceeds declared limit"]
    | .coreEval, .executed observation =>
        if observation.schema == valueObservationSchema then
          []
        else
          ["Core value observation schema mismatch"]
    | _, .internalError _ code =>
        if code.isEmpty then ["internal error code must not be empty"] else []
    | _, _ => ["verdict is incompatible with query"]
  envelopeErrors ++ verdictErrors

def DecodeError.toProtocolError
    (error : DecodeError)
    (id : Option String := none) :
    ProtocolError := {
  id
  code := error.code
  path := error.path
  arguments := error.arguments
  display := error.display
}

end Solcore.Oracle.V3
