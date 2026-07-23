import Lean.Data.Json
import Solcore.Foundation.Json
import Solcore.Profile

set_option autoImplicit false

namespace Solcore.Oracle.V2

def schemaVersion : String := "solcore-oracle/v2"

def capabilitiesSchema : String := "solcore-capabilities/v2"

def checkResultSchema : String := "solcore-core-check-result/v1"

def valueObservationSchema : String := "solcore-core-value-observation/v1"

inductive QueryKind where
  | capabilities
  | coreCheck
  | coreEval
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

namespace QueryKind

def all : Array QueryKind := #[.capabilities, .coreCheck, .coreEval]

end QueryKind

inductive Phase where
  | protocol
  | coreDecoding
  | coreChecking
  | coreEvaluation
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive Severity where
  | error
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive ResourceKind where
  | inputDepth
  | inputNodes
  | evaluationSteps
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive VerdictKind where
  | accepted
  | rejected
  | inconclusive
  | executed
  | internalError
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure ProfileRef where
  id : String
  digest : String
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure CoreLimits where
  inputDepth : Nat
  inputNodes : Nat
  evaluationSteps : Nat
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

def CoreLimits.default : CoreLimits := {
  inputDepth := 256
  inputNodes := 100000
  evaluationSteps := 1000000
}

structure Query where
  kind : QueryKind
  program : Option Lean.Json := none
  deriving BEq

protected def Query.toJson (query : Query) : Lean.Json :=
  match query.kind, query.program with
  | .capabilities, _ =>
      .mkObj [("kind", Lean.toJson QueryKind.capabilities)]
  | .coreCheck, some program =>
      .mkObj [
        ("kind", Lean.toJson QueryKind.coreCheck),
        ("program", program)
      ]
  | .coreEval, some program =>
      .mkObj [
        ("kind", Lean.toJson QueryKind.coreEval),
        ("program", program)
      ]
  | .coreCheck, none =>
      .mkObj [("kind", Lean.toJson QueryKind.coreCheck)]
  | .coreEval, none =>
      .mkObj [("kind", Lean.toJson QueryKind.coreEval)]

instance : Lean.ToJson Query := ⟨Query.toJson⟩

structure Request where
  schema : String
  id : String
  spec : String
  profile : ProfileRef
  limits : CoreLimits := CoreLimits.default
  query : Query
  deriving BEq, Lean.ToJson

structure ResultPayload where
  schema : String
  value : Lean.Json
  deriving BEq, Lean.ToJson

structure ObservationPayload where
  schema : String
  value : Lean.Json
  deriving BEq, Lean.ToJson

structure Diagnostic where
  code : String
  severity : Severity := .error
  phase : Phase
  path : Array String
  arguments : Lean.Json := .null
  display : Option String := none
  deriving BEq, Lean.ToJson

inductive Verdict where
  | accepted (phase : Phase) (result : ResultPayload)
  | rejected (phase : Phase) (primary : Diagnostic) (additional : Array Diagnostic)
  | inconclusive
      (phase : Phase)
      (resource : ResourceKind)
      (limit : Nat)
      (consumed : Option Nat)
  | executed (observation : ObservationPayload)
  | internalError (phase : Option Phase) (code : String)
  deriving BEq

namespace Verdict

def kind : Verdict → VerdictKind
  | .accepted .. => .accepted
  | .rejected .. => .rejected
  | .inconclusive .. => .inconclusive
  | .executed .. => .executed
  | .internalError .. => .internalError

protected def toJson : Verdict → Lean.Json
  | .accepted phase result =>
      .mkObj [
        ("kind", Lean.toJson VerdictKind.accepted),
        ("phase", Lean.toJson phase),
        ("result", Lean.toJson result)
      ]
  | .rejected phase primary additional =>
      .mkObj [
        ("kind", Lean.toJson VerdictKind.rejected),
        ("phase", Lean.toJson phase),
        ("diagnostics", Lean.toJson (#[primary] ++ additional))
      ]
  | .inconclusive phase resource limit consumed =>
      .mkObj [
        ("kind", Lean.toJson VerdictKind.inconclusive),
        ("phase", Lean.toJson phase),
        ("resource", Lean.toJson resource),
        ("limit", Lean.toJson limit),
        ("consumed", Lean.toJson consumed)
      ]
  | .executed observation =>
      .mkObj [
        ("kind", Lean.toJson VerdictKind.executed),
        ("observation", Lean.toJson observation)
      ]
  | .internalError phase code =>
      .mkObj [
        ("kind", Lean.toJson VerdictKind.internalError),
        ("phase", Lean.toJson phase),
        ("code", Lean.toJson code)
      ]

end Verdict

instance : Lean.ToJson Verdict := ⟨Verdict.toJson⟩

structure Response where
  schema : String
  id : String
  spec : String
  profile : ProfileRef
  query : QueryKind
  verdict : Verdict
  deriving BEq, Lean.ToJson

structure ProtocolError where
  kind : String := "protocolError"
  schema : String := schemaVersion
  id : Option String := none
  code : String
  path : String := ""
  arguments : Lean.Json := .null
  display : String
  deriving BEq, Lean.ToJson

structure DecodeError where
  code : String
  path : String
  arguments : Lean.Json := .null
  display : String
  deriving BEq

private def ensureOnlyKeys
    (json : Lean.Json)
    (path : String)
    (allowed : List String) :
    Except DecodeError Unit := do
  let object ←
    match json.getObj? with
    | .ok object => pure object
    | .error message =>
        throw {
          code := "expected-object"
          path
          display := message
        }
  match object.keys.find? (fun key => !allowed.contains key) with
  | some key =>
      throw {
        code := "unknown-field"
        path := s!"{path}/{key}"
        arguments := .mkObj [("field", Lean.toJson key)]
        display := s!"unknown field: {key}"
      }
  | none => pure ()

private def ensureRequiredKeys
    (json : Lean.Json)
    (path : String)
    (required : List String) :
    Except DecodeError Unit := do
  let object ←
    match json.getObj? with
    | .ok object => pure object
    | .error message =>
        throw {
          code := "expected-object"
          path
          display := message
        }
  match required.find? (fun key => !object.contains key) with
  | some key =>
      throw {
        code := "missing-field"
        path := s!"{path}/{key}"
        arguments := .mkObj [("field", Lean.toJson key)]
        display := s!"missing field: {key}"
      }
  | none => pure ()

private def getAs
    {α : Type}
    [Lean.FromJson α]
    (json : Lean.Json)
    (path field : String) :
    Except DecodeError α :=
  match json.getObjValAs? α field with
  | .ok value => pure value
  | .error message =>
      throw {
        code := "invalid-field"
        path := s!"{path}/{field}"
        arguments := .mkObj [("field", Lean.toJson field)]
        display := message
      }

private def getJson
    (json : Lean.Json)
    (path field : String) :
    Except DecodeError Lean.Json :=
  match json.getObjVal? field with
  | .ok value => pure value
  | .error message =>
      throw {
        code := "invalid-field"
        path := s!"{path}/{field}"
        arguments := .mkObj [("field", Lean.toJson field)]
        display := message
      }

private def getNat
    (json : Lean.Json)
    (path field : String) :
    Except DecodeError Nat := do
  let value ← getJson json path field
  match Foundation.jsonNatural? value with
  | some result => pure result
  | none =>
      throw {
        code := "invalid-field"
        path := s!"{path}/{field}"
        arguments := .mkObj [
          ("field", Lean.toJson field),
          ("expected", "non-negative integer")
        ]
        display := "non-negative integer expected"
      }

private def decodeProfile (json : Lean.Json) : Except DecodeError ProfileRef := do
  ensureOnlyKeys json "/profile" ["id", "digest"]
  ensureRequiredKeys json "/profile" ["id", "digest"]
  return {
    id := ← getAs json "/profile" "id"
    digest := ← getAs json "/profile" "digest"
  }

private def decodeLimits (json : Lean.Json) : Except DecodeError CoreLimits := do
  ensureOnlyKeys json "/limits" ["inputDepth", "inputNodes", "evaluationSteps"]
  ensureRequiredKeys json "/limits" ["inputDepth", "inputNodes", "evaluationSteps"]
  return {
    inputDepth := ← getNat json "/limits" "inputDepth"
    inputNodes := ← getNat json "/limits" "inputNodes"
    evaluationSteps := ← getNat json "/limits" "evaluationSteps"
  }

private def decodeQuery (json : Lean.Json) : Except DecodeError Query := do
  ensureRequiredKeys json "/query" ["kind"]
  let kind : QueryKind ← getAs json "/query" "kind"
  match kind with
  | .capabilities =>
      ensureOnlyKeys json "/query" ["kind"]
      ensureRequiredKeys json "/query" ["kind"]
      return { kind }
  | .coreCheck | .coreEval =>
      ensureOnlyKeys json "/query" ["kind", "program"]
      ensureRequiredKeys json "/query" ["kind", "program"]
      return {
        kind
        program := some (← getJson json "/query" "program")
      }

def decodeRequest (json : Lean.Json) : Except DecodeError Request := do
  ensureOnlyKeys json "" ["schema", "id", "spec", "profile", "limits", "query"]
  ensureRequiredKeys json "" ["schema", "id", "spec", "profile", "limits", "query"]
  return {
    schema := ← getAs json "" "schema"
    id := ← getAs json "" "id"
    spec := ← getAs json "" "spec"
    profile := ← decodeProfile (← getJson json "" "profile")
    limits := ← decodeLimits (← getJson json "" "limits")
    query := ← decodeQuery (← getJson json "" "query")
  }

def Request.validationErrors (request : Request) : List String :=
  (if request.schema == schemaVersion then [] else ["unknown oracle schema"]) ++
  (if request.spec == Solcore.m1aLanguage.id then [] else ["unknown language specification"]) ++
  (if request.profile.id == Solcore.m1aCoreProfile.id then [] else ["unknown profile"]) ++
  (if request.profile.digest == Solcore.m1aCoreProfileDigest then
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
    (if response.spec == Solcore.m1aLanguage.id then [] else ["unknown language specification"]) ++
    (if response.profile.id == Solcore.m1aCoreProfile.id then [] else ["unknown profile"]) ++
    (if response.profile.digest == Solcore.m1aCoreProfileDigest then
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

end Solcore.Oracle.V2
