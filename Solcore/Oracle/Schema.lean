import Lean.Data.Json
import Solcore.Baseline
import Solcore.Feature

set_option autoImplicit false

namespace Solcore.Oracle

def schemaVersion : String := "solcore-oracle/v1"

def capabilitiesSchema : String := "solcore-capabilities/v1"

private def hasDuplicates {α : Type} [BEq α] : List α → Bool
  | [] => false
  | item :: rest => rest.contains item || hasDuplicates rest

def isSafeSourcePath (path : String) : Bool :=
  let parts := path.splitOn "/"
  !path.isEmpty &&
    path.endsWith ".solc" &&
    !path.startsWith "/" &&
    !path.contains '\\' &&
    !path.contains ':' &&
    !path.contains (Char.ofNat 0) &&
    parts.all fun part => !part.isEmpty && part != "." && part != ".."

inductive QueryKind where
  | capabilities
  | parse
  | resolve
  | check
  | elaborate
  | eval
  | contract
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

namespace QueryKind

def all : Array QueryKind :=
  #[.capabilities, .parse, .resolve, .check, .elaborate, .eval, .contract]

end QueryKind

inductive Phase where
  | protocol
  | parsing
  | resolution
  | checking
  | elaboration
  | evaluation
  | contractExecution
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive Severity where
  | error
  | warning
  | information
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive ResourceKind where
  | solverSteps
  | solverTables
  | solverAnswers
  | evaluationSteps
  | callDepth
  | transactions
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive VerdictKind where
  | accepted
  | rejected
  | unsupported
  | inconclusive
  | executed
  | internalError
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure SourceSpan where
  source : String
  startByte : Nat
  endByte : Nat
  deriving Repr, BEq, DecidableEq, Lean.ToJson

structure Diagnostic where
  code : String
  severity : Severity
  phase : Phase
  primary : SourceSpan
  related : Array SourceSpan := #[]
  arguments : Lean.Json := .null
  display : Option String := none
  deriving Lean.ToJson

structure SourceFile where
  path : String
  content : String
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure Workspace where
  entry : String
  sources : Array SourceFile
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure ProfileRef where
  id : String
  digest : String
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure OracleLimits where
  solverSteps : Nat
  solverTables : Nat
  solverAnswers : Nat
  evaluationSteps : Nat
  callDepth : Nat
  transactions : Nat
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

def OracleLimits.default : OracleLimits := {
  solverSteps := 100000
  solverTables := 10000
  solverAnswers := 100000
  evaluationSteps := 1000000
  callDepth := 1024
  transactions := 64
}

structure Query where
  kind : QueryKind
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure Request where
  schema : String
  id : String
  spec : String
  profile : ProfileRef
  workspace : Option Workspace := none
  limits : OracleLimits := OracleLimits.default
  query : Query
  deriving Lean.ToJson, Lean.FromJson

structure CapabilityReport where
  schema : String
  spec : String
  profile : SpecProfile
  profileDigest : String
  baselines : Array ImplementationBaseline
  implementedQueries : Array QueryKind
  unavailableQueries : Array QueryKind
  features : Array FeatureRow
  deriving Repr, Lean.ToJson, Lean.FromJson

private def ensureOnlyKeys
    (json : Lean.Json) (context : String) (allowed : List String) : Except String Unit := do
  let object ← json.getObj?
  match object.keys.find? (fun key => !allowed.contains key) with
  | some key => throw s!"unknown field in {context}: {key}"
  | none => pure ()

private def ensureRequiredKeys
    (json : Lean.Json) (context : String) (required : List String) : Except String Unit := do
  let object ← json.getObj?
  match required.find? (fun key => !object.contains key) with
  | some key => throw s!"missing field in {context}: {key}"
  | none => pure ()

structure ResultPayload where
  schema : String
  value : Lean.Json
  deriving Lean.ToJson

structure ObservationPayload where
  schema : String
  value : Lean.Json
  deriving Lean.ToJson

protected def SourceSpan.fromJson? (json : Lean.Json) : Except String SourceSpan := do
  ensureOnlyKeys json "source span" ["source", "startByte", "endByte"]
  ensureRequiredKeys json "source span" ["source", "startByte", "endByte"]
  let span : SourceSpan := {
    source := ← json.getObjValAs? String "source"
    startByte := ← json.getObjValAs? Nat "startByte"
    endByte := ← json.getObjValAs? Nat "endByte"
  }
  unless isSafeSourcePath span.source do
    throw "source span contains an unsafe source path"
  return span

instance : Lean.FromJson SourceSpan := ⟨SourceSpan.fromJson?⟩

protected def Diagnostic.fromJson? (json : Lean.Json) : Except String Diagnostic := do
  ensureOnlyKeys json "diagnostic"
    ["code", "severity", "phase", "primary", "related", "arguments", "display"]
  ensureRequiredKeys json "diagnostic"
    ["code", "severity", "phase", "primary", "related", "arguments", "display"]
  return {
    code := ← json.getObjValAs? String "code"
    severity := ← json.getObjValAs? Severity "severity"
    phase := ← json.getObjValAs? Phase "phase"
    primary := ← json.getObjValAs? SourceSpan "primary"
    related := ← json.getObjValAs? (Array SourceSpan) "related"
    arguments := ← json.getObjVal? "arguments"
    display := ← json.getObjValAs? (Option String) "display"
  }

instance : Lean.FromJson Diagnostic := ⟨Diagnostic.fromJson?⟩

protected def ResultPayload.fromJson? (json : Lean.Json) : Except String ResultPayload := do
  ensureOnlyKeys json "result payload" ["schema", "value"]
  ensureRequiredKeys json "result payload" ["schema", "value"]
  return {
    schema := ← json.getObjValAs? String "schema"
    value := ← json.getObjVal? "value"
  }

instance : Lean.FromJson ResultPayload := ⟨ResultPayload.fromJson?⟩

protected def ObservationPayload.fromJson?
    (json : Lean.Json) : Except String ObservationPayload := do
  ensureOnlyKeys json "observation payload" ["schema", "value"]
  ensureRequiredKeys json "observation payload" ["schema", "value"]
  let payload : ObservationPayload := {
    schema := ← json.getObjValAs? String "schema"
    value := ← json.getObjVal? "value"
  }
  if payload.schema.isEmpty then
    throw "observation schema must not be empty"
  return payload

instance : Lean.FromJson ObservationPayload := ⟨ObservationPayload.fromJson?⟩

private def ensureStdFileDigestShape (json : Lean.Json) : Except String Unit := do
  ensureOnlyKeys json "capability standard-library file" ["path", "byteSize", "sha256"]
  ensureRequiredKeys json "capability standard-library file" ["path", "byteSize", "sha256"]

private def ensureStdBundleShape (json : Lean.Json) : Except String Unit := do
  ensureOnlyKeys json "capability standard-library bundle"
    ["sourceRevision", "manifestAlgorithm", "manifestSha256", "files"]
  ensureRequiredKeys json "capability standard-library bundle"
    ["sourceRevision", "manifestAlgorithm", "manifestSha256", "files"]
  let files ← (← json.getObjVal? "files").getArr?
  for fileJson in files do
    ensureStdFileDigestShape fileJson

private def ensureLanguageVersionShape (json : Lean.Json) : Except String Unit := do
  ensureOnlyKeys json "capability language version"
    ["id", "release", "grammarVersion", "staticSemanticsVersion",
      "dynamicSemanticsVersion", "abiVersion", "storageLayoutVersion",
      "standardLibrary", "knownFeatures"]
  ensureRequiredKeys json "capability language version"
    ["id", "release", "grammarVersion", "staticSemanticsVersion",
      "dynamicSemanticsVersion", "abiVersion", "storageLayoutVersion",
      "standardLibrary", "knownFeatures"]
  let releaseJson ← json.getObjVal? "release"
  ensureOnlyKeys releaseJson "capability semantic version"
    ["major", "minor", "patch", "prerelease"]
  ensureRequiredKeys releaseJson "capability semantic version"
    ["major", "minor", "patch", "prerelease"]
  ensureStdBundleShape (← json.getObjVal? "standardLibrary")

private def ensureSpecProfileShape (json : Lean.Json) : Except String Unit := do
  ensureOnlyKeys json "capability profile"
    ["id", "language", "scope", "enabledFeatures", "solver", "observation",
      "contractRuntime", "spanUnit", "sourceEncoding"]
  ensureRequiredKeys json "capability profile"
    ["id", "language", "scope", "enabledFeatures", "solver", "observation",
      "contractRuntime", "spanUnit", "sourceEncoding"]
  ensureLanguageVersionShape (← json.getObjVal? "language")
  let runtimeJson ← json.getObjVal? "contractRuntime"
  unless runtimeJson.isNull do
    ensureOnlyKeys runtimeJson "capability contract runtime" ["evmRevision", "gasSchedule"]
    ensureRequiredKeys runtimeJson "capability contract runtime" ["evmRevision", "gasSchedule"]

private def ensureImplementationBaselineShape (json : Lean.Json) : Except String Unit := do
  ensureOnlyKeys json "capability implementation baseline"
    ["implementation", "repository", "revision", "role", "standardLibraryBundle",
      "nativeSettings", "notes"]
  ensureRequiredKeys json "capability implementation baseline"
    ["implementation", "repository", "revision", "role", "standardLibraryBundle",
      "nativeSettings", "notes"]
  let settingsJson ← json.getObjVal? "nativeSettings"
  ensureOnlyKeys settingsJson "capability implementation settings"
    ["solver", "generatedDispatch", "primitiveSurface", "bytecodeRuntime",
      "nativeBackendTarget", "externalYulCompilerTarget"]
  ensureRequiredKeys settingsJson "capability implementation settings"
    ["solver", "generatedDispatch", "primitiveSurface", "bytecodeRuntime",
      "nativeBackendTarget", "externalYulCompilerTarget"]

private def ensureFeatureRowShape (json : Lean.Json) : Except String Unit := do
  ensureOnlyKeys json "capability feature row"
    ["feature", "specStatus", "leanTarget", "leanStatus", "adr", "note"]
  ensureRequiredKeys json "capability feature row"
    ["feature", "specStatus", "leanTarget", "leanStatus", "adr", "note"]

def decodeCapabilityReport (json : Lean.Json) : Except String CapabilityReport := do
  ensureOnlyKeys json "capability report"
    ["schema", "spec", "profile", "profileDigest", "baselines",
      "implementedQueries", "unavailableQueries", "features"]
  ensureRequiredKeys json "capability report"
    ["schema", "spec", "profile", "profileDigest", "baselines",
      "implementedQueries", "unavailableQueries", "features"]
  ensureSpecProfileShape (← json.getObjVal? "profile")
  let baselines ← (← json.getObjVal? "baselines").getArr?
  for baselineJson in baselines do
    ensureImplementationBaselineShape baselineJson
  let featureRows ← (← json.getObjVal? "features").getArr?
  for featureJson in featureRows do
    ensureFeatureRowShape featureJson
  let report : CapabilityReport ← Lean.fromJson? json
  unless report.schema == capabilitiesSchema do
    throw "capability report schema mismatch"
  unless report.spec == Solcore.draftLanguage.id do
    throw "capability report language specification mismatch"
  unless report.profileDigest == Solcore.draftCoreProfileDigest do
    throw "capability report profile digest mismatch"
  unless Lean.toJson report.profile == Lean.toJson Solcore.draftCoreProfile do
    throw "capability report profile mismatch"
  if hasDuplicates report.implementedQueries.toList then
    throw "implemented capability queries must be unique"
  if hasDuplicates report.unavailableQueries.toList then
    throw "unavailable capability queries must be unique"
  return report

inductive Verdict where
  | accepted (phase : Phase) (result : ResultPayload)
  | rejected (phase : Phase) (primary : Diagnostic) (additional : Array Diagnostic)
  | unsupported (phase : Phase) (features : Array Feature)
  | inconclusive
      (phase : Phase)
      (resource : ResourceKind)
      (limit : Nat)
      (consumed : Option Nat)
  | executed (observation : ObservationPayload)
  | internalError (phase : Option Phase) (code : String)

namespace Verdict

def kind : Verdict → VerdictKind
  | .accepted .. => .accepted
  | .rejected .. => .rejected
  | .unsupported .. => .unsupported
  | .inconclusive .. => .inconclusive
  | .executed .. => .executed
  | .internalError .. => .internalError

def phase? : Verdict → Option Phase
  | .accepted phase _ => some phase
  | .rejected phase _ _ => some phase
  | .unsupported phase _ => some phase
  | .inconclusive phase _ _ _ => some phase
  | .executed _ => none
  | .internalError phase _ => phase

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
  | .unsupported phase features =>
      .mkObj [
        ("kind", Lean.toJson VerdictKind.unsupported),
        ("phase", Lean.toJson phase),
        ("features", Lean.toJson features)
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

protected def fromJson? (json : Lean.Json) : Except String Verdict := do
  let kind ← json.getObjValAs? VerdictKind "kind"
  match kind with
  | .accepted =>
      ensureOnlyKeys json "accepted verdict" ["kind", "phase", "result"]
      ensureRequiredKeys json "accepted verdict" ["kind", "phase", "result"]
      let result ← json.getObjValAs? ResultPayload "result"
      unless result.schema == capabilitiesSchema do
        throw "unknown accepted result schema"
      let _ ← decodeCapabilityReport result.value
      return .accepted (← json.getObjValAs? Phase "phase") result
  | .rejected =>
      ensureOnlyKeys json "rejected verdict" ["kind", "phase", "diagnostics"]
      ensureRequiredKeys json "rejected verdict" ["kind", "phase", "diagnostics"]
      let phase ← json.getObjValAs? Phase "phase"
      let diagnostics ← json.getObjValAs? (Array Diagnostic) "diagnostics"
      match diagnostics.toList with
      | [] => throw "rejected verdict requires at least one diagnostic"
      | primary :: additional => return .rejected phase primary additional.toArray
  | .unsupported =>
      ensureOnlyKeys json "unsupported verdict" ["kind", "phase", "features"]
      ensureRequiredKeys json "unsupported verdict" ["kind", "phase", "features"]
      let features ← json.getObjValAs? (Array Feature) "features"
      if hasDuplicates features.toList then
        throw "unsupported feature identifiers must be unique"
      return .unsupported (← json.getObjValAs? Phase "phase") features
  | .inconclusive =>
      ensureOnlyKeys json "inconclusive verdict"
        ["kind", "phase", "resource", "limit", "consumed"]
      ensureRequiredKeys json "inconclusive verdict"
        ["kind", "phase", "resource", "limit", "consumed"]
      return .inconclusive
        (← json.getObjValAs? Phase "phase")
        (← json.getObjValAs? ResourceKind "resource")
        (← json.getObjValAs? Nat "limit")
        (← json.getObjValAs? (Option Nat) "consumed")
  | .executed =>
      ensureOnlyKeys json "executed verdict" ["kind", "observation"]
      ensureRequiredKeys json "executed verdict" ["kind", "observation"]
      return .executed (← json.getObjValAs? ObservationPayload "observation")
  | .internalError =>
      ensureOnlyKeys json "internalError verdict" ["kind", "phase", "code"]
      ensureRequiredKeys json "internalError verdict" ["kind", "phase", "code"]
      return .internalError
        (← json.getObjValAs? (Option Phase) "phase")
        (← json.getObjValAs? String "code")

end Verdict

instance : Lean.ToJson Verdict := ⟨Verdict.toJson⟩
instance : Lean.FromJson Verdict := ⟨Verdict.fromJson?⟩

structure Response where
  schema : String
  id : String
  spec : String
  profile : ProfileRef
  query : QueryKind
  verdict : Verdict
  deriving Lean.ToJson, Lean.FromJson

structure ProtocolError where
  kind : String := "protocolError"
  schema : String := schemaVersion
  id : Option String := none
  code : String
  display : String
  deriving Repr, Lean.ToJson, Lean.FromJson

def QueryKind.phase : QueryKind → Phase
  | .capabilities => .protocol
  | .parse => .parsing
  | .resolve => .resolution
  | .check => .checking
  | .elaborate => .elaboration
  | .eval => .evaluation
  | .contract => .contractExecution

def Phase.rank : Phase → Nat
  | .protocol => 0
  | .parsing => 1
  | .resolution => 2
  | .checking => 3
  | .elaboration => 4
  | .evaluation => 5
  | .contractExecution => 6

def Phase.allowedFor (phase : Phase) (query : QueryKind) : Bool :=
  phase.rank <= query.phase.rank

def Verdict.validationErrorsFor (query : QueryKind) (verdict : Verdict) : List String :=
  let phaseErrors (phase : Phase) :=
    if phase.allowedFor query then [] else ["verdict phase is later than the requested query"]
  match verdict with
  | .accepted phase result =>
      (if phase == query.phase then [] else ["accepted verdict must complete the requested phase"]) ++
      (match query with
        | .capabilities =>
            if result.schema == capabilitiesSchema then
              []
            else
              ["capabilities result schema mismatch"]
        | _ => ["accepted payload is not yet defined for this query"])
  | .rejected phase primary additional =>
      phaseErrors phase ++
      (if primary.phase == phase && additional.all (fun diagnostic =>
          diagnostic.phase == phase) then
        []
      else
        ["diagnostic phases must match the rejected phase"])
  | .unsupported phase _ => phaseErrors phase
  | .inconclusive phase _ limit consumed =>
      phaseErrors phase ++
      (match consumed with
        | none => []
        | some value =>
            if value <= limit then [] else ["consumed resource exceeds the declared limit"])
  | .executed observation =>
      (if query == .eval || query == .contract then
        []
      else
        ["executed verdict is only valid for dynamic queries"]) ++
      (if observation.schema.isEmpty then
        ["observation schema must not be empty"]
      else
        [])
  | .internalError phase code =>
      (match phase with
        | none => []
        | some value => phaseErrors value) ++
      (if code.isEmpty then ["internalError code must not be empty"] else [])

def Workspace.validationErrors (workspace : Workspace) : List String :=
  let paths := workspace.sources.toList.map (·.path)
  (if workspace.sources.isEmpty then ["workspace sources must not be empty"] else []) ++
  (if paths.contains workspace.entry then [] else ["workspace entry is missing"]) ++
  (if hasDuplicates paths then ["workspace source paths must be unique"] else []) ++
  (if paths.all isSafeSourcePath then [] else ["workspace contains an unsafe source path"])

def Request.validationErrors (request : Request) : List String :=
  (if request.schema == schemaVersion then [] else ["unknown oracle schema"]) ++
  (if request.spec == Solcore.draftLanguage.id then [] else ["unknown language specification"]) ++
  (if request.profile.id == Solcore.draftCoreProfile.id then [] else ["unknown profile"]) ++
  (if request.profile.digest == Solcore.draftCoreProfileDigest then
    []
  else
    ["profile digest mismatch"]) ++
  (if request.id.isEmpty then ["request id must not be empty"] else []) ++
  match request.query.kind, request.workspace with
  | .capabilities, none => []
  | .capabilities, some _ => ["capabilities query must not include a workspace"]
  | _, none => ["workspace is required for this query"]
  | _, some workspace => workspace.validationErrors

def Response.validationErrors (response : Response) : List String :=
  (if response.schema == schemaVersion then [] else ["unknown oracle schema"]) ++
  (if response.id.isEmpty then ["response id must not be empty"] else []) ++
  (if response.spec == Solcore.draftLanguage.id then [] else ["unknown language specification"]) ++
  (if response.profile.id == Solcore.draftCoreProfile.id then [] else ["unknown profile"]) ++
  (if response.profile.digest == Solcore.draftCoreProfileDigest then
    []
  else
    ["profile digest mismatch"]) ++
  response.verdict.validationErrorsFor response.query

def decodeRequest (json : Lean.Json) : Except String Request := do
  ensureOnlyKeys json "request"
    ["schema", "id", "spec", "profile", "workspace", "limits", "query"]
  ensureRequiredKeys json "request"
    ["schema", "id", "spec", "profile", "workspace", "limits", "query"]
  let profileJson ← json.getObjVal? "profile"
  ensureOnlyKeys profileJson "profile" ["id", "digest"]
  ensureRequiredKeys profileJson "profile" ["id", "digest"]
  let queryJson ← json.getObjVal? "query"
  ensureOnlyKeys queryJson "query" ["kind"]
  ensureRequiredKeys queryJson "query" ["kind"]
  let limitsJson := json.getObjValD "limits"
  unless limitsJson.isNull do
    ensureOnlyKeys limitsJson "limits"
      ["solverSteps", "solverTables", "solverAnswers", "evaluationSteps", "callDepth",
        "transactions"]
    ensureRequiredKeys limitsJson "limits"
      ["solverSteps", "solverTables", "solverAnswers", "evaluationSteps", "callDepth",
        "transactions"]
  let workspaceJson := json.getObjValD "workspace"
  unless workspaceJson.isNull do
    ensureOnlyKeys workspaceJson "workspace" ["entry", "sources"]
    ensureRequiredKeys workspaceJson "workspace" ["entry", "sources"]
    let sourceArray ← (← workspaceJson.getObjVal? "sources").getArr?
    for sourceJson in sourceArray do
      ensureOnlyKeys sourceJson "source" ["path", "content"]
      ensureRequiredKeys sourceJson "source" ["path", "content"]
  Lean.fromJson? json

def decodeResponse (json : Lean.Json) : Except String Response := do
  ensureOnlyKeys json "response" ["schema", "id", "spec", "profile", "query", "verdict"]
  ensureRequiredKeys json "response" ["schema", "id", "spec", "profile", "query", "verdict"]
  let profileJson ← json.getObjVal? "profile"
  ensureOnlyKeys profileJson "profile" ["id", "digest"]
  ensureRequiredKeys profileJson "profile" ["id", "digest"]
  let response : Response ← Lean.fromJson? json
  match response.validationErrors with
  | [] => return response
  | error :: _ => throw error

end Solcore.Oracle
