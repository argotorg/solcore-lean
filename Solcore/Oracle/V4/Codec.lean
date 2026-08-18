import Solcore.Foundation.Json
import Solcore.Oracle.StrictJson
import Solcore.Oracle.V4.Capabilities
import Solcore.Surface.Wire.V1.PublicationCodec

set_option autoImplicit false

namespace Solcore.Oracle.V4

open Solcore.Surface.Wire.V1

/-!
Canonical JSON codecs for the closed Oracle v4 values.  Raw-text entry points
always use the duplicate-rejecting Oracle parser before typed decoding.
Surface parse results retain their caller-supplied decode limits and the path
of the enclosing Oracle value.
-/

private def invalidTagAt {alpha : Type}
    (path : DecodePath)
    (actual : Lean.Json)
    (expected : Lean.Json) :
    DecodeResult alpha :=
  failAt path .invalidTag (.mkObj [
    ("actual", actual),
    ("expected", expected)
  ])

private def requireLiteralAt
    (path : DecodePath)
    (json : Lean.Json)
    (expected : String) :
    DecodeResult Unit := do
  let actual <- decodeStringAt path json
  unless actual == expected do
    invalidTagAt path actual expected

private def requireNullAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Unit :=
  if json.isNull then
    pure ()
  else
    invalidTagAt path json .null

private def decodeNatAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Nat :=
  match Solcore.Foundation.jsonNatural? json with
  | some value => pure value
  | none => failAt path .expectedNatural (.mkObj [
      ("expected", "natural")
    ])

private def decodeSingletonAt {alpha : Type}
    (decodeValue : DecodePath -> Lean.Json -> DecodeResult alpha)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult alpha :=
  match json with
  | .arr values =>
      match values.toList with
      | [value] => decodeValue (path.index 0) value
      | _ => invalidTagAt path json (.mkObj [
          ("length", 1)
        ])
  | _ => failAt path .expectedArray (.mkObj [
      ("expected", "array")
    ])

inductive TextDecodeError where
  | malformedJson (message : String)
  | invalidValue (error : DecodeError)

abbrev TextDecodeResult (alpha : Type) := Except TextDecodeError alpha

private def decodeTextWith {alpha : Type}
    (decode : Lean.Json -> DecodeResult alpha)
    (text : String) :
    TextDecodeResult alpha :=
  match StrictJson.parse text with
  | .error message => .error (.malformedJson message)
  | .ok json =>
      match decode json with
      | .error error => .error (.invalidValue error)
      | .ok value => .ok value

def encodeRequestId (id : RequestId) : Lean.Json :=
  id.value

def decodeRequestIdAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult RequestId := do
  let value <- decodeStringAt path json
  match RequestId.ofString? value with
  | some id => pure id
  | none => invalidTagAt path value (.mkObj [
      ("constraint", "nonempty-string")
    ])

def decodeRequestId (json : Lean.Json) : DecodeResult RequestId :=
  decodeRequestIdAt .root json

def encodeSourcePath (path : SourcePath) : Lean.Json :=
  path.value

def decodeSourcePathAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult SourcePath := do
  let value <- decodeStringAt path json
  match SourcePath.ofString? value with
  | some sourcePath => pure sourcePath
  | none => invalidTagAt path value (.mkObj [
      ("constraint", "nonempty-string")
    ])

def decodeSourcePath (json : Lean.Json) : DecodeResult SourcePath :=
  decodeSourcePathAt .root json

def encodeSourceInput (source : SourceInput) : Lean.Json :=
  .mkObj [
    ("path", encodeSourcePath source.path),
    ("content", source.content)
  ]

def decodeSourceInputAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult SourceInput := do
  ensureExactObject path json ["path", "content"] ["path", "content"]
  let sourcePath <- decodeSourcePathAt (path.field "path")
    (← requireField path json "path")
  let content <- decodeStringAt (path.field "content")
    (← requireField path json "content")
  pure { path := sourcePath, content }

def decodeSourceInput (json : Lean.Json) : DecodeResult SourceInput :=
  decodeSourceInputAt .root json

def encodeLimits (limits : Limits) : Lean.Json :=
  .mkObj [
    ("sourceBytes", Lean.toJson limits.sourceBytes)
  ]

def decodeLimitsAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Limits := do
  ensureExactObject path json ["sourceBytes"] ["sourceBytes"]
  let sourceBytes <- decodeNatAt (path.field "sourceBytes")
    (← requireField path json "sourceBytes")
  pure { sourceBytes }

def decodeLimits (json : Lean.Json) : DecodeResult Limits :=
  decodeLimitsAt .root json

def encodeQueryKind : QueryKind -> Lean.Json
  | .capabilities => "capabilities"
  | .parse => "parse"

def decodeQueryKindAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult QueryKind := do
  let value <- decodeStringAt path json
  match value with
  | "capabilities" => pure .capabilities
  | "parse" => pure .parse
  | _ => invalidTagAt path value (.arr #["capabilities", "parse"])

def decodeQueryKind (json : Lean.Json) : DecodeResult QueryKind :=
  decodeQueryKindAt .root json

def encodeProfileRef (profile : ProfileRef) : Lean.Json :=
  .mkObj [
    ("id", profile.id),
    ("digest", profile.digest)
  ]

def decodeProfileRefAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult ProfileRef := do
  ensureExactObject path json ["id", "digest"] ["id", "digest"]
  requireLiteralAt (path.field "id")
    (← requireField path json "id") ProfileRef.canonical.id
  requireLiteralAt (path.field "digest")
    (← requireField path json "digest") ProfileRef.canonical.digest
  pure ProfileRef.canonical

def decodeProfileRef (json : Lean.Json) : DecodeResult ProfileRef :=
  decodeProfileRefAt .root json

def encodeQuery : Query -> Lean.Json
  | .capabilities => .mkObj [
      ("kind", "capabilities")
    ]
  | .parse source => .mkObj [
      ("kind", "parse"),
      ("source", encodeSourceInput source)
    ]

def decodeQueryAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Query := do
  ensureExactObject path json ["kind", "source"] ["kind"]
  let kind <- decodeQueryKindAt (path.field "kind")
    (← requireField path json "kind")
  match kind with
  | .capabilities =>
      ensureExactObject path json ["kind"] ["kind"]
      pure .capabilities
  | .parse =>
      ensureExactObject path json ["kind", "source"] ["kind", "source"]
      pure (.parse (← decodeSourceInputAt (path.field "source")
        (← requireField path json "source")))

def decodeQuery (json : Lean.Json) : DecodeResult Query :=
  decodeQueryAt .root json

def encodeRequest (request : Request) : Lean.Json :=
  .mkObj [
    ("schema", request.schema),
    ("id", encodeRequestId request.id),
    ("spec", request.spec),
    ("profile", encodeProfileRef request.profile),
    ("limits", encodeLimits request.limits),
    ("query", encodeQuery request.query)
  ]

def decodeRequestAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Request := do
  ensureExactObject path json
    ["schema", "id", "spec", "profile", "limits", "query"]
    ["schema", "id", "spec", "profile", "limits", "query"]
  requireLiteralAt (path.field "schema")
    (← requireField path json "schema") schemaVersion
  let id <- decodeRequestIdAt (path.field "id")
    (← requireField path json "id")
  requireLiteralAt (path.field "spec")
    (← requireField path json "spec") Solcore.m2bLanguage.id
  let _ <- decodeProfileRefAt (path.field "profile")
    (← requireField path json "profile")
  let limits <- decodeLimitsAt (path.field "limits")
    (← requireField path json "limits")
  let query <- decodeQueryAt (path.field "query")
    (← requireField path json "query")
  pure { id, limits, query }

def decodeRequest (json : Lean.Json) : DecodeResult Request :=
  decodeRequestAt .root json

def decodeRequestText (text : String) : TextDecodeResult Request :=
  decodeTextWith decodeRequest text

def canonicalizeRequest (json : Lean.Json) : DecodeResult Lean.Json :=
  encodeRequest <$> decodeRequest json

def encodePhase : Phase -> Lean.Json
  | .protocol => "protocol"
  | .sourcePreflight => "sourcePreflight"
  | .surfaceLexing => "surfaceLexing"
  | .surfaceParsing => "surfaceParsing"
  | .surfaceEncoding => "surfaceEncoding"

def decodePhaseAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Phase := do
  let value <- decodeStringAt path json
  match value with
  | "protocol" => pure .protocol
  | "sourcePreflight" => pure .sourcePreflight
  | "surfaceLexing" => pure .surfaceLexing
  | "surfaceParsing" => pure .surfaceParsing
  | "surfaceEncoding" => pure .surfaceEncoding
  | _ => invalidTagAt path value (.arr #[
      "protocol", "sourcePreflight", "surfaceLexing", "surfaceParsing",
      "surfaceEncoding"
    ])

def decodePhase (json : Lean.Json) : DecodeResult Phase :=
  decodePhaseAt .root json

private def encodeOptionalPhase : Option Phase -> Lean.Json
  | none => .null
  | some phase => encodePhase phase

def encodeInternalError (error : InternalError) : Lean.Json :=
  .mkObj [
    ("phase", encodeOptionalPhase error.phase),
    ("code", error.code)
  ]

def decodeInternalErrorAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult InternalError := do
  ensureExactObject path json ["phase", "code"] ["phase", "code"]
  let phasePath := path.field "phase"
  let phaseJson <- requireField path json "phase"
  let codePath := path.field "code"
  let code <- decodeStringAt codePath (← requireField path json "code")
  match code with
  | "frontend-invariant" =>
      let phase <- decodePhaseAt phasePath phaseJson
      match phase with
      | .surfaceLexing => pure (.frontendInvariant .surfaceLexing)
      | .surfaceParsing => pure (.frontendInvariant .surfaceParsing)
      | actual => invalidTagAt phasePath (encodePhase actual) <|
          Lean.Json.arr #["surfaceLexing", "surfaceParsing"]
  | "surface-wire-projection-failed" =>
      requireLiteralAt phasePath phaseJson "surfaceEncoding"
      pure .surfaceWireProjectionFailed
  | "oracle-response-invariant" =>
      requireNullAt phasePath phaseJson
      pure .oracleResponseInvariant
  | _ => invalidTagAt codePath code (.arr #[
      "frontend-invariant", "surface-wire-projection-failed",
      "oracle-response-invariant"
    ])

def decodeInternalError (json : Lean.Json) : DecodeResult InternalError :=
  decodeInternalErrorAt .root json

def encodeSourceBytesExceeded
    (exhaustion : SourceBytesExceeded) : Lean.Json :=
  .mkObj [
    ("phase", "sourcePreflight"),
    ("resource", "sourceBytes"),
    ("limit", Lean.toJson exhaustion.limit),
    ("consumed", Lean.toJson exhaustion.consumed)
  ]

def decodeSourceBytesExceededAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult SourceBytesExceeded := do
  ensureExactObject path json
    ["phase", "resource", "limit", "consumed"]
    ["phase", "resource", "limit", "consumed"]
  requireLiteralAt (path.field "phase")
    (← requireField path json "phase") "sourcePreflight"
  requireLiteralAt (path.field "resource")
    (← requireField path json "resource") "sourceBytes"
  let limit <- decodeNatAt (path.field "limit")
    (← requireField path json "limit")
  let consumed <- decodeNatAt (path.field "consumed")
    (← requireField path json "consumed")
  match SourceBytesExceeded.ofValues? limit consumed with
  | some exhaustion => pure exhaustion
  | none => invalidTagAt (path.field "consumed") (Lean.toJson consumed) <|
      Lean.Json.mkObj [
        ("constraint", "strictly-greater-than-limit"),
        ("limit", Lean.toJson limit)
      ]

def decodeSourceBytesExceeded
    (json : Lean.Json) :
    DecodeResult SourceBytesExceeded :=
  decodeSourceBytesExceededAt .root json

private def encodeImplementedQueries : Lean.Json :=
  .arr #["capabilities", "parse"]

private def canonicalCapabilityReportJson : Lean.Json :=
  .mkObj [
    ("schema", capabilityReport.schema),
    ("spec", capabilityReport.spec),
    ("profile", Lean.toJson capabilityReport.profile),
    ("profileDigest", capabilityReport.profileDigest),
    ("surfaceSchema", capabilityReport.surfaceSchema),
    ("parseResultSchema", capabilityReport.parseResultSchema),
    ("baselines", Lean.toJson capabilityReport.baselines),
    ("implementedQueries", encodeImplementedQueries),
    ("features", Lean.toJson capabilityReport.features),
    ("defaultLimits", encodeLimits capabilityReport.defaultLimits)
  ]

def encodeCapabilityReport (_report : CapabilityReport) : Lean.Json :=
  canonicalCapabilityReportJson

def decodeCapabilityReportAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult CapabilityReport := do
  if json.compress == canonicalCapabilityReportJson.compress then
    pure .canonical
  else
    invalidTagAt path json canonicalCapabilityReportJson

def decodeCapabilityReport
    (json : Lean.Json) :
    DecodeResult CapabilityReport :=
  decodeCapabilityReportAt .root json

def decodeCapabilityReportText
    (text : String) :
    TextDecodeResult CapabilityReport :=
  decodeTextWith decodeCapabilityReport text

def canonicalizeCapabilityReport
    (json : Lean.Json) :
    DecodeResult Lean.Json :=
  encodeCapabilityReport <$> decodeCapabilityReport json

private def encodeCapabilityResult
    (report : CapabilityReport) : Lean.Json :=
  .mkObj [
    ("schema", capabilitiesSchema),
    ("value", encodeCapabilityReport report)
  ]

private def decodeCapabilityResultAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult CapabilityReport := do
  ensureExactObject path json ["schema", "value"] ["schema", "value"]
  requireLiteralAt (path.field "schema")
    (← requireField path json "schema") capabilitiesSchema
  decodeCapabilityReportAt (path.field "value")
    (← requireField path json "value")

def encodeCapabilitiesVerdict : CapabilitiesVerdict -> Lean.Json
  | .accepted report => .mkObj [
      ("kind", "accepted"),
      ("phase", "protocol"),
      ("result", encodeCapabilityResult report)
    ]
  | .oracleResponseInvariant => .mkObj [
      ("kind", "internalError"),
      ("phase", .null),
      ("code", "oracle-response-invariant")
    ]

def decodeCapabilitiesVerdictAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult CapabilitiesVerdict := do
  ensureExactObject path json ["kind", "phase", "result", "code"] ["kind"]
  let kindPath := path.field "kind"
  let kind <- decodeStringAt kindPath (← requireField path json "kind")
  match kind with
  | "accepted" =>
      ensureExactObject path json ["kind", "phase", "result"]
        ["kind", "phase", "result"]
      requireLiteralAt (path.field "phase")
        (← requireField path json "phase") "protocol"
      pure (.accepted (← decodeCapabilityResultAt (path.field "result")
        (← requireField path json "result")))
  | "internalError" =>
      ensureExactObject path json ["kind", "phase", "code"]
        ["kind", "phase", "code"]
      let error <- decodeInternalErrorAt path (.mkObj [
        ("phase", ← requireField path json "phase"),
        ("code", ← requireField path json "code")
      ])
      match error with
      | .oracleResponseInvariant => pure .oracleResponseInvariant
      | _ => invalidTagAt path json (.mkObj [
          ("code", "oracle-response-invariant"),
          ("phase", .null)
        ])
  | _ => invalidTagAt kindPath kind (.arr #["accepted", "internalError"])

def decodeCapabilitiesVerdict
    (json : Lean.Json) :
    DecodeResult CapabilitiesVerdict :=
  decodeCapabilitiesVerdictAt .root json

def canonicalizeCapabilitiesVerdict
    (json : Lean.Json) :
    DecodeResult Lean.Json :=
  encodeCapabilitiesVerdict <$> decodeCapabilitiesVerdict json

private def diagnosticPhaseName
    (diagnostic : Solcore.Surface.Wire.V1.Diagnostic) : String :=
  match diagnostic.phase with
  | .surfaceLexing => "surfaceLexing"
  | .surfaceParsing => "surfaceParsing"

def encodeParseVerdict : ParseVerdict -> Lean.Json
  | .accepted result => .mkObj [
      ("kind", "accepted"),
      ("phase", "surfaceParsing"),
      ("result", encodeParseResult result)
    ]
  | .rejected diagnostic => .mkObj [
      ("kind", "rejected"),
      ("phase", diagnosticPhaseName diagnostic),
      ("diagnostics", .arr #[encodeDiagnostic diagnostic])
    ]
  | .inconclusive exhaustion => .mkObj [
      ("kind", "inconclusive"),
      ("phase", "sourcePreflight"),
      ("resource", "sourceBytes"),
      ("limit", Lean.toJson exhaustion.limit),
      ("consumed", Lean.toJson exhaustion.consumed)
    ]
  | .internalError error => .mkObj [
      ("kind", "internalError"),
      ("phase", encodeOptionalPhase error.phase),
      ("code", error.code)
    ]

private def decodeParseVerdictKindAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult String := do
  ensureExactObject path json
    ["kind", "phase", "result", "diagnostics", "resource", "limit",
      "consumed", "code"] ["kind"]
  decodeStringAt (path.field "kind") (← requireField path json "kind")

private def decodeAcceptedParseVerdictAt
    (surfaceLimits : DecodeLimits)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult ParseVerdict := do
  ensureExactObject path json ["kind", "phase", "result"]
    ["kind", "phase", "result"]
  requireLiteralAt (path.field "phase")
    (← requireField path json "phase") "surfaceParsing"
  pure (.accepted (← decodeParseResultAt surfaceLimits (path.field "result")
    (← requireField path json "result")))

private def decodeRejectedParseVerdictAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult ParseVerdict := do
  ensureExactObject path json ["kind", "phase", "diagnostics"]
    ["kind", "phase", "diagnostics"]
  let diagnostic <- decodeSingletonAt decodeDiagnosticAt
    (path.field "diagnostics") (← requireField path json "diagnostics")
  requireLiteralAt (path.field "phase")
    (← requireField path json "phase") (diagnosticPhaseName diagnostic)
  pure (.rejected diagnostic)

private def decodeInconclusiveParseVerdictAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult ParseVerdict := do
  ensureExactObject path json
    ["kind", "phase", "resource", "limit", "consumed"]
    ["kind", "phase", "resource", "limit", "consumed"]
  let exhaustion <- decodeSourceBytesExceededAt path (.mkObj [
    ("phase", ← requireField path json "phase"),
    ("resource", ← requireField path json "resource"),
    ("limit", ← requireField path json "limit"),
    ("consumed", ← requireField path json "consumed")
  ])
  pure (.inconclusive exhaustion)

private def decodeInternalParseVerdictAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult ParseVerdict := do
  ensureExactObject path json ["kind", "phase", "code"]
    ["kind", "phase", "code"]
  pure (.internalError (← decodeInternalErrorAt path (.mkObj [
    ("phase", ← requireField path json "phase"),
    ("code", ← requireField path json "code")
  ])))

def decodeParseVerdictAt
    (surfaceLimits : DecodeLimits)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult ParseVerdict := do
  let kind <- decodeParseVerdictKindAt path json
  match kind with
  | "accepted" => decodeAcceptedParseVerdictAt surfaceLimits path json
  | "rejected" => decodeRejectedParseVerdictAt path json
  | "inconclusive" => decodeInconclusiveParseVerdictAt path json
  | "internalError" => decodeInternalParseVerdictAt path json
  | _ => invalidTagAt kindPath kind (.arr #[
      "accepted", "rejected", "inconclusive", "internalError"
    ])
where
  kindPath := path.field "kind"

def decodeParseVerdict
    (surfaceLimits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult ParseVerdict :=
  decodeParseVerdictAt surfaceLimits .root json

def canonicalizeParseVerdict
    (surfaceLimits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult Lean.Json :=
  encodeParseVerdict <$> decodeParseVerdict surfaceLimits json

def ParseVerdict.WithinSurfaceLimits
    (surfaceLimits : DecodeLimits) : ParseVerdict -> Prop
  | .accepted result =>
      fileDepth result.value <= surfaceLimits.maxDepth ∧
        fileNodes result.value <= surfaceLimits.maxNodes
  | _ => True

def encodeResponseBody : ResponseBody -> Lean.Json
  | .capabilities verdict => encodeCapabilitiesVerdict verdict
  | .parse verdict => encodeParseVerdict verdict

def encodeResponse (response : Response) : Lean.Json :=
  .mkObj [
    ("schema", response.schema),
    ("id", encodeRequestId response.id),
    ("spec", response.spec),
    ("profile", encodeProfileRef response.profile),
    ("query", encodeQueryKind response.queryKind),
    ("verdict", encodeResponseBody response.body)
  ]

def decodeResponseAt
    (surfaceLimits : DecodeLimits)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Response := do
  ensureExactObject path json
    ["schema", "id", "spec", "profile", "query", "verdict"]
    ["schema", "id", "spec", "profile", "query", "verdict"]
  requireLiteralAt (path.field "schema")
    (← requireField path json "schema") schemaVersion
  let id <- decodeRequestIdAt (path.field "id")
    (← requireField path json "id")
  requireLiteralAt (path.field "spec")
    (← requireField path json "spec") Solcore.m2bLanguage.id
  let _ <- decodeProfileRefAt (path.field "profile")
    (← requireField path json "profile")
  let query <- decodeQueryKindAt (path.field "query")
    (← requireField path json "query")
  let verdictJson <- requireField path json "verdict"
  let body <- match query with
    | .capabilities =>
        .capabilities <$> decodeCapabilitiesVerdictAt
          (path.field "verdict") verdictJson
    | .parse =>
        .parse <$> decodeParseVerdictAt surfaceLimits
          (path.field "verdict") verdictJson
  pure { id, body }

def decodeResponse
    (surfaceLimits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult Response :=
  decodeResponseAt surfaceLimits .root json

def decodeResponseText
    (surfaceLimits : DecodeLimits)
    (text : String) :
    TextDecodeResult Response :=
  decodeTextWith (decodeResponse surfaceLimits) text

def canonicalizeResponse
    (surfaceLimits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult Lean.Json :=
  encodeResponse <$> decodeResponse surfaceLimits json

def Response.WithinSurfaceLimits
    (surfaceLimits : DecodeLimits)
    (response : Response) : Prop :=
  match response.body with
  | .capabilities _ => True
  | .parse verdict => verdict.WithinSurfaceLimits surfaceLimits

private def encodeOptionalRequestId : Option RequestId -> Lean.Json
  | none => .null
  | some id => encodeRequestId id

private def decodeOptionalRequestIdAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (Option RequestId) :=
  if json.isNull then
    pure none
  else
    some <$> decodeRequestIdAt path json

def encodeProtocolError (error : ProtocolError) : Lean.Json :=
  .mkObj [
    ("kind", error.kind),
    ("schema", error.schema),
    ("id", encodeOptionalRequestId error.id),
    ("code", error.code),
    ("path", error.path),
    ("arguments", error.arguments),
    ("display", error.display)
  ]

def decodeProtocolErrorAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult ProtocolError := do
  ensureExactObject path json
    ["kind", "schema", "id", "code", "path", "arguments", "display"]
    ["kind", "schema", "id", "code", "path", "arguments", "display"]
  requireLiteralAt (path.field "kind")
    (← requireField path json "kind") "protocolError"
  requireLiteralAt (path.field "schema")
    (← requireField path json "schema") schemaVersion
  let id <- decodeOptionalRequestIdAt (path.field "id")
    (← requireField path json "id")
  let code <- decodeStringAt (path.field "code")
    (← requireField path json "code")
  let errorPath <- decodeStringAt (path.field "path")
    (← requireField path json "path")
  let arguments <- requireField path json "arguments"
  let display <- decodeStringAt (path.field "display")
    (← requireField path json "display")
  pure { id, code, path := errorPath, arguments, display }

def decodeProtocolError
    (json : Lean.Json) :
    DecodeResult ProtocolError :=
  decodeProtocolErrorAt .root json

def decodeProtocolErrorText
    (text : String) :
    TextDecodeResult ProtocolError :=
  decodeTextWith decodeProtocolError text

def canonicalizeProtocolError
    (json : Lean.Json) :
    DecodeResult Lean.Json :=
  encodeProtocolError <$> decodeProtocolError json

@[simp] theorem decodeRequestIdAt_encodeRequestId
    (path : DecodePath)
    (id : RequestId) :
    decodeRequestIdAt path (encodeRequestId id) = .ok id := by
  change (match RequestId.ofString? id.value with
    | some decoded => Except.ok decoded
    | none => invalidTagAt path id.value (.mkObj [
        ("constraint", "nonempty-string")
      ])) = .ok id
  rw [RequestId.ofString?_value]

@[simp] theorem decodeSourcePathAt_encodeSourcePath
    (path : DecodePath)
    (sourcePath : SourcePath) :
    decodeSourcePathAt path (encodeSourcePath sourcePath) = .ok sourcePath := by
  change (match SourcePath.ofString? sourcePath.value with
    | some decoded => Except.ok decoded
    | none => invalidTagAt path sourcePath.value (.mkObj [
        ("constraint", "nonempty-string")
      ])) = .ok sourcePath
  rw [SourcePath.ofString?_value]

@[simp] theorem decodeRequestId_encodeRequestId
    (id : RequestId) :
    decodeRequestId (encodeRequestId id) = .ok id :=
  decodeRequestIdAt_encodeRequestId .root id

@[simp] theorem decodeSourcePath_encodeSourcePath
    (sourcePath : SourcePath) :
    decodeSourcePath (encodeSourcePath sourcePath) = .ok sourcePath :=
  decodeSourcePathAt_encodeSourcePath .root sourcePath

@[simp] theorem decodeSourceInputAt_encodeSourceInput
    (path : DecodePath)
    (source : SourceInput) :
    decodeSourceInputAt path (encodeSourceInput source) = .ok source := by
  change (do
    let decodedPath <- decodeSourcePathAt (path.field "path")
      (encodeSourcePath source.path)
    pure ({ path := decodedPath, content := source.content } : SourceInput)) =
      .ok source
  rw [decodeSourcePathAt_encodeSourcePath]
  cases source
  rfl

@[simp] theorem decodeSourceInput_encodeSourceInput
    (source : SourceInput) :
    decodeSourceInput (encodeSourceInput source) = .ok source :=
  decodeSourceInputAt_encodeSourceInput .root source

@[simp] theorem decodeLimitsAt_encodeLimits
    (path : DecodePath)
    (limits : Limits) :
    decodeLimitsAt path (encodeLimits limits) = .ok limits := by
  change (do
    let sourceBytes <- decodeNatAt (path.field "sourceBytes")
      (Lean.toJson limits.sourceBytes)
    pure ({ sourceBytes } : Limits)) = .ok limits
  simp [decodeNatAt]
  cases limits
  rfl

@[simp] theorem decodeLimits_encodeLimits
    (limits : Limits) :
    decodeLimits (encodeLimits limits) = .ok limits :=
  decodeLimitsAt_encodeLimits .root limits

@[simp] theorem decodeQueryKindAt_encodeQueryKind
    (path : DecodePath)
    (kind : QueryKind) :
    decodeQueryKindAt path (encodeQueryKind kind) = .ok kind := by
  cases kind <;> rfl

@[simp] theorem decodeQueryKind_encodeQueryKind
    (kind : QueryKind) :
    decodeQueryKind (encodeQueryKind kind) = .ok kind :=
  decodeQueryKindAt_encodeQueryKind .root kind

@[simp] theorem decodeProfileRefAt_encodeProfileRef
    (path : DecodePath)
    (profile : ProfileRef) :
    decodeProfileRefAt path (encodeProfileRef profile) = .ok profile := by
  cases profile
  rfl

@[simp] theorem decodeProfileRef_encodeProfileRef
    (profile : ProfileRef) :
    decodeProfileRef (encodeProfileRef profile) = .ok profile :=
  decodeProfileRefAt_encodeProfileRef .root profile

@[simp] theorem decodeQueryAt_encodeQuery
    (path : DecodePath)
    (query : Query) :
    decodeQueryAt path (encodeQuery query) = .ok query := by
  cases query with
  | capabilities => rfl
  | parse source =>
      change (do
        let decoded <- decodeSourceInputAt (path.field "source")
          (encodeSourceInput source)
        pure (Query.parse decoded)) = .ok (Query.parse source)
      rw [decodeSourceInputAt_encodeSourceInput]
      rfl

@[simp] theorem decodeQuery_encodeQuery
    (query : Query) :
    decodeQuery (encodeQuery query) = .ok query :=
  decodeQueryAt_encodeQuery .root query

@[simp] theorem decodeRequestAt_encodeRequest
    (path : DecodePath)
    (request : Request) :
    decodeRequestAt path (encodeRequest request) = .ok request := by
  change (do
    let id <- decodeRequestIdAt (path.field "id")
      (encodeRequestId request.id)
    let _ <- decodeProfileRefAt (path.field "profile")
      (encodeProfileRef request.profile)
    let limits <- decodeLimitsAt (path.field "limits")
      (encodeLimits request.limits)
    let query <- decodeQueryAt (path.field "query")
      (encodeQuery request.query)
    pure ({ id, limits, query } : Request)) = .ok request
  rw [decodeRequestIdAt_encodeRequestId]
  rw [decodeProfileRefAt_encodeProfileRef]
  rw [decodeLimitsAt_encodeLimits]
  rw [decodeQueryAt_encodeQuery]
  rfl

@[simp] theorem decodeRequest_encodeRequest
    (request : Request) :
    decodeRequest (encodeRequest request) = .ok request :=
  decodeRequestAt_encodeRequest .root request

@[simp] theorem canonicalizeRequest_encodeRequest
    (request : Request) :
    canonicalizeRequest (encodeRequest request) = .ok (encodeRequest request) := by
  unfold canonicalizeRequest
  rw [decodeRequest_encodeRequest]
  rfl

theorem canonicalizeRequest_idempotent
    (json : Lean.Json)
    (request : Request)
    (decoded : decodeRequest json = .ok request) :
    canonicalizeRequest json >>= canonicalizeRequest =
      canonicalizeRequest json := by
  unfold canonicalizeRequest
  rw [decoded]
  change canonicalizeRequest (encodeRequest request) =
    .ok (encodeRequest request)
  exact canonicalizeRequest_encodeRequest request

@[simp] theorem decodePhaseAt_encodePhase
    (path : DecodePath)
    (phase : Phase) :
    decodePhaseAt path (encodePhase phase) = .ok phase := by
  cases phase <;> rfl

@[simp] theorem decodePhase_encodePhase
    (phase : Phase) :
    decodePhase (encodePhase phase) = .ok phase :=
  decodePhaseAt_encodePhase .root phase

@[simp] theorem decodeInternalErrorAt_encodeInternalError
    (path : DecodePath)
    (error : InternalError) :
    decodeInternalErrorAt path (encodeInternalError error) = .ok error := by
  cases error with
  | frontendInvariant phase =>
      cases phase with
      | surfaceLexing =>
          change (decodePhaseAt (path.field "phase")
              (encodePhase .surfaceLexing) >>= fun phase =>
            match phase with
            | .surfaceLexing =>
                (Except.ok (InternalError.frontendInvariant .surfaceLexing) :
                  DecodeResult InternalError)
            | .surfaceParsing =>
                Except.ok (InternalError.frontendInvariant .surfaceParsing)
            | actual => invalidTagAt (path.field "phase")
                (encodePhase actual) (Lean.Json.arr #[
                  "surfaceLexing", "surfaceParsing"])
          ) =
            .ok (InternalError.frontendInvariant .surfaceLexing)
          rw [decodePhaseAt_encodePhase]
          rfl
      | surfaceParsing =>
          change (decodePhaseAt (path.field "phase")
              (encodePhase .surfaceParsing) >>= fun phase =>
            match phase with
            | .surfaceLexing =>
                (Except.ok (InternalError.frontendInvariant .surfaceLexing) :
                  DecodeResult InternalError)
            | .surfaceParsing =>
                Except.ok (InternalError.frontendInvariant .surfaceParsing)
            | actual => invalidTagAt (path.field "phase")
                (encodePhase actual) (Lean.Json.arr #[
                  "surfaceLexing", "surfaceParsing"])
          ) =
            .ok (InternalError.frontendInvariant .surfaceParsing)
          rw [decodePhaseAt_encodePhase]
          rfl
  | surfaceWireProjectionFailed | oracleResponseInvariant => rfl

@[simp] theorem decodeInternalError_encodeInternalError
    (error : InternalError) :
    decodeInternalError (encodeInternalError error) = .ok error :=
  decodeInternalErrorAt_encodeInternalError .root error

@[simp] theorem decodeSourceBytesExceededAt_encode
    (path : DecodePath)
    (exhaustion : SourceBytesExceeded) :
    decodeSourceBytesExceededAt path (encodeSourceBytesExceeded exhaustion) =
      .ok exhaustion := by
  change (do
    let limit <- decodeNatAt (path.field "limit")
      (Lean.toJson exhaustion.limit)
    let consumed <- decodeNatAt (path.field "consumed")
      (Lean.toJson exhaustion.consumed)
    match SourceBytesExceeded.ofValues? limit consumed with
    | some decoded => pure decoded
    | none => invalidTagAt (path.field "consumed") (Lean.toJson consumed) <|
        Lean.Json.mkObj [
          ("constraint", "strictly-greater-than-limit"),
          ("limit", Lean.toJson limit)
        ]) = .ok exhaustion
  simp [decodeNatAt]
  rfl

@[simp] theorem decodeSourceBytesExceeded_encode
    (exhaustion : SourceBytesExceeded) :
    decodeSourceBytesExceeded (encodeSourceBytesExceeded exhaustion) =
      .ok exhaustion :=
  decodeSourceBytesExceededAt_encode .root exhaustion

@[simp] theorem decodeCapabilityReportAt_encodeCapabilityReport
    (path : DecodePath)
    (report : CapabilityReport) :
    decodeCapabilityReportAt path (encodeCapabilityReport report) =
      .ok report := by
  cases report
  change (if canonicalCapabilityReportJson.compress ==
        canonicalCapabilityReportJson.compress then
      pure CapabilityReport.canonical
    else
      invalidTagAt path canonicalCapabilityReportJson
        canonicalCapabilityReportJson) =
    .ok CapabilityReport.canonical
  rw [beq_self_eq_true]
  rfl

@[simp] theorem decodeCapabilityReport_encodeCapabilityReport
    (report : CapabilityReport) :
    decodeCapabilityReport (encodeCapabilityReport report) = .ok report :=
  decodeCapabilityReportAt_encodeCapabilityReport .root report

@[simp] theorem canonicalizeCapabilityReport_encode
    (report : CapabilityReport) :
    canonicalizeCapabilityReport (encodeCapabilityReport report) =
      .ok (encodeCapabilityReport report) := by
  unfold canonicalizeCapabilityReport
  rw [decodeCapabilityReport_encodeCapabilityReport]
  rfl

theorem canonicalizeCapabilityReport_idempotent
    (json : Lean.Json)
    (report : CapabilityReport)
    (decoded : decodeCapabilityReport json = .ok report) :
    canonicalizeCapabilityReport json >>= canonicalizeCapabilityReport =
      canonicalizeCapabilityReport json := by
  unfold canonicalizeCapabilityReport
  rw [decoded]
  change canonicalizeCapabilityReport (encodeCapabilityReport report) =
    .ok (encodeCapabilityReport report)
  exact canonicalizeCapabilityReport_encode report

@[simp] theorem decodeCapabilitiesVerdictAt_encode
    (path : DecodePath)
    (verdict : CapabilitiesVerdict) :
    decodeCapabilitiesVerdictAt path (encodeCapabilitiesVerdict verdict) =
      .ok verdict := by
  cases verdict with
  | accepted report =>
      change (do
        let decoded <- decodeCapabilityReportAt
          ((path.field "result").field "value")
          (encodeCapabilityReport report)
        pure (CapabilitiesVerdict.accepted decoded)) =
          .ok (CapabilitiesVerdict.accepted report)
      rw [decodeCapabilityReportAt_encodeCapabilityReport]
      rfl
  | oracleResponseInvariant => rfl

@[simp] theorem decodeCapabilitiesVerdict_encode
    (verdict : CapabilitiesVerdict) :
    decodeCapabilitiesVerdict (encodeCapabilitiesVerdict verdict) =
      .ok verdict :=
  decodeCapabilitiesVerdictAt_encode .root verdict

@[simp] theorem canonicalizeCapabilitiesVerdict_encode
    (verdict : CapabilitiesVerdict) :
    canonicalizeCapabilitiesVerdict (encodeCapabilitiesVerdict verdict) =
      .ok (encodeCapabilitiesVerdict verdict) := by
  unfold canonicalizeCapabilitiesVerdict
  rw [decodeCapabilitiesVerdict_encode]
  rfl

theorem canonicalizeCapabilitiesVerdict_idempotent
    (json : Lean.Json)
    (verdict : CapabilitiesVerdict)
    (decoded : decodeCapabilitiesVerdict json = .ok verdict) :
    canonicalizeCapabilitiesVerdict json >>= canonicalizeCapabilitiesVerdict =
      canonicalizeCapabilitiesVerdict json := by
  unfold canonicalizeCapabilitiesVerdict
  rw [decoded]
  change canonicalizeCapabilitiesVerdict
      (encodeCapabilitiesVerdict verdict) =
    .ok (encodeCapabilitiesVerdict verdict)
  exact canonicalizeCapabilitiesVerdict_encode verdict

private theorem decodeParseVerdictKindAt_encode
    (path : DecodePath)
    (verdict : ParseVerdict) :
    decodeParseVerdictKindAt path (encodeParseVerdict verdict) =
      .ok (match verdict with
        | .accepted _ => "accepted"
        | .rejected _ => "rejected"
        | .inconclusive _ => "inconclusive"
        | .internalError _ => "internalError") := by
  cases verdict <;> rfl

private theorem decodeAcceptedParseVerdictAt_encode
    (surfaceLimits : DecodeLimits)
    (path : DecodePath)
    (result : Solcore.Surface.Wire.V1.ParseResult)
    (depthEnough : fileDepth result.value <= surfaceLimits.maxDepth)
    (nodesEnough : fileNodes result.value <= surfaceLimits.maxNodes) :
    decodeAcceptedParseVerdictAt surfaceLimits path
        (encodeParseVerdict (.accepted result)) =
      .ok (.accepted result) := by
  change (do
    let decoded <- decodeParseResultAt surfaceLimits
      (path.field "result") (encodeParseResult result)
    pure (ParseVerdict.accepted decoded)) =
      .ok (ParseVerdict.accepted result)
  rw [decodeParseResultAt_encodeParseResult surfaceLimits
    (path.field "result") result depthEnough nodesEnough]
  rfl

private theorem decodeRejectedParseVerdictAt_encode
    (path : DecodePath)
    (diagnostic : Solcore.Surface.Wire.V1.Diagnostic) :
    decodeRejectedParseVerdictAt path
        (encodeParseVerdict (.rejected diagnostic)) =
      .ok (.rejected diagnostic) := by
  change (do
    let decoded <- decodeDiagnosticAt
      ((path.field "diagnostics").index 0)
      (encodeDiagnostic diagnostic)
    requireLiteralAt (path.field "phase")
      (diagnosticPhaseName diagnostic)
      (diagnosticPhaseName decoded)
    pure (ParseVerdict.rejected decoded)) =
      .ok (ParseVerdict.rejected diagnostic)
  rw [decodeDiagnosticAt_encodeDiagnostic]
  cases diagnostic with
  | mk primary kind display =>
      cases kind <;> rfl

private theorem decodeInconclusiveParseVerdictAt_encode
    (path : DecodePath)
    (exhaustion : SourceBytesExceeded) :
    decodeInconclusiveParseVerdictAt path
        (encodeParseVerdict (.inconclusive exhaustion)) =
      .ok (.inconclusive exhaustion) := by
  change (do
    let decoded <- decodeSourceBytesExceededAt path
      (encodeSourceBytesExceeded exhaustion)
    pure (ParseVerdict.inconclusive decoded)) =
      .ok (ParseVerdict.inconclusive exhaustion)
  rw [decodeSourceBytesExceededAt_encode]
  rfl

private theorem decodeInternalParseVerdictAt_encode
    (path : DecodePath)
    (error : InternalError) :
    decodeInternalParseVerdictAt path
        (encodeParseVerdict (.internalError error)) =
      .ok (.internalError error) := by
  change (do
    let decoded <- decodeInternalErrorAt path (encodeInternalError error)
    pure (ParseVerdict.internalError decoded)) =
      .ok (ParseVerdict.internalError error)
  rw [decodeInternalErrorAt_encodeInternalError]
  rfl

theorem decodeParseVerdictAt_encode
    (surfaceLimits : DecodeLimits)
    (path : DecodePath)
    (verdict : ParseVerdict)
    (within : verdict.WithinSurfaceLimits surfaceLimits) :
    decodeParseVerdictAt surfaceLimits path (encodeParseVerdict verdict) =
      .ok verdict := by
  cases verdict with
  | accepted result =>
      rcases within with ⟨depthEnough, nodesEnough⟩
      unfold decodeParseVerdictAt
      rw [decodeParseVerdictKindAt_encode]
      exact decodeAcceptedParseVerdictAt_encode surfaceLimits path result
        depthEnough nodesEnough
  | rejected diagnostic =>
      unfold decodeParseVerdictAt
      rw [decodeParseVerdictKindAt_encode]
      exact decodeRejectedParseVerdictAt_encode path diagnostic
  | inconclusive exhaustion =>
      unfold decodeParseVerdictAt
      rw [decodeParseVerdictKindAt_encode]
      exact decodeInconclusiveParseVerdictAt_encode path exhaustion
  | internalError error =>
      unfold decodeParseVerdictAt
      rw [decodeParseVerdictKindAt_encode]
      exact decodeInternalParseVerdictAt_encode path error

theorem decodeParseVerdict_encode
    (surfaceLimits : DecodeLimits)
    (verdict : ParseVerdict)
    (within : verdict.WithinSurfaceLimits surfaceLimits) :
    decodeParseVerdict surfaceLimits (encodeParseVerdict verdict) =
      .ok verdict :=
  decodeParseVerdictAt_encode surfaceLimits .root verdict within

theorem canonicalizeParseVerdict_encode
    (surfaceLimits : DecodeLimits)
    (verdict : ParseVerdict)
    (within : verdict.WithinSurfaceLimits surfaceLimits) :
    canonicalizeParseVerdict surfaceLimits (encodeParseVerdict verdict) =
      .ok (encodeParseVerdict verdict) := by
  unfold canonicalizeParseVerdict
  rw [decodeParseVerdict_encode surfaceLimits verdict within]
  rfl

theorem canonicalizeParseVerdict_idempotent
    (surfaceLimits : DecodeLimits)
    (json : Lean.Json)
    (verdict : ParseVerdict)
    (decoded : decodeParseVerdict surfaceLimits json = .ok verdict)
    (within : verdict.WithinSurfaceLimits surfaceLimits) :
    canonicalizeParseVerdict surfaceLimits json >>=
        canonicalizeParseVerdict surfaceLimits =
      canonicalizeParseVerdict surfaceLimits json := by
  unfold canonicalizeParseVerdict
  rw [decoded]
  change canonicalizeParseVerdict surfaceLimits (encodeParseVerdict verdict) =
    .ok (encodeParseVerdict verdict)
  exact canonicalizeParseVerdict_encode surfaceLimits verdict within

theorem decodeResponseAt_encodeResponse
    (surfaceLimits : DecodeLimits)
    (path : DecodePath)
    (response : Response)
    (within : response.WithinSurfaceLimits surfaceLimits) :
    decodeResponseAt surfaceLimits path (encodeResponse response) =
      .ok response := by
  cases response with
  | mk id body =>
      cases body with
      | capabilities verdict =>
          change (do
            let decodedId <- decodeRequestIdAt (path.field "id")
              (encodeRequestId id)
            let _ <- decodeProfileRefAt (path.field "profile")
              (encodeProfileRef ProfileRef.canonical)
            let query <- decodeQueryKindAt (path.field "query")
              (encodeQueryKind .capabilities)
            let body <- match query with
              | .capabilities =>
                  ResponseBody.capabilities <$> decodeCapabilitiesVerdictAt
                    (path.field "verdict")
                    (encodeCapabilitiesVerdict verdict)
              | .parse =>
                  ResponseBody.parse <$> decodeParseVerdictAt surfaceLimits
                    (path.field "verdict")
                    (encodeCapabilitiesVerdict verdict)
            pure ({ id := decodedId, body } : Response)) =
              .ok ({ id, body := .capabilities verdict } : Response)
          rw [decodeRequestIdAt_encodeRequestId]
          rw [decodeProfileRefAt_encodeProfileRef]
          rw [decodeQueryKindAt_encodeQueryKind]
          rw [decodeCapabilitiesVerdictAt_encode]
          rfl
      | parse verdict =>
          change verdict.WithinSurfaceLimits surfaceLimits at within
          change (do
            let decodedId <- decodeRequestIdAt (path.field "id")
              (encodeRequestId id)
            let _ <- decodeProfileRefAt (path.field "profile")
              (encodeProfileRef ProfileRef.canonical)
            let query <- decodeQueryKindAt (path.field "query")
              (encodeQueryKind .parse)
            let body <- match query with
              | .capabilities =>
                  ResponseBody.capabilities <$> decodeCapabilitiesVerdictAt
                    (path.field "verdict") (encodeParseVerdict verdict)
              | .parse =>
                  ResponseBody.parse <$> decodeParseVerdictAt surfaceLimits
                    (path.field "verdict") (encodeParseVerdict verdict)
            pure ({ id := decodedId, body } : Response)) =
              .ok ({ id, body := .parse verdict } : Response)
          rw [decodeRequestIdAt_encodeRequestId]
          rw [decodeProfileRefAt_encodeProfileRef]
          rw [decodeQueryKindAt_encodeQueryKind]
          rw [decodeParseVerdictAt_encode surfaceLimits
            (path.field "verdict") verdict within]
          rfl

theorem decodeResponse_encodeResponse
    (surfaceLimits : DecodeLimits)
    (response : Response)
    (within : response.WithinSurfaceLimits surfaceLimits) :
    decodeResponse surfaceLimits (encodeResponse response) = .ok response :=
  decodeResponseAt_encodeResponse surfaceLimits .root response within

theorem canonicalizeResponse_encodeResponse
    (surfaceLimits : DecodeLimits)
    (response : Response)
    (within : response.WithinSurfaceLimits surfaceLimits) :
    canonicalizeResponse surfaceLimits (encodeResponse response) =
      .ok (encodeResponse response) := by
  unfold canonicalizeResponse
  rw [decodeResponse_encodeResponse surfaceLimits response within]
  rfl

theorem canonicalizeResponse_idempotent
    (surfaceLimits : DecodeLimits)
    (json : Lean.Json)
    (response : Response)
    (decoded : decodeResponse surfaceLimits json = .ok response)
    (within : response.WithinSurfaceLimits surfaceLimits) :
    canonicalizeResponse surfaceLimits json >>=
        canonicalizeResponse surfaceLimits =
      canonicalizeResponse surfaceLimits json := by
  unfold canonicalizeResponse
  rw [decoded]
  change canonicalizeResponse surfaceLimits (encodeResponse response) =
    .ok (encodeResponse response)
  exact canonicalizeResponse_encodeResponse surfaceLimits response within

private theorem decodeOptionalRequestIdAt_encode
    (path : DecodePath)
    (id : Option RequestId) :
    decodeOptionalRequestIdAt path (encodeOptionalRequestId id) = .ok id := by
  cases id with
  | none => rfl
  | some id =>
      have notNull : (encodeRequestId id).isNull = false := by
        cases id
        rfl
      simp [decodeOptionalRequestIdAt, encodeOptionalRequestId, notNull]
      rfl

@[simp] theorem decodeProtocolErrorAt_encodeProtocolError
    (path : DecodePath)
    (error : ProtocolError) :
    decodeProtocolErrorAt path (encodeProtocolError error) = .ok error := by
  change (do
    let decodedId <- decodeOptionalRequestIdAt (path.field "id")
      (encodeOptionalRequestId error.id)
    pure ({
      id := decodedId
      code := error.code
      path := error.path
      arguments := error.arguments
      display := error.display
    } : ProtocolError)) = .ok error
  rw [decodeOptionalRequestIdAt_encode]
  cases error
  rfl

@[simp] theorem decodeProtocolError_encodeProtocolError
    (error : ProtocolError) :
    decodeProtocolError (encodeProtocolError error) = .ok error :=
  decodeProtocolErrorAt_encodeProtocolError .root error

@[simp] theorem canonicalizeProtocolError_encodeProtocolError
    (error : ProtocolError) :
    canonicalizeProtocolError (encodeProtocolError error) =
      .ok (encodeProtocolError error) := by
  unfold canonicalizeProtocolError
  rw [decodeProtocolError_encodeProtocolError]
  rfl

theorem canonicalizeProtocolError_idempotent
    (json : Lean.Json)
    (error : ProtocolError)
    (decoded : decodeProtocolError json = .ok error) :
    canonicalizeProtocolError json >>= canonicalizeProtocolError =
      canonicalizeProtocolError json := by
  unfold canonicalizeProtocolError
  rw [decoded]
  change canonicalizeProtocolError (encodeProtocolError error) =
    .ok (encodeProtocolError error)
  exact canonicalizeProtocolError_encodeProtocolError error

end Solcore.Oracle.V4
