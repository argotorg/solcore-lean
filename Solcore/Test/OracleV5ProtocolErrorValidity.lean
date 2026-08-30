import Solcore.Oracle.V5.Wire.Protocol
import Solcore.Oracle.V5.Wire.ResponseEncode

/-! Closure regressions for proof-carrying Oracle v5 protocol errors. -/

set_option autoImplicit false

namespace Tests.OracleV5ProtocolErrorValidity

open Solcore.Oracle.V5
open Solcore.Oracle.V5.Wire

private def requestId : RequestId := ⟨"protocol-error-test", by decide⟩

private def expectedArguments (expected : String) : Lean.Json :=
  .mkObj [("expected", expected), ("actual", "null")]

private def oracleArguments : DecodeErrorCode → Lean.Json
  | .expectedObject => expectedArguments "object"
  | .expectedArray => expectedArguments "array"
  | .expectedString => expectedArguments "string"
  | .expectedBool => expectedArguments "boolean"
  | .expectedNatural => expectedArguments "number"
  | .missingField => .mkObj [("field", "missing")]
  | .unknownField => .mkObj [("field", "future")]
  | .invalidSchema => .mkObj [("expected", schemaVersion), ("actual", "future")]
  | .invalidSpec => .mkObj [
      ("expected", Solcore.m3aLanguage.id), ("actual", "future")]
  | .invalidProfile => .mkObj [
      ("expectedId", ProfileRef.canonical.id),
      ("expectedDigest", ProfileRef.canonical.digest),
      ("actualId", "future"),
      ("actualDigest", "sha256:future")
    ]
  | .invalidTag => .mkObj [("actual", "future"), ("expected", .arr #["known"])]
  | .invalidWord => .mkObj [("reason", "prefix")]
  | .invalidAddress => .mkObj [("reason", "length")]
  | .invalidBytes => .mkObj [("reason", "odd-length")]
  | .invalidRequestId => .mkObj [("constraint", "nonempty-utf8")]
  | .invalidLimit => .mkObj [
      ("field", "calldataBytes"),
      ("constraint", "strictly-less-than-2^256")
    ]

private def oracleCodes : List DecodeErrorCode := [
  .expectedObject, .expectedArray, .expectedString, .expectedBool,
  .expectedNatural, .missingField, .unknownField, .invalidSchema,
  .invalidSpec, .invalidProfile, .invalidTag, .invalidWord,
  .invalidAddress, .invalidBytes, .invalidRequestId, .invalidLimit
]

private def coreArguments :
    Solcore.Core.Wire.V3.DecodeErrorCode → Lean.Json
  | .expectedObject => expectedArguments "object"
  | .expectedArray => expectedArguments "array"
  | .expectedString => expectedArguments "string"
  | .expectedBool => expectedArguments "boolean"
  | .expectedNatural => expectedArguments "number"
  | .missingField => .mkObj [("field", "missing")]
  | .unknownField => .mkObj [("field", "future")]
  | .invalidSchema => .mkObj [
      ("expected", Solcore.Core.Wire.V3.schemaVersion), ("actual", "future")]
  | .invalidTag => .mkObj [("actual", "future"), ("expected", .arr #["known"])]
  | .invalidType => .mkObj [
      ("actual", "future"), ("allowed", .arr #["unit", "bool", "word"])]
  | .invalidWord => .mkObj [("reason", "lowercase-hex")]

private def coreCodes : List Solcore.Core.Wire.V3.DecodeErrorCode := [
  .expectedObject, .expectedArray, .expectedString, .expectedBool,
  .expectedNatural, .missingField, .unknownField, .invalidSchema,
  .invalidTag, .invalidType, .invalidWord
]

private def oraclePath (code : DecodeErrorCode) : Path :=
  match code with
  | .missingField => Path.root.field "missing"
  | .unknownField => Path.root.field "future"
  | .invalidSchema => Path.root.field "schema"
  | .invalidSpec => Path.root.field "spec"
  | .invalidProfile => Path.root.field "profile"
  | .invalidRequestId => Path.root.field "id"
  | .invalidLimit => (Path.root.field "limits").field "calldataBytes"
  | _ => Path.root.field "value"

private def corePath
    (code : Solcore.Core.Wire.V3.DecodeErrorCode) :
    Solcore.Core.Wire.V3.DecodePath :=
  match code with
  | .missingField => Solcore.Core.Wire.V3.DecodePath.root.field "missing"
  | .unknownField => Solcore.Core.Wire.V3.DecodePath.root.field "future"
  | .invalidSchema => Solcore.Core.Wire.V3.DecodePath.root.field "schema"
  | _ => Solcore.Core.Wire.V3.DecodePath.root.field "program"

private def oracleProducerDoesNotFallback (code : DecodeErrorCode) : Bool :=
  let internal : Solcore.Oracle.V5.Wire.ProtocolError :=
    .oracle (oraclePath code) code (oracleArguments code)
  let sealed := internal.toPublic (some requestId)
  sealed.value == ({
    id := some requestId
    code := internal.code
    path := internal.path.toPointer
    arguments := internal.arguments
    display := internal.display
  } : Solcore.Oracle.V5.ProtocolError)

private def coreProducerDoesNotFallback
    (code : Solcore.Core.Wire.V3.DecodeErrorCode) : Bool :=
  let core : Solcore.Core.Wire.V3.DecodeError := {
    path := corePath code
    code
    arguments := coreArguments code
  }
  let internal : Solcore.Oracle.V5.Wire.ProtocolError := .core core
  let sealed := internal.toPublic (some requestId)
  sealed.value == ({
    id := some requestId
    code := internal.code
    path := internal.path.toPointer
    arguments := internal.arguments
    display := internal.display
  } : Solcore.Oracle.V5.ProtocolError)

private def allCatalogProducersDoNotFallback : Bool :=
  oracleCodes.all oracleProducerDoesNotFallback &&
    coreCodes.all coreProducerDoesNotFallback

private def schemaProducerDoesNotFallback (expected : String) : Bool :=
  let internal : Solcore.Oracle.V5.Wire.ProtocolError := .oracle
    (Path.root.field "schema") .invalidSchema (.mkObj [
      ("expected", expected), ("actual", "future")])
  let sealed := internal.toPublic (some requestId)
  sealed.value == ({
    id := some requestId
    code := internal.code
    path := internal.path.toPointer
    arguments := internal.arguments
    display := internal.display
  } : Solcore.Oracle.V5.ProtocolError)

private def allSchemaProducersDoNotFallback : Bool :=
  [schemaVersion, capabilitiesSchema, checkResultSchema,
    executionSchema, stateObservationSchema].all schemaProducerDoesNotFallback

private def validRaw : Solcore.Oracle.V5.ProtocolError := {
  code := "oracle.wire.unknown-field"
  path := "/query/future"
  arguments := .mkObj [("field", "future")]
  display := "invalid Oracle v5 value"
}

private def invalidRaws : List Solcore.Oracle.V5.ProtocolError := [
  { validRaw with code := "oracle.wire.future" },
  { validRaw with display := "invalid Semantic Core v3 program" },
  { validRaw with path := "query/future" },
  { validRaw with path := "/query/~2future" },
  { validRaw with arguments := .mkObj [
      ("field", "future"), ("extra", true)] },
  { validRaw with
      code := "oracle.wire.expected-natural"
      arguments := .mkObj [("expected", "natural"), ("actual", "null")]
    },
  { validRaw with
      code := "oracle.wire.expected-natural"
      arguments := .mkObj [("expected", "number"), ("actual", "number")]
    },
  { validRaw with
      code := "oracle.wire.invalid-schema"
      path := "/schema"
      arguments := .mkObj [("expected", "future"), ("actual", "actual")]
    },
  { validRaw with
      code := "oracle.wire.invalid-spec"
      path := "/spec"
      arguments := .mkObj [("expected", "future"), ("actual", "actual")]
    },
  { validRaw with
      code := "oracle.wire.invalid-profile"
      path := "/profile"
      arguments := .mkObj [
        ("expectedId", "future"),
        ("expectedDigest", ProfileRef.canonical.digest),
        ("actualId", "actual"), ("actualDigest", "actual")]
    },
  { validRaw with
      arguments := .mkObj [("field", "other")]
    },
  { validRaw with
      code := "oracle.wire.missing-field"
      arguments := .mkObj [("field", "other")]
    },
  { validRaw with
      code := "oracle.wire.invalid-bytes"
      arguments := .mkObj [("reason", "length")]
    },
  { validRaw with
      code := "oracle.wire.invalid-request-id"
      path := "/query/id"
      arguments := .mkObj [("constraint", "nonempty-utf8")]
    },
  { validRaw with
      code := "oracle.wire.invalid-limit"
      path := "/calldataBytes"
      arguments := .mkObj [
        ("field", "calldataBytes"),
        ("constraint", "strictly-less-than-2^256")]
    },
  { validRaw with
      code := "core.wire.invalid-type"
      display := "invalid Semantic Core v3 program"
      arguments := .mkObj [
        ("actual", "future"), ("allowed", .arr #["future"])]
    },
  { validRaw with
      id := some requestId
      code := "malformed-json"
      path := ""
      arguments := .null
      display := "parser failure"
    },
  { validRaw with
      code := "malformed-json"
      path := "/query"
      arguments := .null
      display := "parser failure"
    },
  { validRaw with
      code := "malformed-json"
      path := ""
      arguments := .mkObj []
      display := "parser failure"
    }
]

private def rawInvalidValuesRejected : Bool :=
  (ValidProtocolError.of? validRaw).isSome &&
    invalidRaws.all (fun raw => (ValidProtocolError.of? raw).isNone)

private def malformedClosed : Bool :=
  let error := ValidProtocolError.malformedJson "duplicate object key"
  error.value == ({
    code := "malformed-json"
    path := ""
    arguments := .null
    display := "duplicate object key"
  } : Solcore.Oracle.V5.ProtocolError) && error.value.isValid

private def pointersClosed : Bool :=
  ProtocolError.canonicalPointer "" &&
    ProtocolError.canonicalPointer "/query/~0/~1" &&
    !ProtocolError.canonicalPointer "query" &&
    !ProtocolError.canonicalPointer "/query/~" &&
    !ProtocolError.canonicalPointer "/query/~2"

/-- This annotation regresses the public encoder's proof-carrying domain. -/
private def sealedEncoder : ValidProtocolError → Lean.Json :=
  encodeProtocolError

private def sealedEncoderExact : Bool :=
  match ValidProtocolError.of? validRaw with
  | some error =>
      match (sealedEncoder error).getObjVal? "code" with
      | .ok code => code == "oracle.wire.unknown-field"
      | .error _ => false
  | none => false

private def allChecks : Bool :=
  allCatalogProducersDoNotFallback && allSchemaProducersDoNotFallback &&
    rawInvalidValuesRejected && malformedClosed && pointersClosed &&
    sealedEncoderExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ProtocolErrorValidity : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 protocol-error sealing changed")

end Tests.OracleV5ProtocolErrorValidity
