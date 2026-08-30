import Solcore.Oracle.V5.Wire.CapabilityDecode

/-! Focused precedence and singleton tests for Oracle v5 response components. -/

set_option autoImplicit false

namespace Tests.OracleV5ResponseShape

open Solcore.Oracle.V5
open Solcore.Oracle.V5.Wire

private def errorAt {α : Type}
    (result : DecodeResult α)
    (pointer : String)
    (code : DecodeErrorCode) : Bool :=
  match result with
  | .error (.oracle path actualCode _) =>
      path.toPointer == pointer && actualCode == code
  | _ => false

private def capabilityRoundTrip : Bool :=
  match decodeCapabilityResultAt .root
      (encodeCapabilityResult capabilityReport) with
  | .ok report => report == capabilityReport
  | .error _ => false

private def replaceCapabilityField
    (json : Lean.Json)
    (name : String)
    (value : Lean.Json) : Lean.Json :=
  json.setObjVal! "value" ((json.getObjValD "value").setObjVal! name value)

private def capabilityFieldSetPrecedence : Bool :=
  let expected := encodeCapabilityResult capabilityReport
  let unknown := replaceCapabilityField expected "future" true
  let missingAndLaterUnknown :=
    expected.setObjVal! "value" (.mkObj [("zzz", true)])
  errorAt (decodeCapabilityResultAt .root unknown)
      "/value/future" .unknownField &&
    errorAt (decodeCapabilityResultAt .root missingAndLaterUnknown)
      "/value/abiProfiles" .missingField

private def capabilityScalarPrecedence : Bool :=
  let expected := encodeCapabilityResult capabilityReport
  let twoBad := replaceCapabilityField
    (replaceCapabilityField expected "abiProfiles" true)
    "baselines" .null
  let limits := (expected.getObjValD "value").getObjValD "defaultLimits"
  let badLimits := (limits.setObjVal! "calldataBytes" 1)
    |>.setObjVal! "coreDepth" false
  let defaultBad := replaceCapabilityField expected "defaultLimits" badLimits
  errorAt (decodeCapabilityResultAt .root twoBad)
      "/value/abiProfiles" .expectedArray &&
    errorAt (decodeCapabilityResultAt .root defaultBad)
      "/value/defaultLimits/calldataBytes" .invalidTag &&
    errorAt (decodeCapabilityResultAt .root <|
      replaceCapabilityField expected "maxNestedCallDepth" 2)
      "/value/maxNestedCallDepth" .invalidTag

private def capabilityRecursivePrecedence : Bool :=
  let expected := encodeCapabilityResult capabilityReport
  let wrongFirst := replaceCapabilityField expected "abiProfiles"
    (.arr #["wrong", 7])
  let profile := (expected.getObjValD "value").getObjValD "profile"
  let unknownNested := replaceCapabilityField expected "profile"
    (profile.setObjVal! "future" true)
  errorAt (decodeCapabilityResultAt .root wrongFirst)
      "/value/abiProfiles/0" .invalidTag &&
    errorAt (decodeCapabilityResultAt .root unknownNested)
      "/value/profile/future" .unknownField

private def capabilityIdentitiesAndCanonicalNaturals : Bool :=
  let expected := encodeCapabilityResult capabilityReport
  let decimalOne : Lean.Json := .num { mantissa := 10, exponent := 1 }
  let canonicalizable :=
    replaceCapabilityField expected "maxNestedCallDepth" decimalOne
  let canonicalAccepted :=
    match decodeCapabilityResultAt .root canonicalizable with
    | .ok report => report == capabilityReport
    | .error _ => false
  canonicalAccepted &&
    errorAt (decodeCapabilityResultAt .root <|
      replaceCapabilityField expected "schema" "future")
      "/value/schema" .invalidSchema &&
    errorAt (decodeCapabilityResultAt .root <|
      replaceCapabilityField expected "spec" "future")
      "/value/spec" .invalidSpec

private def coreResultOwnership : Bool :=
  let result := encodeCoreCheckResult { resultType := .word }
  let bad := result.setObjVal! "value" <|
    (result.getObjValD "value").setObjVal! "resultType" false
  match decodeCoreCheckResultAt .root bad with
  | .error (.core error) =>
      error.path.toPointer == "/value/resultType" &&
        error.code == .invalidType
  | _ => false

private def inconclusive
    (consumed limit : Nat)
    (phase resource : String) : Lean.Json :=
  .mkObj [
    ("kind", "inconclusive"),
    ("phase", phase),
    ("resource", resource),
    ("limit", limit),
    ("consumed", consumed)
  ]

private def inconclusiveCrossFieldPrecedence : Bool :=
  let consumedFirst := inconclusive 1 2 "protocol" "jsonDepth"
  let phaseAfterConsumption :=
    inconclusive 3 2 "protocol" "jsonDepth"
  let resourceAfterConsumption :=
    inconclusive 2 2 "contractExecution" "evaluationSteps"
  errorAt (decodeInconclusiveAt true .root consumedFirst)
      "/consumed" .invalidTag &&
    errorAt (decodeInconclusiveAt true .root phaseAfterConsumption)
      "/phase" .invalidTag &&
    errorAt (decodeInconclusiveAt false .root resourceAfterConsumption)
      "/resource" .invalidTag

private def internalErrorClosed : Bool :=
  (match decodeInternalErrorVerdictAt .root (.mkObj [
    ("kind", "internalError"),
    ("phase", .null),
    ("code", "oracle-response-invariant")
  ]) with
  | .ok .oracleResponseInvariant => true
  | _ => false) &&
  errorAt (decodeInternalErrorVerdictAt .root (.mkObj [
    ("kind", "internalError"),
    ("phase", .null),
    ("code", "future")
  ])) "/code" .invalidTag

private def allChecks : Bool :=
  capabilityRoundTrip && capabilityFieldSetPrecedence &&
    capabilityScalarPrecedence && capabilityRecursivePrecedence &&
    capabilityIdentitiesAndCanonicalNaturals && coreResultOwnership &&
    inconclusiveCrossFieldPrecedence && internalErrorClosed

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ResponseShape : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 response component decoding changed")

end Tests.OracleV5ResponseShape
