import Solcore.Oracle.V5.Wire.ScenarioShape

/-! Shallow-envelope and complete Oracle-only request shape decoding. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

structure ShallowRequest where
  id : RequestId
  limits : Limits
  limitsValid : limits.Valid
  queryKind : QueryKind

structure RawRequest where
  id : RequestId
  limits : Limits
  limitsValid : limits.Valid
  query : RawQuery

private def invalidIdentityAt {α : Type}
    (path : Path)
    (code : DecodeErrorCode)
    (expected actual : String) : DecodeResult α :=
  failAt path code (.mkObj [
    ("expected", expected),
    ("actual", actual)
  ])

private def decodeShallowProfileAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ProfileRef := do
  ensureExactObject path json ["digest", "id"] ["digest", "id"]
  let actualDigest ← decodeStringAt (path.field "digest")
    (← requireField path json "digest")
  let actualId ← decodeStringAt (path.field "id")
    (← requireField path json "id")
  let expected := ProfileRef.canonical
  unless actualId == expected.id && actualDigest == expected.digest do
    failAt path .invalidProfile (.mkObj [
      ("expectedId", expected.id),
      ("expectedDigest", expected.digest),
      ("actualId", actualId),
      ("actualDigest", actualDigest)
    ])
  pure expected

private def decodeShallowQueryKindAt
    (path : Path)
    (json : Lean.Json) : DecodeResult QueryKind := do
  let kindPath := path.field "kind"
  let kind ← decodeStringAt kindPath (← requireField path json "kind")
  match kind with
  | "capabilities" => pure .capabilities
  | "coreCheck" => pure .coreCheck
  | "execute" => pure .execute
  | _ => invalidTagAt kindPath (.str kind) <|
      .arr #["capabilities", "coreCheck", "execute"]

def decodeLimitsAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Limits := do
  let fields := [
    "calldataBytes", "coreDepth", "coreNodes", "evaluationSteps",
    "identifierBytes", "jsonDepth", "jsonNodes", "scenarioEntries"
  ]
  ensureExactObject path json fields fields
  let calldataBytes ← decodeNatAt (path.field "calldataBytes")
    (← requireField path json "calldataBytes")
  unless calldataBytes < Core.wordModulus do
    failAt (path.field "calldataBytes") .invalidLimit (.mkObj [
      ("field", "calldataBytes"),
      ("constraint", "strictly-less-than-2^256")
    ])
  let coreDepth ← decodeNatAt (path.field "coreDepth")
    (← requireField path json "coreDepth")
  let coreNodes ← decodeNatAt (path.field "coreNodes")
    (← requireField path json "coreNodes")
  let evaluationSteps ← decodeNatAt (path.field "evaluationSteps")
    (← requireField path json "evaluationSteps")
  let identifierBytes ← decodeNatAt (path.field "identifierBytes")
    (← requireField path json "identifierBytes")
  let jsonDepth ← decodeNatAt (path.field "jsonDepth")
    (← requireField path json "jsonDepth")
  let jsonNodes ← decodeNatAt (path.field "jsonNodes")
    (← requireField path json "jsonNodes")
  let scenarioEntries ← decodeNatAt (path.field "scenarioEntries")
    (← requireField path json "scenarioEntries")
  pure {
    jsonDepth
    jsonNodes
    coreDepth
    coreNodes
    scenarioEntries
    identifierBytes
    calldataBytes
    evaluationSteps
  }

/--
Recover exactly the fields needed before whole-tree JSON resource accounting.
Root unknown-field validation intentionally belongs to the later full pass.
-/
def decodeShallowRequest
    (json : Lean.Json) : DecodeResult ShallowRequest := do
  let path := Path.root
  let _ ← match json with
    | .obj _ => pure ()
    | _ => failAt path .expectedObject (expectedArguments "object" json)
  let schemaPath := path.field "schema"
  let actualSchema ← decodeStringAt schemaPath
    (← requireField path json "schema")
  unless actualSchema == schemaVersion do
    invalidIdentityAt schemaPath .invalidSchema schemaVersion actualSchema
  let id ← decodeRequestIdAt (path.field "id")
    (← requireField path json "id")
  let _ ← decodeShallowProfileAt (path.field "profile")
    (← requireField path json "profile")
  let limits ← decodeLimitsAt (path.field "limits")
    (← requireField path json "limits")
  let queryKind ← decodeShallowQueryKindAt (path.field "query")
    (← requireField path json "query")
  if valid : limits.calldataBytes < Core.wordModulus then
    pure {
      id
      limits
      limitsValid := by simpa [Limits.Valid] using valid
      queryKind
    }
  else
    failAt (path.field "limits" |>.field "calldataBytes") .invalidLimit
      (.mkObj [
        ("field", "calldataBytes"),
        ("constraint", "strictly-less-than-2^256")
      ])

def decodeProfileAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ProfileRef :=
  decodeShallowProfileAt path json

def decodeRawStaticMethodAt
    (path : Path)
    (json : Lean.Json) : DecodeResult RawStaticMethod := do
  ensureExactObject path json
    ["implementation", "name"] ["implementation", "name"]
  let implementationPath := path.field "implementation"
  let implementation ← requireField path json "implementation"
  let name ← decodeStringAt (path.field "name")
    (← requireField path json "name")
  pure { name, implementation, implementationPath }

def decodeRawContractAt
    (path : Path)
    (json : Lean.Json) : DecodeResult RawContract := do
  ensureExactObject path json
    ["id", "kind", "methods", "program"] ["id", "kind"]
  let kindPath := path.field "kind"
  let kind ← decodeStringAt kindPath (← requireField path json "kind")
  let (id, spec) ← match kind with
  | "checkedCore" => do
      ensureExactObject path json
        ["id", "kind", "program"] ["id", "kind", "program"]
      let id ← decodeStringAt (path.field "id")
        (← requireField path json "id")
      let programPath := path.field "program"
      let program ← requireField path json "program"
      pure (id, .checkedCore program programPath)
  | "staticWordAbi" => do
      ensureExactObject path json
        ["id", "kind", "methods"] ["id", "kind", "methods"]
      let id ← decodeStringAt (path.field "id")
        (← requireField path json "id")
      let methods ← decodeArrayAt decodeRawStaticMethodAt
        (path.field "methods") (← requireField path json "methods")
      pure (id, .staticWordAbi methods)
  | _ => invalidTagAt kindPath (.str kind) <|
      .arr #["checkedCore", "staticWordAbi"]
  pure { id, spec }

def decodeRawScenarioAt
    (path : Path)
    (json : Lean.Json) : DecodeResult RawScenario := do
  ensureExactObject path json
    ["contracts", "environment", "invocation", "kind", "world"]
    ["contracts", "environment", "invocation", "kind", "world"]
  let contracts ← decodeArrayAt decodeRawContractAt
    (path.field "contracts") (← requireField path json "contracts")
  let environment ← decodeEnvironmentAt (path.field "environment")
    (← requireField path json "environment")
  let invocation ← decodeInvocationAt (path.field "invocation")
    (← requireField path json "invocation")
  let world ← decodeWorldAt (path.field "world")
    (← requireField path json "world")
  pure { contracts, world, environment, invocation }

def decodeRawQueryAt
    (path : Path)
    (json : Lean.Json) : DecodeResult RawQuery := do
  ensureExactObject path json
    ["contracts", "environment", "invocation", "kind", "program", "world"]
    ["kind"]
  let kindPath := path.field "kind"
  let kind ← decodeStringAt kindPath (← requireField path json "kind")
  match kind with
  | "capabilities" => do
      ensureExactObject path json ["kind"] ["kind"]
      pure .capabilities
  | "coreCheck" => do
      ensureExactObject path json ["kind", "program"] ["kind", "program"]
      let programPath := path.field "program"
      let program ← requireField path json "program"
      pure (.coreCheck program programPath)
  | "execute" => do
      ensureExactObject path json
        ["contracts", "environment", "invocation", "kind", "world"]
        ["contracts", "environment", "invocation", "kind", "world"]
      let scenario ← decodeRawScenarioAt path json
      pure (.execute scenario)
  | _ => invalidTagAt kindPath (.str kind) <|
      .arr #["capabilities", "coreCheck", "execute"]

/-- Complete Oracle-only shape pass, leaving every Core subtree opaque. -/
def decodeRequestShape
    (shallow : ShallowRequest)
    (json : Lean.Json) : DecodeResult RawRequest := do
  let path := Path.root
  ensureExactObject path json
    ["id", "limits", "profile", "query", "schema", "spec"]
    ["id", "limits", "profile", "query", "schema", "spec"]
  let _ ← decodeProfileAt (path.field "profile")
    (← requireField path json "profile")
  let query ← decodeRawQueryAt (path.field "query")
    (← requireField path json "query")
  let specPath := path.field "spec"
  let actualSpec ← decodeStringAt specPath
    (← requireField path json "spec")
  unless actualSpec == Solcore.m3aLanguage.id do
    invalidIdentityAt specPath .invalidSpec Solcore.m3aLanguage.id actualSpec
  pure {
    id := shallow.id
    limits := shallow.limits
    limitsValid := shallow.limitsValid
    query
  }

end Solcore.Oracle.V5.Wire
