# Oracle v5 wire catalog

This page is the closed JSON catalog for `solcore-oracle/v5`. It fixes the
public names and shapes chosen by ADR-0151; implementations must not infer new
fields from later internal Lean types. Semantic Core programs use the separate
[Core Wire v3 catalog](CORE_WIRE_V3.md).

Every object has exactly the fields shown. All shown fields are required unless
the text explicitly says otherwise. Unknown and missing fields are rejected.
Examples are pretty-printed for readability; canonical encoding is compact.

## Fixed identities and scalar forms

| Name | Exact value |
| --- | --- |
| Oracle schema | `solcore-oracle/v5` |
| Specification | `solcore/0.1.0-draft.5` |
| Profile ID | `contract-m3a-v1` |
| Profile digest | `sha256:da3d49b830d25705634cfda568691f1f12fe5a7d038bd0b7ca5839134c1073d5` |
| Capability schema | `solcore-capabilities/v5` |
| Core schema | `solcore-semantic-core/v3` |
| Check-result schema | `solcore-core-check-result/v3` |
| Execution schema | `solcore-contract-execution/v1` |
| State-observation schema | `solcore-world-state-observation/v1` |
| Static Word ABI profile | `staticWordAbiV1` |

The complete canonical profile object is
[`profiles/solcore-0.1.0-draft.5-contract-m3a.json`](../profiles/solcore-0.1.0-draft.5-contract-m3a.json).

- A Word is `0x` followed by exactly 64 lowercase hexadecimal digits.
- An Address is `0x` followed by exactly 40 lowercase hexadecimal digits.
- Bytes are `0x` followed by an even number of lowercase hexadecimal digits;
  `0x` is the empty byte sequence.
- A natural is any JSON number accepted by `Foundation.jsonNatural?`.
  Encoding always emits its integer spelling.
- A request ID is a nonempty UTF-8 string.
- A contract ID is an ASCII string matching
  `[A-Za-z_][A-Za-z0-9_.-]*`.
- A method name follows ADR-0150's stricter ASCII grammar
  `[A-Za-z_][A-Za-z0-9_]*`.
- Nullable values use JSON `null`; an absent field never means `null`.

The `identifierBytes` limit applies separately to the UTF-8 byte length of the
request ID, every contract ID, and every method name.

## Request envelope

Every request is this exact object:

```json
{
  "schema": "solcore-oracle/v5",
  "id": "request-id",
  "spec": "solcore/0.1.0-draft.5",
  "profile": {
    "id": "contract-m3a-v1",
    "digest": "sha256:da3d49b830d25705634cfda568691f1f12fe5a7d038bd0b7ca5839134c1073d5"
  },
  "limits": {
    "jsonDepth": 2048,
    "jsonNodes": 2000000,
    "coreDepth": 1024,
    "coreNodes": 1000000,
    "scenarioEntries": 100000,
    "identifierBytes": 256,
    "calldataBytes": 1048576,
    "evaluationSteps": 1000000
  },
  "query": { "kind": "capabilities" }
}
```

All eight limit fields are required. The numbers above are the advertised
defaults, not decoder fallbacks. Every field is an otherwise-unbounded natural;
the sole additional range constraint is `calldataBytes < 2^256`. A missing or
malformed natural is `oracle.wire.missing-field` or
`oracle.wire.expected-natural`; violation of that sole range constraint is
`oracle.wire.invalid-limit`. Zero is valid for every limit.

### Counting rules

- A JSON node is one object, array, string, number, Boolean, or `null`. The root
  has depth one; every contained value increases depth by one. `jsonNodes` and
  `jsonDepth` measure the complete parsed request, including unknown subtrees.
- A Core node is one expected Program, DataDefinition, Type, or Expression
  position from Core Wire v3. Embedded Types count recursively. Operator
  strings, tags, natural identities, and array containers add no Core node.
  `coreNodes` is the sum for every Program in the request. `coreDepth` is the
  greatest Program-to-Core-node nesting depth among them, with the Program at
  depth one. The Core decoder consumes the depth and node budget before
  validating the node at that position. If counting an expected Core node would
  make demand exceed the limit, that inconclusive result precedes validation of
  the node; demand equal to the limit still validates it and may produce a
  protocol error.
- `scenarioEntries` is the sum of the lengths of `contracts`, every
  `staticWordAbi.methods`, `world.accounts`, every account's `storage`,
  `callRegistry`, `creationTemplates`, `creationAddressPolicy.routes`, and
  `invocation.probes`. Lists inside Core Programs are excluded because their
  elements already count as Core nodes.
- `calldataBytes` measures the decoded byte length, not hexadecimal source
  characters. `evaluationSteps` is passed unchanged as executor fuel.

Resource and structural selection is ordered as follows:

1. recover and validate the shallow schema, request ID, profile, complete
   Limits, and query-kind discriminator;
2. measure whole-tree `jsonDepth`, then `jsonNodes`, including unknown subtrees;
3. decode exact Oracle envelope/scenario structure and non-Core scalars, treating
   each embedded Program subtree as opaque;
4. decode Programs in canonical package order, consuming `coreDepth` and then
   `coreNodes` before validating each expected Core node;
5. after structural decoding, measure `scenarioEntries`, `identifierBytes`, then
   `calldataBytes`; and
6. perform semantic checking, admission, materialization, and execution.

Only the query's `kind` field is read in the shallow pass. Its remaining exact
object shape is still validated in step 3. Retaining the validated kind before
resource traversal is what makes a JSON-budget `inconclusive` response carry
the required query-compatible response envelope.

Execution fuel is considered only after admission. A structural error found in
step 3 precedes the later typed-size measurements; a Core budget overrun at the
same position as a Core structural error precedes that error.

## Queries

The query tag is exactly one of `capabilities`, `coreCheck`, or `execute`.

### `capabilities`

```json
{ "kind": "capabilities" }
```

### `coreCheck`

```json
{
  "kind": "coreCheck",
  "program": {
    "schema": "solcore-semantic-core/v3",
    "resultType": "word",
    "dataDefinitions": [],
    "body": { "tag": "word", "value": "0x0000000000000000000000000000000000000000000000000000000000000007" }
  }
}
```

`program` is exactly one Core Wire v3 Program. Checking uses the frozen
14-entry host context in the Core Wire v3 catalog.

### `execute`

```json
{
  "kind": "execute",
  "contracts": [],
  "world": { "accounts": [] },
  "environment": {
    "callRegistry": [],
    "creationTemplates": [],
    "creationAddressPolicy": {
      "routes": [],
      "defaultAddress": "0x0000000000000000000000000000000000000000"
    }
  },
  "invocation": {
    "target": "0x0000000000000000000000000000000000000000",
    "caller": "0x0000000000000000000000000000000000000000",
    "callValue": "0x0000000000000000000000000000000000000000000000000000000000000000",
    "calldata": "0x",
    "probes": []
  }
}
```

The empty example is structurally valid but is rejected at root installation.
The root contract is derived from the target Account's `code`; it is never a
second caller-controlled invocation field.

## Contract package

`contracts` is an array of either exact variant below.

```json
{
  "id": "counter",
  "kind": "checkedCore",
  "program": { "schema": "solcore-semantic-core/v3", "resultType": "word", "dataDefinitions": [], "body": { "tag": "word", "value": "0x0000000000000000000000000000000000000000000000000000000000000000" } }
}
```

```json
{
  "id": "counterAbi",
  "kind": "staticWordAbi",
  "methods": [
    {
      "name": "increment",
      "implementation": { "schema": "solcore-semantic-core/v3", "resultType": { "tag": "function", "parameter": "word", "result": "word" }, "dataDefinitions": [], "body": { "tag": "lambda", "parameterType": "word", "resultType": "word", "body": { "tag": "var", "index": 0 } } }
    }
  ]
}
```

For `checkedCore`, the result type determines the only two v5 profiles:

| Result Type | Profile |
| --- | --- |
| `"word"` | `returnWord` |
| `{"tag":"sum","left":"word","right":{"tag":"sum","left":"word","right":"word"}}` | `wordOutcomeV1` |

A Static Word method has exactly `name` and `implementation`; signature, input,
output, and selector are derived. Its Program must have empty data definitions
and result type `word -> word`.

Contract IDs are unique. After admission, underlying checked Core Programs are
also pairwise distinct across both variants. A duplicate generated ABI Program
therefore conflicts with an equal `checkedCore` Program as well as another ABI
definition. Every later contract reference must name one admitted entry.

## Finite world

`world` has exactly the field `accounts`. Every Account is:

```json
{
  "address": "0x0000000000000000000000000000000000000001",
  "balance": "0x0000000000000000000000000000000000000000000000000000000000000000",
  "nonce": "0x0000000000000000000000000000000000000000000000000000000000000000",
  "storage": [
    {
      "slot": "0x0000000000000000000000000000000000000000000000000000000000000001",
      "value": "0x0000000000000000000000000000000000000000000000000000000000000002"
    }
  ],
  "code": "counter"
}
```

`code` is a contract ID or `null`. Account addresses and slots within one
Account are unique. A storage `value` of zero is rejected; a missing slot is
the canonical sparse representation of zero. An omitted Account is absent,
which remains distinct from an explicitly present empty Account.

## Immutable environment

`callRegistry` entries are:

```json
{ "address": "0x0000000000000000000000000000000000000002", "contract": "callee" }
```

Addresses are unique. A binding may deliberately be absent from or disagree
with the current world's installed code; nested resolution then produces the
ordinary semantic `unavailable` result. Only dangling contract IDs are input
rejections.

`creationTemplates` entries are:

```json
{
  "templateId": "0x0000000000000000000000000000000000000000000000000000000000000003",
  "initializer": "initializer",
  "runtime": "runtime"
}
```

Template IDs are unique. Both contract references must resolve.

`creationAddressPolicy` is:

```json
{
  "routes": [
    {
      "creator": "0x0000000000000000000000000000000000000001",
      "nonce": "0x0000000000000000000000000000000000000000000000000000000000000000",
      "address": "0x0000000000000000000000000000000000000003"
    }
  ],
  "defaultAddress": "0x0000000000000000000000000000000000000000"
}
```

Route keys `(creator, nonce)` are unique. Lookup returns the route Address on an
exact key match and `defaultAddress` otherwise. This is a total injected policy,
not an EVM CREATE-address formula.

## Invocation and probes

`invocation` has exactly `target`, `caller`, `callValue`, `calldata`, and
`probes`. The first three fields build the corresponding
`TopLevelInvocation`; `calldata` becomes its exact `InputData.bytes`.

A probe is one of these five exact variants:

```json
{ "kind": "accountPresence", "address": "0x0000000000000000000000000000000000000001" }
```

```json
{ "kind": "storage", "address": "0x0000000000000000000000000000000000000001", "slot": "0x0000000000000000000000000000000000000000000000000000000000000002" }
```

```json
{ "kind": "balance", "address": "0x0000000000000000000000000000000000000001" }
```

```json
{ "kind": "nonce", "address": "0x0000000000000000000000000000000000000001" }
```

```json
{ "kind": "code", "address": "0x0000000000000000000000000000000000000001" }
```

Probe order is semantic and is echoed by the observation. Duplicate probes
mean equal complete tagged values, so different kinds at the same Address are
not duplicates.

## Response envelope

Every non-protocol response is this exact object:

```json
{
  "schema": "solcore-oracle/v5",
  "id": "request-id",
  "spec": "solcore/0.1.0-draft.5",
  "profile": {
    "id": "contract-m3a-v1",
    "digest": "sha256:da3d49b830d25705634cfda568691f1f12fe5a7d038bd0b7ca5839134c1073d5"
  },
  "query": "coreCheck",
  "verdict": {}
}
```

`id` repeats the validated request ID. `query` is exactly `capabilities`,
`coreCheck`, or `execute` and must agree with the verdict family below.

### Phase and resource strings

Phase is one of:

```text
protocol
requestPreflight
coreDecoding
coreChecking
contractAdmission
worldValidation
environmentValidation
probeValidation
rootInstallation
contractExecution
observationEncoding
```

Resource is one of the eight limit field names:

```text
jsonDepth jsonNodes coreDepth coreNodes scenarioEntries identifierBytes
calldataBytes evaluationSteps
```

The resource-to-phase mapping is fixed:

| Resource | Phase |
| --- | --- |
| `jsonDepth`, `jsonNodes`, `scenarioEntries`, `identifierBytes`, `calldataBytes` | `requestPreflight` |
| `coreDepth`, `coreNodes` | `coreDecoding` |
| `evaluationSteps` | `contractExecution` |

### Accepted verdict

```json
{
  "kind": "accepted",
  "phase": "coreChecking",
  "result": {
    "schema": "solcore-core-check-result/v3",
    "value": { "resultType": "word" }
  }
}
```

Only `capabilities` and `coreCheck` return `accepted`. Their phases are
`protocol` and `coreChecking`, respectively, and their result schemas must be
the matching fixed schema.

### Rejected verdict

```json
{
  "kind": "rejected",
  "phase": "rootInstallation",
  "diagnostics": [
    {
      "code": "oracle.v5.root.target-absent",
      "severity": "error",
      "phase": "rootInstallation",
      "path": ["world", "accounts", "0x0000000000000000000000000000000000000001"],
      "arguments": { "target": "0x0000000000000000000000000000000000000001" },
      "display": null
    }
  ]
}
```

`diagnostics` is exactly a singleton in v5. Its phase equals the verdict phase,
its `severity` is exactly `error`, and canonical responses set `display` to
`null`. `path` is an array of semantic path strings and `arguments` is always an
object. Rejection is available to `coreCheck` and `execute`, not
`capabilities`.

### Inconclusive verdict

```json
{
  "kind": "inconclusive",
  "phase": "contractExecution",
  "resource": "evaluationSteps",
  "limit": 12,
  "consumed": 12
}
```

For pre-execution resources, `consumed` is the exact measured demand and is
strictly greater than `limit`. All three queries may return such an
`inconclusive` verdict because their complete envelopes are budgeted. For fuel
exhaustion, `limit` and `consumed` are both the supplied `evaluationSteps`;
this case is available only to `execute`.

### Executed verdict

```json
{
  "kind": "executed",
  "observation": {
    "schema": "solcore-contract-execution/v1",
    "value": {
      "outcome": { "kind": "preflightRejected", "reason": "senderAbsent" },
      "journal": { "logs": [], "createdAddresses": [] },
      "state": {
        "schema": "solcore-world-state-observation/v1",
        "probes": []
      }
    }
  }
}
```

Only `execute` returns `executed`, and only after a terminal result exists.
Fuel exhaustion is the inconclusive shape above and never fabricates this
observation.

### Internal-error verdict

```json
{
  "kind": "internalError",
  "phase": null,
  "code": "oracle-response-invariant"
}
```

The defensive code-to-phase mapping is closed:

| Code | Phase |
| --- | --- |
| `core-wire-projection-failed` | `observationEncoding` |
| `world-code-reference-invariant` | `observationEncoding` |
| `oracle-response-invariant` | `null` |

These failures are not substitutes for a listed rejection or inconclusive
case.

### Query/verdict compatibility

| Query | Allowed verdicts |
| --- | --- |
| `capabilities` | `accepted`, `inconclusive`, `internalError` |
| `coreCheck` | `accepted`, `rejected`, `inconclusive`, `internalError` |
| `execute` | `rejected`, `inconclusive`, `executed`, `internalError` |

The strict response decoder first checks the exact six-field envelope, then
decodes `id`, `profile`, `query`, `schema`, `spec`, and `verdict` in that
order. A verdict first admits only fields from the selected query's complete
variant union. `kind` and `phase` are common required fields for
`capabilities` and `coreCheck`; only `kind` is common to every `execute`
variant because `executed` carries no separate phase. The decoder then selects
the variant, checks its exact field set, and validates the remaining fields in
lexicographic order.

This reconstruction is query-indexed: a verdict from a different query family
cannot be decoded and re-labeled. Diagnostic arguments are decoded by their
closed code, an embedded Core Type or constructor identity retains Core wire
error ownership, and a rejected verdict's outer phase must equal its sealed
diagnostic phase. Inconclusive values validate their limit/consumed relation,
resource, and phase; executed observations validate the rollback constraints
described below before they enter the typed response.

## Capability result

The accepted capability result uses schema `solcore-capabilities/v5`. Its
`value` has exactly these fields:

| Field | Exact value |
| --- | --- |
| `schema` | `solcore-capabilities/v5` |
| `spec` | `solcore/0.1.0-draft.5` |
| `profile` | complete canonical `contract-m3a-v1` SpecProfile object |
| `profileDigest` | the fixed digest above |
| `coreSchema` | `solcore-semantic-core/v3` |
| `checkResultSchema` | `solcore-core-check-result/v3` |
| `executionSchema` | `solcore-contract-execution/v1` |
| `stateObservationSchema` | `solcore-world-state-observation/v1` |
| `contractProfiles` | `["returnWord", "wordOutcomeV1"]` |
| `abiProfiles` | `["staticWordAbiV1"]` |
| `implementedQueries` | `["capabilities", "coreCheck", "execute"]` |
| `maxNestedCallDepth` | `1` |
| `observationKinds` | `["accountPresence", "storage", "balance", "nonce", "code"]` |
| `defaultLimits` | the eight-field default Limits object |
| `baselines` | canonical existing `implementationBaselines` array |
| `features` | canonical `m3aContractFeatureMatrix` array |

The exact `baselines` value is:

```json
[
  {
    "implementation": "solcore-haskell",
    "nativeSettings": {
      "bytecodeRuntime": "prague",
      "externalYulCompilerTarget": null,
      "generatedDispatch": true,
      "nativeBackendTarget": null,
      "primitiveSurface": "osaka",
      "solver": "legacy"
    },
    "notes": "Defaults are evidence only. The external Yul compiler target is not pinned.",
    "repository": "https://github.com/argotorg/solcore",
    "revision": "1d490d8bb5f374356f06e0720655496482eb1fb4",
    "role": "upstreamEvidence",
    "standardLibraryBundle": "canonical-haskell-1d490d8"
  },
  {
    "implementation": "solcore-rs",
    "nativeSettings": {
      "bytecodeRuntime": "osaka",
      "externalYulCompilerTarget": null,
      "generatedDispatch": true,
      "nativeBackendTarget": "osaka",
      "primitiveSurface": "osaka",
      "solver": "tabled"
    },
    "notes": "The vendored std is older, and the external Yul compiler target is not pinned.",
    "repository": "https://github.com/argotorg/solcore-rs",
    "revision": "38f4778ea461edfe59106bdb1f9f08c3307b0fc0",
    "role": "comparisonImplementation",
    "standardLibraryBundle": "rust-compatibility-ac6f8957"
  }
]
```

The exact `features` value is:

```json
[
  {
    "adr": "0151",
    "feature": "coreProductsV1",
    "leanStatus": "implemented",
    "leanTarget": "M3a",
    "note": "Checked Core products and projections are published by Core Wire v3.",
    "specStatus": "normative"
  },
  {
    "adr": "0151",
    "feature": "coreFunctionsV1",
    "leanStatus": "implemented",
    "leanTarget": "M3a",
    "note": "Checked Core lambdas, application, and lexical closures are published.",
    "specStatus": "normative"
  },
  {
    "adr": "0151",
    "feature": "coreSumsV1",
    "leanStatus": "implemented",
    "leanTarget": "M3a",
    "note": "Checked Core sums, injections, and case analysis are published.",
    "specStatus": "normative"
  },
  {
    "adr": "0151",
    "feature": "coreLocalCellsV1",
    "leanStatus": "implemented",
    "leanTarget": "M3a",
    "note": "Checked Core local cell allocation, reads, and writes are published.",
    "specStatus": "normative"
  },
  {
    "adr": "0151",
    "feature": "coreNamedDataV1",
    "leanStatus": "implemented",
    "leanTarget": "M3a",
    "note": "Checked named data construction and matching are published.",
    "specStatus": "normative"
  },
  {
    "adr": "0151",
    "feature": "coreExtendedWordOperationsV1",
    "leanStatus": "implemented",
    "leanTarget": "M3a",
    "note": "The complete current checked Word operator algebra is published.",
    "specStatus": "normative"
  },
  {
    "adr": "0151",
    "feature": "checkedContractExecutionV1",
    "leanStatus": "implemented",
    "leanTarget": "M3a",
    "note": "Checked contracts execute through the balanced state lifecycle.",
    "specStatus": "normative"
  },
  {
    "adr": "0151",
    "feature": "staticWordAbiV1",
    "leanStatus": "implemented",
    "leanTarget": "M3a",
    "note": "Static uint256-to-uint256 ABI dispatch is published.",
    "specStatus": "normative"
  }
]
```

The complete profile object is the linked canonical profile JSON. The capability
report is a singleton: decoding accepts only a value equal to these exact
derived fields and arrays.

## Core-check result and diagnostics

The accepted check-result `value` is exactly:

```json
{ "resultType": "word" }
```

`resultType` is the complete Core Wire v3 Type and equals the Program's declared
result type. No checker witness or inferred environment is serialized.

Checker diagnostic paths start with `program` for `coreCheck`, or with
`contracts`, the canonical contract ID, and `program` for `checkedCore`. A
Static Word implementation uses `contracts`, its contract ID, `methods`, its
method name, and `implementation`. Remaining elements preserve these exact
`Core.CheckPathStep` strings:

```text
pairLeft pairRight firstOperand secondOperand lambdaBody applyFunction
applyArgument inLeftPayload inRightPayload caseScrutinee caseLeftBranch
caseRightBranch newCellInitializer loadCellReference storeCellReference
storeCellValue constructPayload matchScrutinee unaryOperand binaryLeft
binaryRight ternaryFirst ternarySecond ternaryThird letValue letBody
ifCondition ifThen ifElse
```

A match branch step is the single string `matchBranch[N]`, where `N` is its
natural decimal index.

A checker rejection from `coreCheck` has phase `coreChecking`. A checker
rejection while admitting any `execute` contract or method has phase
`contractAdmission`. The diagnostic and verdict carry that same phase.

The checker code and `arguments` object are a total encoding of
`Core.CheckErrorData`:

| Code suffix after `core.check.` | Arguments |
| --- | --- |
| `unbound-variable` | `index`, `contextSize` naturals |
| `expected-bool`, `expected-product`, `expected-function`, `expected-sum`, `invalid-cell-payload`, `expected-cell`, `expected-named-data`, `invalid-result-type` | `actual` Type |
| `function-argument-type-mismatch`, `cell-initializer-type-mismatch`, `cell-value-type-mismatch`, `constructor-payload-type-mismatch`, `primitive-operand-type-mismatch` | `expected`, `actual` Types |
| `lambda-result-type-mismatch` | `declared`, `actual` Types |
| `case-branch-type-mismatch` | `leftType`, `rightType` Types |
| `invalid-definition-payload` | `dataTypeIndex`, `constructorIndex` naturals; `actual` Type |
| `unknown-named-data-type`, `unknown-data-type` | `dataType` natural |
| `unknown-constructor` | `constructor` ConstructorId |
| `match-data-type-mismatch` | `expected`, `actual` data-type naturals |
| `match-branch-count-mismatch` | `expected`, `actual` naturals |
| `match-branch-result-type-mismatch` | `branchIndex` natural; `expected`, `actual` Types |
| `branch-type-mismatch` | `thenType`, `elseType` Types |
| `declared-result-type-mismatch` | `declaredType`, `inferredType` Types |
| `inference-failure` | empty object |

## Scenario rejection codes

All non-checker rejection codes and their exact phases are closed below. The
diagnostic path identifies the offending field; `arguments` has exactly the
listed fields.

| Code | Phase | Arguments |
| --- | --- | --- |
| `oracle.v5.contract.invalid-id` | `contractAdmission` | `actual` string |
| `oracle.v5.contract.duplicate-id` | `contractAdmission` | `id` string |
| `oracle.v5.contract.unsupported-entry-result-type` | `contractAdmission` | `actual` Type |
| `oracle.v5.method.invalid-name` | `contractAdmission` | `actual` string |
| `oracle.v5.method.nonempty-data-definitions` | `contractAdmission` | `count` natural |
| `oracle.v5.method.result-type-mismatch` | `contractAdmission` | `actual` Type |
| `oracle.v5.abi.empty-method-table` | `contractAdmission` | empty object |
| `oracle.v5.abi.duplicate-signature` | `contractAdmission` | `signature`, `firstMethod`, `secondMethod` strings |
| `oracle.v5.abi.selector-collision` | `contractAdmission` | `selector` eight-digit lowercase hex without `0x`; `firstSignature`, `secondSignature` strings |
| `oracle.v5.contract.duplicate-code` | `contractAdmission` | `firstId`, `secondId` strings |
| `oracle.v5.reference.dangling-contract` | `worldValidation` | `id` string |
| `oracle.v5.reference.dangling-contract` | `environmentValidation` | `id` string |
| `oracle.v5.world.duplicate-account` | `worldValidation` | `address` Address |
| `oracle.v5.world.duplicate-storage-slot` | `worldValidation` | `address` Address, `slot` Word |
| `oracle.v5.world.zero-storage-value` | `worldValidation` | `address` Address, `slot` Word |
| `oracle.v5.environment.duplicate-call-address` | `environmentValidation` | `address` Address |
| `oracle.v5.environment.duplicate-template-id` | `environmentValidation` | `templateId` Word |
| `oracle.v5.environment.duplicate-creation-route` | `environmentValidation` | `creator` Address, `nonce` Word |
| `oracle.v5.probe.duplicate` | `probeValidation` | `firstIndex`, `secondIndex` naturals |
| `oracle.v5.root.target-absent` | `rootInstallation` | `target` Address |
| `oracle.v5.root.target-code-absent` | `rootInstallation` | `target` Address |

`unsupported-entry-result-type.actual` must be different from both published
checked-contract result types. `method.result-type-mismatch.actual` must be
different from `word -> word`. For selector collisions, `firstSignature` is
strictly byte-lexicographically smaller than `secondSignature`; both signatures
must derive the reported selector. For duplicate underlying code, `firstId` is
strictly byte-lexicographically smaller than `secondId`. These relations match
the canonical package and method order and prevent a response from admitting a
reversed or otherwise producer-impossible conflict.

Diagnostic paths are the following exact semantic string arrays. Placeholders
denote their canonical wire spelling: `C` contract ID, `M` method name, `A`
Address, `W` Word, and `N` natural decimal index.

| Failure | Exact path |
| --- | --- |
| invalid/duplicate contract ID | `["contracts", C, "id"]` |
| unsupported entry result | `["contracts", C, "program", "resultType"]` |
| invalid method name | `["contracts", C, "methods", M, "name"]` |
| nonempty method definitions | `["contracts", C, "methods", M, "implementation", "dataDefinitions"]` |
| method result mismatch | `["contracts", C, "methods", M, "implementation", "resultType"]` |
| empty/duplicate/colliding method table | `["contracts", C, "methods"]` |
| duplicate underlying code | `["contracts", C]`, where `C` is `secondId` |
| duplicate Account | `["world", "accounts", A]` |
| duplicate storage slot | `["world", "accounts", A, "storage", W]` |
| zero storage value | `["world", "accounts", A, "storage", W, "value"]` |
| dangling Account code | `["world", "accounts", A, "code"]` |
| duplicate call binding | `["environment", "callRegistry", A]` |
| dangling call contract | `["environment", "callRegistry", A, "contract"]` |
| duplicate template | `["environment", "creationTemplates", W]` |
| dangling initializer/runtime | `["environment", "creationTemplates", W, "initializer"]` or the same path ending in `"runtime"` |
| duplicate creation route | `["environment", "creationAddressPolicy", "routes", A, W]` |
| duplicate probe | `["invocation", "probes", N]`, where `N` is `secondIndex` |
| absent root target | `["world", "accounts", A]` |
| absent root code | `["world", "accounts", A, "code"]` |

For an invalid ID or method name, `C` or `M` is the rejected raw string. A
registry entry whose admitted contract differs from installed world code is not
dangling and is not rejected.

## Terminal execution observation

An executed observation `value` has exactly these fields:

```json
{
  "outcome": { "kind": "returned", "returndata": "0x" },
  "journal": { "logs": [], "createdAddresses": [] },
  "state": { "schema": "solcore-world-state-observation/v1", "probes": [] }
}
```

Outcome is exactly one of four variants:

```json
{ "kind": "preflightRejected", "reason": "senderAbsent" }
```

```json
{ "kind": "returned", "returndata": "0x" }
```

```json
{ "kind": "reverted", "revertdata": "0x" }
```

```json
{ "kind": "trapped", "reason": "0x0000000000000000000000000000000000000000000000000000000000000000" }
```

The preflight reason is exactly `senderAbsent`, `recipientAbsent`,
`insufficientBalance`, or `recipientOverflow`, preserving
`BalanceTransferFailure`. The executor's installed-root invariant currently
makes `recipientAbsent` unreachable, but the total encoding remains closed over
the complete semantic type. Return and revert Bytes are not required to have an
ABI-specific length.

A log has exactly:

```json
{
  "emitter": "0x0000000000000000000000000000000000000001",
  "topic": "0x0000000000000000000000000000000000000000000000000000000000000002",
  "payload": "0x0000000000000000000000000000000000000000000000000000000000000003"
}
```

Logs and `createdAddresses` are the committed journal in chronological order.
They preserve duplicates. They are empty for preflight rejection, root revert,
and root trap. Rolled-back child and initializer entries never appear.

### Probe endpoints

`state.probes` has the same length and order as `invocation.probes`. Each entry
repeats its key and adds exact initial and committed endpoints:

```json
{ "kind": "accountPresence", "address": "0x0000000000000000000000000000000000000001", "initial": true, "committed": true }
```

```json
{ "kind": "storage", "address": "0x0000000000000000000000000000000000000001", "slot": "0x0000000000000000000000000000000000000000000000000000000000000002", "initial": null, "committed": "0x0000000000000000000000000000000000000000000000000000000000000000" }
```

```json
{ "kind": "balance", "address": "0x0000000000000000000000000000000000000001", "initial": null, "committed": "0x0000000000000000000000000000000000000000000000000000000000000000" }
```

```json
{ "kind": "nonce", "address": "0x0000000000000000000000000000000000000001", "initial": null, "committed": "0x0000000000000000000000000000000000000000000000000000000000000000" }
```

```json
{ "kind": "code", "address": "0x0000000000000000000000000000000000000001", "initial": null, "committed": "runtime" }
```

For storage, balance, and nonce, `null` means the Account is absent; a present
zero value is the full zero Word. For code, `null` means no checked code, whether
because the Account is absent or has no code. An account-presence probe is the
separate way to distinguish those cases. Pairwise code uniqueness makes every
non-null package ID canonical.

The committed endpoint is the working world only for `returned`. Preflight
rejection, `reverted`, and `trapped` use the original checkpoint, so every probe
has equal endpoints and the committed journal is empty.

After ordinary shape and scalar decoding, the observation decoder enforces
that rollback invariant in this fixed order: a nonempty `createdAddresses`
array, then a nonempty `logs` array, then the first probe whose endpoints
differ. Each failure is `oracle.wire.invalid-tag`. Journal failures point to the
offending array and expect `[]`; a probe failure points to that probe's
`committed` field, reports the committed endpoint as `actual`, and the initial
endpoint as `expected`.

## Protocol errors

A protocol error is outside the response union and has exactly:

```json
{
  "kind": "protocolError",
  "schema": "solcore-oracle/v5",
  "id": null,
  "code": "oracle.wire.unknown-field",
  "path": "/query/future",
  "arguments": { "field": "future" },
  "display": "invalid Oracle v5 value"
}
```

`id` is the recovered valid request ID or `null`. `path` is an RFC 6901 JSON
Pointer, with the empty string denoting the root. `display` is deterministic
human-readable text but has no semantic information beyond `code`, `path`, and
`arguments`.

The public encoder accepts only a protocol error that has passed the complete
closed validity check. The strict decoder checks the exact envelope and then
visits `arguments`, `code`, `display`, `id`, `kind`, `path`, and `schema` in
lexicographic order. A non-failing read of raw `code` directs argument checking
without moving a code error ahead of an earlier argument error. The final value
is sealed only after ownership display, fixed identities, request-ID shape,
canonical pointer syntax, and code-specific pointer/argument relationships all
agree. Decoding and re-encoding therefore produces one canonical spelling.

Malformed JSON, including duplicate object keys, has the unprefixed code
`malformed-json`, `arguments: null`, and the strict parser's deterministic
message as `display`. All typed decoder codes retain the existing ownership
prefix:

- `oracle.wire.<suffix>` owns request/response envelopes, profile references,
  scenario values, observations, and their scalar forms; and
- `core.wire.<suffix>` owns a failure strictly inside an embedded Core Wire v3
  value. This includes Programs and the standalone Types or constructor
  identities carried by results and diagnostic arguments. Its pointer still
  starts at the containing Oracle field; the surrounding Oracle object remains
  owned by `oracle.wire.*`.

The closed Oracle suffixes are:

```text
expected-object expected-array expected-string expected-bool expected-natural
missing-field unknown-field invalid-schema invalid-spec invalid-profile
invalid-tag invalid-word invalid-address invalid-bytes invalid-request-id
invalid-limit
```

The closed Core suffixes are:

```text
expected-object expected-array expected-string expected-bool expected-natural
missing-field unknown-field invalid-schema invalid-tag invalid-type invalid-word
```

For both prefixes, `expected-*` uses exactly `{"expected": <kind>, "actual":
<kind>}`, where kind is `null`, `boolean`, `number`, `string`, `array`, or
`object`. `missing-field` and `unknown-field` use exactly `{"field": <string>}`.
`invalid-schema` and `invalid-spec` use exact string fields `expected` and
`actual`; `invalid-profile` uses `expectedId`, `expectedDigest`, `actualId`, and
`actualDigest`. `invalid-tag` uses the existing v4 shape with arbitrary JSON
fields `actual` and `expected`. Core `invalid-type` uses `actual` and `allowed`.
Each invalid Word, Address, or Bytes value uses exactly `{"reason": <string>}`.
Word and Address use `prefix`, `length`, or `lowercase-hex`; Bytes use
`prefix`, `odd-length`, or `lowercase-hex`. `invalid-request-id` uses
`{"constraint":"nonempty-utf8"}`. `invalid-limit` uses exactly `field` and
`constraint` strings. Its only v5 instance is
`{"field":"calldataBytes","constraint":"strictly-less-than-2^256"}`.

For every `expected-*` code except `expected-natural`, `actual` differs from
`expected`. A negative or fractional JSON number is still a JSON `number`, so
the valid `expected-natural` producer shape is
`{"expected":"number","actual":"number"}`. Missing/unknown `field` must
equal the final decoded JSON-Pointer token. Schema/spec/profile errors carry
the fixed v5 identities, and invalid request-ID and limit errors use `/id` and
`/limits/calldataBytes`, respectively.

Shape decoding precedes scalar constraints at a field: for example, a negative
or fractional limit is `oracle.wire.expected-natural`, while a natural
`calldataBytes >= 2^256` is `oracle.wire.invalid-limit`. Dedicated
`invalid-schema`, `invalid-spec`, and `invalid-profile` take precedence over
generic `invalid-tag`; `invalid-tag` owns all other closed-enum or literal
mismatches. During the exact structural pass in step 3, every object first
performs an exact field-set pass; an unknown or missing field found there
precedes errors in field values, and competing unknown/missing fields are
selected by lexicographic field name. The request root and query discriminator
have the explicitly earlier shallow reads described in steps 1–2; their full
field-set checks still occur in step 3. A tagged object applies the structural
pass to its union envelope and fields common to every variant, then decodes
`kind` or `tag`, then checks the selected variant's exact field set. Remaining
scalar fields use lexicographic order.
Embedded Core nodes additionally validate node-local metadata such as an
operator or constructor identity before descending into child Core nodes; child
positions use lexicographic field order. These rules and the resource order
above select one path when more than one failure exists.

An `oracle.wire.*` error has display `invalid Oracle v5 value`; a
`core.wire.*` error retains the compatibility display `invalid Semantic Core v3
program`, including when the embedded value is a Type or constructor identity.
Declared
budget excess is never a protocol code: it is the outer `inconclusive` verdict.
Duplicate entries in keyed arrays are typed scenario rejections, not protocol
errors.

This catalog also closes the direct v5 text codec. The compatible NDJSON
dispatcher first parses enough JSON to select an exact schema discriminator;
malformed text or a missing/non-v5 discriminator therefore follows the existing
dispatcher error path and cannot produce a v5 `malformed-json` or
`oracle.wire.invalid-schema`. Those two codes remain reachable through the
direct codec. Once NDJSON has selected exact v5, all later failures use this v5
catalog. No v1-v4 dispatch or error encoding changes.

## Canonical ordering and validation

The decoder accepts object fields in any order and rejects duplicate keys. The
canonical encoder emits compact JSON with object keys in lexicographic order.
After scalar decoding it sorts these keyed arrays before further validation:

| Array | Numeric or byte-exact key |
| --- | --- |
| `contracts` | ASCII contract ID |
| Static Word `methods` | canonical ASCII signature |
| `world.accounts` | Address value |
| Account `storage` | slot Word value |
| `callRegistry` | Address value |
| `creationTemplates` | template-id Word value |
| creation `routes` | creator Address, then nonce Word |

Equal adjacent keys after sorting are rejected. Core definition, constructor,
branch, and expression order is semantic and retained. Probes retain request
order. Response diagnostics, logs, created Addresses, and probe observations
retain their specified semantic order.

After the resource/structural sequence in Counting rules, semantic validation
selects one result in this order:

1. contract-ID grammar, duplicate IDs, checking/profile admission, Static Word
   method admission, then underlying-code uniqueness;
2. duplicate accounts, duplicate storage slots, zero storage values, then
   dangling Account code references;
3. duplicate call addresses, template IDs, and creation routes, in that order,
   then dangling call, initializer, and runtime references;
4. duplicate probes;
5. root target presence, then root code presence; and
6. exactly one balanced execution.

After the exact field-set pass, ordinary object values and array entries are
visited in lexicographic and increasing-index order, respectively; tagged
objects and Core nodes use the discriminator and node-local-metadata rule
above. After structure and scalar decoding, keyed arrays use the canonical
sorting table. Duplicate validation precedes other semantic validation for the
same collection; a duplicate pair is the first and second equal entry in
canonical order. These rules select duplicate storage before a zero value at
the same key, and duplicate IDs before either contract's admission failure.
They make repeated execution agree exactly. Permutations of the keyed arrays
listed above also agree after canonicalization; semantic-order arrays such as
probes intentionally retain their order.

## Compact examples

The `coreCheck` query shown earlier produces this response when embedded in the
fixed response envelope:

```json
{
  "kind": "accepted",
  "phase": "coreChecking",
  "result": {
    "schema": "solcore-core-check-result/v3",
    "value": { "resultType": "word" }
  }
}
```

A minimal successful execution query may use one constant-return contract:

```json
{
  "kind": "execute",
  "contracts": [{"id":"constant","kind":"checkedCore","program":{"schema":"solcore-semantic-core/v3","resultType":"word","dataDefinitions":[],"body":{"tag":"word","value":"0x0000000000000000000000000000000000000000000000000000000000000007"}}}],
  "world": {"accounts":[{"address":"0x0000000000000000000000000000000000000001","balance":"0x0000000000000000000000000000000000000000000000000000000000000000","nonce":"0x0000000000000000000000000000000000000000000000000000000000000000","storage":[],"code":"constant"}]},
  "environment": {"callRegistry":[],"creationTemplates":[],"creationAddressPolicy":{"routes":[],"defaultAddress":"0x0000000000000000000000000000000000000000"}},
  "invocation": {"target":"0x0000000000000000000000000000000000000001","caller":"0x0000000000000000000000000000000000000002","callValue":"0x0000000000000000000000000000000000000000000000000000000000000000","calldata":"0x","probes":[{"kind":"code","address":"0x0000000000000000000000000000000000000001"}]}
}
```

With sufficient fuel its verdict is:

```json
{
  "kind": "executed",
  "observation": {
    "schema": "solcore-contract-execution/v1",
    "value": {
      "outcome": {"kind":"returned","returndata":"0x0000000000000000000000000000000000000000000000000000000000000007"},
      "journal": {"logs":[],"createdAddresses":[]},
      "state": {"schema":"solcore-world-state-observation/v1","probes":[{"kind":"code","address":"0x0000000000000000000000000000000000000001","initial":"constant","committed":"constant"}]}
    }
  }
}
```

At an insufficient admitted execution budget, the same request returns an
`inconclusive` `evaluationSteps` verdict and contains no observation.
