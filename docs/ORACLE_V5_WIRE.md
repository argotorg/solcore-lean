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
| Profile digest | `sha256:615de959ac8cb6c7e9b91fe6b45ec578a7143d5f74ec092316901cf76431cf46` |
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
    "digest": "sha256:615de959ac8cb6c7e9b91fe6b45ec578a7143d5f74ec092316901cf76431cf46"
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
defaults, not decoder fallbacks. A missing, malformed, or out-of-range limit is
a protocol error. `calldataBytes` must be strictly less than `2^256`. Zero is a
valid value for every limit.

### Counting rules

- A JSON node is one object, array, string, number, Boolean, or `null`. The root
  has depth one; every contained value increases depth by one. `jsonNodes` and
  `jsonDepth` measure the complete parsed request, including unknown subtrees.
- A Core node is one Program, DataDefinition, Type, or Expression from Core
  Wire v3. Embedded Types count recursively. Operator strings, tags, natural
  identities, and array containers add no Core node. `coreNodes` is the sum for
  every Program in the request. `coreDepth` is the greatest Program-to-Core-node
  nesting depth among them, with the Program at depth one.
- `scenarioEntries` is the sum of the lengths of `contracts`, every
  `staticWordAbi.methods`, `world.accounts`, every account's `storage`,
  `callRegistry`, `creationTemplates`, `creationAddressPolicy.routes`, and
  `invocation.probes`. Lists inside Core Programs are excluded because their
  elements already count as Core nodes.
- `calldataBytes` measures the decoded byte length, not hexadecimal source
  characters. `evaluationSteps` is passed unchanged as executor fuel.

The first exceeded resource in this order is reported: `jsonDepth`,
`jsonNodes`, `coreDepth`, `coreNodes`, `scenarioEntries`, `identifierBytes`,
then `calldataBytes`. Execution fuel is considered only after admission.

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

