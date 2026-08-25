# ADR-0010: Publication boundary for the M1b Core wire format and Oracle v2

- Status: Accepted
- Decision date: 2026-07-23
- Scope: M1b Semantic Core publication

## Reader summary / Current implementation

- **Decision:** Publish the completed M1a fragment as draft.2, profile
  `core-m1a-v1`, Semantic Core v1, and Oracle v2 without widening Oracle v1.
- **Current implementation:** The profile and feature matrix, strict Core v1
  codec, Oracle v2 queries, diagnostics, limits, mixed streams, and golden tests
  are present.
- **Boundary:** M1b publishes no primitive operations and accepts no source
  workspace; later versions are additive rather than in-place changes.
- **Suggested reading:** Read “Decision” for the versioned boundary and
  “Conformance requirements” for compatibility guarantees.

## Context

M1a implemented declarative typing and evaluation, an executable checker and CEK
machine, and correspondence and safety theorems for a closed Semantic Core
consisting of unit, booleans, 256-bit words, de Bruijn variables, initialized
immutable `let`, and conditionals.

However, the M0 language version `solcore/0.1.0-draft.1` and profile `core-v1`
enable no feature with complete normative semantics. Furthermore,
`corePrimitives`, `localBindings`, and `conditionals` are aggregate features
intended to cover the source language as a whole and cannot be considered
complete on the basis of M1a alone. Allowing Core check or evaluation to succeed
under that profile would violate the publication invariant
`implemented ⊆ enabled ⊆ normative ⊆ known`.

The existing Oracle queries `check` and `eval` are reserved for source-level
queries whose input is a `.solc` workspace. Their meaning cannot be changed to
accept a Core AST directly.

## Decision

### Fine-grained normative features

Add the following independent feature identifiers for the M1a scope that has
complete rules, decision procedures, correspondence proofs, and safety proofs.

- `coreUnit`: unit type, literals, values, typing, and evaluation
- `coreBool`: boolean type, literals, values, typing, and evaluation
- `coreWord`: in-range 256-bit word type, literals, values, typing, and evaluation
- `coreImmutableLet`: initialized immutable de Bruijn bindings
- `coreConditional`: condition-first, selected-branch-only conditionals

These features are `normative` and `implemented` in Lean. `coreWord` does not
include word arithmetic, comparisons, division, or shifts. The existing aggregate
features `corePrimitives`, `localBindings`, and `conditionals` are not promoted.

To avoid changing the feature set enumerated by the M0 capabilities schema, retain
an explicit legacy feature array and feature matrix for draft.1. The new
identifiers are published only by Oracle v2 capabilities.

### Language version and profile

The new language version is `solcore/0.1.0-draft.2`.

- `staticSemanticsVersion = 1`
- `dynamicSemanticsVersion = 1`
- `grammarVersion = null`
- ABI and storage-layout versions remain undefined
- The standard-library revision and digest are unchanged from draft.1

The new profile is `core-m1a-v1`, enabling only the five features above. Its scope
is `core`, its observation is `valueV1`, and it has no contract runtime.

`solcore/0.1.0-draft.1`, `core-v1`, and their canonical JSON and digest remain
unchanged.

### Semantic Core wire format

The Core AST is carried by a separate strict JSON schema named
`solcore-semantic-core/v1`. A Program has an explicit `resultType` and `body`.
Expressions are tagged objects representing only unit, booleans, words,
variables, `let`, and `if`.

The wire representation of a Word is a fixed-width string consisting of `0x`
followed by 64 lowercase hexadecimal digits. Out-of-range values, short forms,
uppercase forms, and JSON numbers are not accepted. The encoder always emits this
canonical form. Lean constructor names and the internal JSON representation of
`Fin` are not part of the wire contract.

De Bruijn indices and resource limits are JSON numbers with nonnegative integral
values. The decoder treats JSON numbers such as `1` and `1.0`, which represent the
same nonnegative integer, as equivalent. The encoder emits canonical decimal with
neither a fractional part nor an exponent. Negative and non-integral values are
not accepted.

Unknown fields, missing fields, fields irrelevant to a variant, unknown tags, and
invalid words are Core wire-shape protocol errors, not language-level rejections.

For Core input limits, each `Expr` constructor counts as one node and a leaf has
depth 1. The Program wrapper, type annotations, and object fields themselves do
not count toward node or depth limits.

### Oracle v2

`solcore-oracle/v2` defines the following queries.

- `capabilities`
- `coreCheck`
- `coreEval`

`coreCheck` and `coreEval` accept a `solcore-semantic-core/v1` Program directly,
not a `.solc` workspace. The meanings of v1 `check` and `eval` do not change.

A successful `coreCheck` returns a typed
`solcore-core-check-result/v1` result. A successful `coreEval` returns a
canonical typed `solcore-core-value-observation/v1` value. Type errors map to
`rejected`, evaluation fuel exhaustion maps to `inconclusive`, and a machine
fault proved unreachable from a type-checked Program maps to `internalError` if
it nevertheless occurs.

A Core diagnostic does not fabricate a nonexistent source span. It has an AST
path from the root, a stable code, a phase, and structured arguments.

The NDJSON dispatcher selects v1 or v2 using the top-level `schema`. An
argument-free stream may mix both versions, while the existing `capabilities` CLI
continues to use v1.

## Consequences

- M1b publishes the M1a semantics without adding primitive operations or
  functions.
- Core JSON validity, type validity, resource exhaustion, and Oracle defects can
  be distinguished.
- Neither the source parser nor an M1-specific convenience parser becomes the
  entry point to the semantics.
- v1 consumers can continue using the existing schema, profile, digest, and query
  semantics.
- A request that omits the draft.2 profile digest cannot obtain normative M1a
  results.

## Conformance requirements

- Provide strict-decode and canonical-encode round trips for Core Ty, Word, and
  Value. Expr and Program round-trip under an explicit premise that the specified
  depth and node limits contain the encoder input; under the same premise,
  canonicalization is idempotent.
- Accept zero and the maximum word value, and reject a noncanonical
  representation equivalent to `2^256`.
- Assign stable codes and AST paths to an unbound variable, a non-boolean
  condition, a branch mismatch, and a declared-result mismatch.
- For the existing seven-transition witness, return `inconclusive` with fuel 6
  and `executed` with fuel 7.
- Include an Oracle golden case showing that the unselected conditional branch is
  not evaluated.
- v1 `.check` and `.eval` remain `unsupported`.
- Do not change the bytes of the v1 capability, profile, or golden output.
- Continue processing after a malformed record and in a stream that mixes v1 and
  v2.
