# ADR-0010: Publication Boundary for M1b Core Wire and Oracle v2

- Status: Accepted
- Decision date: 2026-07-23
- Scope: M1b Semantic Core publication

## Context

M1a implemented declarative typing and evaluation, an executable checker and
CEK machine, and correspondence and safety theorems for a closed Semantic Core
consisting of unit, bool, 256-bit words, de Bruijn variables, initialized
immutable lets, and conditionals.

However, the M0 `solcore/0.1.0-draft.1` and `core-v1` enable no features with
completed normative semantics. Furthermore, `corePrimitives`, `localBindings`,
and `conditionals` are aggregate features designed for the entire source
language and cannot be considered complete based on M1a alone. Allowing Core
check/eval to succeed under that profile would violate the publication
condition `implemented ⊆ enabled ⊆ normative ⊆ known`.

The existing Oracle `check` and `eval` queries are reserved as source-level
queries that accept a `.solc` workspace. Their meaning cannot be changed to
accept a Core AST directly.

## Decision

### Subdivision of normative features

The M1a scope for which rules, decision procedures, correspondence proofs, and
safety proofs are complete is added under the following independent feature
identifiers:

- `coreUnit`: unit type, literal, value, typing, and evaluation
- `coreBool`: bool type, literal, value, typing, and evaluation
- `coreWord`: in-range 256-bit word type, literal, value, typing, and evaluation
- `coreImmutableLet`: initialized immutable de Bruijn binding
- `coreConditional`: condition-first, selected-branch-only conditional

These features are `normative` and `implemented` in Lean. `coreWord` does not
include word arithmetic, comparisons, division, or shifts. The existing
aggregate features `corePrimitives`, `localBindings`, and `conditionals` are
not promoted.

To avoid changing the feature set enumerated by the M0 capabilities schema, the
legacy feature array and feature matrix for draft.1 are retained explicitly.
The new identifiers are published only by Oracle v2 capabilities.

### Language version and profile

The new language version is `solcore/0.1.0-draft.2`.

- `staticSemanticsVersion = 1`
- `dynamicSemanticsVersion = 1`
- `grammarVersion = null`
- ABI and storage-layout versions remain undefined
- The standard-library revision and digest are unchanged from draft.1

The new profile is `core-m1a-v1` and enables only the five features above. Its
scope is `core`, its observation is `valueV1`, and it has no contract runtime.

`solcore/0.1.0-draft.1`, `core-v1`, and their canonical JSON and digests remain
unchanged.

### Semantic Core wire

The Core AST is carried by an independent strict JSON schema named
`solcore-semantic-core/v1`. A Program contains an explicit `resultType` and
`body`. Expressions are tagged objects that represent only unit, bool, word,
var, let, and if.

The wire representation of a word is a fixed-width string consisting of `0x`
followed by 64 lowercase hexadecimal digits. Out-of-range values, short
representations, uppercase letters, and JSON numbers are not accepted. The
encoder always produces this canonical form. Lean constructor names and the
internal JSON representation of `Fin` are not part of the wire contract.

Unknown fields, missing fields, fields irrelevant to a variant, unknown tags,
and invalid words are protocol errors in the Core wire shape, not language
rejections.

### Oracle v2

`solcore-oracle/v2` defines the following queries:

- `capabilities`
- `coreCheck`
- `coreEval`

`coreCheck` and `coreEval` accept a `solcore-semantic-core/v1` Program directly,
not a `.solc` workspace. The meanings of v1 `check` and `eval` remain unchanged.

A successful `coreCheck` returns a typed
`solcore-core-check-result/v1` result. A successful `coreEval` returns a
canonical typed value under `solcore-core-value-observation/v1`. Type errors
map to `rejected`, evaluation-fuel exhaustion maps to `inconclusive`, and a
machine fault proved unreachable from a type-checked Program maps to
`internalError` only if such a fault occurs.

Core diagnostics do not fabricate nonexistent source spans. They contain an
AST path from the root, a stable code, a phase, and structured arguments.

The NDJSON dispatcher selects v1 or v2 by the top-level `schema`. The
argument-free stream permits records from both versions to be mixed, while the
existing `capabilities` CLI remains on v1.

## Consequences

- M1b publishes the M1a semantics without adding primitive operations or
  functions.
- Core JSON validity, typing validity, resource exhaustion, and oracle defects
  can be distinguished.
- Neither the source parser nor an M1-specific simplified parser becomes the
  entry point to the semantics.
- v1 consumers can continue using the existing schema, profile, digest, and
  query semantics.
- A request that does not specify the draft.2/profile digest cannot obtain M1a
  normative results.

## Conformance Requirements

- Strict decoding and canonical encoding round trips exist for Core Ty, Expr,
  Value, and Program.
- Zero and the maximum word are accepted, while a noncanonical representation
  corresponding to `2^256` is rejected.
- Stable codes and AST paths are assigned to an unbound variable, a non-bool
  condition, a branch mismatch, and a declared-result mismatch.
- For the existing seven-transition witness, fuel 6 produces `inconclusive`
  and fuel 7 produces `executed`.
- An Oracle golden test verifies that an unselected conditional branch is not
  evaluated.
- v1 `.check` and `.eval` remain `unsupported`.
- The bytes of v1 capabilities, the profile, and golden output do not change.
- Processing continues after a malformed record and in a mixed v1/v2 stream.
