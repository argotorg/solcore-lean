# Solcore Lean Specification Charter

- Status: Draft
- Target specification: `solcore/0.1.0-draft.3`
- Adopted: 2026-07-23

## Purpose

`solcore-lean` is an executable formal specification of the Solcore language,
developed independently of the Haskell and Rust implementations. Its eventual
purpose is to serve as the reference oracle for semantic differential fuzzing
by comparing the observations produced by each implementation for the same
input program and execution environment. At the current milestone, its
executable reference boundary is the published closed Semantic Core; a
source-level parser, resolver, and elaborator are not yet part of that boundary.

The internal M2a kernel now lexes and parses the closed fragment fixed by
[ADR-0012](adr/0012-m2a-surface-parser-kernel.md). It is intentionally not a
published reference boundary: it has no versioned Surface wire format or
Oracle query, and it performs no name resolution, checking, or elaboration.
Its public success path is checked against declarative span, grammar, and
token-correspondence predicates. A declarative maximal-munch lexer judgment,
direct construction of the full parser grammar derivation, relational
determinism/completeness, and frontend fuel sufficiency remain proof
obligations.

To achieve this purpose, the specification provides the following three
elements as one coherent whole:

1. Declarative relations describing typing, class constraints, evaluation, and
   execution-state transitions
2. A deterministic, executable specification comprising a parser, checker,
   solver, and evaluator
3. Correspondence proofs showing that the executable specification follows the
   declarative relations

## Specification authority

Sources of semantic information have the following order of precedence:

1. The versioned Lean declarative specification
2. Accepted ADRs and the version manifests designated by those ADRs
3. Lean executors proved to correspond to the declarative specification
4. Normative conformance tests
5. Existing language documentation, the Haskell implementation, the Rust
   implementation, the standard library, and existing test corpora

When a higher-ranked source conflicts with a lower-ranked source, the
higher-ranked source prevails. A conflict between the declarative specification
and an executor is treated as a defect in the executor or its correspondence
proof. Agreement between the two existing implementations, a majority vote,
long-standing behavior, or inclusion in a test corpus does not by itself
constitute a specification decision.

Every new specification choice or observable change requires an Accepted ADR.
The component versions of all affected areas—grammar, static semantics, dynamic
semantics, ABI, and storage layout—must be updated.

## Design principles

- Make the boundaries between Surface, Resolved, and Semantic Core explicit.
- Surface preserves source order, spans, and syntactic boundaries.
- Semantic Core directly represents lexical closures, pattern matching, type
  application, class evidence, and comptime/runtime stages.
- Hull, Yul, and EVM bytecode are not the specification kernel; they are targets
  of future verified lowering.
- The semantic kernel is pure and total, and does not depend on `partial`,
  `unsafe`, or real I/O.
- Evaluation or search that may not terminate uses an explicit resource limit.
  A limit does not change the semantics; it can only make the result
  inconclusive.
- The host, block context, initial state, and transaction sequence are explicit
  inputs rather than implicit global state.
- Semantically irrelevant differences, such as generated names, internal map
  enumeration order, and English diagnostic prose, are excluded from semantic
  observations.

## Versions and comparison baselines

`LanguageVersion` identifies the component versions for grammar, static
semantics, dynamic semantics, ABI, and storage layout, together with the
standard-library digest and known feature IDs. A component whose normative rules
are incomplete has version `none`. EVM revisions and gas schedules are not mixed
into the pure Core; they are fixed by a contract-scoped
`ContractRuntimeProfile`.

Feature status distinguishes whether an ID is known, an Accepted ADR has chosen
its design direction, its normative rules are complete, a profile enables it,
and Lean implements it. Successful queries require
`implemented ⊆ enabled ⊆ normative ⊆ known`. At M0, no language feature has
complete normative rules, so `core-v1` has an empty `enabledFeatures` list.

M1b published the first closed Core as `solcore/0.1.0-draft.2`, profile
`core-m1a-v1`, `solcore-semantic-core/v1`, and `solcore-oracle/v2`. M1c
publishes the primitive extension as `solcore/0.1.0-draft.3`, profile
[`core-m1c-v1`](../profiles/solcore-0.1.0-draft.3-core-m1c.json),
[`solcore-semantic-core/v2`](../schema/semantic-core-v2.schema.json), and
[`solcore-oracle/v3`](../schema/oracle-v3.schema.json). The exact semantics and
publication boundary are fixed by
[`ADR-0011`](adr/0011-m1c-primitive-semantics-and-publication.md).

The M1c profile enables boolean negation and the specified word arithmetic,
comparison, bitwise, and shift operations in addition to the five M1b
features. Primitive operands are evaluated exactly once, binary operands from
left to right; arithmetic is modulo `2^256`; division and modulo by zero return
zero; and shifts by at least 256 return zero. The declarative and executable
typing/evaluation layers are connected by soundness, completeness,
determinism, CEK correspondence, progress, preservation, sufficient-fuel, and
fault-unreachability results for this fragment.

All draft.1 and draft.2 language/profile documents, digests, Core/Oracle schema
contracts, capability bytes, and golden streams are immutable. Semantic changes
are appended under new version identifiers; Oracle v2 remains bound to
Semantic Core v1 and Oracle v3 remains bound to Semantic Core v2.

The Haskell and Rust commits, solver mode, dispatch setting, backend, resource
limits, and similar implementation settings are recorded separately in an
`ImplementationBaseline`. Updating an implementation does not by itself change
the language version.

Every comparison must align all of the following:

- Language version and feature profile
- Standard-library contents
- Solver policy
- Reached phase, such as frontend, specialization, or dispatch
- EVM revision and deterministic host
- Initial state and transaction sequence
- Semantic observation policy

In addition to the request ID, every oracle response returns the specification,
profile ID and digest, and query kind, so that a response record identifies its
comparison conditions by itself.

`capabilities-v3` is the current capability report. It identifies draft.3,
`core-m1c-v1`, the canonical profile digest, Semantic Core v2, supported Core
queries, observation schemas, feature states, and resource limits. It does not
claim that either existing compiler accepts the Core wire format or that
source-level differential conformance has been established.

## Verdicts

The oracle has the following six language verdicts:

| Verdict | Meaning |
| --- | --- |
| `accepted` | The requested static phase completed successfully |
| `rejected` | The input violates a language rule defined by the target profile |
| `unsupported` | A required feature or its semantics is undefined in the target profile |
| `inconclusive` | A resource limit prevented a definitive verdict or execution result |
| `executed` | A dynamic query ran and produced a normative observation |
| `internalError` | The oracle itself encountered an invariant violation or implementation defect |

Malformed JSON, duplicate object keys, unknown schemas, unsafe source paths, and
similar conditions are not language properties. They are reported as
`protocolError`, outside the verdicts above.

The following reinterpretations are forbidden:

- Do not report an unimplemented feature as `rejected`.
- Do not report a timeout, exhausted solver fuel, or exhausted evaluation fuel
  as `rejected`.
- Do not report a crash or invariant violation as `rejected` for the source
  program.
- Do not report a runtime `revert` or defined `trap` as `internalError`.

## Observational equivalence

Static queries normatively compare diagnostic codes, phases, severities, UTF-8
byte spans, and structured arguments. English messages and presentation layout
are not compared.

Value evaluation compares canonical values and halt status. Contract execution
compares at least the following for every transaction:

- The distinction between return, revert, and trap
- Return data or revert data
- Storage delta
- Balance delta
- Logs
- External-call trace
- Address and code of each created contract

The standard profile does not compare gas. A dedicated profile that fixes the
EVM revision, gas schedule, warm/cold state, and related parameters is required
before gas becomes part of the specification.

## Non-goals

At least during the initial stages, the project does not aim to:

- Reproduce the current behavior of the Haskell or Rust implementation
  unconditionally
- Match Hull, Yul, bytecode, generated names, or optimizer output
- Define Lean semantics through a backend
- Prove both existing implementations correct in their entirety at once
- Guess unresolved ABI, storage, or inline-Yul behavior
- Match diagnostic prose, colors, or presentation order exactly
- Match gas consumption in the standard profile
- Treat resource exhaustion as language rejection

## Conformance-test requirements

Every normative rule should normally have all of the following:

1. A minimal positive witness that satisfies the rule
2. A minimal negative witness that violates only that rule
3. The expected verdict and, for a failure, its phase
4. A theorem or property test checking correspondence between the declarative
   specification and executor
5. A golden test for the oracle's canonical serialization

The following are additionally required:

- When a Haskell/Rust discrepancy is resolved, add the minimized witness to the
  normative corpus.
- Verify that semantically equivalent input ordering, JSON key ordering, and map
  construction ordering produce the same canonical output.
- Include tests that distinguish `unsupported`, `inconclusive`, and
  `internalError` from `rejected`.
- Run contract tests against every implementation with the same EVM revision,
  initial state, and transaction sequence.
- A revert test also verifies state rollback.
- An ABI test exercises the complete metadata, selector spelling, decode, and
  encode paths.
- Verify that selector collisions are detected before code generation.
- Leave no `sorry`, `admit`, `partial`, or `unsafe` in the semantic kernel.

The conformance corpus is evidence for discovering the specification, not an
authority by itself. A change to an expected result must include the
corresponding specification change or ADR.

Short-circuit boolean conjunction/disjunction, boolean/word conversions, and
functions, closures, application, and return remain outside the M1c normative
fragment. They require explicit source/Core elaboration rules and any necessary
new feature, language, and wire versions before an Oracle may report them as
supported.

## M0 completion criteria

M0 is complete when all of the following hold:

- The boundaries between the language version, profile, and baseline are
  defined in types and documentation.
- Accepted ADRs agree with the feature and compatibility matrices.
- The versioned NDJSON schema and verdict taxonomy are implemented.
- The `capabilities` query deterministically returns the version, profile, and
  baseline.
- Queries for unimplemented semantics return `unsupported`.
- Tests for schemas, canonicalization, path validation, and streaming pass.

## Current M1c publication criteria

M1c is published only because all of the following hold for its closed Core
fragment:

- the primitive signatures and edge cases are fixed independently of compiler
  defaults
- declarative typing and evaluation include every published unary and binary
  expression
- executable checking and evaluation are proof-connected to those relations
- progress, preservation, sufficient-fuel completion, and typed fault
  unreachability cover the extended machine
- Semantic Core v2 and Oracle v3 are closed, version-bound schemas with
  canonical codecs and cross-version rejection tests
- the draft.1/Oracle v1 and draft.2/Oracle v2 artifacts retain their existing
  bytes
