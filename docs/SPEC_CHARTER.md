# Solcore Lean Specification Charter

- Status: Draft
- Target specification: `solcore/0.1.0-draft.1`
- Enacted: 2026-07-23

## Purpose

`solcore-lean` is an executable formal specification of the Solcore language
and a reference implementation independent of the Haskell and Rust
implementations. Its eventual role is to serve as an oracle for semantic
differential fuzzing by comparing the observations produced by each
implementation for the same input program and execution environment.

To serve this purpose, the specification provides the following three elements
as a unified whole:

1. Declarative relations describing typing, class constraints, evaluation, and
   execution-state transitions
2. A deterministic, executable specification comprising a parser, checker,
   solver, and evaluator
3. Correspondence proofs showing that the executable specification follows the
   declarative relations

## Specification authority

Sources of semantic information have the following precedence:

1. The versioned declarative Lean specification
2. Accepted ADRs and the version manifests they designate
3. Lean executors whose correspondence with the declarative specification has
   been proved
4. Normative conformance tests
5. Existing language documentation, the Haskell implementation, the Rust
   implementation, the standard library, and existing test corpora

When higher- and lower-priority sources conflict, the higher-priority source
prevails. A conflict between the declarative specification and an executor is
treated as a defect in the executor or its correspondence proof. Agreement
between the two existing implementations, a majority decision, long-standing
behavior, or inclusion in a test corpus does not by itself constitute a
specification decision.

Every new specification choice or observable change requires an Accepted ADR.
The component versions of all affected areas—grammar, static semantics, dynamic
semantics, ABI, and storage layout—must be updated.

## Design principles

- The boundaries between Surface, Resolved, and Semantic Core are explicit.
- Surface preserves source order, spans, and syntactic boundaries.
- Semantic Core directly represents lexical closures, pattern matching, type
  application, class evidence, and comptime/runtime stages.
- Hull, Yul, and EVM bytecode are not the core of the specification; they are
  targets for future verified lowering.
- The semantic kernel is constructed from pure, total functions and does not
  depend on `partial`, `unsafe`, or actual IO.
- Potentially nonterminating evaluation and search use explicit resource
  limits. A limit does not change the semantics and is used only to make a
  result inconclusive.
- The host, block context, initial state, and transaction sequence are explicit
  inputs rather than implicit global state.
- Semantically irrelevant differences, such as generated names, internal map
  enumeration order, and English diagnostic prose, are excluded from semantic
  observations.

## Versions and comparison baselines

`LanguageVersion` identifies the component versions for grammar, static
semantics, dynamic semantics, ABI, and storage layout, as well as the
standard-library digest and known feature IDs. A component version whose
normative rules are incomplete is `none`. The EVM revision and gas schedule do
not enter the pure Core; they are fixed by a contract-scope
`ContractRuntimeProfile`.

Feature status distinguishes between a known ID, a design direction decided by
an Accepted ADR, completed normative rules, enablement in a profile, and an
implementation in Lean. A successful query requires
`implemented ⊆ enabled ⊆ normative ⊆ known`. At M0, normative rules for
language features are incomplete, and `enabledFeatures` is empty in `core-v1`.

Haskell and Rust commits, solver modes, dispatch configuration, backends,
resource limits, and related implementation settings are recorded separately
in `ImplementationBaseline`. Updating an implementation does not by itself
change the language version.

All of the following must match in a comparison:

- Language version and feature profile
- Standard-library contents
- Solver policy
- Phase reached, including frontend, specialization, and dispatch
- EVM revision and deterministic host
- Initial state and transaction sequence
- Semantic-observation policy

In addition to the request ID, an oracle response returns the specification,
profile ID and digest, and query kind so that the comparison conditions can be
identified from the response record alone.

## Verdict categories

An oracle language query has one of the following six verdicts:

| Verdict | Meaning |
| --- | --- |
| `accepted` | Completed the requested static phase successfully |
| `rejected` | Violated a language rule defined by the target profile |
| `unsupported` | A required feature or its semantics is undefined in the target profile |
| `inconclusive` | A resource limit prevented a definitive verdict or execution result |
| `executed` | Ran a dynamic query and obtained a normative observation |
| `internalError` | An invariant violation or implementation defect occurred in the oracle |

Malformed JSON, duplicate object keys, unknown schemas, unsafe source paths,
and similar conditions are not properties of the language. They are handled as
`protocolError` outside the verdict categories above.

The following reinterpretations are prohibited:

- An unimplemented feature must not be returned as `rejected`.
- A timeout, exhausted solver fuel, or exhausted evaluation fuel must not be
  returned as `rejected`.
- A crash or invariant violation must not be returned as `rejected` for the
  source program.
- A runtime `revert` or defined `trap` must not be returned as `internalError`.

## Observational equivalence

Static queries compare diagnostic codes, phases, severities, UTF-8 byte spans,
and structured arguments normatively. English messages and presentation layout
are not compared.

Value evaluation compares canonical values and halt statuses. Contract
execution compares at least the following for each transaction:

- The distinction between return, revert, and trap
- Return data or revert data
- Storage delta
- Balance delta
- Logs
- External-call trace
- Addresses and code of created contracts

The standard profile does not compare gas. If gas becomes part of the
specification, it uses a dedicated profile that fixes the EVM revision, gas
schedule, warm/cold state, and other relevant conditions.

## Non-goals

At least during the initial stages, the following are not goals:

- Reproducing the current behavior of the Haskell or Rust implementation
  unconditionally
- Matching Hull, Yul, bytecode, generated names, or optimizer output
- Defining Lean semantics through a backend
- Proving the correctness of both existing implementations in their entirety
  at once
- Guessing and implementing undecided ABI, storage, or inline Yul behavior
- Exactly matching diagnostic prose, colors, or display order
- Matching gas consumption in the standard profile
- Treating resource exhaustion as a language rejection

## Conformance-test requirements

As a rule, every normative rule has all of the following:

1. A minimal positive witness that satisfies the rule
2. A minimal negative witness that violates only that rule
3. The expected verdict category and, for a failure, its phase
4. A theorem or property test checking correspondence between the declarative
   specification and the executor
5. A golden test of the oracle's canonical serialization

The following are additionally required:

- When a difference from Haskell or Rust is resolved, its minimized witness is
  added to the normative corpus.
- Equivalent input orderings, JSON key orderings, and map construction orders
  must produce the same canonical output.
- Tests distinguish `unsupported`, `inconclusive`, and `internalError` from
  `rejected`.
- Contract tests run every implementation with the same EVM revision, initial
  state, and transaction sequence.
- Revert tests also check state rollback.
- ABI tests exercise every path through metadata, selector spelling, decoding,
  and encoding.
- Tests verify that selector collisions are detected before code generation.
- The semantic kernel contains no `sorry`, `admit`, `partial`, or `unsafe`.

A conformance corpus is evidence used to discover the specification; it is not
by itself a specification authority. A change to an expected result must
include the corresponding specification change or ADR in the same change.

## M0 completion criteria

M0 is complete when all of the following hold:

- The boundaries among language versions, profiles, and baselines are defined
  in types and documentation.
- Accepted ADRs are consistent with the feature and compatibility matrices.
- A versioned NDJSON schema and the verdict categories are implemented.
- The `capabilities` query returns the version, profile, and baseline
  deterministically.
- Unimplemented semantic queries return `unsupported`.
- Tests for schemas, canonicalization, path validation, and streaming pass.
