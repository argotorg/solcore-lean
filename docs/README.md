# Documentation guide

The root README explains what can be run. The documents in this directory
explain what the implementation means, what is proved, and what remains.

## Where to start

| Question | Document |
| --- | --- |
| What works today? | [Current status](CURRENT_STATUS.md) |
| What is the active development direction? | [Semantic Core roadmap](M1_PLAN.md) |
| Why is parser work paused? | [Frontend freeze and resumption plan](M2_PLAN.md) |
| How are the layers separated? | [Architecture](ARCHITECTURE.md) |
| Which features exist? | [Feature matrix](FEATURE_MATRIX.md) |
| What makes a rule normative? | [Specification charter](SPEC_CHARTER.md) |
| How do I build and review changes? | [Development guide](DEVELOPMENT.md) |
| What can be compared with other compilers? | [Compatibility matrix](COMPATIBILITY_MATRIX.md) |

## Current development policy

Concrete Solcore syntax may change substantially. The published parsers remain
available as versioned reference implementations, but new grammar-dependent
proof work is paused. Active work is directed toward a syntax-independent
Semantic Core and explicit runtime semantics. First-order local cells from
ADR-0022 and the program-local named algebraic data and normalized constructor
matching from [ADR-0023](adr/0023-core-vnext-named-algebraic-data.md) are
complete internal slices. The derived boolean and word conversions from
[ADR-0024](adr/0024-core-vnext-bool-word-conversions.md) are complete as ordinary
existing Core expressions. The derived word-valued zero test from
[ADR-0025](adr/0025-core-vnext-word-is-zero.md) is also complete.
The [ADR-0026](adr/0026-core-vnext-short-circuit-booleans.md) slice completes
selected-branch-only boolean conjunction and disjunction using existing
conditionals without adding a Core tag. Its expansion, typing, inference, four
store-threaded branches, effects, faults, exact fuel, weakening, and exact wire
v1/v2 projection are proved and tested. Core vNext remains active, with
the completed `wordIsNonzero` from
[ADR-0027](adr/0027-core-vnext-word-is-nonzero.md) as its ninth slice.
It composes `boolToWord(wordToBool(x))`, maps zero to word zero and nonzero words
to word one, evaluates its operand exactly once, and preserves its final store.
It adds no tag and is separate from boolean truthiness and ABI decoding.
Its named expansion, typing, inference, store-preserving evaluations, weakening,
effects, exact fuel, distinctions, and exact v1/v2 boundaries are proved and
tested, and the audits pass.
Additional conversions and primitives remain planned.
The completed tenth slice, [ADR-0028](adr/0028-core-vnext-word-comparison-flags.md),
derives canonical word-valued equality and unsigned greater-than flags from
the existing boolean comparisons. It preserves left-to-right evaluation and
adds no tag or source, standard-library, ABI, opcode, or gas commitment.
Its named expansions, typing, inference, store-threaded cases, weakening,
effects and fault order, exact fuel, boolean preservation, and exact v1/v2
boundaries are proved and tested; the audits pass. Core vNext remains active.
The completed eleventh slice,
[ADR-0029](adr/0029-core-vnext-renaming-simulation.md), provides binder-aware
syntax renaming, typing preservation, structural value/environment/store
relations, simulation for every evaluation form, ground-value and typed-store
exactness, and an exact word-result head-insertion theorem. Static and dynamic
tests cover the foundation. It changes no execution, source, or wire meaning.
The active twelfth slice,
[ADR-0030](adr/0030-core-vnext-derived-word-comparisons.md), completes the proof
interfaces for the existing `wordNe`, `wordLt`, `wordLe`, and `wordGe`
builders. Their expansions remain unchanged; the nested-let comparisons keep
left-to-right exactly-once evaluation for arbitrary effectful expressions. No
new syntax, tag, or public behavior is added. Additional primitives remain
planned.
These slices add no source spelling for mutable
declarations, assignment, data declarations, patterns, or casts; the conversions
also remain separate from future ABI decoding. Further Core work follows the
roadmap through separate semantic decisions.

This policy is recorded by
[ADR-0018](adr/0018-semantics-first-development-order.md). It changes
development order, not the meaning of any published protocol.

## Status vocabulary

The repository keeps four claims separate:

- Implemented: executable Lean code exists.
- Proved: stated theorems connect the code to independent judgments.
- Published: a versioned schema, profile, and Oracle expose the behavior.
- Runtime-ready: performance has been measured for the intended workload.

An Accepted ADR fixes a decision. It does not imply that the decision has been
implemented. Conversely, an internal implementation does not silently expand
a published profile.

## Decision records

The [ADR directory](adr/) contains durable decisions and rationale.

- ADR-0001 through ADR-0008 define authority, semantic layers, verdicts,
  resolution direction, ABI boundaries, standard-library pinning, and
  observations.
- ADR-0009 through ADR-0011 define the published Semantic Core.
- ADR-0012 through ADR-0017 record the parser, workspace, identity, and
  proposed resolution work.
- ADR-0018 records the semantics-first development pivot.
- ADR-0019 defines the first internal Core vNext feature.
- ADR-0020 defines non-recursive functions and lexical closures.
- ADR-0021 defines binary sums and exhaustive elimination.
- ADR-0022 defines first-order local cells and their explicit local store.
- ADR-0023 defines named algebraic data and direct normalized matching.
- ADR-0024 defines derived boolean and word conversions.
- ADR-0025 defines the derived word-valued zero test.
- ADR-0026 defines derived short-circuit boolean conjunction and disjunction.
- ADR-0027 defines the derived word-valued nonzero test.
- ADR-0028 defines derived word-valued equality and unsigned-greater flags.
- ADR-0029 defines the renaming and environment-insertion proof foundation.
- ADR-0030 completes proof interfaces for existing derived word comparisons.

Historical ADRs are retained even when their implementation is no longer the
active priority.

## Sources of truth

When two sources disagree, use this order:

1. versioned declarative Lean definitions;
2. Accepted ADRs and the manifests or schemas they designate;
3. executable Lean definitions proved to implement those rules;
4. normative conformance tests;
5. explanatory documentation and comparison evidence.

Pinned Haskell and Rust behavior is evidence, never specification authority.
