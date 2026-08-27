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
Semantic Core and explicit runtime semantics.

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
