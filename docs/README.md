# Documentation guide

This directory explains what `solcore-lean` specifies, what is executable
today, and which decisions are still only plans. Start here if you are reading
the repository for the first time.

## Choose a starting point

| If you want to… | Read… |
| --- | --- |
| understand the project in five minutes | [the project README](../README.md) |
| see exactly what is finished and what remains | [current status](CURRENT_STATUS.md) |
| understand the implementation and proof boundaries | [architecture](ARCHITECTURE.md) |
| build, test, or review a change | [development guide](DEVELOPMENT.md) |
| understand the normative authority and publication rules | [specification charter](SPEC_CHARTER.md) |
| check support for individual language features | [feature matrix](FEATURE_MATRIX.md) |
| compare Solcore with the pinned Haskell and Rust implementations | [compatibility matrix](COMPATIBILITY_MATRIX.md) |
| follow the completed Semantic Core work | [M1 plan](M1_PLAN.md) |
| follow the frontend work and remaining stages | [M2 plan](M2_PLAN.md) |

## How status words are used

The documents deliberately keep four questions separate:

- **Implemented** — executable Lean code exists.
- **Proved** — the implementation is connected to its declarative judgment by
  the stated theorem boundary.
- **Published** — a versioned profile, schema, or Oracle protocol exposes the
  behavior to external tools.
- **Performance-ready** — representative execution has been measured and is
  fast enough for its intended use.

For example, the M2c chart-based lexer/parser milestone is implemented with
selected-outcome and soundness theorems, but the complete ADR-0015 delivery is
not finished and no Oracle publishes it. Its executor also needs performance
work before it is suitable for high-volume differential testing.

An accepted ADR records a decision. It does not, by itself, prove that every
piece of the decision has been implemented. The status page and matrices are
the implementation ledger.

## Decision records

The [ADR directory](adr/) contains the durable decisions behind the code. The
recommended reading order is:

1. [ADR-0001](adr/0001-specification-authority-and-versioning.md) through
   [ADR-0008](adr/0008-observation-and-evm-revision.md) for project-wide rules,
   authority, profiles, verdicts, and observation.
2. [ADR-0009](adr/0009-m1a-core-machine-and-evaluation-order.md) through
   [ADR-0011](adr/0011-m1c-primitive-semantics-and-publication.md) for Semantic
   Core and its public wire protocols.
3. [ADR-0012](adr/0012-m2a-surface-parser-kernel.md) and
   [ADR-0013](adr/0013-m2b-surface-parser-publication.md) for the published
   single-file parser.
4. [ADR-0014](adr/0014-m2c-workspace-identity.md) through
   [ADR-0016](adr/0016-m2c-structural-syntax-identity.md) for the internal M2c
   workspace and Multi parser work.
5. [ADR-0017](adr/0017-m2c-module-resolution.md) for the proposed resolver. It
   is not an implemented feature.

ADRs preserve detailed rationale and rejected alternatives. Their short
reader summaries are the quickest way to decide whether the full record is
relevant.

## Sources of truth

When sources appear to disagree, use the authority order fixed by ADR-0001:

1. the versioned declarative Lean specification;
2. accepted ADRs and the version manifests they designate, including checked-in
   profiles and schemas;
3. Lean executors proved to correspond to that declarative specification;
4. normative conformance tests; and
5. other documentation and Haskell/Rust comparison evidence.

The pinned Haskell and Rust repositories are comparison evidence. They are not
the authority for Solcore semantics.
