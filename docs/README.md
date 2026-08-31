# Documentation guide

This directory explains the public Solcore specification, the executable
semantics behind it, and the limits of the current implementation. Start with
the document that matches what you are trying to do; the decision records are
background material, not a progress log.

## Recommended reading order

| If you want to… | Start here |
| --- | --- |
| Build the repository or run the Oracle | [Root README](../README.md) |
| Generate reproducible checked Core inputs | [Root README](../README.md#use-as-a-lean-library) |
| See exactly what works today | [Current status](CURRENT_STATUS.md) |
| Send checked-contract requests | [Oracle v5 wire catalog](ORACLE_V5_WIRE.md) |
| Produce or consume Semantic Core | [Core Wire v3 catalog](CORE_WIRE_V3.md) |
| Understand the semantic layers | [Architecture](ARCHITECTURE.md) |
| Understand what is normative | [Specification charter](SPEC_CHARTER.md) |
| Compare with the Haskell or Rust compiler | [Compatibility matrix](COMPATIBILITY_MATRIX.md) |
| Follow canonical source frontend work | [Canonical syntax plan](M2_PLAN.md) |
| Build and review a change | [Development guide](DEVELOPMENT.md) |

The [feature matrix](FEATURE_MATRIX.md) is a detailed inventory. Use it when
you need to locate the status of one specific language or runtime feature;
use Current status for the concise supported boundary.

## Public interfaces

The command-line Oracle is versioned additively. Older inputs keep their
original meaning when a new version is added.

| Oracle | Input language | Purpose |
| --- | --- | --- |
| v1 | Legacy request envelope | Compatibility and capability discovery |
| v2 | Semantic Core v1 | Historical Core checking and evaluation |
| v3 | Semantic Core v2 | Frozen Core checking and evaluation |
| v4 | Surface v1 | Restricted single-file parsing |
| v5 | Semantic Core v3 plus an explicit scenario | Core checking and checked-contract execution |

Oracle v5 is the current checked-contract interface. It is public and
executable. Its `capabilities`, `coreCheck`, and `execute` queries share one
strict request envelope and return query-compatible total results.

The older machine-readable schemas are kept under [`schema/`](../schema).
Core v3 and Oracle v5 are documented by their closed wire catalogs:

- [Semantic Core Wire v3](CORE_WIRE_V3.md)
- [Oracle v5 requests and responses](ORACLE_V5_WIRE.md)

Both catalogs define exact objects, scalar encodings, limits, canonical order,
and error priority. Do not infer a public field from an internal Lean type.

## How Oracle v5 fits together

The v5 path is deliberately independent of concrete source syntax:

```text
Oracle v5 JSON
  → strict and resource-bounded decoding
  → Semantic Core v3 checking
  → checked-contract admission
  → explicit world and environment validation
  → top-level execution with commit or rollback
  → total execution and state observation
```

Well-typedness is required before execution. The request also supplies the
initial accounts, storage, balances, code references, nested-call registry,
creation policy, invocation data, fuel, and requested state probes. This makes
the initial conditions and observable result reproducible.

The current runtime includes depth-one checked calls, value transfer, checked
creation, ordered Word logs, and the static Word ABI. A top-level return commits
the working state. Preflight rejection, revert, and trap select the checkpoint.
Fuel exhaustion is an inconclusive response, not a fabricated terminal state.

For exact JSON fields and rejection order, use the Oracle v5 catalog rather
than this overview.

## Source parsing is separate

Oracle v4 and Surface v1 are frozen historical interfaces. Current Solcore
syntax is modeled afresh under `Solcore.Syntax` from the implementation pinned
by ADR-0153. The replacement does not reuse or extend the old Surface AST and
parser.

The complete executable canonical lexer and parser remain separate from
Semantic Core and Oracle v5. They are available through the public Lean
library. Name resolution, source type checking, and elaboration into checked
Core are subsequent stages. This separation lets frontend work proceed without
changing the meaning of any published Oracle protocol.

## Semantics and verification

The [architecture](ARCHITECTURE.md) explains the separation among source
syntax, resolved input, Semantic Core, contract runtime state, and observable
results. It also explains why runtime state and Core-local mutable cells are
different stores.

The [specification charter](SPEC_CHARTER.md) defines authority. In short,
versioned Lean definitions and their published wire contracts define Solcore;
the Haskell and Rust implementations provide comparison evidence rather than
language authority.

The [compatibility matrix](COMPATIBILITY_MATRIX.md) records which comparisons
are meaningful today. Oracle v5 provides a deterministic Core execution and
observation boundary, but there is not yet an end-to-end source elaborator or
external compiler adapter. Agreement at a different layer must not be reported
as full source-language conformance.

## Decision records

The [`adr/`](adr) directory contains accepted design decisions and their
rationale. Read an ADR when you need to understand why a representation,
evaluation rule, rollback policy, or publication boundary was chosen.

An ADR describes the scope and state of the decision when it was written.
Statements such as “not yet public” in an older ADR are historical and do not
override a later publication. Use [Current status](CURRENT_STATUS.md) for the
revision-local answer and the wire catalogs for an exact public contract.

## Contributing to the specification

The [development guide](DEVELOPMENT.md) covers build checks, proof and test
expectations, compatibility rules, and review hygiene. Public changes require
an additive versioned boundary; existing Core, Surface, and Oracle versions are
never silently reinterpreted.
