# Documentation guide

This directory explains the current Lean specification. The source tree and
kernel-checked declarations remain authoritative when prose and code differ.

## Recommended reading order

1. [Specification charter](SPEC_CHARTER.md) — authority, scope, and trust.
2. [Architecture](ARCHITECTURE.md) — layer ownership and dependency rules.
3. [Current status](CURRENT_STATUS.md) — implemented boundaries and open work.
4. [Feature matrix](FEATURE_MATRIX.md) — compact coverage by subsystem.
5. [Project map](PROJECT_MAP.md) — task-oriented source navigation.
6. [Development guide](DEVELOPMENT.md) — validation and contribution workflow.

The two implementation policies divide work by abstraction:

- [Semantic Core policy](M1_PLAN.md) covers Core, checked-contract execution,
  ABI support, and Core synthesis.
- [Canonical syntax plan](M2_PLAN.md) covers lexing, parsing, recovery, AST
  validity, and the handoff into workspace/frontend processing.

## Public Lean interfaces

| Need | Import | Primary responsibility |
| --- | --- | --- |
| Everything supported | `Solcore` | Public umbrella |
| Parse source | `Solcore.Syntax` | Tokens, diagnostics, recovery-aware AST |
| Check and compile a workspace | `Solcore.Frontend.Current` | Resolution, typing, specialization, backend selection |
| State language rules independently | `Solcore.SourceSemantics` | Declarative static, staging, and dynamic judgments |
| Work with the executable IR | `Solcore.Core` | Core syntax, checking, evaluation, machines, proofs |
| Execute checked contracts | `Solcore.ContractRuntime` | World, transaction, frame, call, creation, and observation semantics |
| Encode supported ABI values | `Solcore.Abi` | Keccak-256 and static-word ABI utilities |
| Generate checked Core inputs | `Solcore.Synthesis` | Seeded generation and shrinking |

These are direct Lean APIs. Individual submodules may be imported when a
smaller dependency boundary matters.

## Reference catalogs

- [Semantic Core Wire](CORE_WIRE.md) describes the current Core data
  encoding.
- [Compatibility evidence](COMPATIBILITY_MATRIX.md) records what comparisons
  with the pinned Haskell and Rust revisions do and do not establish.
- [`adr/`](adr/) contains durable design decisions. Start with
  [ADR-0153](adr/0153-canonical-syntax-boundary.md) for the canonical syntax
  boundary, [ADR-0377](adr/0377-declarative-source-semantics-foundation.md)
  and [ADR-0378](adr/0378-declarative-resolved-source-semantics.md) for the
  proof-facing source model, and
  [ADR-0379](adr/0379-module-boundaries-and-contract-runtime-naming.md) for
  module ownership.

## Document roles

- The charter and architecture describe stable policy.
- Current status is the revision-local implementation ledger.
- The feature matrix summarizes coverage without replacing detailed proofs.
- Plans record sequencing and completion criteria.
- ADRs retain the rationale for accepted decisions.

When implementation changes, update the narrowest document that owns the
claim. Avoid copying long theorem inventories into several files.
