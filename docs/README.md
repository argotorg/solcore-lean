# Documentation guide

Start with the **[Solcore semantics and proven guarantees guide](../manual/README.md)**.
It explains the language through checked examples and the meaning of its
theorems: values and bindings, checking, execution and fuel, state, contract
rollback, source lowering, and reproducible Oracle experiments. It assumes no
experience reading Lean proofs.

## Choose a reading path

| Your question | Read |
| --- | --- |
| What does a program mean? | [Values and expressions](../manual/Guide/Language.lean), then [execution](../manual/Guide/Execution.lean) |
| What is proven, and under what assumptions? | [Reading theorems](../manual/Guide/Theorems.lean) and the [guarantee map](../manual/Guide/Guarantees.lean) |
| What survives return, revert, or trap? | [State](../manual/Guide/State.lean) and [contracts](../manual/Guide/Contracts.lean) |
| How does source reach Core? | [Frontend guide](../manual/Guide/Frontend.lean) |
| How do I run an experiment? | [Oracle guide](../manual/Guide/Oracle.lean) and [root usage instructions](../README.md) |
| Where are the architectural boundaries? | [Architecture](ARCHITECTURE.md) |
| What works at this revision? | [Current status](CURRENT_STATUS.md) and [feature matrix](FEATURE_MATRIX.md) |
| What are the exact public bytes? | [Core Wire v3](CORE_WIRE_V3.md) and [Oracle v5](ORACLE_V5_WIRE.md) |
| Which rules are authoritative? | [Specification charter](SPEC_CHARTER.md) |
| What has been compared with Rust or Haskell? | [Compatibility evidence](COMPATIBILITY_MATRIX.md) |
| How do I build or contribute? | [Development](DEVELOPMENT.md) |

The chapter links above open their checked source. Follow the manual's build
instructions for the rendered site with navigation, search, and signature
hovers.

## Public boundaries

| Oracle | Input | Purpose |
| --- | --- | --- |
| v1 | Legacy envelope | Compatibility and capability discovery |
| v2 | Core v1 | Historical Core checking and evaluation |
| v3 | Core v2 | Frozen Core checking and evaluation |
| v4 | Surface v1 | Restricted historical parsing |
| v5 | Core v3 and an explicit scenario | Core checking and checked-contract execution |

Oracle v5 begins at Core. Canonical parsing, restricted source checking,
specialization, and elaboration are separate Lean interfaces; they do not
silently extend a published source protocol. See Current status for their
precise admitted fragments.

Published formats retain their original meaning. Older schemas live in
[`schema/`](../schema); Core v3 and Oracle v5 have closed wire catalogs.
Use the catalogs for exact object fields, scalar encodings, resource limits,
canonical ordering, and rejection priority.

## Reference and history

Each document has one primary job. The manual teaches semantics and explains
guarantees. Architecture records stable responsibilities. Current status is the
revision-local ledger; the feature matrix indexes coverage. Wire catalogs and
the charter define public contracts and authority.

[Decision records](adr) preserve the rationale for selected rules. Historical
statements about what was incomplete do not override later publications or the
current ledger. [M1](M1_PLAN.md) and [M2](M2_PLAN.md) describe implementation
sequencing and milestone boundaries; they are not the introductory reading path.

Keep proof scripts in source and detailed inventories in their reference homes.
The guide should explain what a theorem lets a reader conclude and which
assumptions must hold before using it.
