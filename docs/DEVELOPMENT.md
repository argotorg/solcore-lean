# Development guide

This guide describes the local checks and the workflow for changing the Lean
specification. Keep changes within the layer that owns the behavior and make
cross-layer adapters explicit.

## Build and test

Use the checked-in Lean toolchain from the repository root:

```text
lake build
lake test
node scripts/verify-metadata.mjs
node scripts/check-kernel.mjs
```

Warnings are errors. During development, build the narrowest changed module
first, then run the complete suite before handing off the change.

To verify the embedded canonical standard-library bytes against an upstream
checkout:

```text
node scripts/verify-metadata.mjs --canonical-source-root <solcore-checkout>/std
```

## Choose the owning layer

| Change | Primary location | Also inspect |
| --- | --- | --- |
| Tokens, grammar, recovery, AST | `Solcore/Syntax` | parser properties, fixtures, workspace handoff |
| Library/module identity | `Solcore/Workspace` | loading, imports, standard-library catalog |
| Source types and inference machinery | `Solcore/TypeSystem` | frontend inference and declarative source judgments |
| Executable resolution/checking/compilation | `Solcore/Frontend` | Syntax, Workspace, TypeSystem, Core adapters |
| Normative source judgments | `Solcore/SourceSemantics` | substitutions, staging, dynamics, preservation |
| Executable intermediate language | `Solcore/Core` | typing, evaluation, checker, machine, safety, wire isolation |
| Accounts, frames, transactions, calls | `Solcore/ContractRuntime` | Core host operations, ABI boundary, observations |
| Hashing and call-data encoding | `Solcore/Abi` | contract-entry profiles and tests |
| Seeded Core generation/shrinking | `Solcore/Synthesis` | checker sealing, scope and size proofs |
| Canonical source bytes | `Solcore/Standard` | hashes, logical paths, workspace consumers |

Do not place source-language rules in contract execution, contract state in the
Core local store, or executable frontend success as a premise of an
independent source judgment.

## Semantic feature workflow

Before implementation:

1. identify the smallest observable feature and its owning layer;
2. write or update an ADR when the behavior is a durable design choice;
3. list affected syntax, static, dynamic, resource, diagnostic, and proof
   obligations; and
4. identify every retained encoding or adapter that must reject or represent
   the new form.

During implementation:

1. add the declarative data and rules;
2. add executable checking or evaluation where the layer requires it;
3. prove soundness, completeness, correspondence, or preservation at the
   boundary being changed;
4. preserve deterministic error priority and evaluation order;
5. add focused positive, negative, resource, and regression tests; and
6. keep each intermediate commit independently buildable when practical.

After implementation:

1. build changed modules with warnings as errors;
2. run the full test suite;
3. run repository-data and kernel-policy checks;
4. inspect axiom reports for new critical theorems;
5. update [Current status](CURRENT_STATUS.md) and the
   [feature matrix](FEATURE_MATRIX.md); and
6. check documentation links and stale module names.

## Completion standard

A semantic feature is not complete merely because one example evaluates to
the expected value. Reviewers should be able to locate, as applicable:

- the independent rule;
- the executable implementation;
- soundness and completeness;
- dynamic correspondence;
- value, environment, heap, frame, or state preservation;
- resource and resumption behavior;
- deterministic diagnostic behavior; and
- isolation of retained encodings.

If a proof direction is delayed, mark the feature partial and name the missing
result. Do not describe a local theorem as an end-to-end guarantee.

## Syntax and frontend changes

Canonical syntax changes belong under `Solcore/Syntax`. Keep the lexer,
declarative grammar, executable parser, recovery behavior, AST validity, and
their proofs synchronized.

The parser reaches executable semantics only through explicit workspace,
resolution, typing, staging, specialization, and linking phases. Preserve that
separation when adding a source form. A parser test is not a source-typing or
execution test.

For an upstream syntax change:

1. record the exact upstream revision used as evidence;
2. classify token, grammar, recovery, AST, and diagnostic impact;
3. update focused fixtures and exactness proofs; and
4. run both the syntax-focused and complete repository checks.

## Core and runtime changes

Core changes must update the independent typing/evaluation rules, executable
checker/evaluator, machine paths, safety/correspondence theorems, and retained
wire projections. Older encodings are closed; unsupported new constructors
must be rejected rather than silently coerced.

Contract changes belong in `Solcore.ContractRuntime` when they concern world
state, transaction/frame lifecycle, host effects, calls, creation, or
observations. State every commit/rollback and fuel boundary explicitly. ABI
admission and encoding remain separate checks under `Solcore.Abi`.

## Kernel policy

`scripts/check-kernel.mjs` scans the configured semantic roots for disallowed
escape hatches, including appearances in comments. It complements Lean's
kernel; it does not replace reviewing the actual axioms reported for critical
theorems.

## Documentation policy

- `README.md` contains purpose, build instructions, and public entry points.
- `CURRENT_STATUS.md` is the revision-local implementation ledger.
- `ARCHITECTURE.md` describes stable responsibilities and dependency rules.
- ADRs record durable decisions and rationale.
- plans record sequencing and exit conditions.
- matrices summarize feature and external-evidence coverage.

Prefer one authoritative explanation and link to it. Remove documentation for
code or interfaces that no longer exist rather than preserving instructions
that cannot be followed.
