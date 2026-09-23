# Solcore Lean specification charter

## Purpose

`solcore-lean` is an executable, kernel-checked specification of Solcore. It
aims to make syntax, static semantics, execution, resource behavior, and
contract-state effects precise enough to inspect, test, and prove.

The project is independent of any production compiler. Existing Haskell and
Rust implementations supply evidence and comparison cases; neither is the
definition of the language.

## Specification authority

Authority is ordered as follows:

1. Lean definitions and theorem statements in the retained public modules;
2. accepted ADRs that constrain choices not yet fully encoded;
3. executable tests and pinned comparison evidence; and
4. explanatory documentation.

When these disagree, fix the lower-authority artifact or make an explicit ADR
and code change. Do not silently change a judgment to imitate one compiler.

## Semantic layers

The specification keeps the following responsibilities distinct:

1. `Solcore.Syntax`: canonical tokens, diagnostics, recovery, and source AST;
2. `Solcore.Workspace`: library/module identity and workspace validity;
3. `Solcore.Resolved`, `Solcore.TypeSystem`, and `Solcore.Frontend`: executable
   resolution, inference, staging, specialization, linking, and compilation;
4. `Solcore.SourceSemantics`: independent resolved-source judgments;
5. `Solcore.Core`: syntax-independent checked executable semantics;
6. `Solcore.ContractRuntime`: accounts, frames, transactions, calls,
   creation, commit/rollback, and observations;
7. `Solcore.Abi`: explicitly supported hashing and data encoding; and
8. `Solcore.Synthesis`: reproducible checked Core input generation.

An adapter between layers must be explicit. Success in one layer is not
silently treated as proof of a different layer's judgment.

## Public boundaries

The public interfaces are Lean imports:

- `Solcore` for the complete library;
- `Solcore.Syntax` for canonical parsing;
- `Solcore.Frontend.Current` for the current whole-program pipeline;
- `Solcore.SourceSemantics` for declarative source rules;
- `Solcore.Core` for Core checking and execution;
- `Solcore.ContractRuntime` for checked-contract execution;
- `Solcore.Abi` for the retained ABI utilities; and
- `Solcore.Synthesis` for checked Core generation and shrinking.

Core Wire v1, v2, and v3 are retained closed data encodings. A new internal
Core form does not enter an older encoding without a separately reviewed
version decision.

## Required semantic structure

For each executable feature, the specification should distinguish as
applicable:

- syntax or data representation;
- well-formedness and static admission;
- declarative dynamic meaning;
- executable implementation;
- diagnostics and failure priority;
- resource accounting and resumption;
- correspondence between executable and declarative forms; and
- preservation of values, environments, heaps, frames, and world state.

Missing proof directions must be recorded as partial. Tests do not substitute
for a general theorem, and a theorem over successful derivations does not
imply progress or termination.

## Outcomes and failures

Language and runtime results use typed outcomes owned by their layer. The
specification distinguishes at least:

- static rejection from dynamic failure;
- normal source control from source faults;
- Core checking failure from Core evaluation exhaustion;
- contract preflight failure from return, revert, trap, and incomplete
  execution; and
- unsupported input from an internal invariant violation.

Failure categories must not be collapsed merely to simplify an adapter.
Deterministic error priority is part of an executable boundary when tests or
proofs rely on it.

## Resources and divergence

Fuel and bounded search make executable functions total. Exhausting such a
bound means the computation is inconclusive under that bound; it is not a
proof of semantic rejection.

The specification must state separately whether a result concerns:

- a mathematical relation without fuel;
- a fuel-bounded evaluator;
- a resumable machine state; or
- a bounded frontend search such as trait resolution or specialization.

Exact-fuel and resumption theorems should prevent already completed effects
from being replayed.

## Contract observation

Checked-contract behavior is defined from explicit inputs: admitted Core code,
initial world state, execution environment, invocation, and resource bound.
Observable results are typed Lean values describing the modeled outcome,
journal, logs, created addresses, and selected state changes.

Commit and rollback are semantic operations. A top-level return commits the
working state; the modeled failing outcomes select the appropriate checkpoint.
Child failures must resolve their local state before returning control to a
parent.

This model does not imply equivalence with EVM gas, bytecode, fees, block
context, or every Ethereum fork.

## External evidence

Cross-implementation comparisons are valid only when source and standard
library bytes, profiles, initial state, resource limits, and observed results
are aligned. Native defaults are evidence, not implicit specification choices.

Use the classifications in
[Compatibility evidence](COMPATIBILITY_MATRIX.md). Do not claim conformance
from source acceptance alone or from replaying two paths through the same Lean
semantics.

## Trust and audit

Lean's kernel is the proof checker. The repository additionally:

- builds with warnings as errors;
- runs executable regression and property tests;
- validates owned data, digests, and references; and
- scans configured semantic roots for prohibited escape hatches.

Critical theorem reviews should inspect their actual axiom reports. Project
documentation must distinguish kernel-checked statements, executable tests,
and unverified design intent.
