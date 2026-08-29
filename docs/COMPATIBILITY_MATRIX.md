# Haskell and Rust compatibility evidence

This document records comparison evidence. It is not the language
specification, and agreement between compilers is not sufficient to establish a
Solcore rule.

## Pinned evidence baseline

| Target | Revision or digest |
| --- | --- |
| Haskell argotorg/solcore | 1d490d8bb5f374356f06e0720655496482eb1fb4 |
| Rust argotorg/solcore-rs | 38f4778ea461edfe59106bdb1f9f08c3307b0fc0 |
| Canonical upstream standard library | 3f81bebfd1fc161ee08972be9e7a52150d02bdf55dd7449dfa058cd81cfafc22 |
| Rust standard-library Git tree | c58489d2d544b314b7fa843b331062f6f5129655 |
| Rust compatibility snapshot | c23c43897bb3f9e8d55abc5369dc9bb1ae984e9da1ef9457440aee642923f430 |

Results from other revisions, different standard bytes, different solver
settings, or different EVM revisions do not belong to this baseline.

## What can be compared now

| Lean boundary | Adapter state | Valid claim |
| --- | --- | --- |
| Semantic Core v2 / Oracle v3 | Neither compiler consumes the Core wire | Lean supplies closed semantic fixtures, not source-level three-way conformance |
| Surface v1 / Oracle v4 | Parser fixtures can share source text | Restricted parser outcomes can be compared |
| Workspace identity | Internal Lean values | Logical identity behavior is specified but has no external adapter |
| Frozen Multi frontend | Internal certified one-file API | Frozen lexical, parse, structural, location, and token behavior can be investigated |
| Resolution and elaboration | No Lean implementation | No source semantic comparison exists |
| Contract runtime | Internal storage/frame carriers and address-selected handled storage reads and writes; no compiler adapter | Lean can test its internal working-state semantics, but no end-to-end compiler conformance claim exists |

The internal runtime row includes typed Core requests, a generic fuel-preserving
host driver, and a combined handler for one separately selected working-storage
Account. It is complete at that Lean boundary and remains unpublished. The
frozen Core Wire v1/v2 formats reject the internal host-function values, and no
Oracle or compiler adapter exposes the driver. A handled write updates the
returned working context, including when later execution runs out of fuel; this
is not a transaction commit or rollback rule.

## Evidence rules

Use these labels:

- conformant: agrees with a normative result under the same profile;
- divergent: differs from that result;
- mode-dependent: changes with a solver or compiler mode;
- phase-dependent: changes with the phase reached;
- partial: implements only part of a required path;
- unsupported: the selected boundary defines no behavior;
- unverified: the aligned baseline has not been rerun.

Historical source inspection remains unverified until the exact pinned
revisions are run with aligned inputs and settings.

## Semantic decisions motivated by existing implementations

The following decisions were informed by implementation discrepancies but are
owned by the Lean specification:

| Topic | Solcore specification direction |
| --- | --- |
| Binding initializer scope | Evaluate before introducing the new binding |
| Primitive operand order | Evaluate left to right, exactly once |
| Conditional evaluation | Evaluate only the selected branch |
| Word arithmetic | Use bounded 256-bit modular results |
| Word division and modulo by zero | Return zero |
| Callability | Require a function type or explicit invokable evidence |
| Contract main arity | Require zero parameters |
| ABI admissibility | Require metadata, signature, decode, and encode together |
| Selector collision | Reject before dispatch generation |
| Resource exhaustion | Report inconclusive, not rejected |

These rules must be tested through the relevant Lean boundary before a compiler
is classified.

## Current limitations

The Haskell and Rust compilers do not consume Semantic Core v1 or v2, so Core
results cannot yet establish end-to-end source conformance. Oracle v4 stops at
parsing. The internal Multi frontend now includes structural certification,
but it still performs no name resolution, source typing, or elaboration.

Consequently there is currently no valid three-way claim about:

- source type acceptance;
- polymorphism or class resolution;
- comptime staging;
- source-to-Core meaning;
- contract dispatch;
- ABI behavior;
- source-level storage, transaction commit, or rollback; or
- EVM execution observations.

## Semantics-first comparison plan

During Core vNext development, tests should isolate semantic choices as closed
Core fixtures. Compiler comparisons resume at source level only after a
stabilized Surface adapter elaborates those fixtures into the same Core
meaning.

For contract execution, every comparison must align:

- language and feature profile;
- exact source and standard-library bytes;
- initial state and transaction sequence;
- EVM revision;
- resource limits; and
- observation schema.

Bytecode equality, generated names, optimization traces, and wall-clock time
are not semantic conformance criteria.
