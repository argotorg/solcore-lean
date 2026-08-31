# Haskell and Rust compatibility evidence

This document records comparison evidence. It is not the language
specification, and agreement between compilers is not sufficient to establish a
Solcore rule.

## Pinned evidence baseline

| Target | Revision or digest |
| --- | --- |
| Haskell argotorg/solcore | 1d490d8bb5f374356f06e0720655496482eb1fb4 |
| Rust legacy compatibility baseline | 38f4778ea461edfe59106bdb1f9f08c3307b0fc0 |
| Rust canonical-syntax source (PR #20) | 18fd9f75d290df0070e21ee56e0a5691f232596f |
| Canonical upstream standard library | 3f81bebfd1fc161ee08972be9e7a52150d02bdf55dd7449dfa058cd81cfafc22 |
| Rust standard-library Git tree | c58489d2d544b314b7fa843b331062f6f5129655 |
| Rust compatibility snapshot | c23c43897bb3f9e8d55abc5369dc9bb1ae984e9da1ef9457440aee642923f430 |

Results from other revisions, different standard bytes, different solver
settings, or different EVM revisions do not belong to this baseline.

## What can be compared now

| Lean boundary | Adapter state | Valid claim |
| --- | --- | --- |
| Semantic Core v2 / Oracle v3 | Neither compiler consumes the Core wire | Lean supplies closed semantic fixtures, not source-level three-way conformance |
| Semantic Core v3 / Oracle v5 `coreCheck` | Neither compiler consumes Core Wire v3 | Lean can check closed current-Core fixtures; no cross-compiler acceptance claim follows |
| Surface v1 / Oracle v4 | Parser fixtures can share source text | Restricted parser outcomes can be compared |
| Canonical Syntax | Complete executable Lean lexer/parser against pinned PR #20; 23 embedded fixtures and an external 490-file fixed-revision corpus audit | Lexical and parsed-syntax behavior can be compared; source semantic conformance cannot yet be claimed |
| Workspace identity | Internal Lean values | Logical identity behavior is specified but has no external adapter |
| Frozen Multi frontend | Internal certified one-file API | Frozen lexical, parse, structural, location, and token behavior can be investigated |
| Resolution and elaboration | No Lean implementation | No source semantic comparison exists |
| Checked-contract runtime / Oracle v5 `execute` | Public Core/scenario, normalized observation, and reproducible pure-Core fixture generation; no external compiler adapter | Lean execution is reproducible, but no end-to-end or cross-compiler conformance claim exists |

Oracle v5 publishes the checked-contract model: a finite package, initial
world, call and creation environment, invocation, limits, probes, and total
result. It makes Lean runs reproducible and gives future adapters a comparison
target. The Haskell and Rust compilers do not currently consume Core Wire v3 or
emit the v5 observation format, so publication alone establishes no agreement
with either compiler.

The Lean synthesis library can generate and shrink a checked pure Core subset
into canonical v5 requests. That removes manual fixture construction from the
Lean side, but replaying those requests twice through the same Lean semantics
is not differential evidence.

The v5 runtime defines its own checked Core, depth-one calls, balances,
creation, logs, commit, and rollback behavior. It does not assert that those
rules are equivalent to compiler-generated EVM bytecode or to any EVM revision.

The external fixed-revision syntax audit found no acceptance or source-AST gap
across the 490 accepted files. Four malformed inputs differed only in
diagnostic cardinality. This is parser comparison evidence, not resolution,
typing, elaboration, or execution evidence.

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

The Haskell and Rust compilers do not consume Semantic Core v1, v2, or v3, so
Core results cannot establish end-to-end source conformance. The canonical
Lean lexer and parser implement the pinned Rust syntax, but Lean does not yet
resolve, source-check, or elaborate those parsed programs into Core. Oracle v4
remains a historical parser, while Oracle v5 starts from already structured
Core and a scenario.

Consequently there is currently no valid three-way claim about:

- source type acceptance;
- polymorphism or class resolution;
- comptime staging;
- source-to-Core meaning;
- cross-compiler contract dispatch or ABI behavior;
- cross-compiler source-level storage, transaction commit, or rollback; or
- EVM execution observations.

## Canonical frontend comparison plan

Core v3 fixtures can isolate semantic choices at the checked Core boundary.
Source-level compiler comparison requires the canonical frontend to parse,
resolve, type, and elaborate programs into the same Core meaning, followed by
an adapter from each external implementation to normalized results.

For contract execution, every comparison must align:

- language and feature profile;
- exact source and standard-library bytes;
- initial state and transaction sequence;
- execution model and, for EVM comparisons, EVM revision;
- resource limits; and
- observation schema.

Bytecode equality, generated names, optimization traces, and wall-clock time
are not semantic conformance criteria.
