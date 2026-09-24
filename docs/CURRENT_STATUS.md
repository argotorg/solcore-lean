# Current status

This document is the revision-local implementation ledger. It describes what
the current Lean modules expose and which larger claims remain open. The
[architecture](ARCHITECTURE.md) owns stable layer responsibilities; the
[feature matrix](FEATURE_MATRIX.md) gives the compact view.

## At a glance

| Area | Current state | Public Lean import |
| --- | --- | --- |
| Canonical syntax | Executable lexer/parser, diagnostics and recovery, source-preserving AST, grammar and parser properties | `Solcore.Syntax` |
| Workspace and frontend | Explicit-root workspace checking, resolution, inference, trait evidence, staging, specialization, linking, and restricted backend selection | `Solcore.Frontend.Current` |
| Declarative source semantics | Independent static, staging, successful dynamic, fault, substitution, and preservation judgments for the modeled resolved language | `Solcore.SourceSemantics` |
| Semantic Core | Checked executable IR, local and host evaluation, machines, primitives, fuel/resumption, safety, and the Core Wire encoding | `Solcore.Core` |
| Checked-contract runtime | Explicit world, transaction and frame execution, nested calls, creation, checkpoints, commit/rollback, logs, and observations | `Solcore.ContractRuntime` |
| ABI | Keccak-256 and static-word ABI support | `Solcore.Abi` |
| Core synthesis | Seeded checked pure-Core generation and strict shrinking | `Solcore.Synthesis` |

All of these boundaries are library APIs. The repository does not publish a
command-line request/response service for them.

## Canonical syntax

`Solcore.Syntax` contains the current source representation and parser. The
implemented grammar covers complete files and their declarations, imports and
exports, types, expressions, patterns, statements, attributes, contracts, and
inline Yul forms represented by the AST. Tokens, comments, spans, source
spelling, lexical diagnostics, parse diagnostics, and recovery structure are
retained in the parse result.

The parser modules contain executable/declarative agreement results at both
component and public-file boundaries. The public parser returns an ordinary
result for every input; malformed input is represented by diagnostics and
recovery data rather than by treating syntax as type-correct.

A diagnostic-free result establishes syntactic admission only. Workspace
identity, import visibility, name resolution, source typing, and elaboration
remain later phases.

## Workspace and executable frontend

The current whole-program path starts from a raw workspace and an explicit
ground root. It provides:

- canonical library, module, and declaration identities;
- validated imports, exports, aliases, hiding, and public interfaces;
- separate type, trait, and value namespaces;
- source types, rigid parameters, inference variables, substitutions,
  unification, schemes, and rank-1 generalization;
- resolved signatures and implementation-method catalogs;
- bounded trait resolution with explicit success, failure, and inconclusive
  outcomes;
- body checking for the supported expression and statement forms;
- occurrence-addressed typed IR with retained evidence and coercions;
- stage analysis, specialization, source-to-Core elaboration, and linking; and
- selection among direct Core, finite call-graph, and typed-source execution.

The backends intentionally cover different fragments. A selected plan records
the backend and the failures that prevented earlier choices. The caller, not
the library, chooses the root; there is no automatic public-entry discovery or
multi-root execution policy.

The executable frontend has substantial focused proof coverage, including
lookup and renaming laws, local evaluation and cost properties, source/Core
linking results, and preservation results for supported paths. This does not
yet amount to one theorem that every accepted source program has the same
meaning under every backend.

## Declarative source semantics

`Solcore.SourceSemantics` states source rules independently of frontend
success. The static layer covers contexts, well-formedness, exact generic
instantiation, traits and evidence, coercions, ownership, calls, patterns,
places, expressions, statements, bodies, and whole programs.

Structural substitution is syntax directed and has correspondence and
preservation results. The staging layer classifies occurrences and programs
and defines materialization through an explicit representation relation.

The dynamic layer provides mathematical values, closures, runtime
dictionaries, locations, heaps, primitives, defaults, pattern selection,
places, and mutually recursive successful big-step relations. Positive fault
judgments describe modeled failures and their evaluation-order propagation.
Whole-language subject reduction covers successful executions under the
stated context-closure and typing premises, including heap-type extension and
result/control typing.

Not yet claimed here:

- progress for every well-typed source term;
- determinism of all dynamic judgments;
- termination of recursive evaluation;
- an exhaustive or unique classification of every fault; or
- a complete correspondence theorem from executable frontend acceptance to
  all declarative judgments.

## Semantic Core

`Solcore.Core` supplies the syntax-independent checked language used by the
executable backends and contract runtime. The current Core includes unit,
Boolean, Word, products, sums, functions, immutable bindings, conditionals,
local mutable cells, program-local algebraic data, normalized matching, and a
host-operation context.

The implementation includes:

- independent typing and evaluation judgments;
- total checking and fuel-bounded executable evaluation;
- detailed checking and runtime failures;
- local and host-aware machines and runners;
- exact-fuel and resumption theorems;
- renaming and local-fragment laws;
- arithmetic, division, remainder, exponentiation, shifts, byte selection,
  sign extension, bitwise logic, conversions, and comparisons; and
- correspondence, progress, and state/value safety results at their documented
  boundaries.

`Solcore.Core.Wire` is the current Core encoding. Its exact data rules are
cataloged in [CORE_WIRE.md](CORE_WIRE.md). Historical wire variants are not
retained as parallel APIs.

## Checked-contract execution

`Solcore.ContractRuntime` admits checked Core programs into an explicit world
and execution environment. It models:

- accounts, balances, nonces, installed code, and sparse storage;
- top-level transactions and frame-local working state;
- storage reads and writes, caller/value/input access, and ordered Word logs;
- non-wrapping atomic balance transfer;
- checked nested calls and checked contract creation;
- checkpoints, child and top-level commit/rollback, revert, and trap;
- fuel-bounded execution and resumption properties; and
- typed observations and world-state deltas.

Current nested execution is deliberately bounded by the implemented
one-level transition system. Contract execution is not an EVM interpreter:
there is no claim of Ethereum gas, fee, block-context, bytecode, or full EVM
equivalence.

## ABI

`Solcore.Abi.Keccak256` provides the hashing implementation and its supporting
tests. `Solcore.Abi.StaticWord` provides the modeled static `uint256`-style
word call boundary. A general dynamic ABI, arbitrary composite encoding,
memory model, and compiler-to-bytecode pipeline are outside the current API.

## Reproducible Core synthesis

`Solcore.Synthesis.Core` accepts an explicit 64-bit seed and program-node
bound. It generates checked programs in a pure Word/Boolean fragment and
returns the seed state needed for replay. The fragment includes literals,
Word locals, `let`, `if`, and the supported Word operations.

The shrinker preserves binder scope, rechecks candidates, and requires strict
decrease under its fixed measure. It does not currently generate functions,
algebraic data, cells, recursion, or host effects. Generation and shrinking
return Lean values directly; callers decide how to run or serialize them.

## External comparison status

The pinned Haskell and Rust revisions remain evidence sources, not normative
implementations. Canonical syntax behavior can be compared on aligned source
corpora. The current Lean frontend and runtimes make more internal semantic
experiments possible, but the repository has no automated end-to-end adapter
that aligns source, standard-library bytes, settings, initial world, resource
limits, and normalized observations across all implementations.

Accordingly, the repository does not claim general three-way source
conformance or equivalence between checked-contract execution and generated
EVM bytecode. See [Compatibility evidence](COMPATIBILITY_MATRIX.md).

## Main open boundaries

The following remain outside the current complete claim:

- unrestricted execution of arbitrary source programs;
- automatic entry discovery and multiple simultaneous roots;
- all nominal members, storage and ABI effects, symbolic coercions, and
  runtime evidence-dispatch combinations in the source backends;
- unbounded contract-call depth;
- a general dynamic ABI or EVM model;
- broader well-typed Core generation with functions, data, cells, and host
  effects; and
- automated semantic differential testing against independent compilers.

## Validation boundary

Run the full local checks from the repository root:

```text
lake build
lake test
node scripts/check-kernel.mjs
```

The build checks all imported declarations with warnings as errors. Tests
exercise executable examples and regression properties. The kernel-policy check
scans semantic roots for disallowed escape hatches.

These checks establish only the statements and behaviors present in this
revision. They do not fill an explicitly open proof boundary or establish
agreement with an external implementation.
