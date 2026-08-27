# Current status

This page is the revision-local answer to what works now. It distinguishes the
stable published system, internal completed work, paused work, and the active
semantics program.

## Summary

Two external interfaces are stable:

- Oracle v3 checks and evaluates the closed Semantic Core v2 language.
- Oracle v4 parses the closed Surface v1 single-file language.

The larger internal Multi frontend can lex, parse, structurally validate, and
certify one file for its current grammar. That work is not published and is
now frozen because the concrete Solcore syntax may change.

Active development has moved to Semantic Core vNext. The goal is to define
types, evaluation, state, and observations independently of concrete source
spelling, then connect a stabilized future Surface language through a separate
adapter.

## Stable implementation

| Area | Implementation | Proof | Publication |
| --- | --- | --- | --- |
| Versioning, profiles, verdicts | Complete | Applicable invariants checked | Oracle v1 and later |
| Small Semantic Core machine | Complete | Complete for the closed fragment | Oracle v2 and v3 |
| Semantic Core primitive subset | Complete | Complete | Oracle v3 / Core v2 |
| Internal Core binary products | Complete | Complete | Not published |
| Internal non-recursive functions | Complete | Complete, including totality | Not published |
| Restricted single-file parser | Complete | Complete | Oracle v4 / Surface v1 |
| Workspace identity and validation | Complete | Complete | Internal only |
| Multi lexer and chart parser | Complete for the frozen grammar | Soundness, total selection, and grammar-specific certificates | Internal only |
| Structural validation | Complete for the frozen AST | Executable/declarative equivalence and resource bound | Internal only |
| Source locations and retained tokens | Complete for the frozen AST and grammar | Parser-wide correspondence | Internal only |
| Certified one-file Multi frontend | Complete for the frozen grammar | Lexical, parse, structural, location, and token evidence | Internal only |

The committed parser baseline through commit 0209a37 passed the full test,
warning, metadata, kernel-policy, and axiom audits used during development.

## What the published Semantic Core contains

The current public Core is deliberately small:

- unit, boolean, and bounded 256-bit word values;
- de Bruijn variables and initialized immutable bindings;
- condition-first, selected-branch-only conditionals;
- boolean and word negation;
- modular word arithmetic;
- unsigned division and modulo with a zero result for a zero divisor;
- word equality and unsigned greater-than;
- bitwise operations and bounded logical shifts; and
- left-to-right, exactly-once operand evaluation.

For this fragment, executable checking and evaluation are connected to
declarative typing and big-step evaluation. The repository proves typing
uniqueness, machine determinism, checker soundness and completeness, CEK and
big-step correspondence, progress, preservation, sufficient fuel, and fault
unreachability for well-typed closed programs.

## Missing semantics

The public Core fragment is complete, but it is not the complete Solcore
language. The following remain:

- sum values;
- explicit return, recursion, and divergence;
- mutable locals and assignment;
- user-defined algebraic data and direct pattern matching;
- conversions and additional primitives;
- resolved-name and typed intermediate representations;
- polymorphism, class evidence, and staging;
- contract entry and call semantics;
- explicit state, storage, rollback, balances, logs, and creation;
- ABI admissibility, encoding, decoding, and dispatch; and
- versioned contract observations and EVM-revision policy.

Several later items require an Accepted semantic decision before code.

## Frozen frontend work

The published Surface v1 and Oracle v4 remain supported. The internal Multi
frontend remains usable as a reference for its fixed grammar. New work on the
following is paused:

- fast-parser completion and chart equivalence;
- grammar-specific token and location proof maintenance;
- structural syntax identity;
- module and lexical resolution over the current AST;
- source checking and Surface-to-Core elaboration; and
- publication of the Multi frontend.

## Completed Core vNext results

The first Core vNext vertical slice adds:

- a binary product type;
- pair construction;
- first and second projection;
- left-to-right pair evaluation;
- executable inference and detailed checking;
- CEK execution and big-step semantics; and
- soundness, completeness, correspondence, and safety results; and
- regression tests for nesting, exact fuel, evaluation order, invalid
  projection, and old-wire rejection.

This internal extension will not reinterpret Semantic Core v1 or v2. Frozen
wire projections reject product types, values, expressions, and programs.

See the [Semantic Core roadmap](M1_PLAN.md) and
[ADR-0019](adr/0019-core-vnext-products.md).

The second vertical slice adds:

- explicitly typed unary functions;
- callee-before-argument application;
- immutable lexical closures;
- de Bruijn parameters and captured bindings;
- detailed function-checking diagnostics;
- CEK execution and big-step correspondence; and
- a logical-relations proof retaining total evaluation and sufficient fuel for
  non-recursive, well-typed programs.

Frozen wire projections reject function types, lambdas, applications,
closures, and programs containing them. See
[ADR-0020](adr/0020-core-vnext-non-recursive-functions.md).

The next active step is sum values and elimination. User algebraic data and
source-level pattern syntax remain later decisions.

## Meaning of completion

A Core feature is complete only when its declarative rules, total executable
checker and evaluator, correspondence proofs, safety coverage, negative and
boundary tests, and version-isolation behavior agree. Publication is a later,
separate decision.
