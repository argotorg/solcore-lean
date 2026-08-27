# Solcore Lean specification charter

- Status: Draft
- Adopted: 2026-07-23
- Development policy amended: 2026-08-27

This charter defines what counts as Solcore specification work. Revision-local
progress belongs in [Current status](CURRENT_STATUS.md), not in this document.

## Purpose

solcore-lean is an independent executable formal specification. It exists to
state language rules precisely, execute those rules deterministically, and
support reproducible comparison with Solcore implementations.

Compiler output is not the definition of the language. Haskell and Rust
behavior can expose ambiguity or defects, but it does not override an Accepted
decision or a declarative Lean rule.

## Specification authority

The authority order is:

1. versioned declarative Lean definitions;
2. Accepted ADRs and designated manifests or schemas;
3. total executable definitions proved to correspond to the rules;
4. normative conformance tests;
5. explanatory documentation and implementation evidence.

Unproved executable behavior is not promoted to a normative semantic rule.

## Semantic layers

The specification separates:

1. Surface syntax, which preserves concrete source information.
2. Resolved input, which replaces source spellings with structured identity.
3. Semantic Core, which defines typed execution.
4. Contract runtime, which carries explicit external state.
5. Observation, which exposes canonical semantic effects.

Parser data, source spans, compiler IR, Hull, Yul, and EVM bytecode do not
define Semantic Core meaning.

## Published boundaries

| Protocol | Closed purpose | Input |
| --- | --- | --- |
| Oracle v2 | Historical Core checking and evaluation | Semantic Core v1 |
| Oracle v3 | Current Core checking and evaluation | Semantic Core v2 |
| Oracle v4 | Restricted single-file parsing | Surface v1 |

Publication is immutable and additive. A new internal Core constructor does
not change Semantic Core v1 or v2. A future public Core requires a new schema,
profile, capabilities document, Oracle boundary, resource contract, and golden
corpus.

## Development direction

ADR-0018 pauses new grammar-dependent proof work while concrete syntax is
unstable. Active implementation targets a syntax-independent Core vNext and
explicit runtime semantics.

This is an implementation-order decision. It does not deprecate or change any
published parser, Core language, profile, or result.

## Required semantic structure

A complete feature has:

- an Accepted decision fixing observable choices;
- an independent declarative typing rule where applicable;
- an independent declarative dynamic rule;
- a pure total checker and evaluator;
- checker soundness and completeness;
- evaluator or machine correspondence;
- determinism at the stated boundary;
- progress, preservation, or an explicitly justified replacement;
- an explicit resource model;
- positive, negative, order, boundary, and compatibility tests; and
- no accidental expansion of an older wire language.

One-way results must state the missing direction. Resource exhaustion cannot be
reported as source rejection.

## Verdicts and protocol errors

Language queries distinguish:

- accepted;
- rejected;
- unsupported;
- inconclusive;
- executed; and
- internal error.

Malformed JSON or an invalid protocol envelope is a protocol error, not a
language verdict. Runtime return, revert, and defined traps are observations,
not internal errors.

## Resources and divergence

Implementation limits are explicit inputs or published profile limits.
Reaching a limit yields an inconclusive result unless a language rule itself
defines another outcome.

Finite Core fragments may prove a sufficient fuel theorem. Features that add
recursion or other divergence must separately decide the declarative
divergence boundary before weakening that theorem.

## Contract observation

Future contract execution makes the initial state, transaction sequence, and
EVM revision explicit. Standard observations may include halt status,
returndata, storage and balance deltas, logs, external calls, and created
contracts.

Bytecode identity, optimizer traces, generated names, and wall-clock time are
not standard semantic observations. Gas requires its own fork-pinned profile.

## Trust and audit

The semantic kernel is checked by Lean and by repository policy. Audited roots
may not use the escape hatches rejected by scripts/check-kernel.mjs.

Lean still relies on its ordinary foundations. Critical theorem reports may
include propext, Quot.sound, or Classical.choice; the actual report is audited
rather than summarized as having no axioms.
