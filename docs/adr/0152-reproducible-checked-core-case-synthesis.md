# ADR-0152: Reproducible Checked-Core Program Synthesis

- Status: Accepted
- Decision date: 2026-08-30
- Scope: syntax-independent generation and shrinking through a direct Lean API
- Implementation: Complete

## Context

Semantic Core Wire v3 is a closed, versioned target with an executable checker
and a soundness theorem. It is therefore suitable for reproducible generation
of well-typed programs independently of source parsing and lowering.

Generating arbitrary raw trees and discarding checker failures would reject
most binder-rich trees, bias coverage toward simple constructors, and make
shrinking routinely destroy typing. A fully dependent generator for all of
Core would, however, make the first useful executable slice unnecessarily
large.

## Decision

`Solcore.Synthesis.CoreV3` provides a pure Lean library for reproducible Core
v3 program generation and deterministic, checker-sealed shrinking. The first
versioned fragment is G0 and consists of:

1. a fixed pure pseudo-random source;
2. a bounded type-directed Word/Boolean expression generator;
3. a checker-sealed generated Word Program;
4. a deterministic type-preserving shrinker; and
5. structural feature classification for coverage tests.

The library returns Core programs directly. Execution scenarios, text
protocols, process dispatch, and serialized replay records are outside this
decision.

## Public Lean boundary

A caller constructs a `GenerationRequest` from a `Seed` and a maximum Program
node count, then calls `generate`. Success returns a `GeneratedProgram` with:

- the initial and final seed states;
- the requested node bound;
- a constructor-private `CheckedWordProgram`; and
- projections for the generated `V3.Program`, its node count, and its features.

`CheckedWordProgram.ofProgram?` is the sole admission path for an externally
supplied candidate. It requires the v3 checker to accept the Program, the
result type to be Word, the named-data-definition list to be empty, and the
body to belong to G0. Its `wellTyped` theorem projects checker acceptance into
the declarative v3 contract.

The public `shrink` function accepts a `CheckedWordProgram` and returns a list
of `ShrinkCandidate`s. Each candidate records its rechecked Program and exact
source and candidate complexity.

## Reproducible choices

G0 uses a versioned 64-bit linear-congruential sequence. Its multiplier,
increment, wrapping arithmetic, draw order, and bounded-choice behavior are
fixed in code. `Seed.algorithmId` identifies the choice algorithm, and
`generatorVersion` combines it with the G0 generation policy.

The same generator version, initial seed, and node bound produce the same:

- final seed state;
- Core Wire v3 Program;
- node count; and
- structural feature sequence.

The minimum Program-node bound is three: one result-type node, one Program
wrapper node, and at least one body node. A smaller bound returns
`GenerationError.budgetTooSmall` rather than silently widening the request.

## Initial typed fragment

Every G0 Program has:

- result type `word`;
- no named data definitions;
- a body generated without host-function references; and
- no effects or recursion.

The internal targets are Word and Boolean. The fragment contains:

- Word and Boolean literals;
- in-scope Word variables introduced by generated Word `let` bindings;
- Word `let` and Word/Boolean `if` expressions;
- `boolNot`, `wordNot`, and `wordClz`;
- the supported Word binary operations, including Boolean-producing equality
  and signed and unsigned comparisons; and
- `wordAddMod` and `wordMulMod`.

The body receives the Program bound minus the two fixed wrapper nodes. Child
budgets partition the parent's remaining budget, and structural recursion uses
an independently decreasing fuel. The realized Program therefore contains no
more nodes than requested.

## Checker sealing

Generation constructs a type-directed candidate, invokes the existing v3
checker, and admits the result through `CheckedWordProgram.ofProgram?`. Checker
rejection is `GenerationError.checkerInvariant`, because rejection indicates a
bug in the generator rather than an ordinary sampling outcome.

The private constructors of `CheckedWordProgram`, `GeneratedProgram`, and
`ShrinkCandidate` prevent callers from forging checker evidence, generation
provenance, or shrink-measure claims.

## Shrinking

Shrinking operates on typed expression roles rather than raw encodings. It may:

- replace a noncanonical literal with canonical zero or false;
- select an in-scope same-type child when binding scope permits; or
- shrink one child while rebuilding its typed parent.

Every result is admitted again through the same checker-sealed boundary and
must be strictly smaller under the fixed G0 lexicographic complexity order.
The primary component is expression-node count; the secondary component is
the sum of Word literal values plus one for each true Boolean literal.
Candidate order is deterministic, and duplicate candidate bodies are removed
without changing their first-occurrence order.

## Coverage and validation

Coverage is structural. `Feature.catalog` lists every G0 expression form and
included operator, while `GeneratedProgram.features` classifies the generated
AST directly. A fixed seed corpus should cover the complete catalog rather
than rely on an unspecified distribution.

The implementation is validated by tests for:

- exact pseudo-random vectors and bounded-choice behavior;
- same-input generation determinism;
- rejection below the minimum bound and conformance to the Program-node bound;
- checker acceptance and G0 membership of every generated Program;
- the absence of unchecked public constructors or fallback Programs;
- deterministic, distinct, checker-accepted, strictly smaller shrink results;
- binder-safe shrinking without variable capture; and
- complete constructor and operator coverage for the G0 corpus.

The aggregate build, tests, metadata checks, semantic-kernel checks, and axiom
checks remain required.

## Exclusions and next boundary

G0 does not generate functions, products, sums, cells, named data, host
effects, calls, creation, logs, malformed Programs, or execution scenarios.
Later generator versions may add typed fragments while preserving the replay
meaning of existing version identifiers.

This generator is not an independent semantics implementation. Differential
testing requires a separately implemented consumer of the generated Core
programs and is outside this decision.
