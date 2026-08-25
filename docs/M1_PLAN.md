# M1: Semantic Core plan and completion record

M1 defines a small typed Core language that can be checked and evaluated
without the source parser or backend. Its completion standard is deliberately
strong: declarative semantics, total executable procedures, correspondence
proofs, stable wire formats, and conformance tests must agree.

For the revision-local project summary, see [current status](CURRENT_STATUS.md).
For component boundaries, see [architecture](ARCHITECTURE.md).

## Status at a glance

| Stage | Scope | Implementation | Proof | Publication |
| --- | --- | --- | --- | --- |
| M1a | unit/bool/word literals, de Bruijn variables, immutable `let`, conditionals, CEK machine | complete | complete | internal foundation for later releases |
| M1b | five independently named Core features plus Core v1 wire | complete | complete | draft.2, `core-m1a-v1`, Oracle v2 |
| M1c | bool-not and the specified word primitive subset plus Core v2 wire | complete | complete | draft.3, `core-m1c-v1`, Oracle v3 |
| Remaining aggregate M1 language | functions, mutation, products, sums, ADTs, matches, closures, and deferred primitives | not implemented | not started | not published |

The current public Core boundary is M1c. “M1c complete” does not mean every
feature originally considered for M1 has been implemented.

## Completed semantic kernel

The closed M1c fragment contains:

- unit, bool, and range-checked 256-bit word literals and values;
- de Bruijn variables and initialized immutable bindings;
- condition-first, selected-branch-only conditionals;
- `boolNot` and `wordNot`;
- modular `wordAdd`, `wordSub`, and `wordMul`;
- total unsigned `wordDiv` and `wordMod`, returning zero on a zero divisor;
- `wordEq` and unsigned `wordGt`; and
- `wordAnd`, `wordOr`, `wordXor`, `wordShl`, and `wordShr`, with shifts at
  least 256 returning zero.

Unary operands are evaluated once. Binary operands are evaluated exactly once,
left to right, before primitive application. Operation results are bounded
words; wire literals are range-checked rather than silently reduced.
`wordNe`, `wordLt`, `wordLe`, and `wordGe` are derived Core forms, not new wire
primitive tags.

The kernel establishes:

- soundness and completeness of executable inference against declarative
  typing, plus typing uniqueness;
- agreement of detailed checking, inference, and declarative typing;
- totality and result-type preservation of primitive application;
- determinism of declarative evaluation and machine transitions;
- correspondence between CEK transitions and executable `advance`;
- soundness and completeness of the fuelled runner;
- bidirectional correspondence between big-step evaluation and the CEK
  machine;
- value, environment, and state typing;
- progress and preservation; and
- sufficient-fuel termination and fault unreachability for well-typed closed
  programs.

## Published boundaries and compatibility

| Boundary | Fixed contract | Status |
| --- | --- | --- |
| Semantic Core v1 | strict decoder, canonical encoder, fixed-width lowercase word hex, stable type-error codes and AST paths | frozen with Oracle v2 |
| Oracle v2 | `capabilities`, `coreCheck`, and `coreEval` under draft.2 and `core-m1a-v1` | frozen |
| Semantic Core v2 | separate closed AST and codec adding unary and binary expression tags | current Core wire |
| Oracle v3 | `capabilities`, `coreCheck`, and `coreEval` under draft.3 and `core-m1c-v1` | current public Core Oracle |
| Capabilities v3 | exact profile digest, schema IDs, enabled features, limits, and observation schemas | current public Core capabilities |

Core depth/node limits and CEK fuel produce independent `inconclusive`
outcomes. Positive, rejection, malformed-wire, cross-version, exact-fuel,
mixed-stream, round-trip, and canonicalization cases cover the published
boundary.

Publication is additive. Draft.1 and draft.2 profiles, Core v1, Oracle v1 and
v2, their schemas, capability documents, digests, and golden bytes remain
immutable. Oracle v2 rejects Core v2 and Oracle v3 rejects Core v1 rather than
guessing a wire version from expression shape.

## Boundary to M2

Source text does not enter M1 directly. M2 is responsible for parsing,
workspace validation, name resolution, source checking, and elaboration into a
published Core version.

The repository now has two parser layers beyond M1:

- the published M2b single-file parser in Oracle v4; and
- an internal M2c workspace identity kernel and source-preserving Multi
  lexer/parser with an unconditional file-only entry point.

Neither layer currently resolves modules or names, checks source types, or
elaborates source into Core. Therefore Oracle v3 remains a reference for closed
Core fixtures, not an end-to-end source conformance oracle.

## What remains outside M1c

| Family | Current status | Required decision or work |
| --- | --- | --- |
| functions, application, and return | planned | argument order, recursion, control transfer, closure environment |
| lexical closures | planned | capture identity, recursion, divergence boundary |
| mutable locals and assignment | planned | cell identity and assignment evaluation order |
| products and sums | planned | value and wire algebra |
| user ADTs and pattern matching | planned | constructor identity/order, selection order, exhaustiveness, match failure |
| short-circuit boolean conjunction/disjunction | outside M1c | source typing and selected-branch elaboration into Core |
| conversions and additional primitives | outside M1c | source rules, feature split, wire and proof impact |
| divergence | undecided | relation to the explicit-fuel evaluator |

Modules, import/export resolution, type inference, polymorphism, type-class
resolution, and staging belong to M2. ABI, storage, contract hosting, and EVM
execution belong to M3.

## Implementation order for future M1 extensions

The first six steps are complete for the published fragment:

1. Core types, expressions, values, environments, and control results.
2. Well-formedness and declarative typing.
3. CEK transition relation and multi-step closure.
4. Total explicit-fuel evaluator.
5. Mapping to `rejected`, `inconclusive`, and `executed`.
6. Versioned Core codecs, capability reports, and Oracle queries through Core
   v2 / Oracle v3.

Future work proceeds feature by feature:

7. Accept the semantic ADR for the feature and its evaluation order.
8. Extend declarative syntax, typing, evaluation, and machine state.
9. Extend the executable checker and evaluator without weakening old versions.
10. Re-establish determinism, correspondence, progress, preservation, and a
    sufficient-fuel theorem.
11. Publish a new feature/profile/wire boundary only when the schema, limits,
    capabilities, and golden corpus are closed.

Pinned Haskell and Rust behavior remains comparison evidence, not authority.
Minimal source witnesses are retained for later elaboration tests; discrepancies
are summarized in the [compatibility matrix](COMPATIBILITY_MATRIX.md).

## Completion criteria for each feature

A feature is `normative` / `implemented` only when all applicable items hold:

- an Accepted ADR fixes every observable semantic choice;
- declarative typing and evaluation rules exist;
- pure total checker and evaluator procedures exist;
- checker soundness and completeness are proved;
- evaluator/machine correspondence and determinism are proved;
- progress and preservation cover the target fragment;
- sufficient fuel is proved, or the exact missing direction is documented;
- resource exhaustion cannot be misclassified as source rejection;
- positive, negative, boundary, and canonical wire cases exist;
- old language/profile/wire versions retain their previous meaning; and
- the semantic kernel passes the repository policy and public-theorem axiom
  audit.

An aggregate feature such as `corePrimitives` remains `partialSupport` while
only an allowlisted subset is complete. Splitting or promoting it requires an
ADR and a coordinated update to feature metadata, language/profile versions,
schemas, capabilities, and documentation.
