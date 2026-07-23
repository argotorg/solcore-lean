# M1: Semantic Core implementation plan

The objective of M1 is to implement the smallest Semantic Core that can be
evaluated without passing through the Solcore source parser or backend, together
with all three of a declarative specification, an executable evaluator, and
correspondence proofs.
Even when an M0 feature is `directionAccepted`, it is not promoted to
`normative` or `implemented` until it satisfies the completion criteria below.

## Current progress: M1c publication

### M1a semantic kernel

Following ADR-0009, the project implements the closed fragment consisting of
unit/bool/word literals, de Bruijn variables, initialized immutable `let`, and
conditionals. The semantic kernel establishes:

- soundness and completeness of the executable inferencer with respect to
  declarative typing
- typing uniqueness
- determinism of declarative big-step evaluation
- correspondence between CEK transitions and executable `advance`, and their
  determinism
- soundness and completeness of the fuelled runner
- bidirectional correspondence between big-step evaluation and the CEK machine
- value, environment, and state typing
- progress and preservation of CEK transitions
- finite-fuel termination and fault unreachability for well-typed closed
  programs

### M1b publication

Following ADR-0010, the completed fragment is divided into `coreUnit`,
`coreBool`, `coreWord`, `coreImmutableLet`, and `coreConditional`, then
published as normative and implemented in the `core-m1a-v1` profile of
`solcore/0.1.0-draft.2`. M1b additionally implements:

- a strict decoder and canonical encoder for `solcore-semantic-core/v1`
- a fixed-width lowercase hexadecimal wire representation for words
- stable type-error codes, AST paths, and structured arguments
- the `solcore-oracle/v2` `capabilities`, `coreCheck`, and `coreEval` queries
- independent `inconclusive` outcomes for Core depth/node limits and CEK
  evaluation fuel
- mixed v1/v2 streams, canonical output, and a negative wire corpus

### M1c primitive semantics and publication

Following
[ADR-0011](adr/0011-m1c-primitive-semantics-and-publication.md), M1c adds the
following exact primitive set:

- unary boolean negation `boolNot : bool -> bool` and
  `wordNot : word -> word`, which complements all 256 bits
- modular `wordAdd`, `wordSub`, and `wordMul`
- unsigned `wordDiv` and `wordMod`, each returning zero for a zero divisor
- `wordEq : word × word -> bool` and unsigned
  `wordGt : word × word -> bool`
- fixed-width `wordAnd`, `wordOr`, and `wordXor`
- logical `wordShl` and `wordShr`, with the value on the left, shift amount on
  the right, and a zero result for shift amounts greater than or equal to 256

Unary operands are evaluated exactly once. Binary operands are evaluated
exactly once from left to right before primitive application. Operation results
are bounded words; wire literals remain range-checked rather than implicitly
reduced modulo `2^256`. `wordNe`, `wordLt`, `wordLe`, and `wordGe` are Core
derived forms rather than additional primitive tags.

The existing kernel proofs now cover unary and binary primitive expressions:

- executable inference remains sound and complete for declarative typing, with
  typing uniqueness
- detailed checking agrees with both inference and declarative typing
- primitive application is total and result-type preserving when operands have
  the declared types
- declarative evaluation and machine transitions remain deterministic
- big-step evaluation and the CEK machine correspond in both directions
- evaluation preserves types, and CEK transitions satisfy progress and
  preservation
- well-typed closed programs have sufficient fuel, terminate, and cannot reach
  structured machine faults

M1c publishes these semantics as `solcore/0.1.0-draft.3` and profile
[`core-m1c-v1`](../profiles/solcore-0.1.0-draft.3-core-m1c.json). The new
profile enables the five M1b features plus
`coreBoolNot`, `coreWordArithmetic`, `coreWordComparison`, and
`coreWordBitwise`. Static and dynamic semantics versions are both 2. The
publication adds:

- a separate closed
  [`solcore-semantic-core/v2`](../schema/semantic-core-v2.schema.json) AST and
  strict canonical codec with unary and binary expression tags
- bounded decoder/encoder round-trip and canonicalization theorems for Core v2
- [`solcore-oracle/v3`](../schema/oracle-v3.schema.json) `capabilities`,
  `coreCheck`, and `coreEval`
- `solcore-capabilities/v3`, bound to Core v2 and the canonical M1c profile
  digest
- v3 positive, rejection, malformed-wire, cross-version, exact-fuel, and mixed
  stream coverage

The aggregate `corePrimitives` feature remains `partialSupport`: short-circuit
boolean operators, conversions, and other unlisted primitive families remain
outside M1c. Functions, mutation, ADTs, and the remaining aggregate language
features are still planned. All draft.1 and draft.2 profiles, digests, schemas,
capability documents, and golden bytes remain immutable.

## Input boundary

M0 `solcore-oracle/v1` defines a typed result only for `capabilities`. Kinds from
`parse` through `contract` are reserved for capability negotiation and always
return `unsupported` in M0. An undecided Core AST must not be smuggled through
an arbitrary field such as `scenario : Json`.

M1b added all of the following together:

1. the versioned `solcore-semantic-core/v1` JSON Schema
2. a strict decoder and canonical encoder for Core ASTs and values
3. Oracle v2 queries that directly evaluate Core input, typed observations, and
   the detailed phases required by Core
4. round-trip and golden tests between Core JSON fixtures and Lean values

M1c preserves that complete boundary and adds, as a new versioned unit:

1. the closed `solcore-semantic-core/v2` JSON Schema
2. a separate strict decoder and canonical encoder for the v2 wire AST
3. Oracle v3 queries bound to draft.3, `core-m1c-v1`, and Core v2
4. a `capabilities-v3` report that names the exact profile digest, Core schema,
   enabled features, limits, and observation schemas

Oracle v2 remains bound to draft.2 and Core v1. Oracle v3 rejects Core v1
requests, and Oracle v2 rejects Core v2 requests, rather than inferring a
version from an expression tag.

The M2 parser, resolver, and elaborator are responsible for converting a
`.solc` workspace into Core. M1 semantics are not defined by the existing
compilers' lowering behavior or by an ad hoc source parser specific to M1.
Consequently, the current Oracle is a reference implementation for the
published closed Core, not yet a source-level conformance oracle.

## Candidates for M1

- unit, bool, 256-bit words, and the M1c primitive subset
- lexical local bindings and a future explicit local store
- conditionals and future explicitly specified short-circuiting elaboration
- first-class functions, lexical closures, application, and return
- products, sums, user ADTs, constructors, and direct pattern matching
- closed Core programs with explicit types

Modules/imports, type inference, polymorphism, type class resolution, and
comptime remain in M2. The ABI, storage, contract host, and EVM remain in M3.

## ADR status for semantic choices

ADR-0011 resolves modulo behavior, division and modulo by zero, shift ranges,
primitive operand evaluation order, and selected-branch-only behavior for
future `&&`/`||` elaboration. The following choices still require an Accepted
ADR before implementation:

- evaluation order for function arguments and assignment
- the source typing, elaboration, evaluation-order preservation, feature
  boundary, and publication version for `&&` and `||`
- the source typing and elaboration rules for boolean/word conversions and
  other deferred primitives
- closure capture, recursion, and mutable local-cell identity
- constructor identity, ADT field order, and pattern selection order
- match exhaustiveness and unreachable match failure
- control transfer such as return
- the relationship between divergence and the fuelled evaluator

These choices are not decided solely by agreement or majority between the
Haskell and Rust implementations. Each choice must include a minimal
implementation witness.

## Implementation order

1. Define `Core.Ty`, `Core.Expr`, `Core.Value`, environments, and control
   results. Complete for the published M1c fragment.
2. Define well-formedness and the declarative typing judgment. Complete for the
   published M1c fragment.
3. Define a CEK transition relation and its multi-step closure. Complete for the
   published M1c fragment.
4. Implement a total evaluator that takes explicit fuel. Complete for the
   published M1c fragment.
5. Map checker/evaluator results to `rejected`, `inconclusive`, and `executed`.
   Complete.
6. Add versioned Core JSON codecs and Oracle queries. Complete through Core v2
   and Oracle v3.
7. Preserve minimal Haskell/Rust source witnesses as candidates for elaboration
   tests in M2 and later.
8. Add each deferred semantic family only after its rule set, feature boundary,
   wire impact, and proof obligations are accepted.

## Completion criteria for each feature

- An aggregate feature such as `corePrimitives` does not become `implemented`
  when only some of its components are complete. If independently promoting a
  component becomes necessary, an ADR that splits the feature ID must be
  Accepted before changing the profile.
- Declarative typing and evaluation rules exist.
- An executable checker and evaluator exist.
- Checker soundness is proved.
- Evaluator soundness is proved.
- Determinism is proved.
- Progress and preservation are proved for the target fragment.
- An explicit completeness theorem for sufficient fuel exists, or the
  limitation of an unproved direction is documented.
- Positive and negative witnesses and canonical wire golden cases exist.
- The semantic kernel contains no `sorry`, `admit`, `partial`, `unsafe`, or
  undeclared axioms.

Only features satisfying these conditions are changed to `normative` /
`implemented`. The same change updates `staticSemanticsVersion`,
`dynamicSemanticsVersion`, the specification release when necessary, and the
new profile's `enabledFeatures` and digest. Frozen draft.1/Core v1/Oracle v1 and
draft.2/Core v1/Oracle v2 artifacts remain unchanged for backward
compatibility; new semantics are published under new language, profile, Core
wire, capability, and Oracle versions.
