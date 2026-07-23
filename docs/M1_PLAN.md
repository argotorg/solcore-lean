# M1: Semantic Core implementation plan

The objective of M1 is to implement the smallest Semantic Core that can be
evaluated without passing through the Solcore source parser or backend, together
with all three of a declarative specification, an executable evaluator, and
correspondence proofs.
Even when an M0 feature is `directionAccepted`, it is not promoted to
`normative` or `implemented` until it satisfies the completion criteria below.

## Current progress: M1b publication

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

The existing aggregate features remain `partialSupport` or `planned` because
primitive operations, functions, mutation, ADTs, and other components are not
yet implemented. The M0 profile and digest, the Oracle v1 wire schema and query
support, and the golden bytes remain unchanged.

## Input boundary

M0 `solcore-oracle/v1` defines a typed result only for `capabilities`. Kinds from
`parse` through `contract` are reserved for capability negotiation and always
return `unsupported` in M0. An undecided Core AST must not be smuggled through
an arbitrary field such as `scenario : Json`.

M1b adds all of the following together:

1. the versioned `solcore-semantic-core/v1` JSON Schema
2. a strict decoder and canonical encoder for Core ASTs and values
3. Oracle v2 queries that directly evaluate Core input, typed observations, and
   the detailed phases required by Core
4. round-trip and golden tests between Core JSON fixtures and Lean values

The M2 parser, resolver, and elaborator are responsible for converting a
`.solc` workspace into Core. M1 semantics are not defined by the existing
compilers' lowering behavior or by an ad hoc source parser specific to M1.

## Candidates for M1

- unit, bool, and 256-bit words
- lexical local bindings and an explicit local store
- conditionals and explicitly specified short-circuiting
- first-class functions, lexical closures, application, and return
- products, sums, user ADTs, constructors, and direct pattern matching
- closed Core programs with explicit types

Modules/imports, type inference, polymorphism, type class resolution, and
comptime remain in M2. The ABI, storage, contract host, and EVM remain in M3.

## Items requiring an Accepted ADR before implementation

- modulo behavior for word operations, division by zero, and shift ranges
- evaluation order for function arguments, primitive operands, and assignment
- short-circuit behavior for `&&` and `||`
- closure capture, recursion, and mutable local-cell identity
- constructor identity, ADT field order, and pattern selection order
- match exhaustiveness and unreachable match failure
- control transfer such as return
- the relationship between divergence and the fuelled evaluator

These choices are not decided solely by agreement or majority between the
Haskell and Rust implementations. Each choice must include a minimal
implementation witness.

## Implementation order

1. Define `Core.Ty`, `Core.Expr`, `Core.Value`, environments, stores, and control
   results.
2. Define well-formedness and the declarative typing judgment.
3. Define a small-step or CEK transition relation and its multi-step closure.
4. Implement a total evaluator that takes explicit fuel.
5. Map checker/evaluator results to `rejected`, `inconclusive`, and `executed`.
   Complete.
6. Add the Core JSON codec and Oracle queries. Complete.
7. Preserve minimal Haskell/Rust source witnesses as candidates for elaboration
   tests in M2 and later.

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
new profile's `enabledFeatures` and digest. The frozen `core-v1` remains
unchanged for backward compatibility.
