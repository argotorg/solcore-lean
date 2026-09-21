# ADR-0350: Closed staged integer arithmetic and comparisons

## Status

Implemented as an executable extension of ADR-0349 for direct, unqualified
`integerAdd`, `integerEq`, and `integerLt` calls over closed staged integers.

## Context

ADR-0349 introduced collision-free compiler-function identities and a closed
staged evaluator for exact signed subtraction followed by explicit conversion
to `Word`.  The pinned reference compiler catalog also defines exact signed
addition and the two primitive comparisons

```text
integerAdd : (integer, integer) -> integer
integerEq  : (integer, integer) -> Bool
integerLt  : (integer, integer) -> Bool
```

These operations must observe the unbounded staged values.  Reducing either
operand modulo `2^256` before equality or ordering would change the reference
semantics.  The growing compiler-function identity set also makes a separate
hand-written name lookup chain an avoidable source of catalog drift.

## Decision

### Derive exact lookup from one supported catalog

`BuiltinFunctionId.all` records every compiler function currently implemented
by the frontend in stable append-only introduction order.  Exact bare-name
lookup searches that list through each identity's canonical spelling.  Small
completeness, uniqueness, and spelling checks keep identity addition and lookup
extension together.

The priority contract from ADR-0349 is unchanged.  A local binding wins first,
then any visible source-function set wins as a set, and the compiler catalog is
consulted only when that set is empty.  A source candidate that fails arity or
type checking does not fall through to a builtin, and qualified names do not
receive the bare fallback.

### Reuse one exact signed operand evaluator

`integerAdd` joins `integerSub` in the fuel-bounded closed integer evaluator.
Both recursively validate their operands and compute with Lean `Int`, without
wrapping or projecting to `Word`.  Literal requirements are reported in
left-to-right traversal order and remain subject to declaration-wide exact-once
reconciliation.

`integerEq` and `integerLt` are runtime-erasure boundaries rather than integer
expressions.  Source Core intercepts them before ordinary call or coercion
lowering, revalidates the complete builtin call and callee contract, evaluates
both operands through the same closed integer evaluator, and emits one Bool
constant.  Comparison happens before any modulo conversion.  Consequently,
`integerEq(2^256, 0)` is false, and negative results produced by subtraction
sort below nonnegative values.

Compiler arithmetic and comparison calls add no source declaration,
specialization request, or call edge.  A bare `integerAdd` result which is not
consumed by a supported staged boundary remains an unsupported runtime
`integer`, just like `integerSub`.

## Deferred boundaries

- ADR-0351 adds exact `integerMul` for source-generated occurrence trees and
  defers synthetic shared-DAG resource hardening explicitly.
- ADR-0352 connects `wordToInteger` through a separately specified closed Word
  evaluator; general runtime Word expressions remain outside that purity
  boundary.
- Staged locals, parameters, integer-valued conditionals, ordinary calls,
  recursion, and general compile-time control flow remain unsupported.
- Indirect compiler-function invocation, output coercions, and custom execution
  of the compiler builtin `Int` trait remain outside this exact direct profile.
- Graph-wide `TypedSource` ownership, uniqueness, reachability, shared-DAG work
  accounting, and broad inference/lowering metatheory remain shared later work.

## Verification

Regressions cover exact catalog order and name lookup, typed identities and
signatures, large and negative addition, nested addition/subtraction, equality
and ordering before modulo, negative ordering, Bool constant erasure,
conditional use, store preservation, source shadowing without failed-candidate
fallback, and absence of source specialization edges.  Adversarial cases
mutate each new call's identity, spelling, callee/call/argument types, arity,
requirements, coercions, staged child cycles, and requirement accounting; each
must fail at a located checked boundary.
