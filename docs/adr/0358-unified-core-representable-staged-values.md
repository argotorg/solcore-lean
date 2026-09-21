# ADR-0358: Unified Core-representable staged values

## Status

Accepted for the first reusable staged-value evaluation foundation.  This phase
adds a stage-gated standalone evaluator for Unit, Bool, Word and product values.
It does not yet route direct declaration calls through that evaluator or change
the public source-program execution boundary.

## Context

ADR-0357 publishes specialization-specific `Comptime`/`Runtime`/`Deferred`
facts, but classification alone does not produce a value.  The existing closed
staging path can compute signed `integer` expressions and a few values needed by
the compiler-intrinsic boundary.  Its private integer environment and
domain-specific result records are deliberately narrower than the ordinary
Core-representable source values needed by a general comptime function.

The pinned reference revision
`argotorg/solcore@1d490d8bb5f374356f06e0720655496482eb1fb4` treats literals and
constructors whose children are known as compile-time values.  It evaluates a
let initializer before extending the environment, visits tuple children from
left to right, and visits a conditional's guard, then branch and else branch.
ADR-0353 already fixed the Lean convention: all three conditional children are
validated and evaluated before the selected value is returned.  A general
value evaluator must retain those ordering and failure boundaries without
inventing a runtime representation for `integer`.

## Decision

### Publish one closed value carrier

`SourceStagedValue.Value` contains exactly:

- Unit;
- Bool;
- canonical `Core.Word`; and
- a binary product of two staged values.

Products are right-associated in the same way as `Ty.productMany`; an empty
tuple is Unit.  The carrier excludes functions, nominal constructors, mappings,
cells and every other Core value shape, so accepting a staged value cannot
silently widen the source frontend's executable profile.

Every value is checked against its exact source `Ty` before it enters an
environment, crosses a function-input boundary or becomes a function result.
The accepted carrier has a total projection to the corresponding closed
`Core.Value`.

The existing arbitrary-precision staged-integer evaluator remains separate.
ADR-0358 neither changes its accepted intrinsic trees nor creates a Core value
for `integer`.

### Consume the stage sidecar at the evaluation boundary

`SourceCoreElaboration.evaluateStagedValue` receives the exact
`SourceStageAnalysis.Analysis` associated with the typed source.  An expression
must have a recorded `Comptime` stage before the evaluator interprets it.
`Runtime`, `Deferred` and a missing fact are separate located failures.
The function-level entry point additionally recomputes the analysis from its
specialized checked function and requires exact table equality, so a stale or
forged specialization sidecar cannot promote runtime data to a staged value.
Its specialization declaration and concrete argument key are checked against
the retained declaration and parameter substitution before inputs are bound.

`Comptime` describes source dependence, not evaluator completeness.  A
comptime-classified lambda, call, proxy, index or other unsupported shape still
fails explicitly rather than being assigned an invented value.  Expression
metadata is rechecked independently: unsupported requirements, coercions,
types, child categories and graph cycles do not become valid merely because
the sidecar says `Comptime`.

### Evaluate the bounded expression fragment

The standalone evaluator accepts:

- strict compatibility Word literals and source-generated Word literals with
  exact builtin `Int<Word>` evidence;
- builtin Boolean constants;
- local references found by stable declaration-owned binder identity;
- transparent groups;
- empty and nonempty tuples, evaluated from left to right;
- requirement-free, coercion-free builtin unary and binary operations over the
  admitted value types; and
- expression conditionals.

Unary and binary evaluation must agree with the existing Core operation on the
same closed operands.  Trait requirements, method dispatch and coercion paths
are not interpreted by this phase.

A conditional evaluates its guard, then branch and else branch in that order.
Both branch requirement streams and failures are retained even when the guard
already chooses the other branch.  Only after all three evaluations succeed is
the selected value returned.

`StagedValueEvaluation` pairs the value with the exact ordered list of literal
requirements consumed while producing it.  Tuple, operator and conditional
composition preserves source traversal order.

### Thread a stable lexical environment through statements

`evaluateStagedValueFunction` binds supplied positional values to the checked
function inputs after exact arity and type validation.  Its lexical environment
is keyed by `Resolved.LocalId`, not source spelling.

An initialized let is evaluated once under the old environment.  Only after
that succeeds is the new monomorphic binder and value visible to the remaining
statements.  A later reference consumes no initializer requirement again.
Shadowed spellings therefore remain distinct, while a self-reference cannot
capture the binder being defined.

The initial statement profile contains initialized lets, terminal returns,
lexical blocks and two-return-branch statement conditionals.  Branches start
from the same outer environment and do not leak their locals.  Statement
conditionals use the same eager guard/then/else policy as expression
conditionals.  Uninitialized lets, fallthrough and unsupported control flow
reject explicitly.

Before returning, the function evaluator checks the result type and reconciles
the consumed requirement ledger exactly against the function's solved rows.
Missing, duplicated, reordered or unconsumed requirements are errors.

## Phase boundary

This is a standalone evaluator foundation.  It does not yet add:

- staged direct declaration calls or integration with the specialization-plan
  linker;
- predicate-bearing or coerced staging, implementation methods or indirect
  calls;
- mutation, assignment or place-sensitive environments;
- nominal constructors, lambdas/closures, mappings, proxies, indexing or
  staged pattern matching;
- recursive evaluation, memoization, selected-branch-only recursion or
  compile-time Fibonacci;
- automatic staged-root discovery, public source Oracle support; or
- broad soundness, completeness or preservation metatheory.

The next integration phase may pass this carrier across validated direct call
edges.  It must preserve the standalone evaluator's type, stage, traversal and
requirement-ledger checks rather than reimplementing them in the linker.

## Verification target

Executable regressions cover all four value constructors, nested
right-associated products, exact value/type agreement, positional inputs,
stable-ID aliases and shadowing, old-environment let initialization, groups,
requirement-free unary and binary operations, eager expression and statement
conditionals, terminal blocks and returns, left-to-right requirement order and
exact-once ledger reconciliation.  Adversarial cases distinguish missing,
`Runtime` and `Deferred` stage facts and reject wrong types, malformed literal
evidence, requirements, coercions, local identities, child edges, cycles,
fallthrough and failures in an unselected branch.  The ADR-0349–0357 integer
staging and linking suites remain unchanged compatibility checks.
