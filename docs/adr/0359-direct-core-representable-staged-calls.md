# ADR-0359: Direct Core-representable staged calls

## Status

Accepted for the first whole-program integration of the ADR-0358 staged-value
carrier.  This phase materializes validated direct calls returning Unit, Bool,
Word or right-associated products, including nested acyclic calls and calls
inside an otherwise runtime function.  It deliberately retains the existing
predicate-free, coercion-free and non-recursive execution boundary.

## Context

ADR-0357 assigns specialization-owned `Comptime`, `Runtime` or `Deferred`
facts to reached source expressions.  ADR-0358 then evaluates a bounded
standalone fragment to `SourceStagedValue.Value`, but stops before declaration
calls and the whole-program specialization-plan linker.  Consequently a
marked helper can already be evaluated in isolation while the same call cannot
yet be erased to a closed Core constant in its caller.

The direct-call linker already has the canonical ingredients needed to make
that integration safe: a complete specialization plan, an exact
per-occurrence edge, a concrete `SpecializationKey`, a decreasing link-depth
budget, and an active-key stack used by staged integer and runtime expansion.
The integration must reuse those controls.  Starting an unrelated evaluator at
each call would let recursion evade the linker's cycle or fuel checks.

The pinned Haskell and Rust implementations both evaluate call arguments from
left to right.  Their optimization passes can sometimes fold a constant
function even when an ignored argument is not known.  That optimization is not
the contract selected here: canonical comptime-result classification requires
every actual argument to be comptime before this evaluator may execute the
call.  As in ADR-0353 and ADR-0358, the Lean frontend also deliberately
evaluates both written conditional branches before selecting the result.

## Decision

### Admit only authoritative direct staged-call edges

The linker may interpret a call through the general staged-value evaluator
only when all of the following hold:

- the occurrence has an exact canonical edge in the complete specialization
  plan and resolves to the declared callee specialization;
- the call occurrence has the specialization-owned ADR-0357 `Comptime` fact;
- every actual argument has an ADR-0357 `Comptime` fact and agrees exactly
  with its specialized input type;
- the callee has the canonical comptime-result marker, one result, and that
  result is exactly Unit, Bool, Word or a right-associated product of those
  types; and
- the call, callee signature and evaluated body use no predicate or coercion
  execution admitted only by a later phase.

A runtime or `Deferred` actual does not become staged merely because the
callee ignores it.  An unmarked general-value function is not promoted by
purity analysis.  The existing unmarked pure bare-`integer` compatibility rule
is separate and unchanged.

The call arguments are evaluated exactly once, from left to right, before the
callee environment is created.  Their values are bound positionally to the
callee's stable input identities.  Wrong arity, wrong input type, missing or
stale stage facts, a noncanonical plan edge and an unsupported result type are
located failures rather than reasons to fall back to runtime lowering.

### Keep caller and callee requirement ownership separate

The caller consumes requirements in source order: the complete ledger of the
first argument, then the second, and so on, followed by the call occurrence's
own requirements.  The present predicate-free profile requires that final
call-owned segment to be empty.

The callee evaluates against its own solved-requirement table and reconciles
that ledger before returning a value.  Callee requirement identities never
enter the caller's ledger.  This remains necessary even when numerical IDs
coincide, because each table is declaration-owned.

Nested admitted calls repeat the same protocol.  A caller therefore receives a
closed staged value, not a partially consumed callee ledger or a delayed source
expression.

### Reify the result at the caller occurrence

After exact result-type validation, the linker projects the staged value with
`SourceStagedValue.toResolved`.  That projection produces a closed resolved
constant whose Core meaning is independent of the caller's local scope.  The
call itself and its argument-binding temporaries are absent from the resulting
Core expression.

This also permits a runtime-root function to contain a staged helper call.  For
example, an ordinary source let in that caller may alias the closed Bool, Word,
Unit or product produced by the helper; the surrounding let remains an
ordinary Core binding, while only the staged call occurrence is materialized.
This does not make a marked function a legal runtime root and does not admit
runtime-dependent actual arguments.

### Preserve eager traversal and shared termination controls

Expression and statement conditionals retain the established eager order:
guard, then branch, else branch.  Both branches are interpreted, including
their nested calls, failures and requirements, before the guard selects a
value.  A staged call hidden in an unselected branch is therefore still part of
the validated computation.

Runtime call expansion, staged-integer call evaluation and general
staged-value call evaluation use one active stack of canonical
`SpecializationKey`s and one decreasing link-depth fuel.  Entering any of the
three modes records the selected key; encountering an active key rejects the
program.  The source-node fuel used to reject malformed local expression or
statement graphs remains local to each callee and does not replace the shared
link budget.

These rules admit nested finite acyclic calls but intentionally reject direct
recursion, mutual recursion and recursion reachable only through an
unselected eager branch.  No public evaluation entry may reset the shared
stack or link fuel while following a planned call edge.

## Phase boundary

This phase does not add:

- predicate-bearing staged calls, staged coercions, trait evidence execution
  or marked implementation-method calls;
- indirect calls, function values or general higher-order evaluation;
- mutation, assignment or place-sensitive staged environments;
- nominal constructors, mappings, proxies, indexing or other staged value
  shapes beyond Unit, Bool, Word and products;
- direct, mutual or selected-branch-only recursion, memoization, or
  compile-time Fibonacci;
- opportunistic evaluation of unmarked general functions or marked calls with
  any runtime/`Deferred` actual;
- general staged materialization while lowering a runtime callee that itself
  has a `Comptime`-classified input; its reusable runtime draft has no concrete
  input value environment yet, so that draft retains the legacy call path;
- automatic staged-root discovery; or
- broad soundness, completeness and preservation metatheory.

The arbitrary-precision staged-integer evaluator remains a distinct
compatibility path.  General staged-call materialization neither invents a
runtime Core representation for `integer` nor widens the integer path's
accepted intrinsics.

## Verification target

Executable regressions cover direct and nested acyclic marked-result calls for
Unit, Bool, Word and right-associated products; left-to-right argument
evaluation; exact input/result checking; independent caller and callee
requirement ledgers; materialization inside a runtime caller alias; and eager
calls or failures in both expression and statement conditional branches.

Adversarial cases reject missing or noncanonical specialization edges,
runtime/`Deferred` actuals, stale stage facts, arity and type mismatches,
unsupported carriers, call-owned predicates or coercions, marked runtime
roots, self- and mutual recursion, unselected-branch recursion, and exhausted
shared link fuel.  Reified results are checked to contain no surviving source
call and to retain the exact resolved-lowering and Core type equations already
required by the source-to-Core boundary.
