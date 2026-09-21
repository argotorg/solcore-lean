# ADR-0360: Call-site known comptime inputs

## Status

Accepted for the first call-site propagation of concrete Core-representable
values into runtime-callee drafts.  This phase permits a marked-result
call inside such a draft to depend on an explicitly marked input when the exact
caller actual is available to the staged evaluator.  It preserves the runtime
calling convention, specialization identity, requirement ownership and the
existing predicate-free, coercion-free, acyclic execution boundary.

## Context

ADR-0359 materializes authoritative marked-result direct calls as closed Unit,
Bool, Word or product constants.  It originally disabled the general staged
policy for a runtime callee whose stage analysis classified any input as
`Comptime`, because the reusable draft started without concrete values for
those inputs.  That conservative boundary also prevented an input-independent
staged call or closed staged let from materializing in the same function.

Simply enabling the policy fixes the independent case, but it does not make a
dependent input known.  The runtime linker asks Source Core to build the callee
draft from a planned call occurrence, while the concrete actual expressions
belong to the caller and are lowered separately.  A value therefore has to be
queried at that exact occurrence and passed into the callee's private staged
environment.  Caching it only by `SpecializationKey` would be unsound: two
calls such as `helper(2)` and `helper(9)` have the same type specialization but
different compile-time values.

ADR-0357 `Comptime` remains a dependence classification rather than a promise
that every source form has an evaluator.  The integration must distinguish a
known value from an unavailable one without promoting `Runtime` or `Deferred`
data, consuming caller requirements twice, or removing runtime Core inputs.

## Decision

### Query values at the exact call occurrence

The Source Core call boundary supplies the whole-program linker with a lazy,
read-only staged-argument oracle for the current caller expression.  A query
may return a `SourceStagedValue.Value` only when the exact expression has the
specialization-owned ADR-0357 `Comptime` fact, is closed relative to the
caller's currently known staged environment, and succeeds under the existing
general staged evaluator.  Otherwise it returns unavailable or propagates the
same located validation failure; it never invents a value.

The runtime linker queries this oracle only for a callee input carrying the
canonical explicit `comptime` marker.  Inputs and actuals are paired in source
order after exact arity, marker, source-type and value-type validation.  An
ordinary input receives no staged binding even if some wider analysis happens
to classify its expression as `Comptime`.  The existing boundary continues to
reject a `Runtime` or `Deferred` actual passed to a marked parameter.

The ordinary call-elaboration and public source-execution entry points retain
their existing contracts.  The staged-aware callback is an additive internal
coordination boundary rather than a new source calling convention or public
Oracle.

### Seed the callee without specializing the runtime ABI by value

Known values are bound positionally to the callee's declaration-owned stable
input identities before its Source Core draft is lowered.  Unavailable values
are omitted from that private staged environment.  Consequently an
input-independent staged call or closed staged let can still materialize when
another marked input is unavailable, while a marked-result call that actually
depends on a known input can now evaluate and reify its closed result.

Every source input remains in the runtime Core context.  The caller still emits
the same left-to-right argument temporaries and callee-input aliases, and the
linked entry keeps the same Core input type, result type and
`SpecializationKey`.  A known value is only a compile-time hint used while
constructing that occurrence's draft; it does not erase a parameter or alter
the runtime function signature.

Draft construction remains per call occurrence and is not memoized by the type
specialization key.  Distinct calls to the same specialization therefore seed
distinct environments, and no value learned for one occurrence is visible at
another occurrence or root.

### Preserve requirement ownership

The oracle exposes only a staged value.  Any requirement ledger traversed to
discover that value is not transferred to the callee draft.  Ordinary lowering
of the actual expression remains the sole owner of the caller's requirements
and consumes them once in source order.  The callee continues to reconcile only
its own declaration-owned solved-requirement table.

This separation applies recursively and prevents duplicate consumption or
accidental agreement between numerically equal caller and callee requirement
identities.  Supplying a known input does not authorize staged predicate,
coercion or implementation-method execution.

### Keep unavailability and termination explicit

General staged caching is enabled in every runtime draft, but eligibility is
checked recursively against the values currently present in its staged
environment.  A local reference is eligible only when its stable binder has a
known value, and a marked direct call is eligible only when all of its actuals
are eligible.  A dependent call with an unavailable input therefore remains on
the ordinary runtime path and reaches the existing marked-result rejection; it
is not replaced by a guessed constant or silently dropped.

Runtime expansion, staged-integer evaluation, general staged-call evaluation
and call-site value propagation continue to use the same active stack of
canonical `SpecializationKey`s and the same decreasing link-depth fuel.
Expression and statement conditionals retain eager guard/then/else traversal,
including failures and cycles in an unselected branch.  No oracle query resets
those controls or adds a value-indexed recursion cache.

## Phase boundary

This phase does not add:

- staged predicates, coercions, trait evidence or marked implementation-method
  execution;
- indirect calls, function values or general higher-order evaluation;
- mutation, assignment or place-sensitive staged environments;
- nominal constructors, mappings, proxies, indexing or staged value shapes
  beyond Unit, Bool, Word and right-associated products;
- evaluation for every expression merely classified `Comptime`, opportunistic
  folding of unmarked general functions, or promotion of `Runtime`/`Deferred`
  actuals;
- value-indexed specialization keys, cross-occurrence value memoization,
  direct or mutual recursion, selected-branch-only recursion, or compile-time
  Fibonacci;
- automatic staged-root discovery or a public source Oracle; or
- broad soundness, completeness and preservation metatheory.

The arbitrary-precision staged-integer evaluator remains a distinct
compatibility path.  This phase neither gives bare `integer` a runtime Core
representation nor changes its supported compiler-intrinsic tree.

## Verification target

Executable regressions cover direct and let-cached input-independent staged
calls inside a runtime callee carrying a marked input; a marked-result call
depending on a known literal or local-alias actual; two occurrences of the same
specialization receiving different known values; mixed marked and ordinary
runtime inputs; product-valued known inputs; exact closed reification; and store
preservation.

Adversarial cases retain rejection of runtime and `Deferred` marked actuals,
unsupported or unavailable dependent values, arity and type mismatches,
predicate or coercion staging, marked runtime roots, direct and mutual cycles,
cycles in an unselected eager branch, and exhausted shared link fuel.  The
resolved shape must retain every runtime argument and callee-input alias while
containing no surviving call for each successfully materialized marked result.
