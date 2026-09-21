# ADR-0361: Proof-only staged-call predicates

## Status

Accepted for exact proof-only signature predicates on direct staged calls.
Both the arbitrary-precision bare-`integer` evaluator and the
Core-representable Unit/Bool/Word/product evaluator may now cross a constrained
direct-call edge when the caller supplies concrete evidence for every
specialized callee predicate.  This phase does not execute a predicate,
coercion, required operator or implementation method during staging.
It supersedes only the predicate-free call restriction recorded by ADR-0355,
ADR-0359 and ADR-0360; their value, ownership, staging and termination
boundaries remain unchanged.

## Context

ADR-0355 and ADR-0359 established two direct staged-call paths.  Both paths
already use the canonical specialization plan, keep caller and callee
requirement ledgers separate, and share the runtime linker's active-key stack
and decreasing link-depth fuel.  They nevertheless required the selected
declaration instantiation to have an empty predicate list.

The ordinary runtime direct-call path already treats signature predicates as
proof-only obligations.  It checks the call occurrence's exact requirement
identities against the specialized predicate sequence, replaces an assumption
marker with a uniquely available concrete witness, and forwards those
witnesses to the callee without constructing Core evidence values.  The staged
call planners already performed that same exact validation and constructed the
same evidence list before applying their empty-predicate rejection.  Retaining
the rejection therefore excluded constrained pure staging without protecting a
different execution boundary.

This distinction matters for generic wrappers.  A specialized call may carry
an assumption-shaped solved row inherited from a rigid generic body, while the
enclosing concrete invocation has the implementation witness which closes it.
The witness must cross every nested staged call in the specialized predicate
order; forwarding the unresolved assumption itself would merely move the proof
hole.

## Decision

### Validate every call-owned predicate exactly

Before evaluating a staged call, the linker validates the call occurrence in
the specialized declaration instantiation's predicate order.  It requires:

- exactly one call-owned requirement identity for each specialized predicate;
- no duplicate call-owned requirement identity;
- exactly one solved row owned by the caller for every such identity;
- equality between the specialized predicate and the solved row's predicate;
  and
- equality between that predicate and the solved evidence goal.

An implementation witness is retained.  An assumption witness is replaced by
the unique incoming concrete witness with the same goal.  Missing or ambiguous
incoming evidence remains an error.  The linker does not infer, reorder or
silently erase a call-owned obligation.

### Forward concrete evidence into both staged evaluators

The validated witnesses are passed positionally to the selected callee for
both supported staged carriers:

- the bare-`integer` evaluator introduced by ADR-0355; and
- the Unit/Bool/Word/right-associated-product evaluator introduced by
  ADR-0358 and linked by ADR-0359.

At callee entry, the evidence count and each evidence goal are checked against
the specialized callee assumptions.  Every forwarded row must be concrete;
an unresolved assumption is rejected.  Nested staged calls repeat the same
protocol, so a concrete witness may cross a specialized generic relay without
becoming a runtime value.

The predicate is proof-only in this phase.  It authorizes entry into a body
whose supported staged expressions do not consume trait operations.  It does
not select or execute an implementation method, authorize a required unary or
binary expression, or provide coercion behavior.

### Preserve requirement ownership and value-only results

The call plan reports the exact call-owned requirement list as consumed by the
caller.  Argument requirements remain in left-to-right source order, followed
by that call-owned segment.  The callee still evaluates against and reconciles
only its own declaration-owned solved-requirement table.  Numerically equal
requirement identities in different functions therefore cannot cross ledgers.

Only staged argument and result values cross the evaluation boundary.  No
evidence object is reified into `Resolved.Expr` or Semantic Core, and enabling
a proof-only predicate does not change a function type, runtime input, call
alias, specialization key or store behavior.

### Retain the existing termination boundary

Predicate forwarding does not create a new evaluation entry or budget.  The
runtime linker, staged-integer evaluator and Core-representable staged evaluator
continue to use the same canonical `SpecializationKey` visiting stack and the
same decreasing link-depth fuel.  Nested constrained calls are admitted only
when their call graph is finite and acyclic.  Eager traversal of both written
conditional branches is unchanged.

## Phase boundary

This phase does not add:

- staged coercion execution or argument/result conversion;
- staged required unary or binary operations, trait-method dispatch, or marked
  implementation-method execution;
- indirect calls, function values or general higher-order evaluation;
- mutation, assignment or place-sensitive staged environments;
- nominal constructors, mappings, proxies, indexing or staged carriers beyond
  the existing bare `integer`, Unit, Bool, Word and product profiles;
- promotion of `Runtime` or `Deferred` values, value-indexed specialization or
  cross-occurrence memoization;
- direct, mutual or selected-branch-only recursion, or compile-time Fibonacci;
- automatic staged-root discovery or a public source Oracle; or
- broad soundness, completeness and preservation metatheory.

The ordinary runtime evidence profiles remain unchanged.  In particular,
their supported implementation-method-backed unary, binary and coercion
operations do not become available merely because a function is evaluated by
a staged call policy.

## Verification target

End-to-end regressions specialize a generic constrained Word function through
a nested constrained relay and materialize its marked result inside a runtime
callee.  A parallel nested bare-`integer` chain forwards the same kind of
proof-only evidence before projecting its result to Word.  Both cases preserve
the input store and execute through the public whole-program preparation or
canonical linker boundary.

The existing exact call-evidence checks retain located rejection of missing,
duplicate, reordered or predicate/goal-mismatched requirements and of missing
or ambiguous incoming witnesses.  Coerced marked results, requirement-bearing
staged operators, marked implementation methods, recursive edges and exhausted
shared link fuel remain explicit failures.
