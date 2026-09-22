# ADR-0365: Fuel-bounded selected-branch staged recursion

## Status

Accepted for direct whole-program staged calls in both the bare-`integer` and
Core-representable Unit/Bool/Word/product carriers.  Conditional staging now
validates both written branches but invokes calls and evidence-selected
operations only along the selected branch.  Exact active invocations detect
same-value cycles, while the public `Limits.stagingFuel` bounds dynamic staged
call depth.  Ordinary runtime/Core recursion retains its previous rejection.
This completes roadmap phase 5, staged recursion.

## Context

ADR-0355 and ADR-0359 deliberately required acyclic staged call expansion.
Their evaluators visited a conditional's guard, then branch, and else branch in
source order before selecting a value, and the direct linker rejected any
specialization key already on its active stack.  This was sufficient for
nested finite calls but rejected structurally ordinary compile-time programs:
countdown, factorial, mutually recursive countdown, and Fibonacci all revisit
the same type specialization with different concrete arguments.  It also
rejected a recursive call written in an unselected branch even though that
call has no dynamic effect on the staged result.

The canonical specialization plan must still retain every written call edge,
and an unselected branch must not become an unchecked metadata escape hatch.
At the same time, a specialization key alone is too coarse for staged cycle
detection: recursion at decreasing values is productive, whereas returning to
the exact same staged invocation is an immediately observable cycle.  A
separate resource bound is still required for value-changing divergence and
for terminating calls whose requested depth exceeds policy.

## Decision

### Separate validation from invocation

The staged integer and general staged-value evaluators carry an internal
execute/validate-only mode.  An executing conditional evaluates its guard,
executes only the selected branch, and traverses the other branch in
validate-only mode.  A validate-only traversal still checks the complete typed
shape, call edge, specialization, argument and result types, coercion or
operator plan, exact requirement identities, and source-ordered requirement
ledger.  It produces a type-correct inert value where one is needed to
continue structural validation.

Validate-only traversal never invokes a staged callee, selected coercion
method, or selected required unary/binary method.  Consequently a fault or
recursive call in an unselected branch is not executed.  The guard, then
branch, and else branch requirement streams are nevertheless concatenated in
source order, and each owning function still reconciles its complete solved
ledger exactly once.  All written edges also remain present in the canonical
specialization plan and pass its existing whole-program validation.

This policy applies to both expression and terminal statement conditionals.
Standalone compatibility entries retain their closed-call policy; selected
recursive execution is supplied by the whole-program linker.

### Index an active invocation by carrier, specialization, evidence, and value

The linker maintains distinct active-frame types for the bare-`integer`
evaluator and the general staged-value evaluator.  Within either carrier, a
frame is the tuple

`(SpecializationKey, ordered PredicateEvidence, concrete ordered arguments)`.

Carrier separation prevents an integer invocation and a Core-representable
invocation from aliasing.  The specialization key retains the exact ground
type instance; evidence stays in the specialized predicate order already
validated by ADR-0361; and arguments are compared as exact Lean `Int` values
or exact Unit/Bool/Word/product staged values.

Re-entering an exact active frame fails with `stagedInvocationCycle`.  A call
at the same specialization and evidence but different concrete arguments is
permitted, which gives decreasing countdown/factorial recursion and finite
mutual recursion their intended meaning.  Frames are active-stack entries,
not a result cache: a completed invocation may be evaluated again later.

### Bound dynamic staged-call depth

`SourceProgramExecution.Limits.stagingFuel` is the public staged-invocation
depth bound.  Entering either staged function evaluator consumes one unit; a
callee receives the remaining fuel.  Entry at zero fails with
`stagedFuelExhausted`.  This budget is independent of specialization planning,
runtime draft expansion, local source-graph fuel, isolated method-execution
fuel, and final Core execution fuel.

The bound is deliberately stack-shaped.  Sibling calls receive the same
remaining depth after an earlier sibling returns, so small Fibonacci is
executable without charging its whole call tree to one global counter.
Validate-only calls do not consume staging fuel because they are not invoked.
This phase does not claim a total-work bound or share a work counter between
siblings.

### Preserve existing evidence and execution boundaries

Recursive calls continue to use their exact canonical occurrence edge and
specialization, evaluate executing arguments left to right, validate and
forward concrete predicate evidence in order, and reconcile the callee's
declaration-local requirements before returning only a value.  Caller,
callee, and detached-method ledgers remain separate.  ADR-0362 through
ADR-0364 retain their independently typed closed `Resolved.Expr` to Core
method execution, structural fuel, empty initial/final store requirement, and
staged-carrier projection.

The result of successful recursion is still materialized as a closed resolved
and Core constant.  It adds no runtime input and preserves the caller's store.
Runtime calls do not enter this staged invocation machine; the existing
specialization-key `recursiveCallCycle` rejection therefore remains the
runtime/Core policy.

## Phase boundary

Roadmap phase 5 now includes:

- selected-branch direct recursion for the bare-`integer` and
  Unit/Bool/Word/product staged carriers;
- value-changing self recursion, finite mutual recursion, countdown,
  factorial, and small compile-time Fibonacci;
- exact active-frame cycle rejection through `stagedInvocationCycle`; and
- public dynamic-depth exhaustion through `stagedFuelExhausted` and
  `Limits.stagingFuel`.

Still deferred are:

- result memoization or a value-indexed staged-result cache;
- a sibling-shared or global total-work budget;
- ordinary runtime recursion and recursive Core execution;
- indirect or higher-order recursion, function-valued staged carriers, and
  automatic staged-root discovery;
- effects, mutation, nonempty staged stores, nominal values, mappings,
  proxies, indexing, and other unsupported staged carriers;
- nested marked direct calls or marked method dispatch reached from inside a
  selected implementation method;
- type-growing polymorphic recursion beyond the finite specialization budget;
  and
- broad soundness, completeness, resource-bound metatheory, and a public
  source Oracle.

## Verification target

Public check/specialize/link/run regressions cover integer countdown,
factorial, mutually recursive countdown, and small Fibonacci.  General staged
regressions cover Word and Bool results, expression and statement conditionals,
and a constrained generic relay whose ordered evidence is retained through the
recursive call.  Successful programs close to constants and preserve a
nonempty caller store.

Separate regressions require an unselected fault and an unselected infinite
recursive call not to execute, while their written metadata and ledgers still
validate.  Exact same-value self and mutual cycles fail with
`stagedInvocationCycle`; value-changing nontermination and insufficient depth
fail with `stagedFuelExhausted`.  An ordinary runtime self-call continues to
fail with `recursiveCallCycle`.
