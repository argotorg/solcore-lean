# ADR-0357: Scope-aware source stage analysis

## Status

Accepted for the first whole-program `Comptime`/`Runtime`/`Deferred`
classification phase.  This phase adds an executable sidecar analysis over
checked typed source and makes the restricted direct linker consume those
facts.  It does not broaden the set of source values which can already be
evaluated at compile time.

## Context

ADR-0356 retained canonical parameter and result staging markers through
signature resolution, typed source, specialization and linking.  Its final
runtime boundary nevertheless used a small recursive classifier only at each
marked call argument.  That classifier recognized function inputs and a few
transparent expression forms, but it did not propagate a stage through lexical
let bindings or publish reusable facts for the rest of the frontend.

The pinned reference revision
`argotorg/solcore@1d490d8bb5f374356f06e0720655496482eb1fb4` uses three states:

- `Comptime` means that the expression is definitely available during staged
  evaluation;
- `Runtime` means that it definitely depends on an ordinary runtime input; and
- `Deferred` means that this early analysis cannot decide.  It is not another
  spelling of `Runtime` and must not be rejected early merely because it is
  unresolved.

The Lean typed-source node table is occurrence-addressed and append-ordered for
provenance.  It is not a control-flow or lexical-scope order.  A sound reusable
analysis must therefore walk the authoritative roots and child edges with an
explicit environment instead of folding the flat node table.

## Decision

### Publish a sidecar, not a rewritten IR

Add a total, fuel-bounded source-stage analysis whose result is separate from
`TypedSource`.  `Analysis.expressions` and `Analysis.binders` record the stage
of each reached expression and local binder by stable identity.  Consumers
query those facts without changing
expression types, coercion plans, evidence, node identities or source order.

Traversal starts from `TypedSource.roots` and follows the exact category-safe
expression and statement edges.  Statement lists are visited in source order.
An initialized let enters the lexical environment only after its initializer
has been analyzed.  Blocks, conditional branches, match arms and lambda bodies
receive isolated lexical extensions, so a branch-local declaration cannot
leak into a sibling or continuation.  Lambda parameter markers are retained in
the typed carrier so their bodies can use the same rule as named-function
parameters.

Malformed occurrence graphs reject explicitly.  Owner mismatches, missing or
wrong-category children, duplicate occurrence or binder identities, unknown
local references, cycles, conflicting repeated traversal, unreachable nodes
and insufficient traversal fuel are not assigned a convenient fallback stage.
The sidecar remains an analysis of checked source, not a repair pass for forged
typed IR.

### Fix the three-point join

The n-ary join used by binary expressions, tuples and conditionals is exact:

```text
join(stages) = Comptime  when every member is Comptime
             = Runtime   when at least one member is Runtime
             = Deferred  otherwise
```

The empty join is `Comptime`.  Thus a unit/empty tuple is closed, a runtime
dependency dominates a mixed aggregate, and a mixture of only `Comptime` and
`Deferred` remains `Deferred`.

### Seed function and lambda scopes explicitly

For an ordinary named function body, an explicitly marked parameter or a
parameter of a comptime-only type is `Comptime`; every other parameter is
`Runtime`.  Exact bare `integer` and structural `comptime<T>` are the
comptime-only source types in this phase.  When the function has an effective
comptime result—either the separate result marker or a comptime-only result
type—every input is instead analyzed as `Comptime`: the body question is
conditional on all arguments being available at compile time.  This does not
make an unmarked call argument comptime at the caller; call-result
classification still examines every actual argument.

A lambda has no named-function result contract in the current carrier.  Its
marked or comptime-only parameters begin as `Comptime`, its other parameters
begin as `Runtime`, and its body is checked only within the lambda's lexical
scope.  The lambda expression itself remains `Deferred` in this phase.

### Classify the accepted expression forms

The first phase uses these rules:

- literals and builtin Boolean constants are `Comptime`;
- a local reference uses the stage stored for its nearest stable binder;
- groups are transparent;
- unary expressions inherit their operand stage;
- binary expressions, tuples and conditionals join all of their semantic
  children; a conditional includes its guard and both branches;
- an initialized ordinary let inherits its initializer's exact stage, while an
  uninitialized let is `Deferred`;
- declaration and builtin-function references are `Deferred`; and
- lambda values, proxy values, indexing, indirect calls and any other form not
  justified by this phase remain `Deferred`.

A direct call is `Comptime` exactly when its retained declaration
instantiation has an effective comptime result—an authoritative result marker,
or an uncoerced node result whose type is exact bare `integer` or structural
`comptime<T>`—and every actual argument is `Comptime`.  Every other direct call
is `Deferred`.  In particular, call
classification never produces `Runtime`: an early runtime dependency in an
argument makes the result uncertain until the later staged/backend boundary.
The callee reference occurrence remains independently `Deferred` and is not
joined into the call result.

An explicit result marker remains authoritative in the presence of retained
output-coercion metadata.  Type-derived call staging requires an empty output
coercion path: acquiring a comptime-only node type through a retained coercion
does not by itself prove that the conversion can execute at compile time.  The
classifier otherwise records source dependence only; predicate-bearing and
coercion execution remain a later boundary.

### Attach facts to exact specializations

Each `SpecializedFunction` owns the analysis for its exact
`SpecializationKey`.  Specialization recomputes the sidecar from the concrete
checked function after applying its rigid-parameter substitution.  A generic
`T` may legitimately specialize to `integer` or `comptime<U>` and refine the
resulting table; no false pre/post table equality is required.  Stable
expression and binder identities remain unchanged.  The canonical
specialization and worklist comparisons therefore protect the recomputed stage
facts along with the rest of the specialized source carrier.

The restricted direct linker no longer runs an ad hoc classifier.  For every
argument corresponding to a marked callee parameter, it queries the caller's
sidecar:

- `Comptime` is admitted;
- `Runtime` produces the existing definite-runtime error; and
- `Deferred` produces the existing deferred-at-final-boundary error.

A missing sidecar entry is a malformed specialization, not `Deferred`.
ADR-0356's marked-result and runtime-root rules remain unchanged.

## Phase boundary

This ADR deliberately separates classification from evaluation.  It does not
yet add:

- general evaluation of staged Word, Bool, tuple, nominal, function, mapping,
  proxy or structural `comptime<T>` values;
- explicit comptime-let syntax, assignment updates or place-sensitive mutable
  stage tracking;
- staged constructors, indexing, indirect calls, implementation methods,
  predicate-bearing calls or coercion execution;
- selected-branch-only recursion, recursive memoization or compile-time
  Fibonacci;
- a policy for automatically choosing staged roots; or
- broad soundness, completeness or preservation metatheory.

Those extensions may refine `Deferred`, but they must not reinterpret a value
already proved `Runtime` as definitely comptime.  The executable sidecar and
its linker boundary are the stable input to those later stages.

## Verification target

Executable regressions cover the join truth table, function and lambda input
seeding, lexical let propagation, transparent groups and unary expressions,
binary/tuple/conditional joins, direct-call result classification,
declaration-reference separation, representative malformed owners and
duplicate identities, specialization recomputation, and the linker's
distinction between runtime and deferred marked arguments.  Existing tamper
coverage also fixes the early missing-node and cross-owner-binder boundaries.
Specialization coverage checks recomputation and stable-identity preservation
while permitting legitimate type-directed refinement.  Proof density remains
deliberately low for this vertical phase; no broad theorem family is required
before the executable classification boundary is usable.
