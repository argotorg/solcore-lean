# ADR-0354: Let-bound staged integers

## Status

Implemented as an executable extension of the ADR-0349–0353 closed staging
boundary for initialized, monomorphic let bindings whose fully resolved type is
exactly the primitive `integer` type.

## Context

The pinned reference revision
`argotorg/solcore@1d490d8bb5f374356f06e0720655496482eb1fb4` makes integer staging a
type-directed property.  After applying the complete inference substitution,
`markIntegerComptime` marks every let whose identifier type is primitive
`integer` as comptime, whether or not the source wrote an explicit comptime
marker.

`Solcore.Backend.MastEval.evalStmts` then processes `MastLet` statements from
left to right.  It evaluates an initializer under the environment which existed
before the binding, records a known value for later `MastVar` substitution, and
removes a comptime let whose value is known.  An unknown initializer removes
the shadowed environment entry instead.  The backend comptime check rejects a
marked let whose initializer is not comptime, and an integer let which still
survives to `EmitHull` is rejected because `integer` has no runtime
representation.  The pinned `integer-basic.solc` regression relies on this
behavior:

```text
let x = 42;
let y = integerAdd(x, 8);
return wordFromInteger(integerMul(y, 2));
```

Both lets become implicitly comptime after inference and the function returns
the Word value `100`.

The Lean frontend already retains a fully substituted `TypedBinder` with a
declaration-owned local identity, source spelling, and scheme.  Its closed
integer evaluator, however, previously had no lexical value environment, so a
`.local` reference necessarily looked runtime-dependent.  Lowering an integer
let as a Core `letE` would instead invent the runtime integer representation
which the staging boundary is designed to avoid.

## Decision

### Stage lets from their finalized type

No new surface marker or typed-IR comptime flag is introduced.  During
tail-normal statement lowering, an initialized let is staged when its finalized
binder scheme is monomorphic and its body is exactly `integer`.  The statement
must still have Unit type; the binder owner must match the enclosing typed
source; and its stable local identity must not collide with an active runtime
or staged binding.  Missing initializers and polymorphic or malformed integer
binders remain located errors.

The initializer is evaluated exactly once by the existing closed staged-integer
evaluator under the environment preceding the declaration.  Only after that
evaluation succeeds is the binder/value pair prepended while lowering the
remaining statements.  A binding therefore cannot see itself or a later let,
while it may depend on earlier staged-integer bindings.  This matches the
reference `MastLet` order and the existing source lexical-scope rule that a let
initializer uses the old scope.

The successful integer let emits no Core `letE` and is not added to the runtime
Core context.  Its Lean `Int` value lives only in the private staged environment.
Non-integer lets retain the existing runtime lowering path unchanged.

### Resolve local uses without duplicating work or evidence

The staged integer evaluator accepts a local reference only when all of the
following agree:

- the expression node has exact type `integer` and has no requirements or
  output coercions;
- the referenced local and stored binder belong to the current declaration;
- the stable local identity is present in the staged environment;
- the stored binder remains monomorphic with exact type `integer`; and
- the reference spelling exactly matches the stored binder spelling.

Lookup returns the stored `Int` and consumes no requirement.  Literal and call
requirements belong to the initializer evaluation, which is concatenated once
before the requirements consumed by the remaining statement tail.  Reusing a
local any number of times therefore does not duplicate its initializer work or
evidence, while an unused staged let is still evaluated and accounted for once.

The same staged environment is threaded through the integer, Word, and Bool
evaluators.  Earlier integer locals can consequently participate in arithmetic,
comparisons, closed conditionals, `wordFromInteger`, and the existing
Word/integer conversion bridge.  Branches start from the same incoming
environment, block-local extensions do not escape, and same-spelled lexical
shadowing remains unambiguous because lookup uses stable local identity rather
than text alone.  Existing node-derived fuel continues to bound malformed
expression cycles; environment lookup itself does not recursively re-evaluate
an initializer.

The public expression-only staged evaluators still start with an empty
environment.  Only statement lowering establishes lexical bindings, so an
isolated local-reference expression cannot capture a let from elsewhere or
turn this private environment into an ambient public input.

## Deferred boundaries

- The next staging stage addresses comptime function parameters, ordinary
  calls, recursion, and the general `comptime<T>` contract.  This ADR neither
  evaluates source functions nor gives runtime parameters staged meaning.
- Closed Word or Bool constant propagation through local bindings, and using a
  runtime Word local as the input of `wordToInteger`, remain outside this
  integer-only environment.
- Assignment, mutation, loops, general statement control flow, uninitialized
  staged bindings, indirect calls, output coercions, and every surviving runtime
  `integer` remain unsupported.
- Graph-wide ownership/reachability proofs, shared-DAG total-work controls, and
  broad inference/lowering metatheory remain shared hardening work.

## Verification

Regressions cover the pinned `integer-basic.solc` chain and its result `100`,
explicitly annotated and context-inferred integer lets, dependencies on earlier
bindings, repeated and unused local uses, lexical shadowing, nested blocks,
arithmetic, comparisons, conditionals, and integer/Word conversion bridges.
Requirement tests verify initializer-before-tail source order and exactly-once
consumption even when a binding is referenced repeatedly.  Adversarial cases
mutate binder owner, identity, spelling, scheme, initializer type,
requirements/coercions, or scope; self/forward references and runtime-dependent
initializers must reject at a located boundary.  Existing runtime-let
regressions confirm that non-integer Core `letE` lowering is unchanged.
