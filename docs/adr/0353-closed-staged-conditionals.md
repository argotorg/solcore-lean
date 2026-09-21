# ADR-0353: Closed staged conditionals

## Status

Implemented as an executable extension of the ADR-0349–0352 closed staging
boundary for expression conditionals whose guard and both branches are closed.
The value selected by this slice is an unbounded staged `integer` or a
canonical `Word`; closed Bool conditionals are admitted recursively while
evaluating guards.

## Context

The existing source checker already retains a typed occurrence for each
expression conditional, and ordinary runtime lowering preserves it as a Core
conditional.  That behavior is insufficient when a conditional produces the
staged `integer` consumed by the existing staged integer intrinsics, or the
closed Word consumed by `wordToInteger`: `integer` has no runtime Core
representation, while this compiler conversion deliberately accepts no
runtime Word input.

The pinned reference revision
`argotorg/solcore@1d490d8bb5f374356f06e0720655496482eb1fb4` takes a deliberately
conservative approach.  `Solcore.Backend.MastEval.evalExp` evaluates a
`MastCond` guard, then branch, and else branch in that order and reconstructs
the conditional rather than selecting only one branch.  Its compile-time
classification likewise requires all three children to be compile-time.
Consequently, treating the unselected branch as dead during Lean staging would
hide runtime dependencies, malformed typed metadata, or literal obligations
which the reference still visits.

Once all three children have instead produced closed host values, the Lean
boundary can safely take the next executable step and select the branch value.
This is intentionally a closed evaluator operation, not general control-flow
evaluation or an optimization of ordinary runtime conditionals.

## Decision

The mutually fuel-bounded staged evaluators accept an expression conditional
only under the following contract:

- the conditional occurrence has no attached requirements or output
  coercions;
- its guard has exact type `Bool`, both branches have the exact requested
  result type, and the enclosing occurrence has that same type;
- the guard belongs to the closed Bool fragment: an exact builtin `true` or
  `false` reference, a transparent group, an `integerEq`/`integerLt`
  comparison over closed staged integers, or a recursively closed Bool
  conditional; and
- both result branches belong to the existing closed staged-`integer` or
  staged-Word fragment, respectively.  Their literal evidence, builtin-call
  metadata, types, arities, requirements, and coercions are revalidated by the
  existing domain evaluator.

Evaluation is eager and source ordered.  It evaluates the guard, then the
written then branch, then the written else branch regardless of the guard's
value.  Only after all three evaluations succeed does it select the appropriate
closed `Int` or Word value.  Consumed requirement identities are concatenated
in exactly that guard/then/else order and remain subject to the existing
declaration-wide exact-once reconciliation.  An invalid or runtime-dependent
unselected branch therefore still produces a located rejection.

Builtin Boolean references are checked for exact identity, spelling, Bool
type, and empty requirements/coercions.  Conditional recursion shares the
strictly decreasing typed-node-table fuel already used by the integer and Word
evaluators, so malformed same-domain and cross-domain cycles terminate with a
located depth error.

Selection happens only when a supported staged consumer demands the value.
An integer result must still reach a supported comparison or conversion before
Core, and a Word result is staged only where the closed Word evaluator is
required.  Ordinary runtime conditionals continue to lower to Core `ifE`; this
ADR does not globally fold them, add a compiler-function identity, or create a
source specialization edge.

## Deferred boundaries

- The next ADR connects let-bound closed staged values and local references.
  This ADR does not introduce an evaluator environment or change lexical
  binder semantics.
- Function parameters, ordinary or indirect source calls, recursion,
  storage-dependent expressions, and general runtime-dependent conditions or
  branches remain outside the closed staging boundary.
- General `comptime<T>` evaluation, statements and block control flow, general
  Word operators, surviving runtime `integer`, output coercions, and custom
  execution of the compiler builtin `Int` trait remain later work.
- Graph-wide ownership/reachability validation, shared-DAG total-work controls,
  and broad inference/lowering metatheory remain shared hardening work.

## Verification

Regressions cover true and false selection for both integer and Word results,
nested groups, comparisons and integer/Word conversion bridges, nested Bool
guards, and signed values before final modulo projection.  Eager-boundary tests
make the unselected branch fail when it contains a runtime local, malformed
metadata, a cycle, or invalid literal evidence, and verify requirement order as
guard then then-branch then else-branch.  Adversarial cases mutate conditional
and Boolean-reference types, spelling, requirements and coercions.  Separate
runtime-conditional regressions confirm that ordinary Core `ifE` lowering is
unchanged.
