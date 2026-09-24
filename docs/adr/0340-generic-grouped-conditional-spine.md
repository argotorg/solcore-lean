# ADR-0340: Generic grouped-conditional spine

## Status

Accepted for staged implementation.  The first two production deliveries are
the total source-spine foundation and a source-disjoint depth-eight-or-more
standalone semantic adapter.  Independent consumers, registration and the
selecting wrapper remain later, separately auditable steps.

## Context

ADR-0324 checks an immediate conditional application argument whose immediate
branches include an ungrouped direct computation lambda.  ADR-0326 through
ADR-0338 repeat that unchanged contract at exact whole-expression group depths
one through seven, and ADR-0325 through ADR-0339 give those exact adapters fixed
source-first precedence.  ADR-0339 is therefore the complete frozen entry for
depths zero through seven.

Adding exact depth eight and then repeating the same standalone/wrapper staircase
would duplicate a source traversal and an almost identical proof surface for
every further finite depth.  ADR-0323 already demonstrates an admissible generic
solution for direct-lambda group spines: retain the original terminal and every
original span, and implement the recursive peel with an explicit well-founded
fixpoint so every compiled declaration remains total.

The grouped-conditional spine must be reusable, but making it generic must not
reclassify any source already owned by ADR-0317 through ADR-0339.  Structural
recognition and semantic selection therefore have different minimum depths.

## Decision

Add `ConditionalGroupSpine`, a source-evidence relation from an original
expression to an outermost-to-innermost list of group spans and the original
immediate terminal conditional.  Its constructors are:

1. an immediate conditional with an empty span list; and
2. one original group node prepended to the child's span list.

The relation describes every finite depth, including zero.  It neither performs
elaboration nor selects a frontend route.  The terminal must be the immediate
conditional reached after the maximal consecutive group prefix; do not rebuild,
normalize or rewrite any source node or span.

Expose `peelConditionalGroupSpine?` as the corresponding executable analysis.
Copy ADR-0323's total-recursion strategy: define it with
`WellFounded.fix (measure sizeOf).wf`, justify only the strict descent from a
group node to its child, and prove soundness and completeness by well-founded
induction and induction on the relation.  Do not use `partial`, `unsafe`, fuel,
`termination_by`, an authored axiom or a generated/public `_unsafe_rec` helper.

The foundation module is
`Solcore/Frontend/ConditionalGroupSpine.lean`.  It imports only
`Solcore.Syntax.Term` and exposes exactly five authored public roots:

1. `ConditionalGroupSpine`;
2. `peelConditionalGroupSpine?`;
3. `peelConditionalGroupSpine?_conditional`;
4. `peelConditionalGroupSpine?_group`; and
5. `peelConditionalGroupSpine?_iff`.

Keep the directional soundness and completeness lemmas private.  The reviewed
production-shaped prototype is about 85 lines and compiles to 25 owned
declarations, 23 public and two private, with no unsafe, partial or `_unsafe_rec`
declaration.  These counts are audit targets, not permission to add unrelated
surface.

The foundation alone changes no elaboration result or dispatch.  It is the first
production implementation required by this ADR.  The standalone adapter below
is the second delivery; neither delivery changes the current ADR-0339 entry.

## Depth-eight-or-more semantic adapter

Add a production module using the foundation to recognize a singleton call
whose argument has a `ConditionalGroupSpine` with `8 <= spans.length`, ending at
an immediate conditional for which at least one immediate branch satisfies the
unchanged `isImmediateExpectedComputationLambda` predicate.  The minimum belongs
to the semantic classifier and relation, not to the generic spine foundation.

The classifier must be source-only and false for every depth zero through seven.
It must also be false for an all-ordinary terminal conditional, for grouped-only
or nested-only lambda branches, for a spine ending in a direct lambda or another
non-conditional expression, and for zero, multiple or non-call arguments.

The adapter infers the original callee and Bool condition with the unchanged
recursive local checker and checks the two original immediate branches with the
unchanged ADR-0324 branch checker at the literal inferred parameter type.  It
returns exactly

```text
(.apply functionCore (.ifE conditionCore yesCore noCore), resultType)
```

All source groups are Core-transparent only in that result.  The declarative
relation retains the call and argument-list spans, the ordered complete group
span list, the original conditional and punctuation spans, every child, the
minimum-depth proof and all complete child derivations.  Correspondence,
absence, Core typing, classification and provenance must be exact.  Once the
generic classifier is true, semantic failure is final; do not shorten the
spine, retry an exact-depth adapter, inspect ADR-0339, or use `Option.orElse`.

## Compatibility and future selection

ADR-0317 through ADR-0339 are frozen.  Do not edit their classifiers, relations,
checkers, theorems, imports or precedence wrappers.  In particular, do not
replace the exact-depth zero-through-seven implementations with the generic
extractor, even if an extensional proof could later be written.

The depth-eight threshold makes the future generic semantic partition disjoint
from every frozen grouped-conditional partition.  Independent consumers must
prove the generic classifier false at depths zero through seven and prove that
the complete current ADR-0339 `Option` is preserved on that entire false side.

Reachability is a later wrapper decision, expected as ADR-0341:

```text
if generic-depth-eight-or-more-classifier(source)
then exact generic adapter Option(source)
else exact ADR-0339 Option(source)
```

That wrapper must evaluate the classifier once, return the selected complete
child literally, and make classifier-selected `none` final.  The foundation and
standalone adapter do not themselves modify the current local-application entry.

## Verification stages

Deliver in small commits, each within the repository's 300-changed-line limit:

1. record this decision;
2. add only `ConditionalGroupSpine.lean`, then run focused normal, trust-zero and
   warning-as-error builds plus declaration ownership, safe/total, `_unsafe_rec`,
   axiom-closure and source/olean parity audits;
3. add the standalone depth-eight-or-more classifier, relation, checker and exact
   theorem surface, reusing the foundation without changing it;
4. add an independent symbolic consumer covering depths eight, nine and a deeper
   finite spine, selected failures, and complete depth-zero-through-seven
   preservation;
5. add an independent parsed consumer with proof-producing AST/span equality and
   unchanged conditional fuel 13/14, result and store;
6. register only the completed standalone adapter and consumers, update status
   documents, and run focused/full builds, all tests, kernel checks and
   paused-file verification;
7. specify and implement the generic-first wrapper under a separate ADR after the
   standalone adapter is complete.

The initial implementation may stop safely after step 3.  Until independent
consumers and registration land, do not claim that generic grouped-conditionals
are reachable through the current local-application entry or that ADR-0340 is
complete.

## Non-goals

This ADR does not add an exact-depth-eight standalone staircase adapter, alter
any exact-depth implementation, or prove their replacement by the generic
spine.  It does not add fallback based on checker success, source normalization,
span rewriting, arbitrary-expression group transparency or recursive traversal
inside the terminal conditional's branches.

Grouped direct lambdas and nested-call lambdas in branches retain ADR-0324's
unchanged immediate-branch policy.  Broader propagation through nested calls,
tuples, returns, inferred lets, typed bodies, multiple arguments or global
entries remains separate.  Source unions, source closures, parser grammar,
diagnostic proofs, runtime Core forms, runtime-world safety, cost models, wire
formats and backend guarantees are unchanged.  Parser and diagnostic proof work
remains paused while frontend semantics stays prioritized.
