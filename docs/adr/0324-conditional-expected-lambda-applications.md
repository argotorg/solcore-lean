# ADR-0324: Conditional expected-lambda application arguments

## Status

Accepted; add one standalone opt-in adapter for an exact singleton call whose
sole argument is an immediate conditional with at least one immediate,
ungrouped direct computation-lambda branch.

## Context

ADR-0317 passes the parameter type inferred from a local callee to a direct
lambda argument. ADR-0319, ADR-0321 and ADR-0323 extend that policy through
specific group boundaries, while ADR-0318, ADR-0320 and ADR-0322 provide
source-disjoint wrappers for the boundaries they cover. None passes an expected
type into a conditional branch. The unchanged recursive checker can infer an
all-ordinary conditional, but it cannot independently infer a direct lambda in
either branch.

Trying the existing entries in sequence would make acceptance order depend on
checker success. Recursively propagating expected types through arbitrary
expressions would also decide grouped, nested-call, tuple, return and inferred-
let policies that are outside this slice. The smallest new boundary is the
original immediate conditional and its two immediate branches.

## Decision

Add `ConditionalExpectedLambdaArgumentApplication` as a separate additive
adapter. A total syntax-only classifier is true exactly for a call with one
argument whose immediate payload is a conditional and for which the immediate
then branch or immediate else branch is a direct computation lambda. The
classifier ignores the callee, names, types, lambda validity, bodies, spans,
diagnostics and all checker results. A global-looking or unresolved callee is
therefore still a recognized candidate and can fail only during elaboration.

Expose the settled source classifiers
`isImmediateExpectedComputationLambda` and
`isConditionalExpectedLambdaArgumentApplication`; the branch relation and
checker `ConditionalExpectedLambdaBranchElaborates` and
`elaborateConditionalExpectedLambdaBranch?`; and the outer relation and checker
`ConditionalExpectedLambdaArgumentApplicationElaborates` and
`elaborateConditionalExpectedLambdaArgumentApplication?`.

Classify each conditional branch independently. An immediate ungrouped direct
computation lambda uses the unchanged expected computation-lambda checker with
the literal parameter type inferred from the callee. Every other immediate
branch uses the unchanged recursive local checker, and its inferred type must
equal that same literal parameter type exactly. Do not reinterpret a selected
direct lambda as ordinary after expected checking fails.

The standalone checker must:

- run the unchanged recursive local checker on the original callee and require
  an exact `Core.Ty.function parameterType resultType`;
- run the unchanged recursive local checker on the original condition and
  require its inferred type to equal `Core.Ty.bool`;
- statically check both original branches at the literal `parameterType`, even
  though runtime evaluation selects only one branch; and
- return the literal
  `Core.Expr.apply functionCore (Core.Expr.ifE conditionCore thenCore elseCore)`
  paired with `resultType`.

The declarative relation retains the complete original call, argument-list and
conditional spans, both punctuation spans, the callee, condition and both
branch sources, the exact branch-selection evidence, all four child
elaborations, the literal callee parameter and result types, and the exact Core
result. Grouping is not inserted, removed or normalized anywhere.

Once the complete source shape is recognized, every callee, unary-type,
condition, Bool-type, lambda-header, lambda-body, ordinary-branch lookup or
ordinary-branch exact-type failure is final. Return `none`; do not invoke
ADR-0323, ADR-0322 or another checker, switch a branch policy, rebuild the AST,
use `Option.orElse`, or otherwise dispatch from semantic success.

Expose exact executable/declarative correspondence for the branch checker and
outer checker, exact outer absence, Core typing for both relations, a theorem
that every outer evidence term is classified, and complete provenance. These
proofs must reuse the unchanged recursive and expected-lambda correspondence
and typing laws. They must not reconstruct source semantics from `Core.infer?`
or from the final Core term alone.

## Prototype and independent consumers

The independently compiled 299-line prototype fixes these APIs with finite
pattern matching and no new recursion. Port it without adding a recursive,
fuel-based or generated partial helper. Inventory its 13 authored public roots
and every generated declaration; all owned declarations must remain safe and
total, with no unexpected axiom closure or generated public proof leak.

A symbolic consumer covers all three source partitions: lambda/ordinary,
ordinary/lambda and lambda/lambda. It constructs the callee, Bool condition,
both exact branch derivations and the outer relation before using checker
correspondence. The fixture keeps a callee of type
`(Word -> Word) -> Word`, an ordinary `Word -> Word` branch, duplicate names,
foreign owners, sparse indices, opaque runtime values and a nonempty store.
It proves the literal Core expressions, exact parameter indices, Core typing,
classification and full provenance.

The symbolic runtime proof covers both Boolean choices for all three branch
partitions. Every execution returns `Word 7` and preserves the initial nonempty
store literally. Recognized failures cover a non-Bool or unresolved condition,
bad lambda headers on either side, a bad lambda body, an ordinary type mismatch,
an unresolved ordinary branch, and a non-function or unresolved callee. The
consumer also fixes false-classifier boundaries, the frozen ADR-0322 results
for all-ordinary conditionals and direct, one-group and two-group lambdas, and
the ADR-0323 result for depth-three and deeper group spines. Include an
independent deeper finite group control, without relying on the recursive
checker's current inability to infer direct lambdas.

A parsed consumer checks clean lexer and parser diagnostics, EOF, equality to a
hand-built complete AST and every nested span for these three sources:

- `apply(flag ? lam(x){return x;} : ordinary)` has call `0..42`, callee
  `0..5`, arguments `5..42`, conditional `6..41`, condition `6..10`, question
  `11..12`, then lambda `13..30`, colon `31..32` and else identifier `33..41`.
  The lambda keyword, parameters, parameter, body, statement and result spans
  are `13..16`, `16..19`, `17..18`, `19..30`, `20..29` and `27..28`.
- `apply(flag ? ordinary : lam(x){return x;})` has call `0..42`, callee
  `0..5`, arguments `5..42`, conditional `6..41`, condition `6..10`, question
  `11..12`, then identifier `13..21`, colon `22..23` and else lambda `24..41`.
  Its lambda subspans are `24..27`, `27..30`, `28..29`, `30..41`, `31..40`
  and `38..39` in the same order.
- `apply(flag ? lam(x){return x;} : lam(y){return y;})` has call `0..51`,
  callee `0..5`, arguments `5..51`, conditional `6..50`, condition `6..10`,
  question `11..12`, then lambda `13..30`, colon `31..32` and else lambda
  `33..50`. The then subspans are the first fixture's lambda subspans; the else
  keyword, parameters, parameter, body, statement and result spans are
  `33..36`, `36..39`, `37..38`, `39..50`, `40..49` and `47..48`.

For all three parsed modes and both Boolean choices, fuel 13 must be exactly
`outOfFuel`; fuel 14 must finish with `Core.Value.word 7` and the exact initial
nonempty store. The parsed consumer independently establishes the static
relation, checker result, typing and provenance before running this six-case
machine boundary. Its negative and preservation tables mirror the symbolic
consumer, including an all-ordinary conditional that remains outside this
standalone classifier.

## Preserved and deferred boundaries

ADR-0317 through ADR-0323, the recursive checker, canonical source unions and
every existing public entry remain unchanged. This ADR adds no wrapper. Any
future unified entry must dispatch only from the original source: conditional
classifier true to ADR-0324, otherwise group-spine classifier true to ADR-0323,
and otherwise to ADR-0322 or an exactly equivalent already-unified old entry.
Each recognized true result is final; checker failure never permits fallthrough.

There is no expected-type propagation through a group around a branch lambda,
a group around the whole conditional, a nested conditional or call, tuples,
returns, inferred lets, typed bodies, multiple arguments or global resolution.
A conditional whose only lambda-bearing forms are grouped or nested is
classifier-false. If its other branch is an immediate direct lambda, the outer
source is recognized, but the grouped or nested branch is ordinary-selected and
receives no expected propagation. An all-ordinary conditional is likewise
classifier-false and this standalone checker returns `none`, while frozen
ADR-0322 retains its unchanged recursive success. Parser and diagnostic proof
work remains paused.

The production module and each consumer must remain below 300 lines, with
exactly three authored public roots per consumer. Keep fixtures and proof
helpers private; audit all compiled owned declarations for safety, totality,
generated public leaks and the allowed axiom closure. Use no admitted theorem,
unsafe or partial definition, generated partial helper, fuel-based source
checker, or postulated termination fact. Run masked source-policy scans,
focused and aggregate builds, the full tests, both independent consumers,
declaration ownership and public-axiom audits. Keep every commit within 300
changed lines and preserve the paused parser and diagnostic files.
