# ADR-0184: Canonical Word equality in the monomorphic frontend

- Status: Accepted
- Decision date: 2026-09-08
- Scope: strict binary Word equality through existing frontend proof bridges

## Decision

Interpret canonical `Syntax.BinaryOp.equal` (`==`) as the existing resolved and
Core `BinaryOp.wordEq`. Require two Word operands and return Bool with value
`leftWord == rightWord`, matching the existing Core primitive. This is not a
Word-valued comparison flag, truthiness conversion, or polymorphic equality;
Bool, Unit, cells, closures, and nominal values are not equality operands in
this deliberately monomorphic adapter, even when their types agree.

Resolve and type both written operands. Independent raw evaluation remains
strict left to right with explicit initial, intermediate, and final stores.
Cost is the left cost plus the right cost plus three; two reference/literal
operands therefore take five transitions, with the right value and retained
left value in the pending equality application frame at fuel four. Symmetry
of the eventual equality result does not license swapping source operands,
compiled Core children, argument values, or intermediate machine states.

Extend all existing independent resolution, typing, evaluation, cost, name
avoidance, identity renaming, unused-input, store-replay, and structural-bound
proofs. Preserve exact lowering, generic safety and completed-run reflection,
continuation-aware paths, sufficient source bounds, exact residual paths, and
whole return/entry compilation. No new runner, relation wrapper, or evaluation
policy is introduced. Split the oversized raw evaluation module into rules
and proofs while retaining every existing public name and old import path.

## Boundaries

The canonical parser already supports this operator; do not change it. Preserve
non-associative equality, precedence below relational operators and above Boolean
short-circuit operators, and source grouping. `!=`, other comparisons, division,
general overloads, calls, and source mutation remain outside this unit.
Literal interpretation is still strict Word-only and rejects overflow rather
than reducing source literals modulo the Word size. Whole checking still visits
unselected branches. A Bool body under a declared Word return contract is rejected.

## Validation

Independent consumers cover arbitrary Words, equal/unequal values, zero/high-bit/
maximum Words, strict both-side typing and failure, exact fuel-four/five states,
and independently compiled Bool returns with actual typed arguments. Consume
the generic store, source-budget, and genuine-checkpoint resumption interfaces.
Fully parsed tests cover ordered parameter positions over several arities,
different actual values, grouping/precedence, arithmetic and short-circuit guards,
wrong Bool/reference operands, missing/overflowing unselected branches, wrong
declared return type, and non-associative chains. Migrate only the two existing
frontend negative `l == r` fixtures; syntax/wire equality tests remain unchanged.

Register and audit every new public declaration while retaining old names;
run focused/aggregate builds and full tests plus standard-axiom, kernel,
forbidden-token and whitespace checks. Keep proof files below 300
lines and commits small with exact paths. Leave diagnostic proofs untouched.
