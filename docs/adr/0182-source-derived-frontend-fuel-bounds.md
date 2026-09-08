# ADR-0182: Source-derived fuel bounds for the restricted frontend

- Status: Accepted
- Decision date: 2026-09-08
- Scope: computable value-independent upper bounds on existing Core costs

## Decision

Add a total structural `localExpressionFuelBound` on canonical expressions.
Identifiers and literals have bound one, grouping retains the child bound,
supported unary operators add two, and supported strict binary operators add
both child bounds and three. Short-circuit Boolean forms use the left bound
plus the maximum of one and the right bound, plus two. Conditionals use the
condition bound plus the maximum branch bound, plus two. Unsupported forms
have bound zero; that placeholder is never evidence of acceptance or execution.

Prove directly from every independent successful cost derivation that the cost
is at most this bound. Keep raw selected-branch-only evaluation: an unresolved
or unsupported unselected branch does not acquire an evaluation premise.
The maximum with one accounts for the inserted Boolean Core constant on a
short-circuit path even when the unselected source has bound zero.

Lift the bound to singleton return bodies (bare return one, expression return
its bound, unsupported body shapes zero), independently prepared function costs,
and checked execution. Whole typing or preparation remains necessary to obtain
an evaluation; the bound alone is not a checker. Prove termination with a typed
value and unchanged store at any fuel at least the structural bound. Proven
compiled Core requires matching actual typed arguments, not an assumed inhabitant
of every declared type. The bound is independent of those argument values.

## Boundaries

This is a conservative upper bound on existing Core transitions, not an exact
or minimal cost, a gas estimate, or a bound on parsing, checking, lookup, numeric
decoding, runtime allocation, or elapsed time. Different argument values can
select different shorter paths. Source grouping and literal text length add no
Core transitions. Unsupported syntax, missing names, and invalid whole branches
remain rejected even if a numerical bound is available. No general source call,
loop, store effect, or arbitrary Core termination theorem is introduced.

Do not change the evaluator, runtime endpoint, compilation, relations, parser,
literal policy, or language profile. This unit gives existing existential
termination and exact-cost proofs a source-computable sufficient fuel budget.

## Validation

Independent consumers cover all constructor families, conservative versus exact
branch costs, the inserted short-circuit constant, raw skipped unsupported
branches versus whole rejection, and arbitrary typed entry arguments. Fully
parsed cases compare the structural bound with known path costs, run every
matching argument case at and above the bound, and preserve zero-budget
unsupported-body rejection. Register and audit every public declaration, keep
proof files below 300 lines, run focused/aggregate builds and full tests, and
retain standard-axiom, kernel, metadata, forbidden-token and whitespace checks.
Use small exact-path commits and leave diagnostic proofs untouched.
