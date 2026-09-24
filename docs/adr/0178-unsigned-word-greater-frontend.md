# ADR-0178: Unsigned Word greater-than in the restricted frontend

- Status: Accepted
- Decision date: 2026-09-08
- Scope: canonical strict greater-than for explicit Word inputs

## Decision

Extend the monomorphic expression adapter with canonical `.greater`, lowering
directly to resolved/Core `.binary .wordGt left right`. Both written operands
must have type Word; the result has type Bool. Use the existing strict unsigned
ordering on `Core.Word` (`Fin (2^256)`), returning `decide (leftWord > rightWord)`.
Equality yields false, and the maximum Word is greater than zero. Do not use
signed interpretation, a numeric flag result, or a truthiness conversion.

Retain the exact ordered binary tree without folding or swapping operands.
This is the first arithmetic comparison in the restricted source adapter, not
a decision about general overloaded comparisons. It allows computed Word
results to feed existing Boolean conditions and short-circuit forms.

Other comparisons remain outside this unit: `<`, `<=`, `>=`, `==`, and `!=`.
Only `wordGt` and `wordEq` are direct Core comparison primitives. In particular,
`<` and `>=` must not be implemented by swapping operand expressions; their
existing derived Core builders preserve order through intermediate bindings.
No new Core primitive, parser rule, source binder, or equality policy is needed.

## Independent semantics and proofs

Add structural resolution, source typing, raw evaluation, independent cost,
and name-avoidance constructors. Raw evaluation requires two Word results,
evaluates left from initial to intermediate store and then right to final
store, and returns the unsigned Boolean comparison. Cost is both child costs
plus three transitions, including when the values are equal. Whole resolution
and checking still inspect every written child and every conditional branch.

Extend the existing exact resolution/type/value/store correspondence, safety,
continuation-aware Core steps, fuel bounds, identity renaming, and unused-input
laws without weakening their assumptions or conclusions. Existing body,
value-free compilation, and runtime entry bridges then apply with a Bool result.
The declared result type must still match; Word-returning comparison bodies
must not compile merely because their operands are Words.

Keep new and changed proof files below 300 lines. Separate the existing range,
spelling, and grouping resolution laws into a small module if needed, preserving
all public names and the old import path. Re-audit moved declarations as well
as new ones; avoid duplicate definitions or circular imports.

## Validation

Construct arbitrary-Word independent typing, evaluation, cost, compilation,
and preparation evidence. Verify the exact suspended right value and pending
left-valued `wordGt` frame at fuel four, and completion at precisely five.
Test unsigned high-bit/max boundaries, equality, reversed order, wrong operands
and return types, and whole-check rejection in skipped branches.

Fully parse expressions and complete function declarations. Preserve canonical
arithmetic/bitwise/comparison/Boolean precedence, explicit grouping, and the
non-associative comparison boundary. Check every tested source parameter pair
against actual open Core, supplied argument order, and runtime states. Include
computed arithmetic conditions with independently determined exact costs.

Run focused and aggregate builds, full tests, public standard-axiom audits,
kernel checks, forbidden proof-token and whitespace checks. Commit
small exact-path units; preserve unrelated diagnostic work without extending it.
