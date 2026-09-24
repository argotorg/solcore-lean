# ADR-0185: Canonical Word inequality through ordered equality and negation

- Status: Accepted
- Decision date: 2026-09-08
- Scope: derived Word inequality in the monomorphic frontend

## Decision

Interpret canonical `Syntax.BinaryOp.notEqual` (`!=`) as the resolved tree
`.unary .boolNot (.binary .wordEq left right)`. Its exact Core lowering is the
existing `Core.Expr.wordNe` expansion, not a new primitive or an operand swap.
Require Word operands and produce Bool `!(leftWord == rightWord)`. Resolve and
type both written children, including children under unselected branches.
Matching non-Word types do not license polymorphic inequality.

Independent source evaluation is strict left to right with explicit intermediate
and final stores. Its cost is the sum of both child costs plus five: three for
binary equality and two for the enclosing Boolean negation. Reference/literal
pairs take seven transitions. At fuel five the right Word is pending in the
equality frame beneath the negation frame; at six the equality Bool remains
pending under negation; only at seven is the final inequality Bool returned.
Negation cannot be folded away merely because the two values are known or equal.

Extend independent resolution, typing, evaluation, cost, name avoidance, identity
renaming, unused-input, store replay and source fuel-bound proofs. Retain exact
Core shapes, continuation-aware paths, completed-run reflection, generic safety,
whole return/entry compilation and genuine-checkpoint residual guarantees.
The structural source bound uses both child bounds plus five. Keep the existing
public APIs and import boundaries; no wrapper runner or fabricated argument is
introduced. Split proof modules if needed to keep each below 300 lines.

## Boundaries

The canonical parser already accepts non-associative equality/inequality at its
specified precedence; it is unchanged. Division, remainder, other comparisons,
source calls, mutation, general overloads and polymorphic equality remain outside
this unit. Existing strict Word literal, explicit identifier binding and return
contract policies are unchanged. Diagnostic proof work remains paused.

## Validation

Independent consumers check arbitrary equal/unequal Words, exact nested lowering,
seven-step paths and the distinct five/six-step checkpoints, resumed execution,
store replay, structural bounds, whole typing failures and independent Bool entry
compilation using actual ordered typed arguments. Parsed consumers check ordered
parameter positions, zero/high-bit/max values, precedence/grouping, arithmetic and
short-circuit guards, wrong operand and declared return types, invalid unselected
branches and non-associative chains. Migrate only existing semantic negative
fixtures for newly supported `!=`, preserving unrelated parser/wire tests.

Register every new public declaration and audit all changed semantic interfaces
and consumers for standard axioms only. Run focused and aggregate builds, full
tests, kernel-policy, forbidden-token, and whitespace checks, and small exact-path
commits. Place scratch files inside the repository's ignored working directory.
