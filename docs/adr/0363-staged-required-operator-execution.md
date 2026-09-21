# ADR-0363: Staged required-operator execution

## Status

Accepted for evidence-selected unary and binary operations in the
Core-representable staged-value domain.  A `Comptime` expression whose typed
node owns operator requirements now executes the selected implementation
method instead of falling back to the builtin operator.  Requirement-free
builtin operations retain their existing behavior.  The arbitrary-precision
bare-`integer` evaluator remains separate.

## Context

ADR-0362 connected typed coercion paths to the ordinary authoritative
`Coerce.coerce` plan, but a unary or binary node with a nonempty requirement
list still failed before evaluation.  This made proof-only predicates and
coercions usable across staged calls while preventing a staged generic body
from consuming its own `T: Add`, `T: BitNot`, or equivalent operator evidence.

Ordinary source-to-Core linking already has the required authority.  Its unary
and binary plans validate the primary predicate, the selected named trait and
method, every method predicate in declaration order, the canonical evidence
tree, the specialized method inputs and result, and the caller-owned
requirement list.  A separate staged operator semantics would duplicate those
choices and could disagree with runtime execution.

## Decision

### Reuse the ordinary checked method plan

The staged linker adapts the existing required-unary and required-binary
plans.  Selection and validation remain entirely in the ordinary plan:

- the first requirement must be the exact primary operator predicate;
- remaining requirements must equal the selected method predicates in their
  declared order, without omission, duplication, or reordering;
- assumption evidence must close to one concrete incoming implementation
  witness;
- the trait and method names must match the operator dispatch profile;
- the selected implementation method must have the exact operand arity and
  specialized input/result types; and
- the detached method body must consume and reconcile only its own
  declaration-local requirements.

The staged adapter adds no fallback from failed method selection to a builtin
operator.  Endpoint types validate the selected method; they do not define its
result.

### Keep traversal and ledger ownership in Source Core

Source Core requests an operator plan only when the typed node has
requirements.  It checks the plan's exact consumed list against the node,
checks the source child types against the declared Core operand types, then
evaluates operands in source order.  Binary evaluation is strictly left then
right.  Actual carrier types are checked again before invocation, and the
returned carrier is checked against both the plan result type and the node's
authoritative source type.

Child requirements precede the operator requirements in the resulting ledger.
The owning staged function reconciles that complete sequence once.  Numeric
requirement IDs from the detached implementation method never cross into the
caller or callee ledger.

### Execute the closed selected application

Already evaluated operands are reified as closed resolved constants and
inserted into the capture-free application built by the ordinary plan.  The
shared staged evidence runner lowers the complete term in an empty local
context, independently infers the expected Core result type, and executes it
with structural fuel and an empty initial store.

Success requires an empty final store and a result representable as Unit,
Bool, canonical Word, or a recursively supported product.  Fuel exhaustion,
machine faults, store changes, type disagreement, and results outside the
carrier reject.  Runtime, staged-call, coercion, and method expansion continue
to share the same active specialization-key stack and decreasing link fuel.

### Preserve requirement-free compatibility

A unary or binary node with no requirements continues to use the established
builtin staged evaluator.  Concrete Word arithmetic/bitwise operations and
the supported Boolean operations therefore do not acquire synthetic trait
evidence merely because required operations are now executable.

## Phase boundary

This decision does not add:

- coercions or required operators to the bare-`integer` staged evaluator;
- arbitrary trait-method invocation outside the existing operator/coercion
  profiles;
- effectful or store-changing compile-time methods;
- indirect calls, mutation, assignment, nominal values, mappings, proxies, or
  indexing;
- value-indexed specialization or cross-occurrence memoization;
- recursive staged execution or selected-branch-only evaluation; or
- broad preservation, soundness, or completeness metatheory.

Marked implementation-method contracts are handled separately by ADR-0364.

## Verification target

End-to-end regressions execute a nonstandard `Add.add` result of `92` through a
nested generic staged relay.  The selected method consumes an ordered `Eq`
method predicate and calls an evidence-bearing helper, exercising concrete
witness forwarding and detached method-local reconciliation.  A second case
executes nonstandard `BitNot.bnot` and returns `94`.

Both results materialize as exact closed constants and preserve a nonempty
caller store.  A requirement-free Word addition and bit-not pair retains the
builtin result, fixing compatibility at the same public preparation boundary.
