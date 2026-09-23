# ADR-0191: Local-right bridge for ordered Core Word less-than

- Status: Accepted
- Decision date: 2026-09-08
- Scope: reuse exact insertion before adding an identity-free resolved comparison

## Decision

Connect existing `Core.Expr.wordLt` to the independent local-fragment insertion
theorems. Prove that two local operands yield a local expansion. Recover from
typing of the expansion its Bool result and the original Word operand typings,
requiring only local-fragment membership of the right operand. Invert the two
lets and positional comparison references, then reflect right typing through
the inserted left Word type (ADR-0189).

Expose raw forward evaluation, inversion and evaluation equivalence for the
original operands in left-to-right order. Require only that the right operand
belongs to the local fragment. Preserve all three actual stores and exact Word
values, without adding type, runtime-world, scoping, freshness or store-equality
premises. The left operand may perform arbitrary Core effects before returning
its Word. Use exact local insertion/reflection (ADR-0188) on the right.

Add a small frontend continuation-path composition corollary. Given original
left and right paths with continuation-independent exact costs, transport the
right closed final path using ADR-0190 and apply the existing ordered comparison
composition (ADR-0187). The result costs `leftCost + rightCost + 9`, preserves
the ordered stores and retains its arbitrary outer continuation unexecuted.

## Boundaries

Keep existing typed Core comparison theorems unchanged. Do not require left
local-fragment membership except to establish whole-expression membership.
Do not remove right membership: an unrestricted right operand can allocate a
closure whose captured environment changes under insertion, changing the exact
stored value even if its returned Word is unchanged.

This is a Core proof bridge, not a new Core primitive, Resolved constructor,
canonical source operator or hidden LocalId allocator. Parser, resolver
identity-map contracts, wire formats, and diagnostic proofs remain
unchanged. Dedicated resolved `<` representation and its source adapter are
subsequent units.

## Validation

Independent consumers exercise membership, typing inversion, both raw evaluation
directions, exact ordered stores and path costs. Cover arbitrary Word pairs,
equal/strict/reversed comparisons, nested right operands and original references.
Include a non-local allocating left operand whose comparison costs sixteen,
with genuine checkpoints showing allocation before right evaluation. Exhibit
the stored-closure counterexample to dropping the right-fragment boundary.

Register and audit every new public API and consumer. Run focused and aggregate
builds, full tests and standard-axiom/kernel/metadata/forbidden-token/whitespace
checks. Keep new proof files below 300 lines, separate small exact-path commits,
use repository-local scratch and preserve paused diagnostic files.
