# ADR-0177: Word subtraction and multiplication in the restricted frontend

- Status: Accepted
- Decision date: 2026-09-08
- Scope: canonical binary subtraction and multiplication for explicit Word inputs

## Decision

Extend the monomorphic local-expression adapter with canonical `.subtract`
and `.multiply`, mapping directly to resolved/Core `.wordSub` and `.wordMul`.
Both independent typing rules require Word operands and produce a Word. Retain
the exact ordered binary Core tree rather than folding constants or replacing
it with an algebraically equivalent expression.

Use existing `Core.Word.sub` and `Core.Word.mul`, both operations on
`Fin (2^256)`. Subtraction underflow and multiplication overflow use modular
results, not new failure conditions. In particular, zero minus one is the
maximum Word. Strict literal conversion is unchanged: an out-of-range source
literal is rejected rather than interpreted modulo the word size.

These are fixed meanings inside the restricted adapter, not a general source
overload or numeric-conversion decision. Unary minus, unary plus, division,
remainder, comparisons, assignment, and compound assignments remain separate.

## Independent evaluation and exact execution

Evaluate the left operand from the initial store to an intermediate store,
then the right operand from that store to the final store. Both values must
be Words. Multiplication by zero still evaluates its other operand; no
algebraic identity bypasses resolution, typing, or execution of written
children. Whole checking retains unselected conditional branches.

Each independent cost is the sum of the two child costs plus three Core
transitions. Preserve arbitrary-continuation step correspondence, exact
completion/exhaustion bounds, type safety, source-store preservation, identity
renaming, and unused-input invariance. Existing body, entry, and value-free
compilation interfaces acquire the new shapes through their generic bridges;
no new runner or source-call mechanism is introduced.

No parser or Core evaluator changes. The existing parser gives multiplication
higher precedence than addition/subtraction and makes each level left
associative. Noncommutative subtraction, explicit grouping, and mixed operator
trees must be preserved exactly by elaboration.

## Proof organization

Keep proof files below 300 lines. Split the existing fresh-input typing law
from the raw evaluation law while preserving their public names and the old
import path. Place their shared fresh-ID/name and distinct-ID lookup support
in a small proof-support module, with any newly public support declarations
explicitly registered and audited. This organizational change must not alter
the assumptions or meaning of either existing law.

## Validation

Use independent arbitrary-Word typing/evaluation/cost derivations and compiled
entry evidence. Check underflow, overflow, zero/one identities without skipping
operands, and noncommutative results alongside the exact pending binary frame
at fuel four and completion at five. Fully parse mixed precedence/grouping and
all tested argument positions, compare actual compiled Core and runtime value
order, and distinguish operation wrap from rejected literals. Update earlier
unsupported subtraction/multiplication fixtures while retaining other operator
rejection. Re-audit every affected public declaration and new constructor,
focused and aggregate builds, full tests, kernel and metadata checks, forbidden
proof tokens, and whitespace. Preserve unrelated changes and leave diagnostic
proofs untouched.
