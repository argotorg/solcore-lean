# ADR-0176: Word addition in the restricted frontend

- Status: Accepted
- Decision date: 2026-09-08
- Scope: canonical binary addition within the explicit monomorphic Word adapter

## Decision

Extend the existing local-expression adapter with canonical binary `.add`.
Resolve both written operands and retain a `.binary .wordAdd` node in resolved
and Core syntax. The independent source typing rule requires both operands to
have Word type and gives a Word result. This is the fixed interpretation of
addition inside this restricted adapter, not a general overload, numeric
conversion, or whole-language type inference policy.

Reuse existing `Core.Word.add`: addition is modulo `2^256`. Do not introduce
overflow failure or change the Core primitive. Strict literal conversion is
unchanged: a literal outside the Word range remains unsupported even though
adding two accepted Word operands may wrap. Do not fold constants or replace
the actual elaborated binary node with an equally typed result literal.

## Independent evaluation and cost

The source evaluation rule evaluates the left operand from the initial store
to an intermediate store, then the right operand from that store to the final
store. Both results must be Words, and the result is their existing Word sum.
Neither zero nor any other operand bypasses evaluation of the other operand.
Whole expression resolution and typing continue to inspect all written
children, including addition in an unselected conditional branch.

The independent exact-cost rule retains both child costs and adds three Core
transitions. Two leaf operands therefore take exactly five transitions: fuel
four exhausts and fuel five completes. Grouping and source ranges introduce
no transition. Compose with the existing strict binary continuation proof,
checked execution reflection, type safety, and exact fuel contracts.

Extend spelling avoidance, injective identity renaming, and unused-input
invariance to this same shape. Preserve source order, actual Core, and the
existing distinctions between unchanged full states for identity relabeling
and only completion/exhaustion correspondence for input extension.

## Scope and parser boundary

No parser or Core evaluator is changed. The parser already represents addition
with its established precedence and left associativity; compilation must
preserve that exact tree. Multiplication, subtraction, comparisons, assignment,
compound addition assignment, and unary plus remain outside this adapter until
separately specified. Do not infer support for them from binary addition.

Existing return-body, runtime-entry, and value-free compilation interfaces
should acquire addition through their already proved generic expression
bridges, without a new execution endpoint or source-call policy.

## Validation

Update prior tests that treated binary addition as unsupported, retaining
rejection tests for still-unsupported operators. Add independent arbitrary-Word
evaluation, exact costs, wraparound, strict missing/type-mismatched operands,
identity/unused-input transports, and whole-body/entry compilation consumers.
Fully parse arithmetic and mixed bitwise expressions to check grouping,
associativity, precedence, actual Core, argument order, store preservation, and
fuel boundaries. Keep out-of-range literal and unary-plus rejection distinct.
Audit every affected public declaration and new constructor, focused and
aggregate builds, full tests, kernel checks, forbidden proof
tokens, and whitespace. Keep new proof files below 300 lines, preserve existing
user changes, and leave diagnostic proofs untouched.
