# ADR-0164: Canonical Word-only binary bitwise semantics

- Status: Accepted
- Decision date: 2026-09-08
- Scope: the explicit-table monomorphic local-expression adapter

## Decision

Extend the canonical local-expression adapter with `&`, `|`, and `^`, using
the existing resolved and Core binary operations `wordAnd`, `wordOr`, and
`wordXor`. Both source operands and the result have Word type. Source evaluation
computes the established exact Word `bitAnd`, `bitOr`, or `bitXor` value.
This is a fixed interpretation within the adapter, not general source overload
resolution, Boolean conversion, or assignment semantics.

Each operation resolves and type-checks both written operands. Evaluation
visits the left operand exactly once and then the right operand exactly once,
threading the left result store into the right evaluation and retaining the
right final store. Unlike `&&` and `||`, these operations never skip the right
operand based on a left value. Zero or maximum masks do not license skipping
an unresolved or wrongly typed expression. Value commutativity does not
authorize reordering operand expressions; ADR-0037's ordered Core semantics
remain unchanged.

Preserve the canonical parser's current grouping: `&` binds more tightly than
`^`, which binds more tightly than `|`; all three levels associate to the left.
The resolver consumes the returned AST without regrouping, constant folding,
or changes to operand order. Operator and outer expression source ranges have
no semantic effect. Decimal and hexadecimal literal operands retain ADR-0163's
strict, non-wrapping Word interpretation.

## Independent proof boundary

Add direct independent resolution, source typing, and source evaluation rules
for the three source operators. Resolution maps to the exact corresponding
resolved binary form; source evaluation uses the Word operations, not an
executable Core-run success premise. Extend all existing soundness,
completeness, uniqueness, type preservation, value-and-store correspondence,
typed existence, sufficient-fuel execution, and no-fault proofs.

Keep raw evaluation independent of whole-expression typing or resolution.
Each evaluated bitwise operand must produce a Word; raw selected-branch rules
inside an operand can still avoid an invalid unselected branch, while whole
checking rejects it. The source/Core evaluation equivalence retains its
existing whole-resolution premise and no additional typing premise.

Unused-name insertion checks both operands and preserves success and failure.
Arbitrary-map structural resolution and injective-map type/evaluation laws
include all three forms. Typed bundled inputs preserve the exact checker
result and complete run result at the same fuel, including suspended states.

## Validation and exclusions

Test arbitrary Word operands against independent rules, mask examples
`0xAA`/`0xCC` producing `0x88`, `0xEE`, and `0x66`, zero/maximum/self cases,
wrong left/right types, missing names, invalid literals, and the absence of
short-circuiting. Complete parsed-source tests must execute the actual checked
Core and verify grouping, precedence, nonempty stores, exact four/five fuel
boundaries for literal pairs, and composition with complement and conditionals.
Exercise unused inputs and ID relabeling without confusing completed-result
preservation with equality of intermediate states after input insertion.

Audit affected public proofs against standard kernel axioms and run focused
and aggregate builds, complete tests, kernel checks, and metadata checks.
Keep proof files below 300 lines. This adds no Core rule, parser behavior,
arithmetic/comparison policy, assignment or declaration semantics, source-wide
allocator, wire format, external endpoint, or capability change.
