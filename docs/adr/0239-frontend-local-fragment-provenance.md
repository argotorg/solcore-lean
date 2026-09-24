# ADR-0239: Exact frontend provenance into the local Core fragment

- Status: Accepted for implementation
- Decision date: 2026-09-09
- Scope: Proof-only structural bridges for existing expressions, bodies and entries

## Context and reference boundary

The existing `Core.Expr.LocalFragment` is an independent syntax judgment, not
a typing or execution premise. It includes constants, positional variables,
pairs, unary/binary operations, lets and both branches of conditions. It excludes
closure creation/calls, cell operations and other Core forms. A variable may
nevertheless return an actual pre-existing closure or cell reference unchanged.

`Resolved.Lowers.localFragment` already covers exact lowering, including ordered
comparison expansion. Frontend expression elaboration and exact singleton,
terminal-tree and recursive typed-let body provenance do not yet expose that
structural consequence. Compiled and prepared records are data only; their
fields, or even a typing proof for an arbitrary same-typed Core, do not establish
source provenance or membership.

This bridge is useful before strict expression-statement sequencing. At the
fixed canonical reference `argotorg/solcore-rs` commit
`18fd9f75d290df0070e21ee56e0a5691f232596f`, parser
`crates/parser/src/parse/stmt.rs` retains the expression and trailing-semicolon
flag; `crates/hir-ty/src/infer/stmt.rs` checks an expression statement without
requiring its expression type to be Unit, and `crates/specialize/src/specialize/body.rs`
retains `MonoStmtKind::Expr`. However, `crates/specialize/src/evaluate/core.rs:397–427`
may eliminate a known value after processing its effects. Existing Lean exact
Core transition costs are not claims about optimized Rust transition counts.
This decision adds no expression-statement acceptance or new cost policy.

## Decision

Add a body-level proof module deriving local-fragment membership from:

- a successful exact local-expression elaboration;
- independent singleton-return elaboration;
- independent terminal-return-tree elaboration;
- independent recursive typed-let/return-tree elaboration, including both written
  and inferred initialized bindings.

Use structural evidence and the existing Resolved lowering bridge, not execution
correspondence, a manufactured runtime inhabitant or a same-type replacement.
Every original child, including an unselected arm, must contribute its exact
lowered Core membership. Preserve original source, tables, scopes, IDs and types.

Add a separate entry-level proof module projecting the same result from
independent compilation and preparation, with successful executable compilation
and preparation corollaries. Body-level imports must not depend on entry modules.
Avoid redundant body-checker wrappers: their existing elaboration soundness
theorems compose directly with the new independent membership results.

No existing definition, constructor, generic theorem statement, source rejection,
record layout, caller policy or execution function changes. The bridge alone
asserts neither evaluation nor valid indices, typing, totality, store independence
for arbitrary Core, or completion while pending continuation frames remain.

## Independent consumers and verification

Use independent original-source elaboration, explicit Core expectations and
hand-composed execution paths to consume existing positional insertion laws.
Check retained prefixes and nested lets, arbitrary inserted types/values,
exact costs and continuation endpoints, and both directions of insertion.
Nominal static types need no inhabitant; actual typed opaque values remain
unchanged and are not allocated, inspected or invoked.

Complete parsed bodies and entries must retain original ranges and annotation
absence, parameter-only inputs and argument order. Compare genuine checkpoints
and residual completion separately: successful exact-cost transport does not
equate the original and inserted suspended environments or continuations.
Include invalid unselected children, raw-selected/whole-check separation,
same-typed nonlocal Core and arbitrary-record counterexamples.

Keep proof/test modules under 300 lines, separate proof/consumer/publication
commits and repository-local scratch. Run focused and aggregate builds, full
tests, all public and consumer axiom audits, kernel-policy and whitespace checks, and
independent reviews. Diagnostics, Core/Resolved definitions, parser, wire formats
and all accepted/rejected source policies remain unchanged.
