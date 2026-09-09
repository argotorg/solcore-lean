# ADR-0256: Strict direct binary recursion in local computations

Status: Accepted
Date: 2026-09-09

## Context

ADR-0253 admits recursive calls and groups around pure leaves. ADR-0254 and
ADR-0255 now share body and explicit-entry contracts across child semantics.
Extending this same child preserves those contracts without duplicating body,
entry, fuel or resumption theorem families.

The primary reference is Rust commit
`18fd9f75d290df0070e21ee56e0a5691f232596f`,
`crates/hir-ty/src/infer/expr.rs:1077-1188`. It dispatches arithmetic and bit
operators through their classes and supplies Bool expectations for Eq/Ord.
This unit extends the already established fixed Word interpretation, not
general operator-class resolution. The canonical AST and its operator spans
remain the only source representation.

## Decision

Extend RecursiveLocalComputation in place with strict binary recursion for
ten directly lowered operators: addition, subtraction, multiplication,
division, modulo, bitwise and/or/xor, greater-than and equality.
An independent finite relation connects these source tags to their existing
Core binary operators. A separate executable map has one correspondence law.
Neither relation is defined as checking success or by Core evaluation.

For an admitted operator, recursively check both original children in the
same caller scope. Their types must equal the Core operator's left/right
types; retain the exact binary Core and result type. All these operands are
Word, with Bool results only for greater-than and equality.
Unadmitted operator roots retain the old pure fallback, as do other roots.
Recursion still decreases the original AST size.

Extend the independent typing and elaboration judgments with one binary
constructor each. Preserve original outer/operator spans, original children,
first-match lookup, positional layout and exact result type. Existing pure
derivations may overlap new binary derivations. Reconcile that overlap in
private proofs rather than requiring public non-binary or call-free premises.

Extend raw and exact-cost judgments separately with one binary constructor
each. Evaluate the original left child from the initial to the intermediate
store, then the right child from that store to the final store. Apply the
actual Core operator to the two actual returned values only afterward.
Success requires that application to return the stated result.
The exact cost is left cost plus right cost plus three transitions.
No type, checker, runtime-world or early payload gate enters these rules.
A wrong left payload does not suppress a successful strict right child's
effects; a faulting left child still prevents reaching the right child.

Extend the recursive caller-Core fragment by binary closure. Both operands
weaken at the same caller cutoff. Literal raw insertion and paired paths keep
the actual returned values, stores, called bodies and captures. Choose child
costs before quantifying over continuations and use the existing binary path
composition. The fragment does not introduce source lambda construction.

## Contracts and compatibility

Retain the signatures of all fourteen ADR-0253 proof kernels, including pure
embeddings, joint raw determinism and exact supplied-cost Core correspondence.
The finite operator map adds only its one correspondence kernel. Keep helper
case analyses private and avoid per-operator public wrapper laws.
Reuse all ADR-0254 body and ADR-0255 entry definitions and proofs unchanged.

Preserve every previously accepted recursive observation. Explicitly migrate
the three recursive-profile addition rejection fixtures in parsed expression,
body and compilation consumers to independent exact positive assertions.
Do not merely delete them. Older pure, root-application, mixed-body and
ADR-0252 entry endpoints remain unchanged, including their corresponding
nested-under-operator rejection.

Old pure raw judgments may skip unsupported descendants under lazy forms.
Do not replace this with a global syntactic restriction or infer static
acceptance from raw success. Division/modulo by zero retain the existing
Word zero results, not a newly invented fault.

## Validation and limits

Use original parsed operators and spans, fixed Core trees and independent
typing/elaboration/raw/cost certificates. Cover all ten tags, unequal nested
call operands, modular arithmetic and zero divisors, Bool comparisons,
pure/new overlap, caller insertion, actual reader/writer order, and a wrong
runtime payload whose strict right operand changes the store before fault.
Check complete entry results and genuine checkpoints without declaring
structural argument typing sufficient for store safety.
Consume the existing shared body and entry laws directly for the new trees.

Keep new proof and consumer files below 300 lines, separate definitions,
proofs, consumers and publication commits, and run focused, aggregate and full
tests, all-public/all-consumer standard-axiom audits, metadata/kernel/whitespace
checks and independent reviews before publication.

Expanded comparisons (<, <=, >=, !=), lazy Bool operators, tuples, unary and
conditional roots do not gain recursive children here. Source lambdas,
global source-function resolution, general early returns, source-only fuel
bounds, unfuelled execution and arbitrary-store safety remain separate.
