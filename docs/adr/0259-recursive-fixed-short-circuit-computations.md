# ADR-0259: Recursive fixed short-circuit computations

Status: Accepted
Date: 2026-09-09

## Context and reference boundary

ADR-0258 supports recursive calls, direct unary/Word binary operations and
conditionals. Logical conjunction and disjunction still use the old pure
fallback, so their children cannot contain these recursive computations.

The primary reference remains Rust commit
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
`crates/parser/src/parse/expr_pat.rs:338-354` makes each logical operator
left-associative, with conjunction binding more tightly than disjunction.
`crates/parser/src/lower/body.rs:205-221` retains both children and operator span.
`crates/hull/src/emit/emitter.rs:1233-1256` expands residual logical BinOp nodes
to conditionals, matching the existing fixed interpretation in ADR-0159.

This is not the general semantics of resolved Rust source operators.
`crates/hir-ty/src/infer/expr.rs:1181-1190` resolves named and/or functions;
`crates/specialize/src/specialize/call_resolver.rs:208-254` turns successful
function resolution into an ordinary two-argument call. The evaluation path
in `crates/specialize/src/evaluate/core.rs:990-993` visits all arguments, and
`std/std.sol:268,280` explicitly records short circuiting as unimplemented.
This change recursively extends the established ADR-0159 fixed profile only.
General operator-function resolution and its differential agreement remain open.

## Decision

Check both original children in the same caller scope and require Bool on both.
Conjunction emits `ifE left right (bool false)`; disjunction emits
`ifE left (bool true) right`. The constants are internal Core literals, not
lookups of source identifiers. Keep original source/operator spans, grouping,
associativity and precedence. Do not synthesize a source conditional or call.

Add logicalAnd/logicalOr to independent typing and elaboration, and
andTrue/andFalse/orTrue/orFalse to independent raw and cost judgments.
For true conjunction or false disjunction, evaluate the original right child
from the left child's actual final store, returning its actual value and store.
Cost is left cost plus right cost plus two transitions.
For false conjunction or true disjunction, never evaluate the right child;
return the fixed Bool and the left child's actual final store. Cost is left
cost plus three transitions, including evaluation of the internal literal.

Only the left actual payload is required to be Bool. A selected right child
may return any actual Core value. In particular, an unchecked actual store
may make a statically Bool right call return Word successfully. Preserve this
value and the entry's declared Bool tag; do not coerce or fault on the right
payload. A non-Bool left payload faults before the right child is reached.
Whole static checking still rejects ill-typed or unknown unselected syntax.
Raw successful skipping does not require whole checking or a call-free premise.

## Proof structure and integration

Keep existing public theorem names, signatures and import entry points.
Move the two existing typing laws to a dedicated typing proof module, reexported
through the old properties module. Move the existing continuation cost law and
private cost views to a dedicated cost execution module, imported by the old
execution module. Derive forward raw correspondence through cost existence and
Core path soundness; retain independent reverse elaboration induction.
Do not publish extra helper laws merely to cross file boundaries.

The existing recursive Core fragment already contains conditionals and pure
Bool literals. Add only the two elaboration membership cases, without new
fragment constructors or insertion/path rules. Reuse shared body and explicit
entry implementations unchanged. Reconcile overlap with the old pure lazy
rules privately, including raw success with rejected unselected syntax.

Move exactly three newly valid rejection fixtures into explicit positive
coverage with their original source and caller tables. Retain all wrong-type,
unknown-name and genuinely unextended-root rejections and old endpoint results.

## Validation and limits

Exercise original parsed precedence, nesting and spans; independent typing,
elaboration and raw/cost evidence; fixed Core outputs and manual paths; arbitrary
call depths and actual body costs; and both selected and skipped right children.
Check actual left/right effects, missing cells, wrong payloads, saved ifBranches
frames, exact fuel boundaries and resumption. Directly consume the existing
recursive, shared body and entry laws, including arbitrary caller-slot insertion.

Keep proof and consumer files below 300 lines. Run focused, aggregate and full
tests, complete public/consumer standard-axiom audits, kernel, metadata and
whitespace checks, and independent reviews before publication.

Expanded comparisons, recursive tuples, source closure construction, general
operator resolution, early returns, source-only execution bounds and arbitrary
store safety remain separate. Parser, Core machine, diagnostics, frozen wire
and metadata semantics do not change.
