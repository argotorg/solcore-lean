# ADR-0261: Recursive ordered Word comparisons

Status: Accepted
Date: 2026-09-09

## Context and reference boundary

ADR-0260 admits recursive children of fixed Word inequality and less-or-equal.
Less-than and greater-or-equal still fall back to the pure adapter because their
existing Core representation contains ordered positional bindings.

The primary reference remains Rust commit
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
`crates/parser/src/parse/expr_pat.rs:307-336` preserves non-associative relational
operators above equality. `crates/hir-ty/src/infer/expr.rs:1136-1179` selects
named lt/ge with expected Bool. `std/std.sol:386-391` defines ge using le(y,x)
and lt using Ord.gt(y,x): these are already-bound parameter values, not swapped
source expressions. `crates/specialize/src/specialize/call_resolver.rs:208-254`
retains original left/right arguments in the resolved call.

Residual `crates/hull/src/emit/emitter.rs:1210-1232` emits greater-or-equal using
iszero around lt. The ordered two-let representation is the existing Lean
profile of ADR-0193/0194, not a claim that Rust emits that same AST. General
operator resolution, backend fault order and Rust execution-cost agreement are
not established by this extension.

## Decision

Recursively check both original Word children in the same caller scope. Less
elaborates exactly to `left.wordLt right`, namely
`letE left (letE (right.weakenAt 0) (binary wordGt (var 0) (var 1)))`.
Greater-or-equal elaborates to Bool negation around that exact expression.
Do not swap source operands, allocate temporary LocalIds, rewrite source nodes,
fold known values or change operator spans, precedence or grouping.

Add less and greaterEqual to independent source typing, elaboration, raw and
cost judgments. Successful raw rules evaluate the actual left Word then the
actual right Word with original environment and real intermediate stores.
Results are unsigned `decide (left < right)` and its Boolean negation. Costs
are both child costs plus nine or eleven respectively. Both generated bindings
and the final positional comparison remain observable in exact machine paths.

An actual wrong left payload can still allow right-child effects before the
positional comparison faults. A left-child fault prevents those effects. A
right-child fault retains earlier left effects. Preserve the actual stored
values, captured environments, saved frames and declared entry result tags;
structural argument typing is not runtime store validation.

## Proof structure

Add one generic letE constructor to the recursive caller fragment. Generalize
its weakening induction over cutoff and insertion/path induction over the
leading caller prefix. For the body, retain the actual bound value ahead of
that prefix. Choose the paired head/body costs before quantifying over the
continuation. No caller lambda, allocation, load/store or recursive tuple
constructor is introduced; actual called closure bodies remain unrestricted.

Build exact ordered paths with the existing two-let cost composition. Insert
the actual left Word into the original right caller using recursive-fragment
paired paths, and identify their cost with the original closed right path.
Reflect Core evaluation through both lets and remove that same insertion to
recover the original right source evaluation. Do not assume the right is in
the smaller call-free Core local fragment.

Retain all fourteen public recursive theorem signatures and old import entry
points. Extend private pure overlap, including raw selected branches whose
unselected original syntax is unsupported. Split the existing cost judgment
into its own definition module reexported by the evaluation module. Keep proof
files below 300 lines with local inversion factoring; do not expose helpers
merely to cross module boundaries. Shared body and explicit-entry definitions,
the finite direct-operator map and older nonrecursive endpoints stay unchanged.

## Validation and remaining scope

Migrate the original recursive `<` and `>=` rejection fixtures without changing
their original source, spans or ordered caller tables. Add independent parsed,
symbolic and actual-entry consumers: original static/raw evidence, separately
fixed Core and manual paths, arbitrary call depth, actual delays/captures,
unsigned boundaries, literal caller insertion, generated-binding checkpoints,
all fuel thresholds, resumed success/fault and ordered cell effects.

Run focused and aggregate builds, full tests, complete public/consumer standard
axiom audits, kernel/metadata/forbidden-token/whitespace checks and independent
reviews before publication. Keep definitions, proofs, consumers and publication
in small separate commits, using repository-local scratch. Paused syntax and
diagnostic work remains untouched. Recursive tuples, source closure construction,
general resolution, early returns, source-only bounds and store safety remain
separate; the Core machine and frozen wire formats do not change.
