# ADR-0257: Recursive conditional computation expressions

Status: Accepted
Date: 2026-09-09

## Context

ADR-0256 extends recursive calls and groups to direct Word binary roots while
retaining the original fourteen recursive proof kernels. Shared bodies and
explicit entries already select this child through ADR-0254 and ADR-0255.
Canonical ternary expressions still use only the old pure fallback.

The fixed primary reference remains Rust commit
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
`crates/parser/src/parse/expr_pat.rs:356-378` retains the original three
children and right-associative nesting. `crates/parser/src/lower/body.rs:279-295`
lowers those same children. `crates/hir-ty/src/infer/expr.rs:174-195` checks a
Bool condition and both branches under the expected type before unifying them.
Keep the established strict Core.Ty interpretation of ADR-0156, not a claim
to implement the reference's general numeric inference or coercion policy.

## Decision

Extend the existing recursive checker at the canonical conditional root only.
Check the original condition and both original branches in the same caller
scope. Require a Bool condition and exact equality of branch types. Emit the
existing Core ifE with the exact three child Cores and their common result type.
Preserve the original outer, question and colon spans; do not synthesize a
source block or return statement. Recursion decreases the original AST size.

Add one conditional constructor to independent typing and elaboration.
Their premises inspect all written children, including the unselected branch.
Keep all existing pure, call, group and direct binary cases and every previous
successful observation. Pure and recursive conditional evidence may overlap;
private compatibility proofs must reconcile them without public shape exclusions.

Add separate true and false constructors to each raw and cost judgment.
Evaluate the original guard from the initial to the intermediate store, require
its actual Bool value, then evaluate only the selected original branch from that
store to the final store. Retain the actual result, including opaque closures
and captures; neither declared tags nor static evidence supply a runtime value.
The exact cost is guard cost plus selected-branch cost plus two transitions.
The unselected branch contributes no raw premise, effect or evaluation cost.

Raw success may therefore coexist with static rejection caused by unknown or
unsupported unselected syntax. Preserve that distinction, including overlapping
old pure derivations that skip such syntax. A wrong actual guard payload faults
before either branch, and a selected branch may fault; this extension introduces
no runtime-world, store-validation or source-only-bound guarantee.

Extend the recursive caller-Core fragment with ifE closure over all three
children. Weakening uses the same caller cutoff in each child. Raw insertion
uses the guard and selected branch only, keeping their actual intermediate
store. Paired paths choose guard and selected-branch costs once before every
continuation, preserving literal observations without identifying checkpoints.

## Contracts and compatibility

Keep all fourteen recursive proof signatures and the direct-operator map law
unchanged. Add seven constructors, not a new checker family or wrapper laws.
Reuse the shared body and entry implementations without edits.
Keep pure compatibility and conditional cost inversion private, and reuse the
existing Core ifTrue/ifFalse path composition at guard plus branch plus two.

Explicitly migrate the two parsed recursive rejection fixtures:
`c ? f(g(x)) : x` and `c ? f(x) : y`. Their original syntax and independent
expected Cores become success assertions. Preserve the same old pure and
nonrecursive-computation rejection, and retain whole rejection for unselected
unknown names or mismatched types. Revalidate old pure conditionals used as
callees/arguments and the raw-success/whole-rejection regression.

## Validation and limits

Use original parsed punctuation and nesting, independent typing/elaboration
and raw/cost derivations, and separately fixed Core/value/store/cost paths.
Exercise both choices, recursive guards and branches, unequal branch costs,
returned/computed callables, actual guard effects, selected-branch effects and
absence of unselected effects. Keep full entry tags, faults and genuine saved
conditional frames, including branch selection immediately after resumption.
Use shared body/entry laws and arbitrary caller insertion directly.

Keep proof and consumer files below 300 lines; split private-heavy proof modules
only if necessary without exporting helper laws merely to cross a file boundary.
Run focused, aggregate and full tests, complete standard-axiom audits, kernel and
whitespace checks and independent reviews before publication.

Expanded comparisons, lazy Bool operator roots, unary operators and tuples do
not gain recursive children in this unit. Source lambda construction, global
source-function resolution, general early returns, unfuelled execution,
source-only fuel bounds and arbitrary-store safety remain separate.
