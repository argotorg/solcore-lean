# ADR-0190: Exact-cost transport for local Core insertion

- Status: Accepted
- Decision date: 2026-09-08
- Scope: continuation-local paths for the independent eight-form Core fragment

## Decision

Given `Core.Expr.LocalFragment` and successful evaluation under
`leading ++ suffix`, construct original and positionally weakened paths under
`leading ++ inserted :: suffix` with one common cost. Quantify the shared cost
before arbitrary continuations, so each child path can be instantiated with
the correct original or shifted frames and saved environments. Retain the exact
result value and both stores, with no typing, runtime-world, freshness or scope
premise. Extend the retained prefix with the actual bound value beneath a let.

Prove the paired paths directly by structural fragment induction and inversion
of Core evaluation. Leaves cost one; unary primitives add two, binary primitives
add three, lets add two, and conditionals add two to their condition and selected
branch costs. Use small private Core-local path composition helpers, without a
Core dependency on Frontend cost helpers or a new cost judgment.

From a supplied closed final `Steps n` path, extract evaluation, construct the
paired paths and identify the common cost with `n` using final-path uniqueness.
Expose exact forward and reverse transport into any retained outer continuation,
and an equivalence between closed final paths at the same cost. Reverse transport
uses the existing independent evaluation insertion reflection (ADR-0188).

## Boundaries

Use final-path length uniqueness only with empty-continuation final endpoints.
Do not assume uniqueness of lengths between arbitrary intermediate states.
The arbitrary outer continuation is retained, not executed or rewritten by the
transport theorem. Original and shifted entry/intermediate states are generally
different. Do not infer equality of full runner results when they are exhausted.

Existing closures and cell references may be returned as literal values; closure
creation/calls and cell access remain outside the fragment. All syntactic
children belong to the fragment even when a conditional skips one. An untyped
skipped branch may belong structurally and need not execute or contribute cost.
Canonical `<`/`>=`, resolver ID allocation, parser and diagnostic proofs remain
separate. Existing fuel and checkpoint-resumption APIs can consume the paths
without adding a new runner semantics.

## Validation

Independent consumers cover all eight forms, arbitrary retained prefixes,
nested lets, both selected branches, arbitrary returned values and stores, and
an actual Resolved lowering bridge. Test exact costs, same completion/exhaustion
thresholds, different genuine checkpoints and unchanged nonempty continuation
frames. Consume forward transport, reflection and closed-path equivalence.

Register and audit every new public declaration and consumer. Run focused and
aggregate builds, full tests, and standard-axiom, kernel-policy, forbidden-token,
and whitespace checks. Keep new proof files below 300 lines and commits small; use
repository-local scratch and preserve all paused diagnostic files.
