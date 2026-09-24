# ADR-0187: Explicit-identity foundations for ordered Word less-than

- Status: Accepted
- Decision date: 2026-09-08
- Scope: derived resolved bindings and exact Core paths, not canonical `<` support

## Decision

Add `Resolved.Expr.wordLtWithIds leftId rightId left right` as an explicit
builder using existing named lets: bind `left` to `leftId`, then bind `right`
to `rightId`, then compare `rightId > leftId`. The source operand expressions
are neither swapped nor duplicated. Require `leftId` absent from the original
scope when moving the right operand beneath the first binding, and require
`rightId` different from `leftId`. The second ID need not be absent from the
outer scope: its extent contains only the generated comparison of the two
temporary bindings. Inner source binders may shadow these IDs normally.

Prove exact lowering to existing `Core.Expr.wordLt leftCore rightCore`, including
the weakened right Core expression and comparison indices zero/one. Prove
Word/Word-to-Bool typing and explicit-ID renaming compatibility. Independent
forward evaluation uses the two original ordered Word-valued evaluations and
the freshness/difference premises, without typing or runtime-store assumptions.
Reflection additionally requires that the original right expression was
well-scoped, so insertion cannot enable a previously missing variable. Preserve
both child stores and the unsigned result `decide (leftWord < rightWord)`.

Add continuation-aware Core path composition for let binding and the existing
ordered less-than expansion. Its supplied paths evaluate left in the original
environment and the weakened right under the retained left value. Those are
explicit premises, not an unproved general weakening theorem. The exact cost
is both child costs plus nine; two leaves finish at eleven transitions. Keep
the generated binding frames and argument order observable at exhausted budgets.

## Boundaries

This unit does not change the canonical resolver, supported source operators,
Resolved constructors, Core primitives, parser or wire formats. Hidden temporary
allocation would not commute with the current arbitrary identity-map resolution
law, so canonical `<` integration needs a separate hygiene/representation choice.
These builder lemmas do not alone solve the independent correspondence proof for
a hypothetical new Resolved constructor, nor supply an untyped weakening theorem
for arbitrary effectful Core. Existing `>`/`<=`/`==`/`!=` support is unchanged.
Diagnostic proof work remains paused.

## Validation

Independent consumers use actual arbitrary Word operands, nonempty stores and
explicit named scopes. Check exact nested Core, unsigned equality/direction,
second-ID reuse of an outer identity, inner shadowing, safe ID renaming and
both hygiene counterexamples: equal temporary IDs change the result, and a
capturing first ID changes a right reference. An originally missing right
reference also demonstrates why reflection needs original scoping.
Consume exact path costs and genuine-checkpoint resumption without editing
continuations. Register/audit every new public declaration; run focused and
aggregate builds, full tests, and kernel-policy, forbidden-token, and whitespace checks.
Keep files below 300 lines, small exact-path commits and repository-local scratch.
