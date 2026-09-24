# ADR-0192: Identity-free ordered Word less-than in Resolved expressions

- Status: Accepted
- Decision date: 2026-09-08
- Scope: resolved representation and generic semantic correspondence

## Decision

Add a dedicated `Resolved.Expr.wordLt left right` form. Both original operands
lower in the unchanged original scope, and the result lowers to the existing
`Core.Expr.wordLt` two-let expansion. Generated bindings are positional Core
bindings, not allocated LocalIds. No fresh-name choice or source name lookup is
introduced. Keep the explicit-ID `wordLtWithIds` builder and its hygiene-aware
contracts unchanged as a separate interface.

Extend independent resolved typing with Word operands and Bool result, scope
validity with both original children, and raw evaluation with exact Word operands
evaluated left-to-right through the actual intermediate store. Extend structural
ID renaming by renaming both children. Preserve all existing theorem contracts,
including arbitrary-map structural laws and the existing injectivity requirements
for semantic lookup, lowering and evaluation invariance.

Extend lowering/checker correspondence, type preservation/reflection, evaluation
correspondence, store preservation, determinism and fresh scope insertion/
reflection through the new form. Use the Core local-right bridge (ADR-0191) with
the structural lowering-membership proof; keep Core independent of Resolved.
The new resolved form still lowers into the same eight-form Core local predicate.
Use the existing Core weakening/comparison commutation law for scope extension.

## Boundaries

Do not weaken any theorem with typing, runtime-world, freshness or original-scope
premises that were absent before this extension. Raw evaluation may skip an
unresolved or ill-typed conditional child, whereas whole-expression lowering and
typing retain their original stricter requirements. Duplicate IDs retain nearest
first-match behavior. No new Core primitive, parser, canonical source adapter,
wire change, or source-level temporary allocator is part of this unit.
Canonical `<` remains unsupported until the next adapter unit; keep its existing
negative fixtures unchanged. Diagnostic proofs remain paused.

## Validation

Independent consumers cover the exact Core expansion, original reference
positions, arbitrary Word pairs/stores, equal/strict/reversed outcomes, nested
lets, shadowing, duplicate/same identities, arbitrary structural maps versus
injective semantic maps, and fresh insertion/reflection. Check raw success with
skipped unresolved/ill-typed children against whole lowering/typing rejection.
Consume Core correspondence and exact comparison paths without inventing runtime
inhabitants or hidden names. Keep existing explicit-ID consumers passing.

Register and audit all five new constructors and every changed public definition
or proof, as well as independent consumers. Run focused and aggregate builds,
full tests and standard-axiom, kernel-policy, forbidden-token, and whitespace checks.
Keep new/changed proof files below 300 lines and exact-path commits small; use
repository-local scratch and preserve paused diagnostic files.
