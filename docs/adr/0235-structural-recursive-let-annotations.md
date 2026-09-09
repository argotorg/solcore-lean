# ADR-0235: Structural annotations in recursive typed let bodies

- Status: Accepted for implementation
- Decision date: 2026-09-09
- Scope: Annotation meaning at the existing recursive body/entry boundary

## Context

ADR-0232 independently interprets canonical structural types; ADR-0233 and
ADR-0234 connect return and parameter annotations to the existing entry.
The recursive typed let/return tree from ADR-0216, already used by entries
since ADR-0222, is the remaining named-only annotation boundary on that path.
Its raw evaluator and cost semantics only inspect annotation presence, not
annotation meaning.

## Decision

Use `interpretStructuralType?` for the recursive binding's written annotation.
Intentionally widen the meaning premises of `TypedLetReturnTreeHasType.binding`
and `TypedLetReturnTreeElaborates.binding` to `StructuralTypeDenotes`.
The annotation-success conclusion of
`elaborateTypedLetReturnTree?_binding_children` likewise becomes structural.
These three public contracts change meaning; all other general theorem
statements remain unchanged.

Connect exact checker soundness with the structural soundness theorem and
semantic extension with the existing structural extension proof. Preserve both
old prefix-to-tree success embeddings with `TypeNameDenotes.structural`.
The older `TypedLetReturnBody` and terminal adapters, old named-only interpreter
and whole-type membership theorem stay untouched. New tree successes do not
imply full optional equality with old prefix checking.

Original empty/singleton/binary type tuples denote Unit/the child/an ordered
product recursively. All leaves use the same original caller-owned first-match
table, preserving explicit nesting and source spans. Structural annotations
still require matching initializer types; they do not change any value or Core
expression or fabricate inhabitants for arbitrary nominal types.

## Preserved scope and runtime contracts

An annotated initializer remains mandatory and is checked/evaluated strictly
in the old inputs, even when its binding is unused. Only the recursive tail sees
the fresh binding. The name must remain unused, and owner-relative allocation
retains the original current scope. Conditional arms are checked completely and
separately in the same original inputs; sibling-local identities may coincide.
No shadowing, inference, default initialization, early-return unwinding, extra
control forms or global allocator is introduced.

Keep raw evaluation, cost, direct evaluator, fuel bound, Core/resolved semantics,
actual stores, continuations and resumption implementations unchanged. Binding
still costs initializer plus tail plus two transitions. Entry acceptance gains
the structural annotation cases through the existing body checker; its compiled
and prepared records still contain only original parameter inputs. Raw selected
success alone does not prove whole-body or entry acceptance.

## Consumer migration and validation

Migrate the original parsed Unit/product lets and the structurally annotated
unused let in the parameter-entry consumer into independent positives with fixed
Core, values, costs and real checkpoints. Keep neighboring shadow and unrelated
negative cases. Rename the obsolete generic tuple-let rejection accurately and
retain its old named-only and old prefix-adapter rejection claims. A product
annotation on its Unit initializer must still be rejected by the new tree.
Legacy fixed named-annotation decomposition statements retain their old meanings
by recovering that original shape rather than weakening their public statements.

Use independent arbitrary-depth structural annotation/body evidence, exact
fresh positions and nominal static types. Exercise strict unused initializers,
branch isolation, opaque actual values, semantic extension, original full entry
records, all fuel thresholds, actual continuation/residual paths and both stores.
Retain missing/unknown/type-mismatched and unsupported annotations, self/forward/
sibling references and bad unselected children at the appropriate boundary.

Run focused/aggregate builds, full tests, public and all-consumer axiom audits,
kernel/metadata/whitespace checks and independent reviews. Keep files below
300 lines and phase commits small where possible. Use repository-local scratch;
leave diagnostics and frozen wire formats unchanged.
