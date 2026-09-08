# ADR-0209: Static semantics of typed let prefixes

- Status: Accepted
- Decision date: 2026-09-09
- Scope: A separate value-free body adapter, not runtime-entry integration

## Decision

Add `TypedLetReturnBodyHasType`, `TypedLetReturnBodyElaborates` and
`elaborateTypedLetReturnBody?` for a finite outer prefix of canonical local
declarations followed by an existing terminal return tree. Each declaration
must have both an explicit supported type annotation and an initializer. The
declared spelling must be absent from the current local name table. These are
restrictions of this adapter, not language-wide judgments about rejected code.

Interpret annotations with the caller's existing first-match `TypeNameTable`.
Check each initializer in the original inputs, with exactly its annotated type;
only then prepend its name, fresh owner-relative ID and type using
`LocalTypeInputs.bindFresh`. Elaborate the remaining original statements under
that extension. Emit exactly `Core.letE initializerCore tailCore`, without
weakening the already elaborated tail or reversing any inputs. The initializer
cannot read the newly introduced name, and later initializers can read all
earlier declarations. Freshness is relative to current input IDs, not a new
traversal-global allocator.

The independent judgments retain the original annotation, initializer,
statement order, tail, annotation meaning and complete terminal tree. Exact
elaboration additionally retains initializer resolution, lowering and typing.
No constructor is defined by checker success. The total checker recursively
consumes the statement prefix, with no fuel or artificial length limit.

Prove exact checker soundness/completeness, independent typing equivalences,
Core typing, uniqueness and failure characterization. Reuse terminal-tree
successes without changing their Core or type, including full optional equality
on the old singleton return/conditional shapes. Do not claim optional equality
for arbitrary bodies: a valid let prefix is deliberately new success here.

## Boundaries

This static unit supplies no runtime values, evaluation judgment, runner, cost,
fuel bound or function-entry extension. Nominal static inputs remain valid even
when their types have no runtime inhabitants. Data-only same-typed Core is not
exact source provenance. Existing expression, tree and entry APIs are unchanged.

Annotation inference, missing initializers, repeated local spellings, mutation,
calls, loops, fallthrough, early return, separate block wrappers and let prefixes
inside conditional arms remain outside this adapter. Do not infer zero or Unit
initial values. No parser, Core, Resolved or Wire changes are needed. General
injective renaming is not asserted to commute with fresh allocation.

## Validation

Add independent arbitrary-length and arbitrary-type source consumers, including
nominal non-inhabitation, original-scope checking, exact binder positions,
same-typed wrong-Core exclusion and whole checking of invalid unused initializers
or unselected terminal arms. Parse complete bodies and declarations, retaining
actual child structure and source order. Contrast new adapter success with the
unchanged tree and function-entry boundaries. Cover annotation/initializer/name
failures and supported first-match type meanings without runtime placeholders.

Audit all new public contracts and affected consumers for standard axioms and
registration; check dependency direction, focused/aggregate builds, actual parsed
execution, full tests and policy checks. Keep proof files below 300 lines,
commits small, diagnostics paused and scratch files inside the repository.
