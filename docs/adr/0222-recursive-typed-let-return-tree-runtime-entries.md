# ADR-0222: Recursive typed let/return trees at runtime entries

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Connect the existing explicit entry API to the proven recursive body

## Decision

Integrate ADR-0216 through ADR-0221 into the existing value-free compiler,
actual-argument preparer, whole-entry typing and independent entry cost. Replace
the outer-prefix body dependency with `TypedLetReturnTreeElaborates`,
`TypedLetReturnTreeHasType`, `TypedLetReturnTreeEvaluatesWithCost` and their
matching executable checker. Do not create a parallel entry API.

Accepted bodies compose mandatory annotated, initialized, unused-name lets,
single returns and singleton explicit terminal if/else recursively inside both
arms. Every initializer uses its old scope; only its tail gets the fresh binding.
Both branches start from the same original scope and are checked in full, even
when only one branch executes. Sibling identities may coincide scope-locally.
Do not thread one sibling's allocation into the other.

Keep both compiled and prepared data records at their original three fields:
parameter inputs, actual ordered Core and declared return type. Branch-local
bindings do not become parameters, alter arity or rearrange argument values.
Static compilation constructs no runtime inhabitants. Actual preparation keeps
one ordered typed binding and the same complete erased parameter bundle; mere
name/context equality is not a substitute for this bundle when transporting
argument types. Preserve header policy and declared return agreement.

The runner still executes the prepared Core directly at its original positional
values, store and empty continuation. Preparation adds no transitions and the
runner does not recheck the body. Lift exact source cost, store preservation,
typed existence, completion/exhaustion thresholds, fault exclusion and genuine
checkpoint resumption through complete provenance. Raw selected paths alone do
not establish entry acceptance; arbitrary data records receive no new safety.
Owner covariance reuses the fresh-aware owner-only body law. Type-name extension
preserves annotation meanings and the exact compiled record.

## Explicit contract migration

The three generic entry fuel-bound contracts now expose
`typedLetReturnTreeFuelBound declaration.value.body`. A branch-local initializer
can require seven steps where the old outer-prefix/tree bound is four, so the
old bound cannot remain the general entry guarantee. Keep every older body-only
adapter, bound and embedding contract unchanged.

Compilation/preparation body fields, whole-entry typing and the entry-cost
constructor explicitly broaden. Other generic entry theorem names and statements
stay unchanged apart from the three bound formulas. Old terminal and prefix
witnesses embed with exact Core, values, stores and costs. Preserve genuine old
rejections and migrate valid branch-local entry-rejection fixtures to independent
exact success, retaining their old body-adapter rejection checks. Rename only
test declarations whose old names now falsely describe the entry boundary.

## Boundaries and validation

No parser/Core/Resolved/Wire change, general early return, arbitrary statements
after conditionals, loops, calls, mutation, inference, default initialization or
new shadowing policy. Missing annotations/initializers, invalid unselected
children, self/forward/sibling references and declared return mismatches remain
rejected at the whole appropriate boundary.

Use independent arbitrary-depth entry evidence and complete parsed declarations.
Exercise noncommutative and unused initializers, sibling scopes, nominal static
types, actual opaque values, original argument placement and guards, asymmetric
costs/bounds, owner/type-name/store transport and full multi-chunk checkpoints.
Audit all changed public and consumer contracts, allowed axioms, registration and
acyclic entry-to-body dependencies. Run focused/aggregate builds, parsed execution,
full tests and kernel/metadata/whitespace checks. Keep proof files below 300 lines
and commits small. Diagnostics stay paused; scratch stays in the repository.
