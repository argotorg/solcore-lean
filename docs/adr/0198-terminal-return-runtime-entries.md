# ADR-0198: Terminal return bodies at runtime function entries

- Status: Accepted
- Decision date: 2026-09-08
- Scope: connect the existing explicit runtime-entry API to terminal bodies

## Decision

Extend the existing value-free compiler, actual-argument preparer and runner to
the nonrecursive terminal-body union from ADR-0196. A body is either its original
singleton return or one explicit terminal if/else with two singleton-return
arms. Use `TerminalReturnBodyElaborates` in independent compilation/preparation,
`TerminalReturnBodyHasType` in whole-entry typing and
`TerminalReturnBodyEvaluatesWithCost` in independent entry cost. The executable
compiler and preparer use the matching terminal checker; do not add parallel
entry APIs or change the data-only compiled/prepared record layouts.

Keep exact source/Core/return-type correspondence and declared return agreement.
Compilation still constructs no runtime values. Preparation binds the actual
ordered typed arguments, retaining source positions and reversed Core environments.
Preserve type-only/actual-input factorization, compilation/preparation provenance,
matching argument types, injective owner relabeling, and store replay. Hand-built
records alone still provide no semantic or safety guarantee.

The entry wrapper adds no Core transitions. Lift selected-arm exact costs,
completion/exhaustion thresholds, type preservation, fault exclusion, and genuine
checkpoint resumption through the existing contracts. Whole checking covers both
written arms even when raw execution selects only one. Keep stores in their own
results and suspended states; store replay is not equality of whole results.

## Explicit contract migration

The three existing entry fuel-bound theorems (`cost_le_fuelBound` and the
`RuntimeFunctionHasType`/`RuntimeFunctionCompiles.run_done_of_fuelBound` laws)
now use `terminalReturnBodyFuelBound declaration.value.body`. For a conditional,
this is the condition bound plus the maximum arm bound plus two. The old
`returnBodyFuelBound` and singleton body APIs stay unchanged; their conditional
bound is still zero and must not be used as an entry completion guarantee.
All other existing entry theorem statements retain their current premises and
conclusions over the broadened judgments. Singleton proofs embed with `.single`
without changing their exact Core, values, stores, costs or same-fuel results.

## Boundaries and validation

No new parser syntax, source-call semantics, nested statement conditions, extra
statements, general early return, mutable binding, primitive or header policy.
Unsupported/missing arms, mismatched return types, invalid headers and invalid
parameters remain rejected. Migrate only fixtures whose valid conditional body
was previously the rejection reason; retain rejection for genuinely ill-scoped
or mismatched declarations and retain old singleton checker/bound tests.

Independent proofs and parsed execution cover actual Word/Bool/Unit/cell/closure
arguments, unequal selected costs, exact Core and actual suspended environments,
owner/store changes, value-free compilation and binding factorization, and all
fuel thresholds/resumptions. Audit all affected public contracts and consumers
for standard axioms; run focused/aggregate builds, full tests, dependency-cycle,
kernel, forbidden-token and whitespace checks. Keep proof files below
300 lines and commits small; leave paused diagnostics untouched and use local
repository scratch.
