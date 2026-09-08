# ADR-0208: Recursive return trees at runtime function entries

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Connect the existing explicit runtime-entry API to recursive trees

## Decision

Extend the existing value-free compiler, actual-argument preparer and runner
from the nonrecursive terminal-body union to the recursive return-tree adapter
of ADR-0204 through ADR-0207. A body is a singleton return or a finite tree of
singleton explicit if/else nodes with singleton-return leaves. Keep original
source children, exact Core, declared return agreement and whole checking.

Use `TerminalReturnTreeElaborates` in independent compilation and preparation,
`TerminalReturnTreeHasType` in whole-entry typing, and
`TerminalReturnTreeEvaluatesWithCost` in independent entry cost. The compiler and
preparer use the matching tree checker. Do not create parallel entry APIs or
change the data-only compiled/prepared record layouts. Arbitrary records do not
establish provenance, exact source correspondence, typing or safe execution.

Preserve the current header and complete parameter policies. Compilation needs
no actual runtime values, including for nominal parameter types with no runtime
inhabitants. Preparation uses actual ordered typed arguments; retain the existing
reversed Core environment exactly once. Value-free/actual-input factorization,
argument-type transport, parameter positions, owner relabeling and type-table
extension keep their contracts over the broadened body judgments.

The entry wrapper adds no transitions. Lift independent recursive selected-path
cost, exact completed/exhausted fuel thresholds, type preservation, store replay,
fault exclusion and genuine checkpoint resumption through existing provenance.
Whole checking still validates all written branches, including unselected deep
children. Identity relabeling preserves full same-store states, whereas replay
between stores retains each result's own store. Never rebuild checkpoints or
infer generic safety from aligned but untyped environments.

## Explicit contract migration

The three existing entry fuel-bound laws (`cost_le_fuelBound` and the
`RuntimeFunctionHasType`/`RuntimeFunctionCompiles.run_done_of_fuelBound` theorems)
now expose `terminalReturnTreeFuelBound declaration.value.body`. The old
nonrecursive bound can be four on a valid recursive tree whose long path costs
seven, so it cannot remain an entry safety guarantee. Old body adapters and all
their bounds, judgments, checking and runner contracts stay unchanged.

Apart from these three bound statements, preserve generic entry theorem premises
and conclusions. The body fields of compilation/preparation provenance, the
whole-entry typing definition and the entry-cost constructor explicitly broaden.
Singleton evidence embeds with the same constructor; old conditional evidence
uses the established tree embeddings or direct recursive-node evidence. Exact
Core, values, stores and costs of old accepted shapes must not change.

## Boundaries and validation

No parser, Core, Resolved, Wire, source-call, mutation, loop, early-return,
fallthrough, missing-else or multiple-statement extension. Migrate only valid
deep-body entry rejection fixtures to exact new success. Preserve old body-level
deep rejection and every genuinely invalid header, parameter, branch or whole
shape. A block containing an extra nested block is still unsupported.

Add independent arbitrary-depth source proofs and parsed whole-entry execution
with actual Word/Bool/Unit/cell/closure arguments, value-free nominal compilation,
asymmetric costs and bounds, full factorization, owner/store changes, same-typed
wrong-Core rejection and genuine multi-chunk states. Audit changed statements,
all affected public contracts and consumers, dependency direction, standard
axioms, focused/aggregate builds, actual parsed execution, full tests and policy
checks. Keep proof files below 300 lines, commits small, diagnostics paused and
scratch files inside the repository.
