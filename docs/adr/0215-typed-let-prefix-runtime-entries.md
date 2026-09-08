# ADR-0215: Typed let prefixes at runtime function entries

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Connect the existing explicit runtime-entry API to typed let prefixes

## Decision

Extend the existing value-free compiler, actual-argument preparer and runner
with the annotated, initialized, nonshadowing outer let-prefix adapter of
ADR-0209 through ADR-0214. Each initializer uses the old scope, then the tail
uses the freshly extended scope. The terminal remains a recursively checked
return tree. Preserve every source child and the exact positional Core.

Use `TypedLetReturnBodyElaborates types owner inputs` in compilation and the
actual inputs' value-free projection in preparation. Whole-entry typing uses
`TypedLetReturnBodyHasType`; independent entry cost uses
`TypedLetReturnBodyEvaluatesWithCost` with the original actual environment.
Use the matching checker in the existing compiler and preparer, not a parallel
entry API. Compiled and prepared data records retain exactly their three fields:
original parameter inputs, Core and return type. Prefix-local rows do not become
parameters or change the argument count, type-list guard or reversed environment.

Retain complete header and parameter policies, declared return agreement and
all written branch checks. Static compilation constructs no runtime inhabitants,
including for nominal types. Actual preparation still binds ordered typed
arguments exactly once. Derive complete equality of erased parameter bundles
from independent parameter declarations when transporting argument types.

Lift the established exact source cost, typing, fuel thresholds, fault exclusion,
store replay and genuine resumption through provenance. The entry runner keeps
directly executing the prepared Core with its original ordered values and empty
continuation; no wrapper transitions or body rechecking are introduced. Owner
transport uses the fresh-allocation-aware body law. Type-name extension preserves
each annotation meaning while retaining the exact compiled record. Neither
arbitrary data records nor raw selected-path evidence imply whole acceptance.

## Explicit contract migration

The three entry fuel-bound laws (`cost_le_fuelBound` and the
`RuntimeFunctionHasType`/`RuntimeFunctionCompiles.run_done_of_fuelBound` theorems)
now expose `typedLetReturnBodyFuelBound declaration.value.body`. A one-let return
has old tree bound zero but exact cost four, so the old bound cannot remain the
general entry guarantee. All old body-only adapters and bounds remain unchanged.

The body fields of compilation/preparation provenance, their constructors,
whole-entry typing and the entry-cost constructor explicitly broaden. Apart
from the three bound formulas, retain existing generic entry theorem statements.
Embed old tree body evidence through the typed-prefix terminal constructor;
preserve exact Core, values, costs, stores and rejection of genuinely unsupported
old fixtures. Migrate valid annotated-prefix entry rejection tests to independent
exact success, while keeping their old tree-adapter rejection checks.

## Boundaries and validation

No parser, Core, Resolved, Wire, source-call, mutation, loop, inference, default
initialization, arm-local let or general binding-policy extension. Annotation and
initializer are mandatory, the new name must be unused, and the old initializer
scope does not admit self or forward references. This restricted adapter does
not assert a global language prohibition on shadowing.

Use independent arbitrary-length source evidence and parsed whole-function tests.
Cover exact parameter placement, noncommutative and unused initializers, nominal
static inputs without values, actual opaque values, asymmetric costs and bounds,
factorization, owner/type-name/store changes, full real checkpoints and multi-chunk
resumption. Retain complete negative header, parameter and body boundaries.
Audit changed contracts, every public theorem and consumer, standard axioms,
registration and acyclic entry-to-body dependencies. Run focused/aggregate builds,
parsed execution, full tests, kernel/metadata and whitespace checks. Keep proof
files below 300 lines, commits small, diagnostics paused and scratch in the repo.
