# ADR-0202: Value-free positional function compilation

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Exact whole-entry compilation of parameter returns and selectors

## Decision

Lift the value-free parameter position laws into the existing independent
whole-function compilation contract. Cover a singleton return of one source
parameter and a terminal conditional whose guard and both returned expressions
are source parameter references. Prove these contracts for arbitrary annotation
types, including nominal types with no runtime argument inhabitants.

Forward theorems retain all existing whole-entry obligations: independent
declaration of the complete parameter list, actual source-position lookups,
annotation meanings, the whole header and the exact body shape. A selected
parameter or well-typed Core alone must not bypass another invalid parameter,
the return contract, or an invalid written branch. The condition annotation
must mean Bool; both branch annotations must mean the declared result type.

For `n` written parameters and source position `k`, the singleton output is the
exact compiled static input bundle, `Core.var (n - 1 - k)` and the annotation
type. Conditional output is the exact ordered `Core.ifE` of the guard, then and
else positional variables. No distinct-index assumptions are needed: both arms
may return the same parameter, and the guard may also be returned when the
result type is Bool. Real position witnesses supply bounds without extra premises.

Each forward independent theorem has an executable compile-success corollary.
Add inverse theorems that use existing compilation provenance plus the same
body/position/annotation evidence to recover the exact Core and result type.
Do not duplicate header or whole-declaration premises in the inverse; these
already come from compilation evidence. Compare exact independent body
elaborations, not arbitrary expressions with equal Core types.

## Boundaries and validation

This adds proof interfaces only. Compilation, parsing, identity allocation,
parameter/header/body policies, runtime argument guards, Core execution, costs
and frozen interfaces remain unchanged. No source function values, invocation,
recursive conditional bodies or general statement semantics are introduced.
Existing rejection and uniqueness interfaces suffice; no new failure adapter is
needed. Runtime execution still requires actual matching typed arguments.

Independent and parsed consumers cover arbitrary and nominal types, exact source
positions, same-type distinct parameters, repeated arm positions and Boolean
guard/arm aliasing. Consume both forward and inverse contracts, distinguish
equally typed wrong Core trees and retain whole-parameter/header/branch rejection.
Prove compilation without fabricating values, and preserve own source shape and
provenance when connecting to existing owner or execution contracts.

Audit every public declaration and consumer with standard axioms only; run
focused/aggregate builds and full tests, kernel/metadata/whitespace checks, keep
proof files below 300 lines and commits small. Leave diagnostics paused and use
repository-local scratch.
