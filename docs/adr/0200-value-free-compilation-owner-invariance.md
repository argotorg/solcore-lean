# ADR-0200: Value-free compilation owner invariance

- Status: Accepted
- Decision date: 2026-09-08
- Scope: Type-only parameter declarations and restricted function compilation

## Decision

Prove owner relabeling directly for static compilation, without supplying or
constructing runtime arguments. Existing preparation owner laws are insufficient:
nominal parameter types can compile even when no typed runtime argument exists
under the current empty data definitions. Do not add an inhabitation premise or
derive the static result by fabricating representative values.

Add injective local-ID relabeling to `LocalTypeInputs` and its rows. Preserve row
order, source spelling and types; names and identity-bearing contexts are mapped,
not equated. Provide projection, identity and composition laws. Relate this map
to existing actual input relabeling by exact `toTypeInputs` commutation, only in
the direction that erases already supplied values.

Move the existing `ownerLocalIdMap` and injectivity proof unchanged to a shared
module. Retain the public names and old runtime import availability. The map
changes owners and retains binder indices. Prove empty-start annotation-only
parameter declaration covariance under globally injective owner maps by following
its own fresh-binding induction. No arbitrary binder-index map is claimed to
commute with fresh allocation, and no arbitrary nonempty starting-state theorem
is exposed without the exact freshness conditions needed by its private proof.

Lift this result to independent `RuntimeFunctionCompiles` evidence using the
existing terminal-body relabeling theorem. Retain the exact Core and declared
return type and relabel only the compiled static inputs. Connect arbitrary pairs
of owners by an injective swap to prove equality of the complete optional
projection `(core, returnType, inputs.context.values)`, including both-sided
failure. Do not claim equality of whole identity-bearing compiled records.

## Boundaries and validation

Keep declaration/header/body policies, parser, executable compilation, parameter
allocation, Core, runtime preparation/execution and frozen interfaces unchanged.
The supported body remains the nonrecursive singleton/terminal-conditional union.
No argument arity check exists at this value-free stage: ordered parameter types
remain static data and the existing runtime argument guard is a separate contract.

Independent consumers build static provenance for arbitrary types and specialize
to uninhabited nominal types, covering both body shapes, open Core typing, changed
IDs with retained binder indices/spellings/type order and erasure compatibility.
Parsed consumers exercise successful exact projections, distinct and identical
owners, type-only nominal/mixed inputs and complete rejection results. Retain
header, duplicate-name, unsupported-body and malformed-parser rejection boundaries.
No runtime values are needed for these parsed checks.

Audit every public declaration and consumer with standard axioms only; run
focused and aggregate builds and full tests, kernel-policy and whitespace checks, keep
proof files below 300 lines and commits small. Leave diagnostic proofs untouched
and use repository-local scratch files.
