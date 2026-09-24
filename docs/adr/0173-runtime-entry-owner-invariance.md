# ADR-0173: Runtime entry owner invariance

- Status: Accepted
- Decision date: 2026-09-08
- Scope: identity-only relabeling for explicitly supplied runtime entries

## Decision

Changing only the caller-supplied declaration owner must not change a restricted
runtime entry's acceptance, exact Core, return type, runtime value sequence, or
full result at identical fuel and store. The source declaration, explicit type
table, and structurally typed arguments remain fixed. Name tables, identity
lists, and typed contexts contain owner-relative IDs and are related by
relabeling, not asserted equal.

Use an injective declaration-owner map lifted to local IDs while leaving every
binder index unchanged. Transport the independent empty-start runtime parameter
binding to the mapped owner and the existing `LocalInputs.mapIds` result. For
arbitrary old and new owners, choose a declaration-owner swap that fixes all
other owners; simply overwriting every local ID's owner is not globally injective.
The swap also covers equal old/new owners.

## Allocation and exact preparation

Establish the necessary fresh-ID correspondence along the existing allocation
chain. A private generalized binding proof may carry mapped initial inputs and
equality of the next same-owner binder indices. Empty inputs have index zero;
allocating the fresh ID advances both indices by one. This avoids any new claim
about arbitrary allocation order or global declaration identity generation.

This restricted covariance must not be confused with commutation for arbitrary
injective local-ID maps. A map shifting every binder index by ten is injective,
but mapping the fresh ID of an empty scope gives index ten whereas freshly
allocating after mapping that empty scope still gives zero.

Transport exact body elaboration using the established injective resolution,
lowering, and typing laws. Preserve independent whole-header and parameter
conditions and retain the same exact Core and declared return type. Typed
arguments and their runtime values are unchanged. The executable preparation
results agree after projecting to Core, return type, and runtime values, with
`Option` equality preserving rejection as well as successful preparation.

## Execution boundary

The prepared Core and runtime value sequence are identical, so the public
runner agrees at every fuel, including the entire out-of-fuel suspended state.
No successful-checking or sufficient-fuel assumption is needed for this runner
equality. This is stronger than static invariance under changed argument values,
which intentionally permits different runtime states, results, and costs.

No runtime adapter, source-name normalization, declaration lookup, source call,
mutable local policy, argument decoder, or wire interface is changed. Identifier
relabeling utilities are proof support, not a new global allocator.

## Validation

Use independent parameter/preparation transports, distinct and equal owners,
different real ID tables, full same-fuel completion and exhaustion equality,
opaque typed closure/cell values, and rejected whole declarations. Keep the
index-shift allocation counterexample explicit. Add completely parsed entry
regressions and audit every public declaration. Run focused and aggregate builds,
full tests, kernel-policy and whitespace checks, and keep new proof files below
300 lines. Leave diagnostic proofs untouched.
