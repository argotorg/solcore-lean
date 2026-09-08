# ADR-0172: Static invariance under typed runtime argument changes

- Status: Accepted
- Decision date: 2026-09-08
- Scope: proof-only separation of static preparation from runtime values

## Decision

For the same canonical declaration, caller-owned identity, and explicit type
table, changing structurally typed runtime arguments without changing their
ordered type list must preserve preparation success/failure and the exact
static result: name table, context, identities, Core expression, and return type.
The type list is `TypedRuntimeArgument.type`; do not replace its structural
typing evidence with an inspection of `Core.Value.type`.

Prove transport first for the independent parameter-binding relation from
arbitrary initial inputs with equal name tables and contexts. These imply
equal identity lists and therefore identical fresh identities. Equal argument
type lists supply the same arity and head annotation meaning, while the new
values and their typing evidence populate the new rows. No extra initial-name
uniqueness premise is needed beyond the existing binding relation. Do not claim
equality of the complete inputs or their value projections.

Transport the independent whole-function preparation relation using equal
static inputs, unchanged header meaning, and exact body elaboration. Expose
an equality between the two executable preparation results after mapping each
prepared record to its static projections. Keeping `Option` in this statement
preserves failure as well as successful exact Core; it is not merely a theorem
conditioned on both runs having already accepted. A theorem-local projection
lambda is sufficient; no new executable static-view interface is required.

## Dynamic boundary

Runtime environments, complete prepared records, returned values, suspended
states, and source/Core costs may change when argument values change. A
conditional may select a different branch with a different cost even though
its exact checked Core and return type stay fixed. A skipped unresolved or
ill-typed branch still prevents whole preparation for every argument value.
Static invariance must not be presented as dynamic observational equivalence.

This proof layer does not evaluate argument expressions, validate untyped
external values, call source functions, allocate cells, or introduce a cache.
The adapters and supported canonical source forms remain unchanged.

## Validation

Use independent transports and concrete consumers with equal type lists but
different values. Show successful static equality and both-sided rejection;
also demonstrate a changed result or cost and unequal runtime environments.
Use structurally typed cell references or closures as opaque values where
useful, without assuming allocation or application safety.

Add complete-source regressions comparing actual preparation projections and
actual runs, register and audit every public declaration, run focused/aggregate
builds and full tests, and check kernel, metadata, and whitespace policies.
Keep each new proof file below 300 lines; diagnostic proofs and wire data stay
untouched.
