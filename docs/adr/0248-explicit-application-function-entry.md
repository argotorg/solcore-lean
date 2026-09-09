# ADR-0248: An explicit application-return function entry

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Separate whole-function gates for the singleton application-return profile

## Evidence and decision

ADR-0247 connects an original singleton application return to its exact checked
child, actual costs and complete machine outcomes. Now connect that body to an
explicitly supplied original function declaration, owner, type table and argument
list. Retain all existing header and parameter interpretation policies. This
adds no source-function lookup, global resolution, general Invokable selection,
source closure construction, recursion or new Rust language policy.

The existing `RuntimeFunctionHeader` checks the original modifier/generic/where
restrictions and absent-or-single structural return annotation. The original
parameter declaration and binding relations preserve annotation meaning, name
uniqueness, source order and owner-relative IDs. `RuntimeParametersBind.erase_values`
and `RuntimeParametersDeclare.bind_typed_arguments` connect their complete static
records only when the caller supplies the actual matching typed arguments.
`RuntimeParametersBind.argument_values` fixes the actual initial environment as
the original argument values reversed exactly once.

Reuse the existing data-only `CompiledRuntimeFunction` and
`PreparedRuntimeFunction` records without changing their definitions. Introduce
distinct `RuntimeApplicationFunctionCompiles` and
`RuntimeApplicationFunctionPrepares` propositions: each requires the original
header, the original parameters, and exact `LocalApplicationReturnBodyElaborates`
evidence for its own inputs, Core and declared return type. A new proposition
must not be coerced to the old compilation/preparation proposition merely because
the output record has the same type.

Add `compileRuntimeApplicationFunction?`, `prepareRuntimeApplicationFunction?`
and `runRuntimeApplicationFunction?` as separate endpoints. Compilation uses
only the original static parameters. Preparation uses the supplied actual
arguments. Both check the complete original body and require its inferred type
to equal the declared return contract. Execution uses exactly the prepared Core,
the actual prepared values, supplied fuel and store. Header/parameter preparation
does not consume Core transitions. Preserve outer rejection, inner faults,
exhaustion checkpoints and the static result tag.

## Exact contracts and reuse

Prove complete success correspondence with each independent proposition, exact
record uniqueness, absence characterization and open Core typing. For execution,
factor every present outcome through the actual successful preparation and Core
result, and show absence iff preparation fails. Independent preparation gives
full-result equality with that prepared input's application-return body runner,
for every fuel and store. This equality is conditional on the complete original
header/parameter/body contract, not merely on an accepted local call.

Reuse the data-only `PreparedRuntimeFunction.toCompiled` projection. Prove new
preparation erases to new compilation, and new compilation reconstructs a
preparation only from actual supplied arguments whose ordered types match.
Prove the complete-Option preparation/compilation factorization, including
failure and the arity/type-order guard. Also retain full-result compiled execution
using the same Core and the original supplied values in reverse order. Equality
of compiled projections alone must not be mistaken for equality of actual values,
captures or stores. Independent binding fixes the supplied values and captures;
the execution equation separately fixes the supplied store.

No new entry raw/cost relation or duplicate set of runtime-world laws is needed
at this boundary. Consumers transport ADR-0246/0247 guarantees through the exact
body/entry equality. The old entry's arbitrary-store success, unchanged-store,
source-only fuel and local-fragment guarantees cannot be reused for calls.
Runtime safety still needs the same actual environment and store typed in one
world. Missing cells may fault; wrong payloads may return a Bool under a Word
tag; writers and allocation may change the store; identical source and static
types can require arbitrarily different actual closure costs.

## Validation and dependency boundary

Independent consumers retain complete original declarations, signatures,
parameter rows and body syntax. Exercise value-free nominal checking separately
from actual higher-order Function inhabitants. Demonstrate actual reader,
writer, allocator and delayed closures; exact child/body/entry costs; genuine
checkpoint identity, residual paths and full-result resumption. Contrast local
body success with whole rejection from return mismatch, unsupported headers,
wrong argument arity or ordered type lists, or unsupported body shapes. Swapping
same-typed actual values is not rejected: it may change the prepared record and
execution result while leaving the compiled projection unchanged. Old pure/body/entry
endpoints retain their previous success and rejection behavior.

New whole-entry modules may import existing record owners and parameter proofs;
their old recursive-body dependencies are not new safety evidence. Do not add
whole-entry imports to the lower application/body layers. Keep all old endpoint,
record, Core, Resolved, parser, diagnostic and wire definitions unchanged.
Separate definitions, proofs, consumers and publication into small commits, with
each new proof/test file below 300 lines. Require focused and aggregate builds,
full tests, all public/consumer standard-axiom audits, dependency closure checks,
kernel/metadata/whitespace checks and independent reviews.
