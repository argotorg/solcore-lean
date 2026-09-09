# ADR-0242: Type-table extension retains actual runtime preparation

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Existing actual-argument binding, full preparation and execution

## Decision

Complete the runtime side of ADR-0203 without changing an executable definition.
The existing `TypeNameTable.Extends` relation preserves first-match meanings,
not row membership or table order. Static declaration and compilation already
transport exact records. Their value-free projections alone do not establish
equality of records that also contain the caller's actual argument values.

Transport independent `RuntimeParametersBindFrom` evidence for arbitrary
initial and final typed inputs along this relation. Only structural annotation
evidence changes. Retain the original parameters, argument list, owner, initial
and final bindings, types, actual values and typing evidence. Existing fresh
identity allocation and prepend order are untouched. Specialize to the public
empty-start relation and preserve exact successful executable binding results.
Mutual extension additionally preserves the full optional result.

Compose existing header and recursive-body transport with actual binding
transport. Preserve independent whole preparation of the exact same
`PreparedRuntimeFunction`, including its complete value-bearing input bundle,
Core and return type. Transport whole-entry typing without inventing arguments.
Lift these results to successful executable preparation and to full optional
preparation equality under mutual extension.

Execution still runs the same prepared Core with the same environment, fuel
and store. Preserve every successful whole run result under one-way extension,
including present exhaustion and its genuine saved machine state. Under mutual
extension, preserve the entire optional run result, including rejection. These
are exact result equalities, not just equal final values or termination claims.
Resuming identical checkpoints uses existing Core resumption; no new evaluator,
fuel formula or continuation behavior is introduced.

## Boundaries

One-way extension does not preserve rejection: adding a previously unknown
annotation meaning can enable binding and preparation. A duplicate prefix that
changes an existing first-match meaning is not an extension, even if it retains
all old rows. Later hidden duplicates and same-meaning duplicates need not make
tables equal. Mutual extension is sufficient to retain lookup absence.

The actual arguments must remain the same. Equal argument types or equal
`toCompiled` projections do not make different values, prepared records or
execution results interchangeable. Static nominal typing and actual typed
inhabitants remain separate obligations. Opaque cell references do not assert
allocation, and supplied closures do not add source calls or invoke code.

No parser, source acceptance, header/parameter/body policy, diagnostic, Core,
Resolved, wire, table lookup, runtime record or identity-allocation definition
changes. The private arbitrary-initial-state executable binder stays private.
Do not add a redundant lookup-equivalence relation or recover full prepared
equality from an erased projection.

## Validation and integration

Keep the parameter proof module below the function-entry layer. Independently
construct source and complete parsed consumers for original annotated parameter
lists, actual typed arguments, sparse mixed-owner initial rows, first-match
duplicates and unchanged full prepared records. Cover empty/single/multiple
parameters separately from structural tuple components and retain reversal
exactly once. Test both mutual success/rejection and one-way None-to-Some
contrasts, along with actual opaque values and nominal static boundaries.

Whole parsed consumers retain original declarations, parameter rows, actual
values and stores across table changes. Compose exact manual evaluation paths,
mixed recursive bodies, all-fuel machine results and genuine checkpoint
residuals. Preserve invalid headers, arguments and unselected branches rather
than weakening shared checks.

Audit all public declarations and consumers with standard axioms only; run
focused and aggregate builds, full tests, kernel/metadata/whitespace checks and
independent reviews. Keep each new proof/consumer below 300 lines, commit design,
proofs, consumers and publication separately, and leave diagnostics paused.
