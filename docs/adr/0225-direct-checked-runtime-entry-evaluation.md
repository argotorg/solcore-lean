# ADR-0225: Direct evaluation of a checked runtime entry

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Connect actual checked declarations and arguments to direct body results

## Decision

Add one store-free entry evaluator taking the existing type-name table, owner,
original `Syntax.FunctionDecl` and actual `List TypedRuntimeArgument`. Return
`Option (Core.Ty × Core.Value × Nat)` with the declared return type, actual
result and exact existing Core-transition cost. Reuse `prepareRuntimeFunction?`
as the unchanged whole-entry gate, then evaluate the declaration's original
body with ADR-0224 using the prepared original parameter names and actual values.

The gate still checks the header, mandatory parameter types, exact ordered
argument type list and arity, every written body child, annotation/name rules,
and the declared return contract. Preparation performs static lowering; this is
not a lowering-free entry implementation. Result computation does not run Core,
extract an answer from the retained Core or add entry transitions. Argument
values are bound once by existing preparation, never reversed a second time.
Branch-local lets extend only the direct evaluator's scopes, not the prepared
parameter-only record or argument contract.

Raw body success is insufficient for entry success. Unknown unselected types,
return mismatches, invalid headers and unused wrong-typed arguments still reject.
Compiled nominal types do not supply values: only the caller's actual typed
arguments are used. No arbitrary hand-built prepared or compiled record becomes
trusted, and the original declaration is never replaced by a same-typed Core.

## Minimal proof boundary

Publish exact equivalence between the computed triple and the existing
independent `RuntimeFunctionEvaluatesWithCost`. Its general final-store form
retains `finalStore = initialStore`, despite the executable having no store.
Independent preparation provenance and raw body evidence remain mandatory.
Use the direct body's soundness/completeness to construct/consume that evidence.

Publish `none` iff existing preparation is `none`. Unlike raw body absence,
this total checked entry has no additional evaluation-failure case after
successful preparation. Prove that fact from the prepared actual typed inputs
and whole body typing, without manufacturing inhabitants or running Core.

Existing entry cost, type preservation, bounds, exact fuel, compiled provenance,
store observations and real checkpoint/resumption theorems can consume the new
equivalence. Do not duplicate these established contracts as new wrapper APIs.
Static compilation factorization is already available; no new compiled record
evaluator or ad hoc truncated zip of values is introduced here.

## Validation and exclusions

Independent source entry evidence must retain exact headers, original parameter
layout, exact Core and selected body costs. Complete parsed declarations supply
independent expected triples/Core and real argument lists. Cover arbitrary
recursive depth, noncommutative and unused work, asymmetric branch costs, opaque
actual values, all fuel boundaries and genuine checkpoints. Separately test
whole rejection despite a successful raw body, and exact absence for header,
parameter, arity, return and unselected-body failures.

No existing preparation, compilation, runner, raw judgments, parameter records,
parser/Core/Resolved/Wire, source syntax or binding policy changes. No source
calls, mutation, cell allocation, closure invocation, defaults or inference.
Keep definition/proof/consumer/publication commits separate and small, proof
files below 300 lines, public/consumer axiom and dependency audits explicit.
Run focused/aggregate builds, parsed execution, full tests, the kernel-policy
check, and whitespace checks. Diagnostics remain paused; scratch stays in the
workspace.
