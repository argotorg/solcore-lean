# ADR-0181: Store-independent observations for the restricted frontend

- Status: Accepted
- Decision date: 2026-09-08
- Scope: initial-store transport for existing source evaluation and exact costs

## Decision

Prove that the current local-expression fragment can replay any independent
successful evaluation from any replacement initial store, with the same value
and exact cost and with that replacement store unchanged. Keep the caller's
name table and environment, source expression, and all supplied values fixed.

This strengthens the existing store-preservation law: leaving one initial store
unchanged does not by itself prove independence from its contents. Establish
the new law by induction on the independent cost derivation, then erase costs
to transport raw evaluation. No well-typedness, complete resolution, store
allocation, or equality between the two initial stores is needed at this raw
boundary. Skipped invalid branches remain skipped in raw evaluation only.

Extend the transport through single-return bodies and independently prepared
function costs. Whole entry preparation remains mandatory for checked execution.
Derive fixed-fuel equivalence of terminal values, with each side retaining its
own initial store, and equivalence of whether fuel is exhausted. Also expose
these observations for proven compiled Core with matching actual typed arguments.

## Boundaries

Do not assert literal equality of stateful results across distinct stores: a
terminal result and every suspended state carry their own store. Exhaustion
equivalence only quantifies the corresponding suspended state on each side;
this unit does not introduce a state-replacement map or claim equal continuations.

The claim concerns the existing restricted frontend, whose expressions do not
dereference, allocate, mutate, or call closures. A returned reference or closure
is the same supplied value on either store, not an assertion that the reference
is allocated or that executing the closure is store-independent. The property
does not apply to arbitrary Core programs with store effects. A future source
effect extension must explicitly revisit this proof and its public contract.

No syntax, compiler, evaluator, runner, argument guard, or evaluation relation
changes. Preserve all current source/Core identities, operand and branch order,
literal policy, type checking, exact fuel counts, and compilation provenance.

## Validation

Use independent arbitrary-value and arithmetic/conditional derivations, including
raw evaluation that skips an invalid branch while whole checking rejects it.
Check nonempty and empty initial stores, supplied references/closures without
dereferencing/calling them, exact costs, and per-store terminal/exhaustion results.
Fully parsed entries compare matching arguments at every tested fuel and retain
whole rejection independently of the store. Include an effectful Core example
showing why the theorem is not a claim about arbitrary Core execution.

Register and audit all public declarations, keep new files below 300 lines,
and run focused and aggregate builds, full tests, standard-axiom, kernel,
metadata, forbidden-token and whitespace checks. Commit small exact-path units.
Diagnostic proofs remain untouched.
