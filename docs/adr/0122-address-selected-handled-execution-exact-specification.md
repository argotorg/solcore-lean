# ADR-0122: Address-selected handled execution exact specification

- Status: Accepted
- Decision date: 2026-08-29
- Scope: complete the executable specification of address-selected handled Core execution
- Implementation: Not started

## Context

ADR-0119 introduced `runCodeWithStorage?`, the current highest-level internal
entry point for handled Core execution. It first looks up checked code at a
caller-supplied `codeAddress`, then runs that code with the separate retained
`storageAddress` context. The optional result distinguishes selection failure
from an attempted execution.

ADR-0120 made the generic driver and checked-code runner exact executable
specifications. At both boundaries, a concrete result is equivalent to its
fuel-indexed handled-step evidence. The address-selected entry point currently
inherits only the forward direction: a successful optional result identifies
the selected code and produces fuel evidence. There is no public reverse rule
that reconstructs the same optional result from selection and evidence.

Selection failure is likewise covered by separate sufficient rules for an
absent Account and an Account without code, but not by one exact rule at the
`WorldState.code?` abstraction boundary.

The repository charter requires one-way results to state their missing
direction. The missing directions can be closed without adding a runtime
operation, address role, lifecycle policy, or source-language dependency.

## Decision

Publish exact characterizations of both optional branches of
`runCodeWithStorage?`.

Successful selection is characterized by:

```lean
theorem runCodeWithStorage?_eq_some_iff_fuelSound
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (result : HostDriverResult (CodeRunContext RollbackState TraceState)) :
    context.runCodeWithStorage? codeAddress fuel = some result ↔
      ∃ code,
        context.context.values.working.1.code? codeAddress = some code ∧
          HostStorageDriver.FuelSound result fuel context
            (Core.State.initial code.program.body Core.hostEnvironment)
```

Selection failure is characterized by:

```lean
@[simp] theorem runCodeWithStorage?_eq_none_iff
    (context : CodeRunContext RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat) :
    context.runCodeWithStorage? codeAddress fuel = none ↔
      context.context.values.working.1.code? codeAddress = none
```

The successful theorem contains both parts of the selection contract. The
existential code must be exactly the checked code selected from the working
WorldState, and its initial Core state must be the one used by the handled
runner. Fuel evidence records the exact result context and outcome; it does not
erase writes or replace the final context with the input context.

The failure theorem intentionally stops at `WorldState.code? = none`. That
observation includes both an absent Account and a present Account whose
optional code field is empty. The entry point does not distinguish those
causes, so the theorem must not invent a more detailed failure reason.

## Proof construction

Both theorems follow the executable definition rather than duplicating code
lookup or driver semantics.

For the successful forward direction:

1. inspect the one `code?` selection performed by `runCodeWithStorage?`;
2. rule out the `none` branch;
3. recover the exact selected code and concrete checked-run result; and
4. apply the existing `runWithStorage_fuelSound` theorem.

For the reverse direction:

1. rewrite the optional selection with the supplied `code? = some code`
   evidence;
2. apply `CheckedHostCoreProgram.runWithStorage_eq_iff_fuelSound` in the
   reverse direction; and
3. lift the resulting exact driver equality through `some`.

The `none` theorem is a direct case split on the same lookup. A selected code
always maps to `some (code.runWithStorage context fuel)`, including when the
driver outcome itself is out of fuel. Resource exhaustion therefore remains an
execution result and never becomes selection failure.

## Required proof interface

The completed interface must provide:

- exact `some` equivalence between optional execution and selected-code fuel
  evidence;
- exact `none` equivalence with the existing working-WorldState `code?`
  observation;
- continued compatibility of the older forward-only fuel-evidence theorem;
- direct reuse of checked-run completeness for the reverse direction; and
- unchanged selected typing, context preservation, no-fault, and terminal
  fuel-stability results.

No new relation or duplicate evaluator is introduced. The executable
definition of `runCodeWithStorage?` remains unchanged.

## Required regressions

Compile-time consumers must exercise:

- the complete `some` theorem as a public theorem value;
- extraction of selected code and fuel evidence with its forward direction;
- reconstruction of the exact `some result` with its reverse direction;
- the complete `none` theorem as a public theorem value; and
- the distinction between optional selection failure and a selected
  out-of-fuel execution.

Existing runtime fixtures already cover absent Accounts, Accounts without
code, selected checked execution, storage updates, exact final contexts, and
out-of-fuel boundaries. This proof-only slice does not add a second runtime
program merely to repeat those observations.

## Dependency boundary

The proofs live with the existing address-selected execution properties. They
depend on working-WorldState code lookup, checked handled execution, and
ADR-0120's fuel completeness. Core, the generic host driver, and the concrete
storage handler do not change.

No parser, Surface, ABI, Oracle, Wire, schema, profile, gas, frame-outcome, or
transaction-lifecycle module participates. The root README does not change.

## Non-goals

This ADR does not add or define:

- a code-address observation available to Core code;
- equality between code, storage, current, caller, or authority addresses;
- caller, call value, calldata, call kind, balance, or further storage
  operations;
- return-byte encoding or a mapping from Core completion to frame outcomes;
- commit, rollback, nested calls, transaction completion, or publication;
- sufficient fuel for every checked host program; or
- stability of out-of-fuel results under additional fuel.

Those are separate semantic decisions. In particular, this exact
characterization says which result a supplied fuel witness denotes; it does not
prove that some finite fuel always yields a completed result.

## Implementation sequence

Keep each green commit below roughly 300 changed lines:

1. record this exact optional-result boundary;
2. implement the `some` and `none` equivalences;
3. add direct forward- and reverse-direction compile regressions; and
4. run full validation and an independent audit, then record acceptance and
   synchronize internal status documents.

## Consequences

Every branch of the current address-selected entry point has a complete
specification. A caller can reason from execution to selected relational
evidence or replay valid selected evidence to the exact optional result. It can
also prove selection failure exactly at the abstraction level the executable
API observes.

Later lifecycle adapters and entry-input extensions can depend on this boundary
without unfolding optional code selection or relying on a one-way theorem.
