# ADR-0120: Handled-execution completeness and fuel stability

- Status: Accepted
- Decision date: 2026-08-29
- Scope: relational completeness of Core host execution and the generic handled driver
- Implementation: Not started

## Context

ADR-0119 gives handled Core execution a total implementation and an exact
fuel-soundness theorem. For every driver result, `FuelSoundWith` reconstructs
the ordinary Core segments, emitted requests, handler updates, resumed states,
and final context. Completion consumes no more than the supplied budget;
exhaustion consumes it exactly.

That theorem currently runs in only one direction:

```text
executable run result  ->  relational handled-step evidence
```

The relation is intended to be the readable specification of the driver, but
there is no generic theorem that valid relational evidence replays to the same
executable result. There is also no theorem that a completed run remains the
same when more fuel is supplied. Individual tests exercise larger budgets, but
they do not close this proof boundary.

The next roadmap category contains contract-entry inputs and state lifecycle.
Those choices can wait. Caller, value, calldata, current-address identity,
return bytes, commit, and rollback all introduce new meaning. Completing the
existing execution relation adds no behavior and makes every later capability
extension easier to validate.

## Decision

Prove completeness for the Core host runner and then lift it through the
generic dependent handler. The central result is:

```lean
theorem HostDriver.run_eq_iff_fuelSoundWith
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state : Core.State)
    (result : HostDriverResult Context) :
    HostDriver.run handler context fuel state = result ↔
      result.FuelSoundWith handler fuel context state
```

The forward implication is ADR-0119's existing soundness theorem. The reverse
implication replays the recorded deterministic Core transitions and exact
handler boundaries under the supplied budget.

Do not change `HostDriver.run`, `HandledSteps`, `FuelSoundWith`, or their fuel
meaning. This is a proof completion over the existing executable semantics.

## Core replay lemmas

`Core.HostSteps` contains only ordinary host-aware transitions. Publish the
four replay forms needed by the generic driver:

1. a path to `State.final value store` completes whenever its step count is at
   most the supplied fuel;
2. a path to a state whose next observation is a fault returns that exact
   fault whenever its step count is affordable;
3. a path followed by one request emission returns that exact suspension and
   exact remaining fuel; and
4. a path of exactly the supplied fuel ending at an ordinary transition or
   request emission returns out-of-fuel at that state.

The suspension lemma records the same arithmetic as existing soundness:

```text
prefixSteps + remainingFuel + 1 = fuel
```

The additional one is the request emission itself. The handler and response
injection are not Core transitions and do not consume fuel.

These lemmas are host-aware counterparts of the existing pure
`runStateful_complete_of_steps`, fault completeness, and exhaustion
completeness theorems. They should reuse the executable/declarative one-step
correspondence rather than unfold every Core control form again.

## Generic handled replay

Lift Core replay by induction on `HostDriver.HandledSteps`:

- `.core` replays one uninterrupted `Core.HostSteps` path;
- `.handle` replays the prefix to the exact suspension, uses the relation's
  handler equation to obtain the exact next context and resumed state, then
  applies the induction hypothesis to the suffix with the exact remaining
  budget.

Publish separate internal replay theorems for done, fault, and out-of-fuel,
then derive `run_eq_of_fuelSoundWith` and the public iff theorem. Keeping the
outcome-specific lemmas makes arithmetic failures diagnosable and gives later
proofs small reusable interfaces.

No assumption that a handler preserves its context is permitted. The relation
already records every old context, exact handler result, resumed state, and new
context, so replay must return the relation's final context even across writes.

## Terminal fuel stability

Derive monotonicity only for terminal results:

```lean
theorem HostDriver.run_done_stable
    (execution :
      HostDriver.run handler context fuel state =
        ⟨finalContext, .done value store⟩)
    (enough : fuel ≤ largerFuel) :
    HostDriver.run handler context largerFuel state =
      ⟨finalContext, .done value store⟩

theorem HostDriver.run_fault_stable ...
```

More fuel cannot change a deterministic completion or raw fault. It can change
an out-of-fuel result, so no corresponding stability theorem is valid for
exhaustion.

Specialize done stability to:

- `CheckedHostCoreProgram.runWithStorage`; and
- successful `runCodeWithStorage?` selection.

The address-selected theorem must preserve the same selected code and exact
final context. It does not need a new code-selection carrier.

## Required proof interface

Core publishes and verifies:

- done replay from `HostSteps` and an affordable terminal path;
- fault replay from `HostSteps`, an affordable path, and an exact terminal
  fault observation;
- suspension replay from `HostSteps`, exact request emission, and exact fuel
  arithmetic;
- out-of-fuel replay for both pending ordinary transitions and pending request
  emissions; and
- agreement of each replay theorem with the existing soundness theorem.

Semantics publishes and verifies:

- outcome-specific replay through arbitrary `HostHandler Context` values;
- `run_eq_of_fuelSoundWith`;
- the executable-result iff relation;
- generic done and fault fuel stability;
- combined-storage specializations; and
- checked and address-selected done stability, including contexts changed by
  one or more storage writes.

All new declarations must pass trust-zero and the semantic-kernel policy. The
proof must not use whole-context equality, proof irrelevance to erase handler
updates, or an assumption that requests are read-only.

## Required regressions

Compile-time consumers cover:

- each Core replay form directly;
- generic completeness for a handler that changes context;
- the public iff theorem in both directions;
- done stability at the same and a larger budget;
- raw fault stability on an untyped state;
- checked combined-storage done stability; and
- address-selected done stability after storage writes.

Executable regressions reuse the ADR-0119 programs:

- the read/write/read program completes at fuel 28;
- it returns the identical final value, Core-local store, and updated host
  context at a larger budget;
- the repeated-write program likewise retains the second write; and
- the fuel 21/22/27 out-of-fuel boundaries remain deliberately unstable when
  more fuel is supplied.

The tests must consume the public theorems, not merely compare two executions.

## Dependency boundary

Core replay depends only on Core host states, transitions, request emission,
and the existing runner. It imports no Semantics module.

Generic replay depends only on `HostHandler`, `HostDriver`, and the Core replay
interface. Storage specializations live in Semantics and reuse the existing
combined driver and address-selected adapter.

No parser, Surface, ABI, Oracle, Wire schema, gas schedule, frame-outcome, or
transaction-lifecycle module changes.

## Not decided here

This ADR does not add:

- a host capability or request constructor;
- caller, callee, code, storage-address, value, calldata, or call-kind
  observations;
- recursion, coinductive execution, or infinite traces;
- sufficient fuel for every host-checked program independently of a supplied
  handled-step witness;
- commit, rollback, trap classification, or conversion from Core values to
  return bytes; or
- a claim that out-of-fuel results are stable under additional fuel.

## Implementation sequence

Keep every green commit around 300 changed lines or less:

1. record this proof boundary and its non-goals;
2. add Core done/fault replay;
3. add Core suspension/out-of-fuel replay;
4. add generic handled done/fault/exhaustion replay and the iff theorem;
5. add generic and combined-storage terminal fuel stability;
6. add checked/address-selected theorem-use and executable regressions; and
7. run full validation and independent audit, then record acceptance evidence
   and synchronize current-facing internal documentation.

## Consequences

`FuelSoundWith` becomes an executable specification rather than only a
post-hoc explanation of driver output. Later request kinds can inherit a
two-way correctness boundary and terminal fuel stability without proving the
generic loop again.

This proof-first slice deliberately postpones new contract inputs and lifecycle
meaning. The retained storage-address observation remains a viable later
capability, but it should be considered only after the current driver relation
is complete.
