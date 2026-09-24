# ADR-0123: Handled-execution relational metatheory

- Status: Accepted
- Decision date: 2026-08-29
- Scope: composition, type safety, and result uniqueness for handled execution relations
- Implementation: Complete

## Context

ADR-0119 introduced `HostDriver.HandledSteps` and
`HostDriverResult.FuelSoundWith` as readable, fuel-indexed specifications of the
generic dependent host driver. ADR-0120 proved that executable results and
fuel-sound witnesses determine each other. ADR-0122 completed that equivalence
through optional address-selected code lookup.

The relation itself still lacks common proof interfaces. Two handled paths
cannot be joined by a named theorem. Type preservation is available for the
executable driver but not directly for a caller-supplied `HandledSteps` or
`FuelSoundWith` witness. Completeness implies that two witnesses at one fuel
must describe the same result, but that uniqueness is not published.

These gaps force semantic consumers to replay a witness through the executor or
rebuild induction over request boundaries. They can be closed without changing
execution, adding a host capability, or deciding any contract-entry or frame
lifecycle meaning.

## Decision

Expose a compact named relational metatheory at the existing generic boundaries.
It has four parts:

1. composition of ordinary Core host paths and handled paths;
2. direct type preservation across handled requests;
3. uniqueness of fuel-sound results for one exact budget; and
4. monotonicity and uniqueness only for terminal done and raw-fault results.

The theorems retain exact handler contexts. No handler-context preservation
assumption is introduced.

## Path composition

Add the host-aware Core path law:

```lean
theorem Core.HostSteps.trans
    (left : Core.HostSteps leftSteps start middle)
    (right : Core.HostSteps rightSteps middle finish) :
    Core.HostSteps (leftSteps + rightSteps) start finish
```

Then add the handled lift:

```lean
theorem HostDriver.HandledSteps.trans
    (left :
      HostDriver.HandledSteps handler leftSteps
        startContext start middleContext middle)
    (right :
      HostDriver.HandledSteps handler rightSteps
        middleContext middle finalContext finish) :
    HostDriver.HandledSteps handler (leftSteps + rightSteps)
      startContext start finalContext finish
```

The intermediate Core state and handler context must match exactly. Request
emissions already contribute one unit in each input relation, so composition
adds only the two recorded totals. It must not add another unit at the join.

The `.core`/`.handle` case joins the left Core path to the right handled path's
first Core prefix. The `.handle` case recursively joins the existing handled
suffix. Handler updates remain in order and are never commuted or erased.

## Relational type safety

Expose direct preservation:

```lean
theorem HostDriver.HandledSteps.preserve
    (path :
      HostDriver.HandledSteps handler steps
        startContext start finalContext finish)
    (typing :
      Core.HostStateHasType start resultType definitions) :
    Core.HostStateHasType finish resultType definitions
```

For an ordinary Core segment this reuses `Core.HostSteps.preserve`. At a handled
request boundary, the proof:

1. preserves typing to the request-emitting state;
2. obtains the dependent suspension type from the emission;
3. uses `HostHandler.handleSuspension_state_hasType` for the exact response;
4. rewrites with the recorded handler equation; and
5. continues through the suffix.

Lift this result to complete fuel evidence:

```lean
theorem HostDriverResult.FuelSoundWith.hasType
    (sound :
      result.FuelSoundWith handler fuel startContext start)
    (typing :
      Core.HostStateHasType start resultType definitions) :
    result.outcome.HasType resultType definitions
```

A done path yields a typed value and Core-local store. An exhausted path retains
a typed state. A purported raw-fault path contradicts the existing theorem that
a well-typed host state cannot fault. Fuel bounds and readiness evidence do not
alter the typing argument.

## Fuel-sound result uniqueness

For one exact budget, expose:

```lean
theorem HostDriverResult.FuelSoundWith.result_unique
    (leftSound :
      left.FuelSoundWith handler fuel startContext start)
    (rightSound :
      right.FuelSoundWith handler fuel startContext start) :
    left = right
```

ADR-0120 already proves that each witness replays to the same executable run.
Uniqueness therefore includes final handler context and all outcome data. It
applies to done, out-of-fuel, and raw-fault results only when the supplied fuel
is identical.

For terminal outcomes, expose the relation's direct fuel monotonicity:

```lean
theorem HostDriverResult.FuelSoundWith.done_mono ...
theorem HostDriverResult.FuelSoundWith.fault_mono ...
```

Both witnesses store a path cost bounded by the supplied fuel, so the same path
remains valid under a larger budget. The exact final context, value, local
store, fault, and fault state remain unchanged.

Using monotonicity and same-fuel uniqueness at the maximum of two budgets,
expose exact cross-budget terminal uniqueness:

```lean
theorem HostDriverResult.FuelSoundWith.done_result_unique ...
theorem HostDriverResult.FuelSoundWith.fault_result_unique ...
```

These compare complete `HostDriverResult` values, not only returned values or
fault constructors. Handler updates in the final context therefore participate
in equality.

## Out-of-fuel boundary

No out-of-fuel monotonicity or cross-budget uniqueness theorem is valid.
`FuelSoundWith` records an exact-length path and a state ready to move. Extra
fuel may perform an ordinary transition, emit and handle a request, change the
handler context, exhaust later, complete, or fault.

Same-fuel `result_unique` includes out-of-fuel because the executable driver is
deterministic for a fixed budget. It must not be read as stability under a
different budget.

## Required regressions

Compile-time consumers must cover:

- `Core.HostSteps.trans` in execution order;
- `HandledSteps.trans` across a context-changing request boundary;
- `HandledSteps.preserve` for a typed storage-read suspension and response;
- `FuelSoundWith.hasType` on the same one-request done witness;
- same-fuel uniqueness for arbitrary competing fuel-sound results;
- done monotonicity and exact cross-budget done-result uniqueness;
- fault monotonicity and exact cross-budget fault-result uniqueness; and
- a concrete distinction between a lower-budget out-of-fuel result and a
  higher-budget done result.

The existing `changingHandler` fixture is sufficient. It increments its Nat
context when handling a request, so regressions detect accidental replacement
of the final context with the input context. No new runtime operation is needed.

## Dependency boundary

`Core.HostSteps.trans` lives with host-runner path properties and imports no
Semantics module. Handled composition and safety live with the generic fuel
relation, whose existing imports already supply Core path safety, request
typing, and dependent response typing. Result uniqueness lives with generic
driver completeness.

Storage, Account, WorldState, Address, frame outcomes, and concrete handlers do
not enter the generic proofs. No parser, source syntax, ABI, Wire, schema,
profile, or public runtime module changes. The root README does not change.

## Non-goals

This ADR does not prove:

- existence of a completed result for some finite fuel;
- normalization or a sufficient-fuel bound for host-aware checked code;
- cross-budget equality or monotonicity for out-of-fuel results;
- equality or commutativity of handler contexts;
- a new operational step, cost, request, response, or driver;
- a mapping from Core completion to return, revert, or trap; or
- contract inputs, nested invocation, commit, rollback, ABI, or publication.

Normalization remains a larger later proof. Frame lifecycle remains a separate
semantic adapter decision.

## Implementation sequence

Keep every green commit below roughly 300 changed lines:

1. record this relational proof boundary and its non-goals;
2. add Core and handled path composition;
3. add handled-path and fuel-evidence type safety;
4. add fixed-fuel uniqueness and terminal relational stability;
5. add direct compile-time consumers and the out-of-fuel distinction; and
6. run full validation and independent audit, then synchronize acceptance
   evidence and current-facing internal documents.

## Implementation record

`Core.HostSteps.trans` composes host-aware Core paths in execution order.
`HostDriver.HandledSteps.trans` lifts composition through arbitrary dependent
handlers. Its `.core`/`.handle` case joins the left Core path to the next
request prefix; its `.handle` case joins only the handled suffix. The exact
middle state and context remain indices of both paths, and the join adds no
extra request cost.

`HandledSteps.preserve` now follows typing through each Core prefix, typed
request emission, exact dependent response, and handled suffix.
`FuelSoundWith.hasType` lifts that proof to done, out-of-fuel, and impossible
typed-fault outcomes without replaying the witness through the executor.

`FuelSoundWith.result_unique` reuses ADR-0120 completeness to make all results
unique at one exact fuel. `done_mono` and `fault_mono` widen only their stored
path bound. `done_result_unique` and `fault_result_unique` raise two witnesses
to a common maximum budget, then compare their complete results. Final handler
context, Core value/store, error, and fault state all remain part of equality.
No out-of-fuel monotonicity theorem was added.

## Regression record

The existing context-changing handler now supplies one connected regression
story. Two nonempty Core paths compose in order. A handled request changes the
Nat context from zero to one, then composes with two more Core transitions.
The same typed storage-read path directly exercises handled preservation and
fuel-evidence outcome typing.

Further consumers exercise same-fuel result uniqueness, done and fault
monotonicity, and exact cross-budget terminal-result uniqueness. A concrete run
of the composed request fixture is out of fuel at budget 1 and done at budget 3,
preventing terminal monotonicity from being generalized to out-of-fuel.

## Acceptance evidence

- the full build completed successfully with 619 build jobs;
- `lake test` completed successfully with 1,126 jobs;
- all four changed Lean modules passed trust-zero with warnings as errors;
- the semantic-kernel policy check passed;
- printed axioms contain only existing standard `propext` and `Quot.sound`
  dependencies, with no custom axiom, `Classical.choice`, or `sorryAx`;
- independent proof and final audits found no P0, P1, P2, or P3 issue;
- every commit stayed below 300 changed lines; and
- the root README, parser-facing code, runtime behavior, and public formats
  remained unchanged.

## Consequences

Handled paths are compositional and directly type-safe. Fuel-sound result
witnesses are functional at a fixed fuel budget. Terminal relational evidence
is independent of which sufficient budget produced it, including the exact
final handler context.

Later normalization, lifecycle, and contract-entry work can consume these
properties without unfolding the relation or detouring through ad hoc executor
equalities. Resource exhaustion remains explicitly budget-relative.
