# ADR-0136: Resumable handled fuel slices

- Status: Accepted
- Decision date: 2026-08-29
- Scope: resume an exhausted handled Core run with an additional finite budget
- Implementation: In progress

## Context

The generic `HostDriver.run` already executes Core in finite chunks, handles
every emitted request, threads the exact handler context, and reuses the exact
remaining Core fuel. Its executable result is equivalent to the existing
`FuelSoundWith` relation. Completed and raw-faulted results are stable when the
original run receives a larger budget.

An exhausted result retains both the latest handler context and the exact Core
state that is ready for another transition or request. The repository proves
that this state is reached by exactly the supplied budget, but does not yet
connect two ordinary uses of the driver: running with `fuel`, then continuing
an exhaustion with `additional`, and running once with `fuel + additional`.

This missing law matters to internal bounded executors. Without it, a caller
can safely inspect exhaustion, but has no proved way to divide one execution
budget across multiple calls while preserving request count, context updates,
terminal values, Core-local Store, or fault state.

No new execution behavior is needed. `HandledSteps.trans`, driver soundness,
relational completeness, and terminal stability already contain the required
meaning.

## Decision

Add one total result consumer:

```lean
namespace Solcore.Semantics.HostDriverResult

def resumeWithFuel
    {Context : Type u}
    (result : HostDriverResult Context)
    (handler : HostHandler Context)
    (additional : Nat) : HostDriverResult Context :=
  match result with
  | ⟨context, .outOfFuel exhausted⟩ =>
      HostDriver.run handler context additional exhausted
  | terminal => terminal

end Solcore.Semantics.HostDriverResult
```

Only an `outOfFuel` result executes again. A `done` or `fault` result is
returned exactly, without invoking the handler or inspecting Core state.

The handler argument is explicit. Resumption is meaningful only under that
same handler used by the original run. The generic API cannot prove this for
an arbitrary forged result, so its central run law supplies the same handler
on both sides.

## Exact chunk law

Prove the exhaustion-specific equation:

```lean
theorem HostDriver.run_additional_of_outOfFuel
    (execution :
      HostDriver.run handler context fuel state =
        ⟨nextContext, .outOfFuel exhausted⟩) :
    HostDriver.run handler context (fuel + additional) state =
      HostDriver.run handler nextContext additional exhausted
```

The equation preserves the exact intermediate context and exhausted state.
The second run starts after the first budget; it does not replay the last Core
transition, repeat the request that produced the current context, or reset any
handler state.

Expose the total consumer equation in the direction convenient to callers:

```lean
theorem HostDriverResult.resumeWithFuel_run :
    (HostDriver.run handler context fuel state).resumeWithFuel
        handler additional =
      HostDriver.run handler context (fuel + additional) state
```

This theorem covers all three possible outcomes of the first run:

- exhaustion resumes from the exact retained context and state;
- completion stays exact by the existing done stability law; and
- a raw fault stays exact by the existing fault stability law.

Out-of-fuel is not declared stable. Additional fuel may produce another
exhaustion, a completion, or a raw fault.

## Resumption algebra

Sequential additions associate for every result when the handler is fixed:

```lean
theorem HostDriverResult.resumeWithFuel_add :
    (result.resumeWithFuel handler first).resumeWithFuel handler second =
      result.resumeWithFuel handler (first + second)
```

For an actual run this yields exact one-shot coherence:

```lean
((HostDriver.run handler context fuel state).resumeWithFuel handler first)
    |>.resumeWithFuel handler second =
  HostDriver.run handler context (fuel + first + second) state
```

Additional fuel zero is an identity for an actual `run` result. Do not state a
zero identity for arbitrary forged results: a value tagged `outOfFuel` may
retain a state that is already terminal, in which case executing with zero
correctly discovers that terminal outcome.

Constructor equations must also make the non-executing branches explicit:

```lean
resumeWithFuel ⟨context, .outOfFuel state⟩ handler additional =
  HostDriver.run handler context additional state

resumeWithFuel ⟨context, .done value store⟩ handler additional =
  ⟨context, .done value store⟩

resumeWithFuel ⟨context, .fault error state⟩ handler additional =
  ⟨context, .fault error state⟩
```

## Relational proof boundary

Do not unfold the recursive driver to prove the chunk law. Instead:

1. use `run_fuelSound` and the first execution equation to obtain an exact
   `HandledSteps fuel` prefix ending at `nextContext` and `exhausted`;
2. obtain fuel-sound evidence for the additional run;
3. compose its done, exhausted, or fault path with the exact prefix using
   `HandledSteps.trans`;
4. account for `fuel + spent` or `fuel + additional`; and
5. replay the composed evidence with `run_eq_of_fuelSoundWith`.

This proof retains the existing meaning of handled-request cost. It adds no
Core `hostRun` rule, transition, request kind, handler callback, or termination
assumption.

Expose a reusable relational prefix lemma only if it makes the proof boundary
clear. It must preserve exact intermediate context and state and distinguish
the bounded done/fault branches from exact-budget exhaustion.

## Storage specialization

Prove the corresponding theorem for `HostStorageDriver.run`:

```lean
theorem HostStorageDriver.run_additional_of_outOfFuel
    (execution :
      HostStorageDriver.run context inputs fuel state =
        ⟨nextContext, .outOfFuel exhausted⟩) :
    HostStorageDriver.run context inputs (fuel + additional) state =
      HostStorageDriver.run nextContext inputs additional exhausted
```

Both sides use the exact same complete `ExecutionInputs`. Resumption may not
replace code address, call value, caller address, or input data. The retained
mutable context is the one returned at exhaustion, including every completed
storage write and preserved checkpoint/effect component.

No serialized continuation, process token, or new storage carrier is added.
The existing `HostDriverResult` is sufficient.

## Required proof obligations

Provide focused laws for:

- all three constructor equations of `resumeWithFuel`;
- exact additional execution after a proved exhaustion;
- total `resumeWithFuel_run` coherence;
- zero-additional identity for actual run results;
- sequential-resumption/addition coherence;
- exact preservation of context, value, Store, error, and fault state on the
  terminal branches;
- relational path and fuel accounting in every suffix outcome;
- same-handler and exact-intermediate-state boundaries; and
- the same-`ExecutionInputs` storage specialization.

The new laws must remain compatible with driver completeness, result
uniqueness, outcome typing, and the existing statement that out-of-fuel is
budget-relative.

## Required regressions

Generic driver tests must cover:

- exhaustion followed by another exhaustion;
- exhaustion followed by completion;
- exhaustion followed by a raw fault in an intentionally unchecked fixture;
- a request-ready state run first with zero fuel and then one unit, so the
  request is handled once and execution exhausts immediately after that
  handler update;
- resumption of that post-handler exhaustion without handling the same request
  twice;
- one-shot and split execution producing the identical final context, value,
  Store, error, and state;
- zero additional fuel on an actual result;
- two sequential additions agreeing with their summed addition; and
- completed and faulted inputs remaining byte-for-byte unchanged without a
  handler call.

A storage-driver regression must perform a working-storage write before its
first exhaustion. Resumption must retain that write, complete under the same
immutable inputs, and equal the one-shot run. It must also show that changing
one observed input field can change an input-sensitive suffix result. This is
an existential regression, not a general disequality theorem: an arbitrary
program may ignore the changed input. Resumption with changed inputs is not
justified by this ADR.

Use measured budgets from executable states. Do not infer transition costs
from source expression shape.

## Dependency and publication boundary

The generic operation belongs above Core and depends only on the existing host
driver and its relational metatheory. The storage theorem may depend on the
canonical storage handler and complete execution input.

Add no Core constructor, HostFunction, HostRequest, Wire tag, Oracle command,
schema, profile, metadata capability, Surface form, parser rule, ABI rule, or
public protocol. The root README does not change. Publication requires a
separate decision.

## Non-goals

This ADR does not define or prove:

- gas, wall-clock time, scheduling, asynchronous execution, or fairness;
- checkpoint persistence, continuation serialization, or process recovery;
- resumption with a different handler or different `ExecutionInputs`;
- transaction commit, rollback application, parent-frame resumption, nested
  invocation, callback delivery, or call-stack behavior;
- recursion, divergence, infinite traces, or termination with increasing
  fuel;
- stability of an out-of-fuel result under a larger budget; or
- any source, parser, ABI, Wire, Oracle, or public-format behavior.

## Implementation sequence

Every commit must remain green and contain at most 300 changed lines:

1. add this ADR and activate it in the internal status documents separately;
2. add `resumeWithFuel` and its exact constructor equations;
3. prove exhaustion-prefix composition and the generic one-shot/split law;
4. prove zero and sequential-addition algebra over actual runs and the safe
   stronger arbitrary-result law where applicable;
5. add the exact same-input storage specialization;
6. add generic and storage executable regressions and register them;
7. run trust, axiom, dependency, build, test, metadata, kernel, compatibility,
   and independent audits; and
8. synchronize completion evidence without changing the root README.

Temporary proof helpers and test-only production APIs must be removed before
completion.

## Consequences

Internal callers can divide a finite handled execution budget into explicit
chunks and later prove that the combined run is exactly the same execution as
one larger budget. Context updates and Core state are resumed, not replayed,
while completed and faulted results remain terminal.

This law improves bounded execution control without introducing gas,
scheduling, persistence, nested calls, or any new public language behavior.
