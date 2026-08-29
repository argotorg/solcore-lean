# ADR-0131: End-to-end call-value observation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: expose one caller-supplied invocation-value word to internal Core code
- Implementation: Complete

## Context

The internal host boundary can select checked code and storage independently,
execute that code with a typed storage handler, and retain both selectors as
read-only Core observations. ADR-0126 completed `codeAddress : unit -> word`
using the same Address for code lookup and observation. ADR-0125 carries the
completed execution into a parent-indexed continuation without flattening
storage absence, code absence, fuel exhaustion, or completion.

Contract code also needs a value supplied for one invocation. Core already has
a 256-bit Word, arithmetic, comparison, local state, and working-storage
consumers, so this input requires no new value type, byte layout, parser rule,
or ABI decision.

The mutable storage-handler context is the wrong owner for this input. Storage
writes replace that context during a run, while the invocation value must stay
fixed. The existing code selector has the same lifetime. Both values therefore
belong in one immutable parameter threaded through code selection, request
handling, recursive driving, fuel evidence, and completed continuation
construction.

This repository has no balance model. The supplied Word is consequently not
evidence that funds were debited, credited, available, transferred, or
denominated in any external unit. It is exactly the invocation-value word
chosen by the caller of the internal execution API.

## Decision

Add one internal static-input carrier outside the mutable storage context:

```lean
namespace Solcore.Semantics.HostStorageDriver

structure ExecutionInputs where
  codeAddress : Address
  callValue : Core.Word

end Solcore.Semantics.HostStorageDriver
```

The carrier is fixed for one handled run. Its `codeAddress` member replaces the
standalone code-address parameter throughout the combined storage path. The
same member selects checked code and answers the existing code-address request.
Its `callValue` member answers the new call-value request exactly.

Do not add either field to `HostStorageDriver.Context`, WorldState, Account,
the Core-local Store, a continuation context, or a frame result. Callers that
need to retain the static input alongside a result may do so in their own
carrier.

## Core host capability

Append exactly one internal capability after the four existing entries:

```lean
inductive HostFunction where
  | storageRead
  | storageWrite
  | storageAddress
  | codeAddress
  | callValue
```

`HostFunction.callValue` has parameter type Unit, result type Word, and stable
index 4. The existing indexes 0 through 3 do not move. `hostContext` and
`hostEnvironment` append the corresponding function type and runtime host
value, so each has length 5.

Append the matching first-order request:

```lean
inductive HostRequest where
  | storageRead (slot : Word)
  | storageWrite (slot value : Word)
  | storageAddress
  | codeAddress
  | callValue
```

`HostRequest.callValue.Response` is `Word`; its response type is Core Word and
its response value is `.word response`. Applying the capability to Unit emits
that request. Any other argument produces the existing typed invalid-host-
argument fault. Resumption injects the exact returned Word while preserving
the saved continuation and Core-local Store.

The declarative host transition, request-emission, progress, preservation,
runner correspondence, and no-fault boundaries must cover the new constructor.
Checked host programs may use the capability; closed programs remain admitted
unchanged.

## Handler and driver meaning

The final handler equations are:

```lean
handleRequest inputs context .codeAddress =
  (context, addressToWord inputs.codeAddress)

handleRequest inputs context .callValue =
  (context, inputs.callValue)
```

Both observations are read-only. Their suspension handlers resume with the
exact Word, saved continuation, and saved Store. Storage read and write keep
their existing meanings, including the separately retained storage selector.

`handler`, `handleSuspension`, `HostStorageDriver.run`, and
`CheckedHostCoreProgram.runWithStorage` take `ExecutionInputs` instead of a
standalone code Address. The same value indexes every recursive driver call and
its handled-step and fuel-soundness evidence.

The selected-execution chain also takes the same input:

```lean
context.runCodeWithStorage? inputs fuel
context.runCodeWithStorageContinuationContext? inputs fuel doneOutcome
initialization.runCodeWithStorageParentIndexedContinuationContext?
  storageAddress inputs fuel doneOutcome
```

Code lookup uses `inputs.codeAddress`, and the selected checked program is run
with that exact `inputs`. The ADR-0124 two-option result and ADR-0125
three-option result retain their current shapes and meanings. No failure is
flattened, renamed, retried, or converted to a frame trap.

## Exact proof obligations

The existing proof interfaces are migrated from a bare code Address to the
same `ExecutionInputs`. In addition, expose focused exact laws for:

- both carrier projections;
- capability parameter type, result type, and index 4;
- host-context and environment lookup and length 5;
- request response type, response value, and exact suspension resumption;
- begin-application, Unit-request emission, and invalid-argument behavior;
- typed request emission and preservation through resumption;
- exact handler response and unchanged mutable context;
- exact resumed control, continuation, and Store;
- recursive driver handling with the same inputs and remaining fuel;
- driver preservation, type safety, no-fault safety, fuel soundness,
  completeness, and completed larger-fuel stability;
- selected-code absence and success using `inputs.codeAddress`;
- selected execution using the same inputs for lookup and handling; and
- unchanged ADR-0124 and ADR-0125 optional branches, whole-context coherence,
  and completed larger-fuel stability.

No theorem may identify call value with code address, storage address, an
Account balance, or a value stored in WorldState. No theorem calls it paid,
funded, transferred, authorized, or conserved.

## Required regressions

Low-level Core tests must cover:

- the append-only index and context/environment lookup;
- Unit application emitting `.callValue`;
- exact response injection with continuation and Store preservation;
- a non-Unit raw application producing the exact invalid-host-argument fault;
- a checked call-value observation program and rejection of the ill-typed
  variant; and
- rejection of the internal host value by frozen Core Wire v1 and v2.

The end-to-end storage fixture must use three distinct nonzero observations:
storage address, code address, and call value. A checked program applying the
index-4 capability to Unit must stop at the measured request boundary with
fuel 4, complete with the exact supplied call-value Word at fuel 5, and retain
the identical complete result and mutable context with larger fuel. At least
one checked program must feed the observed Word into an existing Core or
storage consumer so the capability is not tested only as an isolated marker.
An observe-write-observe fixture must read the call value on both sides of a
storage write, obtain the same Word twice, and verify that the written storage
value is that Word.

Compile consumers must apply the input-indexed fuel and selected-execution laws
directly, preserve all ADR-0125 optional boundaries, reach the parent-indexed
completed context, consume that exact context through ADR-0129's fold, and
retain completed larger-fuel stability. The completed fixture must make its
outcome depend on the supplied call value, so the parent fold checks the same
value-derived working storage and terminal bytes rather than an unrelated
context. Tests must distinguish the three static/storage observations
numerically.

## Dependency and publication boundary

Core owns only the append-only typed capability and first-order request. It
does not import Address, WorldState, frames, or the storage driver. Semantics
owns `ExecutionInputs`, Address widening, request interpretation, selected code
lookup, and the execution/continuation chain.

The change is internal and additive to Core vNext. Frozen Core Wire v1 and v2
continue to reject all host-function values. Oracle, Surface, Parser, ABI,
schemas, profiles, metadata digests, and the root README do not change.

## Non-goals

This ADR does not define:

- balance fields, debit, credit, transfer, affordability, conservation,
  denomination, payability, refund, or value rollback;
- caller, origin, current contract, callee, beneficiary, owner, or authority;
- equality between any address roles;
- calldata, return-data decoding, call kind, static-call restrictions, or
  delegate-call behavior;
- Account lifetime, checkpoint provenance, parent resumption, nested
  invocation, stack, scheduling, reentrancy, or transaction finalization;
- callback evaluation count, additional fuel charge, gas, or EVM fork policy;
- a new Core value, expression, source construct, parser rule, ABI layout,
  public runtime request, Wire tag, Oracle command, or serialization; or
- a generic contract-input carrier with fields that have no current consumer.

## Implemented sequence

The work was completed in bounded commits in this order:

1. recorded and activated this exact internal contract;
2. introduced `ExecutionInputs` and an explicit input-aware handler/driver
   migration seam without a zero or optional default;
3. migrated handler, driver, fuel, and proof consumers to the immutable input;
4. migrated selected execution, completion, parent continuation, runtime, and
   compile consumers;
5. removed the old bare-address seam and all temporary migration names;
6. promoted the input-aware modules and operations to their canonical names;
7. appended the Core capability and request and closed every machine, progress,
   typing, preservation, runner, and no-fault branch;
8. added exact handler and driver laws plus the low-level Core regressions;
9. added direct observation, observe-write-observe, parent completion, and
   resolution-fold regressions; and
10. ran repository validation and synchronized the completion record.

No completed API manufactures a zero, absent, or otherwise default call value.

## Implementation record

`HostStorageDriver.ExecutionInputs` is now the canonical immutable input to one
handled run. Its exact value is threaded through request handling, recursive
driving, handled-step and fuel evidence, checked-code selection, completed
continuation construction, and parent-indexed continuation construction. Code
lookup uses `inputs.codeAddress`; `.codeAddress` and `.callValue` requests use
the two corresponding projections. The mutable storage context contains
neither field.

Core appends `HostFunction.callValue` at index 4 with type `unit -> word` and
the matching first-order `HostRequest.callValue`. Host-context and environment
lengths are 5. Application, request emission, invalid argument handling,
response injection, resumption, progress, transition preservation, state
typing, runner correspondence, and checked-program no-fault coverage all
include the new constructor. Frozen Wire v1 and v2 continue to reject the
internal host value.

The storage handler returns `inputs.callValue` exactly and leaves its complete
mutable context unchanged. Its suspension law preserves the saved Core
continuation and local Store. The driver law resumes that exact Word with the
exact remaining fuel and the same immutable input.

The end-to-end fixture uses distinct nonzero storage address, code address, and
call value observations. Direct call-value execution stops at the request with
fuel 4, completes with the supplied Word at fuel 5, and has the same completed
result and context at fuel 32. The observe-write-observe program writes the
observed Word, observes the same Word again, completes as a pair of equal
values at fuel 30, and remains identical at fuel 32. The value-dependent
parent-indexed completion reaches ADR-0129's fold, which recovers both the
written call value and the designated terminal bytes without flattening any
ADR-0125 optional boundary.

## Acceptance evidence

- the full build completed successfully with 643 jobs;
- the complete executable test suite passed;
- metadata verification and semantic-kernel policy checks passed;
- focused Core regressions cover acceptance, ill-typed and raw-machine
  rejection, exact emission and resumption, append-only layout, fuel 4/5, and
  frozen Wire v1/v2 rejection;
- end-to-end regressions cover three distinct observations, context identity,
  a value-derived storage write, larger-fuel stability, parent-indexed
  completion, and the exact resolution-fold result; and
- consistency inspection found no old bare-address driver API, temporary
  migration name, default call value, parser change, public-format change, or
  root README change in the completed slice.

## Consequences

Internal checked Core code can observe one exact invocation-value Word that is
fixed across storage updates, suspensions, recursive driver calls, fuel
evidence, selected lookup, and completed parent-indexed construction. The
observation composes immediately with existing Word and storage semantics.

Balance transfer and full call-frame meaning remain separate future decisions.
Root finalization and parent resumption remain blocked on checkpoint lifetime,
parent-machine, byte-delivery, scheduling, and persistence definitions.
