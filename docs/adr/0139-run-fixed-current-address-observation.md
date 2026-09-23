# ADR-0139: Run-fixed current-address observation

- Status: Accepted
- Decision date: 2026-08-30
- Scope: expose one explicit current-context Address to internal Core code
- Implementation: Complete

## Context

Internal handled execution already separates three address roles. A retained
storage selector chooses the Account whose storage is read and written. An
immutable code selector chooses the checked program. A caller-supplied caller
Address is observable by Core. None of these values is defined as the Address
of the currently executing contract context.

The same immutable `HostStorageDriver.ExecutionInputs` also carries call value
and bounded input data through selected execution and fuel resumption. This
gives another contract-entry observation an exact lifetime: one complete input
is fixed for one handled run and every continuation of that run.

Solcore does not yet have a call-kind algebra, nested invocation transition,
active frame stack, or child-input constructor. Therefore this slice cannot
derive a current Address from another role. It can nevertheless make the role
available without inventing such a relationship: the run constructor supplies
the Address explicitly and Core has a concrete consumer for it.

## Decision

Append one required field to the immutable execution input:

```lean
namespace Solcore.Semantics.HostStorageDriver

structure ExecutionInputs where
  codeAddress : Address
  callValue : Core.Word
  callerAddress : Address
  inputData : InputData
  currentAddress : Address

end Solcore.Semantics.HostStorageDriver
```

For an execution parameterized by `inputs`, `inputs.currentAddress` means
exactly the current-context Address explicitly supplied for that run. The same
complete `inputs` value is reused when retained exhaustion is resumed, so the
same-address property applies to every proved split of that execution.

The retained result carrier is not indexed by `ExecutionInputs`, and the
existing resumption function accepts its input explicitly. It is therefore
possible to call that function on a forged result or with different inputs;
this ADR gives such a call no continuation-of-the-same-run interpretation.
Split-fuel and lifetime laws quantify over one unchanged `inputs` value and do
not claim invariance or coherence when a caller replaces it during resumption.

Do not provide a default, optional value, inference rule, or compatibility
constructor. Every construction of `ExecutionInputs` must state the new role.

## Address-role separation

The operational roles remain independent:

| Value | Exact use in this semantics |
| --- | --- |
| storage selector | chooses the Account used by storage reads and writes |
| `inputs.codeAddress` | chooses checked code and answers `codeAddress` |
| `inputs.callerAddress` | answers `callerAddress` |
| `inputs.currentAddress` | answers `currentAddress` |

No equality or inequality is required between these Addresses. In particular,
the current Address does not select code or storage in this slice, and its
Account need not exist. This preserves enough information for a future call
kind to impose the appropriate relationships instead of building one call
model into the base execution input.

Do not add `calleeAddress` in this slice. Naming the existing code selector as
a callee would collapse roles that may differ, while adding an independent
callee target has no operational distinction until nested invocation and call
kind exist.

## Core host capability

Append one internal capability to the canonical registry:

```lean
inductive HostFunction where
  -- existing constructors at indexes 0 through 8
  | currentAddress
```

`currentAddress` has parameter type Unit, result type Word, and stable index 9.
All existing indexes remain unchanged. `HostFunction.all`, `hostContext`, and
`hostEnvironment` therefore have length 10, and index 10 is first unbound.

Append the corresponding `HostRequest.currentAddress`. Its response is Word,
its Core response type is Word, and resumption injects `.word response` while
preserving the saved continuation and Core-local Store. Applying the host
function to Unit emits exactly that request; any other argument produces the
existing `invalidHostArgument` fault.

Core owns only the typed capability and request. It does not import Address,
WorldState, frame, or invocation policy.

## Handler and execution meaning

Interpret the request through the strict Address bridge:

```lean
handleRequest inputs context .currentAddress =
  (context, addressToWord inputs.currentAddress)
```

The request is read-only. It performs no Account or code lookup and preserves
the complete mutable handler context. Strict narrowing of the response recovers
exactly `some inputs.currentAddress`.

The generic driver, selected-code execution, branch-complete parent result,
and resumption operation keep their existing signatures apart from the larger
`ExecutionInputs` record. Selected code lookup still uses only
`inputs.codeAddress`; working storage still uses only the retained storage
selector. Terminal results continue to preserve their exact context, Core
value, Store, and parent continuation.

## Exact proof obligations

Expose focused laws for:

- every `ExecutionInputs` constructor projection, including `currentAddress`;
- capability parameter type, result type, registry membership, and index 9;
- canonical registry, host-context, and host-environment length 10;
- exact registry, host-context, and host-environment lookup and first-unbound
  index 10;
- request response type, response value, and suspension resumption;
- Unit application, request emission, and invalid-argument behavior;
- executable/declarative transition and emission correspondence;
- typed emission, response typing, preservation, progress, and checked
  no-fault execution;
- exact handler response and complete context identity;
- exact resumed control, continuation, and Core-local Store;
- `wordToAddress?` recovery of the supplied Address;
- recursive driving under the same complete execution input; and
- unchanged selected-code lookup, branch classification, split-fuel
  resumption, parent completion, and existing resolution fold behavior.

No theorem may identify `currentAddress` with the storage selector, code
selector, caller Address, a callee, an Account owner, or an authority.

## Required regressions

Low-level Core regressions must cover:

- unchanged indexes 0 through 8, `currentAddress` at 9, table length 10, and
  first-unbound index 10;
- registry membership and exact lookup for the appended capability;
- host-check acceptance of `currentAddress Unit` and closed-check rejection;
- static rejection and exact raw fault for a non-Unit argument;
- exact request emission, response injection, continuation, and Store reuse;
- measured request-ready, suspension, and handled-completion fuel boundaries;
  and
- rejection of the internal host-function value by frozen Wire v1 and v2.

End-to-end regressions must:

- use distinct storage, code, caller, and current Addresses, call-value Word,
  and input-data size Word, making accidental projection swaps observable;
- return the exact widened current Address and remain stable with extra fuel;
- succeed when the current Address has no Account in either checkpoint or
  working WorldState;
- vary only `currentAddress`, changing the returned Word while preserving code
  selection, handler context, checkpoint, effects, and Core Store exactly;
- observe the current Address, write its Word to working storage, observe it
  again, and return both equal observations around the mutation;
- stop at a measured request boundary, resume with split fuel, and agree with
  the corresponding one-shot branch-complete run; the retained Core state must
  be past the write request and begin the exact remaining suffix so idempotence
  of writing the same Word cannot hide request replay;
  and
- carry a current-derived completion through the parent continuation and the
  existing return/revert/trap resolution fold.

Measured fuel values are test results, not assumptions. Record the values found
by the executable machine and update this ADR if implementation changes them.

## Dependency and publication boundary

Semantics owns the explicit Address, lossless widening, strict recovery, and
request interpretation. Core sees only an internal Unit-to-Word capability.
Generic host-driver and frame-continuation modules remain parameterized and do
not acquire Address-specific meaning.

Frozen Wire v1 and v2 continue to reject host-function values. Add no Wire tag,
schema, profile, source form, parser rule, or source
elaboration. Source-syntax and parser proofs remain paused. The root README
does not change.

## Non-goals

This ADR does not define or prove:

- any unconditional equality or inequality between `currentAddress` and
  another address role;
- a callee, call target, `self`, delegate, library, proxy, implementation,
  creator, beneficiary, owner, signer, authority, or transaction origin;
- current-Account presence, code presence, storage ownership, balance, nonce,
  liveness, or private-key control;
- call kind, static-write restrictions, delegate behavior, creation,
  dispatch, fallback, receive, or constructor behavior;
- child `ExecutionInputs` construction, nested invocation, call stack, call
  depth, recursion, reentrancy, scheduling, callback delivery, or parent Core
  resumption;
- balance transfer, affordability, denomination, conservation, refund, gas,
  fork rules, events, or logs;
- checkpoint capture, Account lifetime, transaction commit, rollback
  application, finalization, or persistence;
- conversion of arbitrary Core Value or Store to Bytes, automatic
  `FrameOutcome` selection, return-data policy, ABI, calldata, or storage
  layout; or
- a public representation, compatibility promise, or parser change.

## Implemented sequence

The decision was implemented in bounded green commits:

1. recorded and activated this contract;
2. appended the required input field and migrated explicit constructors;
3. appended the Core capability and request, closing all exhaustive machine and
   safety proofs while retaining indexes 0 through 8;
4. added exact handler, strict-recovery, and driver laws;
5. added focused Core layout, admission, fault, suspension, fuel, and frozen-Wire
   regressions;
6. added end-to-end selected, storage, parent, fold, and resumption regressions;
7. ran full validation, audited the contract independently, and synchronized the
   completion record.

## Implementation and validation

`currentAddress` is the tenth canonical host capability: its stable index is
9, both derived host tables have length 10, and index 10 is first unbound. The
Unit request returns the exact widened run input, preserves the full handler
context, continuation, and Core-local Store, and strict narrowing recovers the
supplied Address. Existing indexes 0 through 8 and frozen Wire v1/v2 remain
unchanged.

Direct execution measures the exact request/completion boundary at fuel 4/5.
The end-to-end observe/write/observe program measures fuel 16, 17, 23, 29,
and 30; resumptions at 17+13 and 23+7 equal the one-shot fuel-30 completion.
Its distinct address sentinels, absent current Accounts, exact current-only
input variation, retained write, equal returned pair, and return/revert/trap
folds make projection swaps, implicit lookup, request replay, and state loss
observable.

The 676-job build, 1,240-job test executable build, and full test run pass.
All 33 changed Lean roots pass trust-zero with warnings as errors; metadata,
semantic-kernel, diff, axiom, compatibility, and independent P0-P3 audits also
pass. The root README and all published formats remain unchanged.

## Consequences

Internal Core code gains one exact observation of the current execution
context's caller-supplied Address. The observation has a precise run and
resumption lifetime, no implicit state lookup, and no public syntax or format.
The model deliberately records the role before fixing the future relationships
among current context, code execution, storage ownership, and call kind.
