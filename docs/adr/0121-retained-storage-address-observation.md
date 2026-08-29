# ADR-0121: Retained storage-address observation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: expose the retained working-storage selector to host-aware Core code
- Implementation: Complete

## Context

The combined host driver can read and write the working storage selected by
`FrameCheckpointedWorkingPairWithPresentStorageAccount`. Core code still cannot
observe which Address that context selected. The selector already has a clear
producer and lifetime: it is the caller-designated retained storage selector,
it is used by every handled storage access, and existing whole-run laws prove
that reads and writes retain it.

This is the narrowest useful contract-entry observation after ADR-0120.
`codeAddress` is not retained in the run context. Caller, value, calldata, and
call kind have no frame inputs or lifetime rules. Frame lifecycle also needs
return-byte encoding and a mapping to returned, reverted, and trapped outcomes.

The new observation must preserve the distinction already established by
address-selected execution. `codeAddress` chooses code; `storageAddress`
chooses the working Account whose storage is handled. They may differ.

## Decision

Append one runtime-only host capability named `storageAddress`, with exact type
`unit -> word` at index 2. Calling it returns the selector as a Core Word.

The name describes the existing selector only, not a current contract, `self`,
callee, caller, owner, origin, code address, or authorized principal. This ADR
does not define EVM `ADDRESS` or Solidity `address(this)`.

It is unary from Unit because Core host functions use unary application. A
typed caller supplies `.unit`; no nullary-call form is introduced.

## Exact Core contract

Extend the append-only capability universe as follows:

```lean
inductive HostFunction where
  | storageRead
  | storageWrite
  | storageAddress

HostFunction.storageRead.index = 0
HostFunction.storageWrite.index = 1
HostFunction.storageAddress.index = 2

HostFunction.storageAddress.parameterType = .unit
HostFunction.storageAddress.resultType = .word
```

The fixed capability tables become:

```lean
hostContext =
  [HostFunction.functionType .storageRead,
   HostFunction.functionType .storageWrite,
   HostFunction.functionType .storageAddress]

hostEnvironment =
  [.hostFunction .storageRead,
   .hostFunction .storageWrite,
   .hostFunction .storageAddress]
```

Read remains at index 0 and write at index 1, with unchanged types and values.
Both table lengths become 3; old read/write behavior and fuel stay fixed.

Extend the first-order request protocol with a payload-free request:

```lean
inductive HostRequest where
  | storageRead (slot : Word)
  | storageWrite (slot value : Word)
  | storageAddress

HostRequest.Response .storageAddress = Word
HostRequest.responseType .storageAddress = .word
HostRequest.responseValue .storageAddress response = .word response
```

Applying `.storageAddress` to `.unit` emits exactly
`HostRequest.storageAddress`. Any other runtime argument produces the existing
`invalidHostArgument` fault. Checked host programs cannot reach that fault.
Resumption injects the returned Word and preserves the saved CEK continuation
and Core-local store exactly.

## Semantics handler

The combined storage handler answers the request from its retained selector:

```lean
HostStorageDriver.handleRequest context .storageAddress =
  (context, addressToWord context.context.storageAddress)
```

The first projection is the exact input context. The request performs no
WorldState lookup or update and does not rebuild Account-presence evidence.

`addressToWord` is ADR-0053's lossless 160-to-256-bit widening. It preserves
the natural-number value, zero-extends the upper 96 bits, is injective, and
strictly narrows back. No second conversion, truncation, or reduction is added.

Account presence in the handler context makes storage access total; it does
not grant authority. Returning the selector likewise grants no permission and
does not make the Address an externally published identity.

## Fuel behavior

The existing host-runner accounting applies without modification:

1. evaluating the Unit argument uses ordinary Core transitions;
2. emitting the storage-address request consumes one Core fuel unit;
3. reading the retained selector, widening it, and injecting the response
   consume no additional Core fuel; and
4. execution resumes with exactly the remaining fuel returned by Core.

Zero fuel observes a terminal state but cannot emit a pending request. The new
request therefore follows the existing request-ready out-of-fuel rule.

ADR-0120's completeness and terminal stability theorems apply to the extended
handler. A completed or faulted run is stable under additional fuel. An
out-of-fuel result may change when more fuel is supplied, so no out-of-fuel
stability theorem is added.

## Required proof interface

Core publishes and verifies:

- exact parameter, result, index, table lookup, and length laws;
- exact begin-application, request-emission, suspension, invalid-argument,
  response, and resume laws;
- executable/declarative correspondence for the new emission branch;
- response typing, suspension typing, typed progress, and preservation;
- no-fault execution for checked host programs;
- unchanged runner soundness, relational replay, and fuel completeness; and
- continued rejection of the new host-function value by frozen Wire v1/v2.

Semantics publishes and verifies:

- the exact handler equation above and exact context identity;
- the exact widened response and recovery of the retained Address through
  `wordToAddress?`;
- continuation and Core-local store preservation;
- preservation of selector, checkpoint, working effect journal, checked code,
  and every non-selected working Account;
- direct use of generic fuel soundness/completeness and done stability; and
- address-selected no-fault and exact-final-context results.

Proofs reuse `addressToWord` and ADR-0120. They do not equate address roles,
erase other request updates, or derive out-of-fuel stability.

## Required regressions

Tests cover:

- fixed indices 0, 1, and 2 and all three capability-table entries;
- host-check acceptance of a `unit -> word` observation and closed-check
  rejection of the same open capability use;
- static rejection and raw-machine faulting for a non-Unit argument;
- exact request emission, Word response, continuation, and local-store reuse;
- a nontrivial storage Address and the maximum 160-bit Address widening to the
  exact expected Word;
- a fixture with `codeAddress != storageAddress` whose program returns the
  widened storage Address, not the code Address;
- observe, write, then observe again: both observations return the same
  selector while the write changes only the selected working Account;
- preservation of checkpoint, effect journal, checked code, and unrelated
  Accounts in that mixed run;
- exact request-ready out-of-fuel boundaries and completion with sufficient
  fuel;
- identical completed value, Core-local store, and final host context under a
  larger budget by the public stability theorem;
- unchanged read/write/read, repeated-write, sparse-zero, and fuel-boundary
  regressions from ADR-0119 and ADR-0120; and
- direct Wire v1 and v2 rejection of `.hostFunction .storageAddress`.

## Dependency boundary

Core owns the capability, tables, request, suspension, machine, and proofs. It
knows only a Word response and imports no Address, WorldState, or frame meaning.

Semantics owns interpretation and reuses the Address-to-Word bridge. Generic
`HostHandler` and `HostDriver` remain independent of storage and Address.

No parser, Surface, ABI, Oracle, schema, profile, or gas module participates in
the implementation.

## Compatibility and publication

This capability is internal and unpublished. Frozen Core Wire v1/v2 continue
to reject host-function values, and Oracle, Surface, Parser, schemas, profiles,
and published metadata remain unchanged. No new Core expression tag is needed;
internal programs use existing variables, application, and Unit syntax.

The extension is behavior-preserving for existing programs because the old
capability positions remain fixed. It is not Lean source-compatible for every
internal consumer: exhaustive matches on `HostFunction` or `HostRequest`, the
request-emission characterization, and every total `HostHandler` must add the
new branch. The fixed table length also changes from 2 to 3. This is an
intentional append-only expansion of an unpublished internal protocol, not a
claim of source compatibility.

## Non-goals

This ADR does not define current/self/callee/caller identity, origin, owner,
code address, authority, provenance, call kind, lifetime, or address equality.

It adds no balance or nonce operation, value transfer, calldata, ABI rule,
return encoding, external call, creation, recursion, reentrancy, stack, depth,
gas, refund, access warmth, log, self-destruction, or EVM revision policy.

The observation does not create an Account, mutate working state, capture a
checkpoint, commit or roll back a transaction, resolve a frame outcome, or
publish the returned context. Writes performed by other requests remain
speculative working-state updates until a later lifecycle decision says
otherwise.

## Implementation record

The implementation follows the existing host boundary rather than adding a
parallel environment mechanism. `HostFunction.storageAddress` and
`HostRequest.storageAddress` are now the third constructors. The fixed
capability indices are read 0, write 1, and storage address 2; both host tables
have length 3. The existing read and write positions and types did not move.

Core publishes the new contract through
`HostFunction.parameterType_storageAddress`,
`HostFunction.resultType_storageAddress`, `HostFunction.index_storageAddress`,
`hostContext_storageAddress`, and `hostEnvironment_storageAddress`. The request
and machine boundary is exposed by `HostRequest.responseType_storageAddress`,
`HostRequest.responseValue_storageAddress`, `HostSuspension.resume_storageAddress`,
`hostAdvance_begin_storageAddress`, `hostAdvance_suspend_storageAddress`, and
`hostAdvance_invalid_storageAddress_argument`. Progress, preservation,
request correspondence, runner replay, and checked-program no-fault proofs now
cover all three constructors.

The concrete semantic equation is exactly:

```lean
HostStorageDriver.handleRequest context .storageAddress =
  (context, addressToWord context.context.storageAddress)
```

`HostStorageDriver.handleRequest_storageAddress` and
`HostStorageDriver.handleSuspension_storageAddress` expose that equation.
`handleSuspension_storageAddress_context` proves exact context identity;
the corresponding `control`, `continuation`, and `store` laws expose the
widened Word and retained CEK data. `wordToAddress?_handler_storageAddress`
reuses the lossless bridge to recover the exact retained Address.

`HostStorageDriver.run_of_suspended_storageAddress` connects the request to the
combined driver without changing remaining fuel. Existing public results such
as `HostStorageDriver.run_storageAddress`,
`HostDriver.run_eq_iff_fuelSoundWith`, `HostDriver.run_done_stable`, and
`runCodeWithStorage?_some_done_stable` apply without a new driver or relation.
No out-of-fuel stability theorem was added.

## Regression record

The Core regressions fix indices 0, 1, and 2, all table entries, Unit argument
typing, exact request and Word resumption, invalid raw arguments, and checked
no-fault execution. The minimal observation is request-ready out of fuel at
fuel 4 and done at fuel 5. Frozen Wire v1 and v2 both continue to reject
`.hostFunction .storageAddress`.

The address-selected fixture deliberately uses different values for
`codeAddress` and `storageAddress`. The minimal program returns
`addressToWord storageAddress`, never the code Address, and a larger run keeps
the same outcome and every observable context projection.

A second program observes the selector, writes `targetSlot`, and observes the
selector again in the same run. Its de Bruijn indices account for both local
binders. Fuel 23 stops at the second address request after the write; fuel 29
stops one Core step before constructing the final pair; fuel 30 completes with
two equal widened selector Words. Fuel 64 returns the same outcome and retains
the exact selected write, checkpoint, effect journal, code, unrelated Account,
and other selected-storage observations. A fixture-specific theorem consumes
`runCodeWithStorage?_some_done_stable` for that exact completed context.

Runtime checks also cover a nontrivial retained Address and the maximum
160-bit Address. Both widen to the exact expected Word and narrow back without
loss. Existing read/write/read, repeated-write, sparse-zero, and deliberate
out-of-fuel regressions remain unchanged.

## Acceptance evidence

- the full build completed successfully with 619 build jobs;
- `lake test` completed successfully with 1,126 jobs;
- all 16 changed Lean modules passed trust-zero with warnings as errors;
- workspace metadata and the semantic-kernel policy were verified;
- an independent final audit found no P0, P1, P2, or P3 issue;
- every implementation and documentation commit stayed below 300 changed
  lines; and
- the root README and all parser-facing code remained unchanged.

The acceptance audit also confirmed exact context identity for the observation,
lossless Address widening, distinct code and storage roles, handled-write
retention, the fuel 4/5/23/29/30/64 boundaries, frozen Wire rejection, and the
intentional absence of an out-of-fuel stability claim. Oracle, Surface,
Parser, schemas, profiles, and published formats remain unchanged.

## Consequences

Host-aware Core code can inspect the exact storage selector already governing
its reads and writes without learning or mutating the surrounding WorldState.
The observation composes with the completed dependent handler, relational
replay, and terminal fuel-stability results rather than creating a parallel
execution path.

Future contract-entry work may prove that a particular invocation derives this
selector from a stronger execution identity. Such a proof must be added at that
future boundary. It must not retroactively reinterpret this ADR's
caller-designated retained storage selector as authority or as an equality
with another address role.
