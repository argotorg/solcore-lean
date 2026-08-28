# ADR-0118: Address-selected host-code driver

- Status: Accepted
- Decision date: 2026-08-29
- Scope: Account code migration, handled host execution, and fuel preservation
- Implementation: In progress

## Context

ADR-0116 stores closed checked Core code in Account state and selects it by
address. ADR-0117 adds a separate checked host-code carrier, a typed
storage-read request, resumable Core execution, and a one-request Semantics
handler. These pieces do not yet execute stored host-aware code to completion:
the raw host runner deliberately stops at every request.

The next boundary must connect code selection to the proven-present working
storage Account without making code address and storage address identical. It
must also prevent a handler loop from restoring the original fuel after every
request.

## Decision

Replace only Account's internal code carrier:

```lean
Option CheckedCoreProgram
```

becomes:

```lean
Option CheckedHostCoreProgram
```

`CheckedCoreProgram` remains the carrier for host-free closed Core programs and
retains its existing completion theorems. The migration changes which carrier
Account stores; it does not weaken or remove the pure Core boundary.

Do not keep parallel pure and host code fields, and do not introduce a sum
type. A single Account has one selected executable program. A closed program
that is to be stored must be admitted by the host checker just like any other
stored program.

## Driver result

Semantics owns a context-threading result with three terminal outcomes:

```lean
inductive HostDriverOutcome where
  | done (value : Core.Value) (store : Core.Store)
  | outOfFuel (state : Core.State)
  | fault (error : Core.MachineFault) (state : Core.State)

structure HostDriverResult (Context : Type) where
  context : Context
  outcome : HostDriverOutcome
```

There is no suspended terminal outcome. The driver handles every emitted
request supported by its context and continues until Core finishes, exhausts
fuel, or faults. Retaining the context in every result is intentional: storage
reads leave it unchanged, while a later storage-write capability can return an
updated context without replacing the driver result protocol.

The raw fault branch remains observable for untyped starting states. Type
safety proves it unreachable for checked stored code.

## Execution and fuel

Run `Core.hostRun` from the current state. On a suspension:

1. interpret the request through the proven-present working storage Account;
2. resume the saved continuation with the typed response; and
3. recurse with exactly the `remainingFuel` returned by `Core.hostRun`.

Recursion is well founded because a suspension result proves
`remainingFuel < fuel`. Ordinary Core transitions and request emission each
consume one unit. Handling the request and injecting its response consume no
additional unit. Completion and fault observation consume no unit.

The driver does not report exact unused fuel after completion because the
current Core terminal results do not carry it. It may claim only bounded
consumption and exact exhaustion. Repeated suspension cannot create fuel:
every handled request strictly decreases the remaining budget.

## Address and state boundary

The checked entry point starts the selected program with the fixed host
environment. The address-selected entry point:

- receives a proven-present storage context;
- receives `codeAddress` separately;
- selects code from the working WorldState at that address; and
- uses the retained `storageAddress` only to interpret host storage requests.

No equality between those addresses is assumed. An absent code Account and a
present Account without code both return `none`; a selected program returns the
complete driver result. This remains below any ABI, call, authority, or frame
outcome policy.

## Required proof interface

Publish and verify:

- driver termination from strict remaining-fuel decrease;
- exact preservation of Core's suspension fuel across every resume;
- context threading across all terminal branches;
- typed done and out-of-fuel outcomes from a typed initial state;
- impossibility of a driver fault from a typed initial state;
- checked-program versions of those safety statements;
- exact absent, no-code, and selected-code address laws;
- impossibility of an address-selected checked run returning a fault; and
- a handled-step accounting relation connecting the complete driver run to the
  underlying Core transitions and request emissions.

For the current read-only handler, also prove that the final context equals the
initial context. Do not make this equality part of the generic driver contract,
because storage write will intentionally change it.

## Dependency boundary

The driver and its handled-step relation live in `Solcore.Semantics`. Core
continues to know only typed host functions, requests, suspensions, and the raw
runner. Core must not import Address, Account, WorldState, checkpoint, rollback,
or frame state.

No frozen wire schema, Oracle command, profile, capability document, or public
source syntax changes. Host function values remain rejected by wire v1 and v2.

## Required regressions

Tests cover:

- host-aware code retained through Account storage writes;
- absent Account and present Account without code;
- distinct code and storage addresses;
- a storage value changing the selected program's returned value;
- two handled reads using the same fixed total budget;
- exact fuel just before and at a request boundary;
- preservation of the Core-local store across handled reads;
- read-only final-context equality; and
- direct use of checked and address-selected no-fault theorems.

## Consequences

Stored code can now use the typed Core host protocol without hiding WorldState
inside Core. The same context-threading loop can later interpret storage write
by extending the request algebra and handler.

This decision does not define contract arguments, caller or callee identity,
call depth, nested invocation, rollback ownership, transaction atomicity, ABI
encoding, or source elaboration.
