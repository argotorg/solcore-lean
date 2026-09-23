# ADR-0119: Typed storage-write capability and generic storage driver

- Status: Accepted
- Decision date: 2026-08-29
- Scope: Core storage-write requests, generic handled execution, and working-state updates
- Implementation: Complete

## Context

ADR-0117 gives Core a typed, resumable storage-read request. ADR-0118 connects
that request to a proven-present working storage Account and repeatedly resumes
execution without restoring fuel. The resulting execution path can inspect
storage, but it cannot yet change the working WorldState.

The state operation needed by a write already exists.
`FrameCheckpointedWorkingPairWithPresentStorageAccount.writeStorage` updates
the selected working Account, keeps the Account-presence proof valid, and
preserves the checkpoint, effect journal, storage address, and unrelated
Accounts. This ADR connects that total operation to Core. It does not introduce
a second storage-update implementation.

Adding a write request changes an important assumption in ADR-0118. Once
`Program.checkHost` admits both capabilities, an arbitrary
`CheckedHostCoreProgram` may emit either request. A public checked-program
runner named `runWithStorageReads` can no longer honestly claim to handle every
request. The driver must therefore become request-generic before the checked
and address-selected APIs become write-capable.

## Core capability

Append one runtime-only host function:

```lean
inductive HostFunction where
  | storageRead
  | storageWrite
-- storageRead  : word -> word
-- storageWrite : (word × word) -> unit
```

The write argument is a Core product whose left component is the slot and
whose right component is the new value. Core host functions are unary and
suspend when that one argument has been evaluated. Using a product therefore
fits the existing machine directly. A curried `word -> word -> unit` function
would instead require a new partially applied host value that captures the
slot, so it is not introduced.

Capability positions are append-only:

```lean
HostFunction.storageRead.index  = 0
HostFunction.storageWrite.index = 1
hostContext =
  [HostFunction.functionType .storageRead,
   HostFunction.functionType .storageWrite]

hostEnvironment =
  [.hostFunction .storageRead,
   .hostFunction .storageWrite]
```

Storage read keeps its existing index and type. The new lookup laws state the
exact type and runtime value at index 1, and both table lengths become 2.
`Expr`, `HasType`, and the frozen Wire expression formats remain unchanged.

## Request and dependent response

Extend the first-order request protocol:

```lean
inductive HostRequest where
  | storageRead (slot : Word)
  | storageWrite (slot value : Word)
def HostRequest.Response : HostRequest -> Type
  | .storageRead _ => Word
  | .storageWrite _ _ => Unit
def HostRequest.responseType : HostRequest -> Ty
  | .storageRead _ => .word
  | .storageWrite _ _ => .unit
```

The response value for a write is Core `.unit`. A successful request means
that the handler has updated its context; the Core program receives no copy of
the WorldState. `HostSuspension.resume` continues to inject the response while
preserving the saved CEK continuation and Core-local store exactly.

Applying `.storageWrite` to `.pair (.word slot) (.word value)` emits exactly
`.storageWrite slot value`. Any other runtime shape produces the existing
`invalidHostArgument` fault. This raw fault remains observable for untyped
states and is proved unreachable for checked host programs.

## Generic handled driver

Separate the fuel loop from storage interpretation. The handler contract is
total over the current request universe and returns the next context together
with the response required by that exact request:

```lean
structure HostHandler (Context : Type u) where
  handle :
    Context -> (request : Core.HostRequest) ->
      Context × request.Response
def HostDriver.run
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state : Core.State) :
    HostDriverResult Context
```

On suspension, the driver calls the handler, resumes the suspension with the
dependent response, and recurses with the returned context. The generic driver
does not import Account, WorldState, Address, checkpoint, journal, or frame
semantics.

The concrete storage handler has two transparent branches:

```lean
HostStorageDriver.handleRequest context (.storageRead slot) =
  (context, context.readStorage slot)

HostStorageDriver.handleRequest context (.storageWrite slot value) =
  (context.writeStorage slot value, ())
```

Read leaves the complete context unchanged. Write replaces it with the
existing proven-present total write result. Both branches resume the same
continuation and preserve the same Core-local store.

## Combined storage API

Replace the read-specific checked and address-selected entry points with:

```lean
def CheckedHostCoreProgram.runWithStorage
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (fuel : Nat) :
    HostDriverResult (HostStorageDriver.Context RollbackState TraceState)
def FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat) :
    Option (HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
```

`HostStorageDriver.Context` is only a readable alias for the existing
`FrameCheckpointedWorkingPairWithPresentStorageAccount` carrier.

These operations supersede `runWithStorageReads` and
`runCodeWithStorageReads?`. Do not retain a compatibility wrapper accepting an
arbitrary `CheckedHostCoreProgram`: after the host context grows, such a
program may write. A genuinely read-only public runner would require a
separate checker and proof-carrying program type, which is outside this slice.

Code selection still uses `codeAddress`; host reads and writes still use the
retained `storageAddress`. No theorem equates them. An absent code Account or a
present Account without code still returns `none`.

## Fuel and handled-step accounting

The generic driver keeps ADR-0118's fuel meaning:

1. `Core.hostRun` executes a chunk from the current Core state.
2. Every ordinary transition consumes one unit.
3. Emitting either a read or write request consumes one unit.
4. Interpreting a request, updating the host context, and injecting its
   response consume no additional Core fuel.
5. The next chunk receives exactly the `remainingFuel` returned by
   `Core.hostRun`.

Recursion remains well founded because every suspension proves
`remainingFuel < fuel`. A write must never reset or recompute that budget.

Zero fuel retains Core's current terminal observation rule: a state already
at `done` or `fault` is observed without cost, while a state requiring an
ordinary transition or request emission returns `outOfFuel` unchanged. The
driver must preserve this behavior after a handled request leaves zero fuel.

Generalize `HandledSteps` and `FuelSound` over the handler. A handled boundary
records the old context, emitted request, exact handler result, resumed state,
and new context. Completion and faults consume at most the supplied budget;
exhaustion consumes it exactly. No whole-run context-equality theorem is valid
for the combined driver.

## Required proof interface

Core must publish and verify:

- exact parameter, result, index, context lookup, environment lookup, and
  length laws for both capabilities;
- product-value inversion sufficient to recover two Words from a well-typed
  write argument;
- exact write begin, suspension, invalid-argument, response, and resume laws;
- executable/declarative correspondence for the new request emission;
- response typing and suspension typing for both request constructors;
- preservation and progress through a typed write application;
- impossibility of a machine fault for checked host execution; and
- unchanged runner soundness, fuel accounting, and frozen Wire rejection.

Semantics must publish and verify:

- exact read and write handler equations;
- read context identity and exact write context update;
- continuation and Core-local store preservation for both branches;
- typing of every resumed state produced by the generic handler;
- generic driver outcome typing and no-fault results from typed starts;
- generic handled-step and fuel-soundness theorems;
- checked-program forms for the combined storage runner;
- absent, no-code, and selected-code address laws;
- address-selected no-fault and fuel-soundness theorems; and
- projection laws showing that a handled write preserves checkpoint, effect
  journal, storage address, and unrelated working Accounts.

The final context is observable in every terminal result. Proofs may state
that a read leaves it unchanged or that one write applies the exact existing
`writeStorage` operation. They must not claim that combined execution is
globally read-only, that all writes persist, or that a final context differs
from the initial one whenever a write was requested.

## Required regressions

Tests cover:

- fixed read index 0 and write index 1;
- host-check acceptance of a `(word × word) -> unit` write call;
- checker rejection and raw-machine faults for incorrect argument shapes;
- the exact write request and `.unit` resumption value;
- write followed by read returning the new value;
- overwrite behavior and zero-as-sparse-deletion behavior;
- isolation across slots and working Accounts;
- distinct code and storage addresses;
- preservation of checkpoint, effect journal, and Core-local cells;
- mixed repeated reads and writes under one fixed budget;
- the read/write/read boundaries at fuel 21, 22, 27, and 28;
- sparse-zero execution immediately before and at completion at fuel 15/16;
- completion observed with zero fuel after the final resume;
- direct use of public typing, no-fault, context-update, and fuel theorems; and
- continued Wire v1/v2 rejection of both host function values.

The executable regressions and public proof-interface regressions are part of
the acceptance evidence below. Repository-wide build, test, metadata, and
kernel-policy gates all pass on the accepted revision.

## Dependency boundary

Core owns only host function types, fixed capability tables, first-order
requests, suspension/resumption, machine execution, and their safety proofs.
It remains independent of `Solcore.Semantics`.

Semantics owns the generic handler driver and the concrete interpretation of
storage requests through the proven-present working Account. Parser, source
syntax, ABI, published profiles, and gas schedules are unchanged.

## Write lifecycle is not decided here

This handler updates the working WorldState immediately because that is the
state already threaded by ADR-0118. It does not decide when the working state
commits, rolls back, or becomes externally visible. Existing checkpoint and
frame-resolution structures are preserved but are not invoked by this driver.

This ADR also does not define static-call restrictions, authorization, gas or
refunds, atomicity, nested calls, reentrancy, logs, self-destruction, balance
or nonce updates, creation, ABI encoding, return bytes, or source syntax.

## Implementation record

The implementation followed the staged boundary above in small green commits.
The final code is split by responsibility rather than collected in one storage
runtime module:

- `Solcore.Core.Syntax`, `Host`, and `HostMachine` define the append-only
  capability, fixed tables, dependent request response, suspension, and exact
  machine branch. The accompanying host safety, progress, transition, and
  runner-property modules cover both request constructors exhaustively.
- `Solcore.Semantics.HostDriver`, `HostDriverProperties`, and
  `HostDriverFuelProperties` contain the Account-independent handler loop,
  outcome typing, no-fault result, handled-step relation, and fuel proof.
- `HostStorageHandler` and `HostStorageHandlerProperties` interpret reads and
  writes through the proven-present working Account. A write returns exactly
  `context.writeStorage slot value`, resumes Core with Unit, and preserves the
  saved continuation and Core-local store. Public laws also expose same-slot
  read-after-write and sparse zero deletion.
- `HostStorageDriver`, `HostStorageDriverProperties`, and
  `HostStorageDriverFuelProperties` specialize the generic loop without adding
  a whole-run context-equality claim. They publish the checked entry point
  `CheckedHostCoreProgram.runWithStorage` together with typing, no-fault,
  invariant, and fuel-soundness results.
- `FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecution` and its
  properties publish `runCodeWithStorage?`. The adapter keeps the absent,
  no-code, and selected-code branches explicit and returns evidence for result
  typing and fuel accounting.

The combined whole-run proofs retain the storage address, checkpoint, working
effect journal, checked code at every working address, and every non-selected
working Account. They intentionally do not retain the old read-only theorem
that equated the complete final context with the initial context.

`AddressSelectedHostStorage` exercises the complete path. Its measured
read/write/read program allocates a Boolean Core cell, reads a selector, writes
the selected slot, and reads it back. Fuel 21 stops immediately before the
write emission with the old context; fuel 22 has handled the write and stops at
the resumed Unit state with the new context; fuel 27 stops immediately before
the final read emission; fuel 28 completes with the new Word and the unchanged
`[true]` Core-local store. These boundaries follow directly from the rule that
ordinary steps and request emissions cost one unit while handling, resumption,
and terminal observation cost zero.

The sparse-zero regression stops at fuel 15 after the zero update is already
visible and completes at the minimum fuel 16 by reading zero. A separate
repeated-write program performs two writes under one budget and confirms that
the second value wins without changing code, checkpoint data, effects,
unrelated slots, or another working Account. `AddressSelectedHostStorageProperties`
also consumes the public handler, selection, typing, no-fault, invariant, and
fuel theorems directly so the executable tests are not the only evidence.

Focused module builds and trust-zero checks passed during implementation. An
independent fuel audit reconstructed the de Bruijn programs, confirmed both
host checks, reproduced the 21/22/27/28 and 15/16 boundaries, and left no
tracked audit artifact. The final 617-job build and 1122-job test suite pass,
as do metadata verification and the semantic-kernel policy check. No P0 or P1
implementation gap remains in the independent acceptance audit. This record
does not expand the feature into ABI, call, or transaction-lifecycle semantics.

## Consequences

Checked Core code can update and then observe its selected working storage
through one typed, fuel-preserving execution path. The driver becomes reusable
for later request kinds without embedding contract state in Core.

The returned context represents the latest working state, not a committed
transaction result. Lifecycle, call, ABI, and source-language semantics remain
separate future work.
