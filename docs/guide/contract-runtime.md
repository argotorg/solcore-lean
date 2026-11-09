# ContractRuntime

`Solcore/ContractRuntime` executes checked Core contracts: accounts and world state, host requests,
frames and transactions, nested calls and creation, commit and rollback, and what a transaction
exposes. The [umbrella](../../Solcore/ContractRuntime.lean) imports the area.

- **Builds on.** [Core](core.md)'s host-aware machine, and `Util` through `RuntimeScalars`.
- **Built on by.**
  - [Synthesis](synthesis.md): the generators run their contracts through `TopLevelExecution.run`
    and the call phases, and the emitters' meaning proofs use `TopLevelExecution.rawRun`,
    `TopLevelExecution.resumeWithFuel_run` and `HostDriver.run_done_complete`
    ([source emitter meaning](../design/scalar-emitter-meaning.md)).
  - `Abi` runs its static Word contracts through `BalancedTopLevelExecution.runWithEnvironment`
    ([Foundations](foundations.md)).
  - The Core wire codec imports `Internal/ScalarText`.
- Native source contracts are not connected to it yet (README's Proof status). The Rust Hull
  import has an account runtime of its own.

## How it builds on Core

- **Code.** An account holds a `CheckedHostCoreProgram`: a `Core.Program` with a proof that
  `Program.checkHost` accepts it.
- **Requests.** `Core.hostRun` stops at each host request with a `Core.HostSuspension`.
  `HostDriver.run` gives it to a `HostHandler`, resumes with the answer, and continues with exactly
  the fuel `hostRun` returned. A request the handler does not support ends the run as
  `unsupported`.
- **Typed answers.** A `HostHandler` has `supports` and `handle`, and `handle` must return a
  `request.Response`. That type is fixed by the request, so no handler can make a typed state
  ill-typed: `HostDriver.run_hasType` and `HostDriver.run_ne_fault` hold for every handler.
- **The handlers.**
  - `HostStorageDriver.handler` answers storage, input, address and value requests. It answers
    calls and creation with `ContractCallFailure.depthExceeded.result`, and marks `emitLogWord`
    unsupported.
  - `TransactionHostStorageDriver.handler` records logs in a `TransactionJournal` and passes every
    other request to the storage handler. It supports every request; the top-level runner relies on
    that.
  - `OneLevelNestedExecution` intercepts the root's call and creation requests in
    `RootFrame.afterSuspensionWithEnvironment`. Children run under the transaction handler, so
    their own calls fail with `depthExceeded`.
- **Outcomes.** A frame ends as returned, reverted or trapped (`FrameOutcome`), read from the Core
  result by the contract's `CoreContractEntryProfile`. A return commits the working world and
  journal; a revert or a trap rolls back to the checkpoint (`TopLevelExecution.finalize`,
  `TopLevelTerminalResult.committedJournal_eq`). None of these is a Core fault
  ([Core](core.md#faults-language-failures-and-fuel)).

## Where things are

The front holds the definitions, each stage's main theorems, and the few theorems a definition
needs:

| File | Holds | Edit it when you change |
| --- | --- | --- |
| [`RuntimeScalars`](../../Solcore/ContractRuntime/RuntimeScalars.lean) | `Address`, `Bytes`, text and byte encodings such as `encodeWordBytesBE` and `encodeAddressText`, `addressToWord`, `wordToAddress?` | scalar encodings |
| [`WorldState`](../../Solcore/ContractRuntime/WorldState.lean) | `CheckedHostCoreProgram`; `Account` and `WorldState`, whose constructors and fields are private, with their operations and the laws that unfold them; `WorldStateDelta` | account operations |
| [`Frames`](../../Solcore/ContractRuntime/Frames.lean) | `FrameOutcome`, `FrameRunResult`, `FrameEffectJournal`, `FrameTrace`, `FrameContinuationContext`, `FrameResolutionResult`, checkpointed working pairs | what a frame records or how it resolves |
| [`Driver`](../../Solcore/ContractRuntime/Driver.lean) | `HostHandler`, `HostDriver.run`, `HostDriverResult`, `HostDriver.HandledSteps`, `HostDriverResult.resumeWithFuel`, and the generic safety theorems | rarely: it is generic over handlers |
| [`StorageDriver`](../../Solcore/ContractRuntime/StorageDriver.lean) | `HostStorageDriver.InputData`, `ExecutionInputs`, `Context`, `handleRequest`, `handler` and `run`; `CheckedHostCoreProgram.runWithStorage`; `ContractCallFailure`; `WordReturnedFrameCompletion` | host requests, call failures |
| [`Contracts`](../../Solcore/ContractRuntime/Contracts.lean) | `CoreContractEntryProfile`, `CheckedCoreContract`, `InstalledCheckedCoreContract`, `TopLevelInvocation`, `CheckedCoreWordOutcome`, `CheckedCoreWordLog`, the registries, `CreationAddressPolicy`, `ExecutionEnvironment` | entry profiles, log records |
| [`Transactions`](../../Solcore/ContractRuntime/Transactions.lean) | `TransactionJournal`, `TransactionHostStorageDriver`, `CheckedHostCoreProgram.runWithTransactionStorage` | observable host effects |
| [`TopLevel`](../../Solcore/ContractRuntime/TopLevel.lean) | `TopLevelExecution.rawRun`, `run`, `finalize` and `resumeWithFuel`, `TopLevelRunResult`, `TopLevelTerminalResult`, `TopLevelStorageDelta`, `CoreLanguageResult` | what a transaction exposes, commits or rolls back |
| [`Creation`](../../Solcore/ContractRuntime/Creation.lean) | `WorldState.transferBalance`, `BalanceTransferFailure`, `CheckedAccountCreation.prepare`, `CheckedCreationPreflight.prepare` | value transfer, creation checks |
| [`NestedExecution`](../../Solcore/ContractRuntime/NestedExecution.lean) | `OneLevelNestedExecution`: `RootFrame`, `ChildFrame`, `CallProfile`, `CreationProfile`, `Mode`, `Reachable`, `run`, `runWithEnvironment`, `resumeWithFuel`, `Result` | kinds of call, the scheduler |
| [`BalancedExecution`](../../Solcore/ContractRuntime/BalancedExecution.lean) | `BalancedTopLevelExecution.run`, `runWithEnvironment`, `resumeWithFuel`, `Result` | the public entry |
| [`CallPhases`](../../Solcore/ContractRuntime/CallPhases.lean) | `CallResumeParent`, `CallChainParent`, `CallChoiceParent` and their `run` | call-phase conventions |

`Internal/` holds the laws, by family of the front. A new law goes in its family's file:

| File | Topic |
| --- | --- |
| [`ScalarLaws`](../../Solcore/ContractRuntime/Internal/ScalarLaws.lean), [`ScalarText`](../../Solcore/ContractRuntime/Internal/ScalarText.lean) | word bytes and the address bridge; text encodings |
| [`WorldStateLaws`](../../Solcore/ContractRuntime/Internal/WorldStateLaws.lean), [`WorldStateDeltaLaws`](../../Solcore/ContractRuntime/Internal/WorldStateDeltaLaws.lean) | account fields under updates, storage reads, code lookup; balances, nonces and delta queries |
| [`FrameLaws`](../../Solcore/ContractRuntime/Internal/FrameLaws.lean) | outcomes, journals, traces, continuation, resolution, checkpointed pairs |
| [`DriverLaws`](../../Solcore/ContractRuntime/Internal/DriverLaws.lean) | `HostDriver.run` by cases, paths, stability under more fuel, resumption |
| [`StorageDriverLaws`](../../Solcore/ContractRuntime/Internal/StorageDriverLaws.lean) | input data, each request's response and effect, the storage driver's run |
| [`ContractLaws`](../../Solcore/ContractRuntime/Internal/ContractLaws.lean), [`EntryOutcomeLaws`](../../Solcore/ContractRuntime/Internal/EntryOutcomeLaws.lean) | Word programs, checked contracts, registries, the environment; recognition and decoding per entry profile |
| [`TransactionLaws`](../../Solcore/ContractRuntime/Internal/TransactionLaws.lean) | the transaction journal, the transaction driver's requests and run |
| [`TopLevelLaws`](../../Solcore/ContractRuntime/Internal/TopLevelLaws.lean) | the top-level run, storage deltas, language results at the boundary |
| [`CreationLaws`](../../Solcore/ContractRuntime/Internal/CreationLaws.lean) | `WorldState.transferBalance` by cases, the two preflights |
| [`NestedLaws`](../../Solcore/ContractRuntime/Internal/NestedLaws.lean), [`BalancedLaws`](../../Solcore/ContractRuntime/Internal/BalancedLaws.lean) | the depth-one call, transition steps, anchoring; projections of a balanced result |
| [`CallPhaseLaws`](../../Solcore/ContractRuntime/Internal/CallPhaseLaws.lean) | balances, code and the final world across call phases |

Only tests use the refinement layers:
[`AddressBytes`](../../Solcore/ContractRuntime/Internal/AddressBytes.lean),
[`CheckedCoreProgram`](../../Solcore/ContractRuntime/Internal/CheckedCoreProgram.lean),
[`CodeExecution`](../../Solcore/ContractRuntime/Internal/CodeExecution.lean),
[`ParentIndexedFrames`](../../Solcore/ContractRuntime/Internal/ParentIndexedFrames.lean),
[`ParentIndexedExecution`](../../Solcore/ContractRuntime/Internal/ParentIndexedExecution.lean) and
[`SelectedWordExecution`](../../Solcore/ContractRuntime/Internal/SelectedWordExecution.lean).

**Definitions and laws are split.** An old module such as `Solcore.ContractRuntime.TopLevelExecution`
has its definitions in the front, under the marker
`-- leanmerge: from Solcore.ContractRuntime.Internal.DefsTopLevelExecution` in `TopLevel`, and its
laws under `-- leanmerge: from Solcore.ContractRuntime.TopLevelExecution` in `Internal/TopLevelLaws`.
Three front files keep laws, because of `private`: `WorldState` (private fields), and
`NestedExecution` and `BalancedExecution`, whose `Result` types have private constructors. A front
file may import an `Internal/` file of a lower family when a definition needs one of its theorems.

## Definitions and theorems you build on

| Declarations | Reading | Used by |
| --- | --- | --- |
| `CheckedHostCoreProgram`, `WorldState`, `Account` | checked code and sparse accounts | every runner; Abi's `WordImplementation` |
| `HostDriver.run`, `HostDriver.run_hasType`, `HostDriver.run_ne_fault`, `HostDriverResult.resumeWithFuel_ne_fault` | a handled run stays typed and never faults, for every handler | the storage and transaction drivers |
| `HostDriver.HandledSteps`, `HostDriver.run_done_complete` (`Internal/DriverLaws`) | a handled path to completion is what `run` returns with enough fuel | Synthesis' emitter meaning proofs |
| `HostDriverResult.resumeWithFuel_run`, `HostDriverResult.resumeWithFuel_run_add` (`Internal/DriverLaws`) | resuming a handled run is one run on the summed budget | top-level resumption |
| `CoreContractEntryProfile`, `CheckedCoreContract`, `CoreContractEntryProfile.decode?_ne_none_of_hasType` | completion conventions, and their decoders are total on typed results | the total decoders `CoreContractEntryProfile.decodeTyped` and `CheckedCoreContract.decodeCompletion`; Synthesis; Abi's `wordOutcomeV1` contracts |
| `TopLevelExecution.run`, `TopLevelExecution.rawRun_ne_fault` | one installed invocation, total, from a raw run that cannot fault | Synthesis, tests |
| `TopLevelExecution.resumeWithFuel_run`, `resumeWithFuel_run_add`, `resumeWithFuel_run_zero` | resuming agrees with one run on the summed budget | Synthesis' emitter meaning proofs |
| `OneLevelNestedExecution.run`, `resumeWithFuel_runMode`, `resumeWithFuel_run`, `resumeWithFuel_run_add` | depth-one calls and creation, with exact resumption | `BalancedTopLevelExecution`, Synthesis |
| `BalancedTopLevelExecution.run`, `run_of_zero_value`, `run_of_transfer_failure`, `run_of_transfer_success`, `resumeWithFuel_run` | the public entry: transfer the call's value, then nested execution; splitting fuel never repeats the transfer | Abi, Synthesis |
| `CallResumeExecution.run`, `CallChainExecution.run`, `CallChoiceExecution.run`, `CallChainExecution.toCallResume_run_ofCallResume`, `CallChoiceExecution.run_ofChain` | parents split at their calls, each phase run through the public runner | Synthesis' call generators |
| `CoreLanguageResult.run`, `CoreLanguageResult.run_hasType` | Core language results read at the contract boundary | tests |

## Making changes

### Add a host effect

Logs were added on 2026-08-30: first Core's `emitLogWord`
([Core](core.md#add-a-host-function-and-its-request)), then the runtime's journal (4a94bf8c1),
transaction context (ecb9fbc56), handler (52512f76e), driver laws (bd7f80386) and nested calls
(0a7901a68). These commits name `Solcore.Semantics.*`, the area's name before b62eeb170; the steps
below use the current files.

1. Add the Core function and request first.
2. `Contracts`: the record the effect leaves, as `CheckedCoreWordLog`.
3. `Transactions`: rollback-scoped storage in `TransactionJournal` (as `recordLog`), the context
   operation (as `TransactionHostStorageDriver.Context.recordLog`), and the arm of
   `TransactionHostStorageDriver.handleRequest`.
4. `StorageDriver`: `HostStorageDriver.handleRequest` is total over requests, so it needs an arm too.
   If the plain storage policy cannot keep the effect, return a placeholder and mark the request
   unsupported in `HostStorageDriver.handler`, as `emitLogWord` is.
5. `NestedExecution`: add the request to every request case analysis:
   `RootFrame.afterSuspensionWithEnvironment`, the private presence, storage-address and checkpoint
   lemmas for root and child frames, and the private `rootAfterSuspension_anchored` behind
   `OneLevelNestedExecution.Reachable.anchored`.
6. `TopLevel`: if the effect is observable, expose it in `TopLevelTerminalResult` and decide in
   `TopLevelExecution.finalize` whether a revert keeps it.
7. Laws: the request's response and effect in `Internal/StorageDriverLaws`; the journal and the
   handler in `Internal/TransactionLaws`.
8. Tests: a file like `Test/ContractRuntime/Logs.lean`, which runs top-level, balanced, nested and
   creation cases, and handler sections in `Test/ContractRuntime/HostDriver.lean`.

The driver, top-level, balanced and call-phase files name no request, so
`TopLevelExecution.rawRun_ne_fault` and `TopLevelExecution.resumeWithFuel_run` need no new case.
They rest on facts about the transaction driver that a new request must keep:
- it supports every request (`TransactionHostStorageDriver.run_ne_unsupported`), which the total
  runner needs;
- it never changes the storage address or the checkpoint
  (`TransactionHostStorageDriver.run_storageAddress` and `run_checkpoint`, proved by cases on the
  request), which the total runner and its resumption need;
- it never changes a balance (`TransactionHostStorageDriver.run_workingBalance?` in
  `Internal/CallPhaseLaws`, also by cases), which the call-phase balance theorems need.

### Add a kind of call

**A new call request.** Value calls were added on 2026-08-30: Core (75dde5648), the boundary
(8b0a942c5), nested execution with transfer (ceaca2606), scheduler provenance (79588c72a), and
tests (979ec39be, c86a6c73f).

1. Core: a host function and request whose `Response` is `ContractCallWordResult`.
2. `StorageDriver`: answer it in `HostStorageDriver.handleRequest` with
   `ContractCallFailure.depthExceeded.result`, as every call is at depth one. Add a
   `ContractCallFailure` constructor if the call can fail in a new way before the child runs.
3. `NestedExecution`:
   - a `CallProfile` constructor, with its `request`, `response`, `target`, `input` and `invocation`;
   - a `TopLevelInvocation` builder, as `TopLevelInvocation.childWordWithValue`;
   - the arm in `RootFrame.afterSuspensionWithEnvironment`: address check, registry lookup, the
     one-Word admission, any transfer;
   - the new transitions in `OneLevelNestedExecution.Reachable`, so that `Reachable.anchored`
     still holds.
4. `Creation`: map transfer failures to call results, as `BalanceTransferFailure.toContractCallResult`.
5. Laws: `Internal/NestedLaws`, `Internal/StorageDriverLaws`, `Internal/CreationLaws`.
6. Keep proved: `OneLevelNestedExecution.resumeWithFuel_runMode` and its corollaries, and the
   `BalancedTopLevelExecution` theorems.
7. Tests: `Test/ContractRuntime/ValueCalls.lean`, `NestedExecution.lean`, and Core's
   `Test/Core/HostMachine.lean`.

**A new call-phase convention.** The choice chain (2b896daab) was one module with its umbrella
import, a test file and its registration in `Tests/Main.lean`. It needs no new request: each phase
runs through the public top-level runner. Put the definitions in `CallPhases`, the laws in
`Internal/CallPhaseLaws` and the tests in `Test/ContractRuntime/ContractCalls.lean`. Prove how it
relates to the existing conventions, as `CallChoiceExecution.run_ofChain` does.

### Add an account operation

Examples: `WorldState.writeCode?` (eaa71f00d), creation nonces (aa356efbf),
`Account.incrementNonce?` (d77c8f382).

1. `WorldState`: define the operation next to `writeCode?` and `writeNonce?`. Anything that reads or
   writes an account field must be here, since the fields are private.
2. Laws that unfold the fields stay in `WorldState`, in its extensionality and update-algebra
   sections; aa356efbf extended those. Laws stated through the public operations go to
   `Internal/WorldStateLaws`, as the code-write and nonce-increment sections do, or to
   `Internal/WorldStateDeltaLaws` for balances, nonces and delta queries.
3. Extend `WorldStateDelta`'s queries if a delta should see the change.
4. Move value only through `WorldState.transferBalance`: the handlers never change balances.
5. Tests: `Test/ContractRuntime/WorldState.lean`, as its `WorldStateCodeWrite` and `WorldStateNonce`
   sections, registered in `Tests/Main.lean`.

### Add an entry profile

Examples: `boundedBytesOutcomeV1` (54fbe2ed7) and `enumOutcomeV1` (647cd47df).

1. `Contracts`: the `CoreContractEntryProfile` constructor and its cases in `resultType`, `decode?`
   and `returnsOneWord`; a builder such as `CheckedCoreContract.boundedBytesOutcomeV1`; the case of
   `CoreContractEntryProfile.decode?_ne_none_of_hasType`, which the total decoder
   `CheckedCoreContract.decodeCompletion` needs. That theorem stays in the front for this reason.
2. `Internal/EntryOutcomeLaws`: exact recognition, injectivity, size and decoding laws.
3. Nested calls and creation admit only profiles with `returnsOneWord = true`.
4. Tests: a section of `Test/ContractRuntime/ContractCalls.lean` with golden bytes, registered in
   `Tests/Main.lean`.

## Pitfalls

- **The total runners take proofs.** `TopLevelExecution.run` is built from
  `TopLevelExecution.validatedRawRun`, which uses
  `CheckedHostCoreProgram.runWithTransactionStorage_hasType`, `runWithTransactionStorage_ne_unsupported`,
  `TransactionHostStorageDriver.run_storageAddress` and `TransactionHostStorageDriver.run_checkpoint`.
  A handler change that breaks one of them breaks the definition, not only a theorem. This is also
  why `TopLevel` imports `Internal/TransactionLaws`.
- **Request case analyses are scattered.** A new request reaches `HostStorageDriver.handleRequest`,
  `TransactionHostStorageDriver.handleRequest`, the private presence proofs and the scheduler in
  `NestedExecution`, and `cases request` proofs in `Internal/StorageDriverLaws`,
  `Internal/TransactionLaws` and `Internal/CallPhaseLaws`.
- **`@[simp]` reach.** `WorldStateLaws` and `WorldStateDeltaLaws`, and `ContractLaws` and
  `EntryOutcomeLaws`, stay apart because many modules import the first of each pair without the
  second. `ScalarText` stays apart from `AddressBytes` because the Core wire codec imports it, and
  `AddressBytes` would bring `Core/Internal/ByteSelection` along.
- **Tests pin statements.** Sections named `…ExternalProperties` in `Test/ContractRuntime` use the
  laws from outside the area; changing a law's statement breaks them on purpose.
- **Older names.** Besides `-- leanmerge:` markers, many sections carry a heading
  `## Consolidated module: …` from an earlier merge, which the moves map does not list. Before
  b62eeb170 the area was `Solcore.Semantics`; `Solcore/Semantics.lean` is a deprecated alias.

## Testing

| File | Covers |
| --- | --- |
| [`WorldState`](../../Solcore/Test/ContractRuntime/WorldState.lean) | accounts, storage, code, nonces, balance transfer, address bytes |
| [`Frames`](../../Solcore/Test/ContractRuntime/Frames.lean), [`ParentIndexedFrames`](../../Solcore/Test/ContractRuntime/ParentIndexedFrames.lean) | frames and the parent-indexed layer |
| [`HostDriver`](../../Solcore/Test/ContractRuntime/HostDriver.lean) | the driver, storage contexts, input data, runtime scalars, the transaction handler and journal |
| [`TopLevelExecution`](../../Solcore/Test/ContractRuntime/TopLevelExecution.lean) | top-level and balanced runs, current address, environments |
| [`NestedExecution`](../../Solcore/Test/ContractRuntime/NestedExecution.lean), [`ValueCalls`](../../Solcore/Test/ContractRuntime/ValueCalls.lean), [`Creation`](../../Solcore/Test/ContractRuntime/Creation.lean), [`Logs`](../../Solcore/Test/ContractRuntime/Logs.lean) | nested calls, value calls, creation, logs |
| [`ContractCalls`](../../Solcore/Test/ContractRuntime/ContractCalls.lean) | entry profiles, language results, call phases |
| [`AddressSelectedHost`](../../Solcore/Test/ContractRuntime/AddressSelectedHost.lean), [`SelectedExecution`](../../Solcore/Test/ContractRuntime/SelectedExecution.lean) | the refinement layers |

`Test/Abi/StaticWord.lean` and the Synthesis tests run contracts through this area too.

```sh
lake build Solcore.ContractRuntime                 # the area
lake build Solcore.Test.ContractRuntime.Logs       # one test file's compile-time checks
lake build                                         # Abi and Synthesis build on it
lake test                                          # all IO tests
```

See [Workflow](workflow.md) and [Tests](tests.md).
