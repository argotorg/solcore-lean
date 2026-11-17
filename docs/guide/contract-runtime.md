# ContractRuntime

`Solcore/ContractRuntime` executes checked Core contracts: accounts and world state, host requests,
frames and transactions, nested calls and creation, commit and rollback, and what a transaction
exposes. The [umbrella](../../Solcore/ContractRuntime.lean) imports the area.

- **Builds on.** [Core](core.md)'s host-aware machine, and `Util` through `RuntimeScalars`.
- **Built on by.** [Synthesis](synthesis.md), whose generators and emitter meaning proofs run
  contracts through `TopLevelExecution` and the call phases; `Abi`, through
  `BalancedTopLevelExecution.runWithEnvironment` ([Foundations](foundations.md)); and the Core wire
  codec, which imports `Internal/ScalarText`.
- Native source contracts are not connected to it yet (README's Proof status). The Rust Hull
  import has an account runtime of its own.

## How it builds on Core

- **Code.** An account holds a `CheckedHostCoreProgram`: a `Core.Program` with a proof that
  `Program.checkHost` accepts it.
- **Requests.** `Core.hostRun` stops at each host request with a `Core.HostSuspension`.
  `HostDriver.run` gives it to a `HostHandler`, resumes with the answer, and continues with exactly
  the fuel `hostRun` returned. A request the handler does not support ends the run as
  `unsupported`.
- **Typed answers.** A `HostHandler`'s `handle` must return a `request.Response`, a type fixed by
  the request, so no handler can make a typed state ill-typed: `HostDriver.run_hasType` and
  `HostDriver.run_ne_fault` hold for every handler.
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
  journal; a revert or a trap rolls back to the checkpoint (`TopLevelExecution.finalize`). None of
  these is a Core fault ([Core](core.md#faults-language-failures-and-fuel)).

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

**Definitions and laws are split**, as
[Conventions](conventions.md#where-a-new-declaration-goes) describes: an old module's definitions
are in the front and its laws in `Internal/`, each under its `-- leanmerge:` marker. Three front
files keep laws, because of `private`: `WorldState` (private fields), and `NestedExecution` and
`BalancedExecution`, whose `Result` types have private constructors. A front file may import an
`Internal/` file of a lower family when a definition needs one of its theorems.

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

Start from Core's host function and request ([Core](core.md#add-a-host-function-and-its-request)),
as logs (`emitLogWord`) did.

1. `Contracts`: the record the effect leaves, as `CheckedCoreWordLog`.
2. `Transactions`: rollback-scoped storage in `TransactionJournal`, its context operation, and the
   arm of `TransactionHostStorageDriver.handleRequest`.
3. `StorageDriver`: an arm of `HostStorageDriver.handleRequest`, which is total over requests. If
   the plain storage policy cannot keep the effect, return a placeholder and mark the request
   unsupported in `HostStorageDriver.handler`, as `emitLogWord` is.
4. `NestedExecution`: the request in every request case analysis, from
   `RootFrame.afterSuspensionWithEnvironment` to the private lemmas behind
   `OneLevelNestedExecution.Reachable.anchored`.
5. `TopLevel`: if the effect is observable, expose it in `TopLevelTerminalResult` and decide in
   `TopLevelExecution.finalize` whether a revert keeps it.
6. Laws in `Internal/StorageDriverLaws` and `Internal/TransactionLaws`; tests like
   `Test/ContractRuntime/Logs.lean` and the handler sections of `HostDriver.lean`.

The driver, top-level, balanced and call-phase files name no request. They rest on three facts
about the transaction driver, each proved by cases on the request, which a new request must keep:
it supports every request (`TransactionHostStorageDriver.run_ne_unsupported`); it never changes
the storage address or the checkpoint (`run_storageAddress`, `run_checkpoint`); and it never
changes a balance (`run_workingBalance?`).

### Add a kind of call

**A new call request**, as for value calls:
1. Core: a host function and request whose `Response` is `ContractCallWordResult`.
2. `StorageDriver`: answer it with `ContractCallFailure.depthExceeded.result`, since every call is
   at depth one, and add a `ContractCallFailure` constructor if it can fail in a new way.
3. `NestedExecution`: a `CallProfile` constructor, a `TopLevelInvocation` builder, the arm in
   `RootFrame.afterSuspensionWithEnvironment`, and the new transitions in
   `OneLevelNestedExecution.Reachable`, so that `Reachable.anchored` still holds.
4. `Creation`: map transfer failures to call results, as
   `BalanceTransferFailure.toContractCallResult`.
5. Laws in `Internal/NestedLaws`, `StorageDriverLaws` and `CreationLaws`. Keep
   `OneLevelNestedExecution.resumeWithFuel_runMode` and the `BalancedTopLevelExecution` theorems
   proved. Tests in `Test/ContractRuntime/ValueCalls.lean` and `NestedExecution.lean`.

**A new call-phase convention**, such as the choice chain, needs no new request: each phase runs
through the public top-level runner. Put it in `CallPhases`, its laws in `Internal/CallPhaseLaws`
and its tests in `Test/ContractRuntime/ContractCalls.lean`, and prove how it relates to the
existing conventions, as `CallChoiceExecution.run_ofChain` does.

### Add an account operation

Define it in `WorldState`, next to `writeCode?` and `writeNonce?`: the fields are private, so
anything that reads or writes one must be there, with the laws that unfold them. Laws stated
through the public operations go to `Internal/WorldStateLaws`, or `Internal/WorldStateDeltaLaws`
for balances, nonces and delta queries; extend `WorldStateDelta`'s queries if a delta should see
the change. Move value only through `WorldState.transferBalance`: the handlers never change
balances. Tests go in `Test/ContractRuntime/WorldState.lean`.

### Add an entry profile

As for `boundedBytesOutcomeV1` and `enumOutcomeV1`: the `CoreContractEntryProfile` constructor in
`Contracts`, with its cases in `resultType`, `decode?` and `returnsOneWord`, a builder, and the case
of `CoreContractEntryProfile.decode?_ne_none_of_hasType`, which the total decoder needs and which
therefore stays in the front. Then the laws in `Internal/EntryOutcomeLaws`, and a test with golden
bytes in `Test/ContractRuntime/ContractCalls.lean`. Nested calls and creation admit only profiles
with `returnsOneWord = true`.

## Pitfalls

- **The total runners take proofs.** `TopLevelExecution.run` is built from
  `TopLevelExecution.validatedRawRun`, which uses the transaction driver's typing, support,
  storage-address and checkpoint theorems. A handler change that breaks one of them breaks the
  definition, not only a theorem; this is also why `TopLevel` imports `Internal/TransactionLaws`.
- **Request case analyses are scattered**: both `handleRequest`s, the private presence proofs and
  the scheduler in `NestedExecution`, and `cases request` proofs in `Internal/StorageDriverLaws`,
  `TransactionLaws` and `CallPhaseLaws`.
- **`@[simp]` reach.** `WorldStateLaws` and `WorldStateDeltaLaws`, and `ContractLaws` and
  `EntryOutcomeLaws`, stay apart because many modules import the first of each pair without the
  second. `ScalarText` stays apart from `AddressBytes`, which would bring
  `Core/Internal/ByteSelection` into the Core wire codec.
- **Tests pin statements.** Sections named `…ExternalProperties` in `Test/ContractRuntime` use the
  laws from outside the area; changing a law's statement breaks them on purpose.
- **Older names.** Many sections carry a `## Consolidated module: …` heading
  ([Conventions](conventions.md#following-older-notes)). The area was once `Solcore.Semantics`;
  `Solcore/Semantics.lean` is a deprecated alias.

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
