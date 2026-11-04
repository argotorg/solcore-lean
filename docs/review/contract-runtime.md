# Reviewer's guide: ContractRuntime

`Solcore/ContractRuntime` executes checked Core contracts: accounts and world state, host requests,
frames and transactions, nested calls and creation, commit and rollback, and top-level observations.
It is distinct from Core's local evaluator and from the source-language judgments. The
[umbrella](../../Solcore/ContractRuntime.lean) gives this reading order in brief.

## Main definitions and theorems

These decided the front. README's "Proof status" names no result of this area, and says that native
source contracts are not connected to it yet. Its claims are the ones its users rely on, which are
also the top of its theorem dependencies:

| Claim | Theorems | Evidence |
| --- | --- | --- |
| Checked code does not fault | `TopLevelExecution.rawRun_ne_fault`, `HostDriverResult.resumeWithFuel_ne_fault` | roots of the dependencies; the Core safety claim, carried through host handling |
| Resuming is one larger run | `TopLevelExecution.resumeWithFuel_run`, `TopLevelExecution.resumeWithFuel_run_add`, `OneLevelNestedExecution.resumeWithFuel_run_add`, `BalancedTopLevelExecution.resumeWithFuel_run` | `TopLevelExecution.resumeWithFuel_run` is cited in `docs/design/scalar-emitter-meaning.md`; the others are roots |
| Host handling agrees with its path | `HostDriver.run_done_complete` | cited in the same note |
| The public entry does what it says | `BalancedTopLevelExecution.run_of_zero_value`, `BalancedTopLevelExecution.run_of_transfer_failure`, `BalancedTopLevelExecution.run_of_transfer_success` | roots of the dependencies, and the largest closures in the area |
| The call phases nest | `CallChainExecution.toCallResume_run_ofCallResume`, `CallChoiceExecution.run_ofChain` | roots of the dependencies |

The definitions in the front are every definition on the path to those runners. Definitions used
only by the refinement layers are in `Internal/`: see "What a reviewer should know".

## Reading order

1. **State.** Scalars, accounts and the world.
2. **One frame.** Outcomes, journals, traces and checkpoints.
3. **Host requests.** The generic loop, then the handler real execution uses.
4. **Contracts.** Completion conventions, checked contracts, registries and the environment.
5. **One transaction.** Then one top-level run.
6. **Nested execution.** Transfer and creation, the scheduler, and the public entry.
7. **Call phases.** Parents in continuation-passing form.

Each stage's main theorems are in its front file, after its definitions.

## Front

| File | Main declarations |
| --- | --- |
| [`RuntimeScalars`](../../Solcore/ContractRuntime/RuntimeScalars.lean) | `Address`, `Bytes`, `encodeWordBytesBE`, `encodeAddressText`, `addressToWord`, `wordToAddress?` |
| [`WorldState`](../../Solcore/ContractRuntime/WorldState.lean) | `CheckedHostCoreProgram`, `Account`, `WorldState`, `WorldState.readStorage?`, `WorldState.writeStorage?`, `WorldState.runCode?`, `WorldStateDelta` |
| [`Frames`](../../Solcore/ContractRuntime/Frames.lean) | `FrameOutcome`, `FrameRunResult`, `FrameEffectJournal`, `FrameTrace`, `FrameContinuationContext`, `FrameResolutionResult`, `FrameCheckpointedWorkingPairWithPresentStorageAccount` |
| [`Driver`](../../Solcore/ContractRuntime/Driver.lean) | `HostHandler`, `HostDriver.run`, `HostDriverResult`, `HostDriver.HandledSteps`, `HostDriverResult.FuelSoundWith`, `HostDriverResult.resumeWithFuel` |
| [`StorageDriver`](../../Solcore/ContractRuntime/StorageDriver.lean) | `HostStorageDriver.handleRequest`, `HostStorageDriver.run`, `CheckedHostCoreProgram.runWithStorage`, `HostStorageDriver.Context`, `ContractCallFailure`, `WordReturnedFrameCompletion` |
| [`Contracts`](../../Solcore/ContractRuntime/Contracts.lean) | `CoreContractEntryProfile`, `CheckedCoreContract`, `InstalledCheckedCoreContract`, `TopLevelInvocation`, `CheckedContractRegistry`, `ExecutionEnvironment` |
| [`Transactions`](../../Solcore/ContractRuntime/Transactions.lean) | `TransactionJournal`, `TransactionHostStorageDriver.handleRequest`, `CheckedHostCoreProgram.runWithTransactionStorage` |
| [`TopLevel`](../../Solcore/ContractRuntime/TopLevel.lean) | `TopLevelExecution.run`, `TopLevelExecution.rawRun`, `TopLevelExecution.finalize`, `TopLevelRunResult`, `TopLevelTerminalResult`, `CoreLanguageResult.run` |
| [`Creation`](../../Solcore/ContractRuntime/Creation.lean) | `WorldState.transferBalance`, `CheckedAccountCreation.prepare`, `CheckedCreationPreflight.prepare`, `PreparedCheckedCreation` |
| [`NestedExecution`](../../Solcore/ContractRuntime/NestedExecution.lean) | `OneLevelNestedExecution.run`, `OneLevelNestedExecution.Mode`, `OneLevelNestedExecution.RootFrame`, `OneLevelNestedExecution.ChildFrame`, `OneLevelNestedExecution.Reachable`, `OneLevelNestedExecution.Result` |
| [`BalancedExecution`](../../Solcore/ContractRuntime/BalancedExecution.lean) | `BalancedTopLevelExecution.run`, `BalancedTopLevelExecution.runWithEnvironment`, `BalancedTopLevelExecution.Result` |
| [`CallPhases`](../../Solcore/ContractRuntime/CallPhases.lean) | `CallResumeExecution.run`, `CallChainExecution.run`, `CallChoiceExecution.run`, `CallResumeParent`, `CallChainParent`, `CallChoiceParent` |

## Main theorems

Each is stated for checked code, so these carry the Core safety theorems through host handling. A
fault is a `Core.MachineFault`: a language failure, a revert and exhausted fuel are not faults.

| Result | Theorems | File | Reading |
| --- | --- | --- | --- |
| Typing with host handling | `HostDriver.run_hasType` | [`Driver`](../../Solcore/ContractRuntime/Driver.lean) | a typed start stays typed across every handled response |
| No fault with host handling | `HostDriver.run_ne_fault`, `HostDriverResult.resumeWithFuel_ne_fault` | [`Driver`](../../Solcore/ContractRuntime/Driver.lean) | neither a run nor a resumed run exposes a machine fault |
| No fault at the top level | `TopLevelExecution.rawRun_ne_fault` | [`TopLevel`](../../Solcore/ContractRuntime/TopLevel.lean) | the checked run behind the total runner cannot fault |
| Typing of a language result | `CoreLanguageResult.run_hasType` | [`TopLevel`](../../Solcore/ContractRuntime/TopLevel.lean) | a run of checked code gives a typed outcome |
| Fuel at the top level | `TopLevelExecution.resumeWithFuel_run`, `TopLevelExecution.resumeWithFuel_run_add`, `TopLevelExecution.resumeWithFuel_run_zero` | [`TopLevel`](../../Solcore/ContractRuntime/TopLevel.lean) | resuming agrees with one run on the summed budget |
| Fuel in nested execution | `OneLevelNestedExecution.resumeWithFuel_runMode`, `OneLevelNestedExecution.resumeWithFuel_run`, `OneLevelNestedExecution.resumeWithFuel_run_add`, `OneLevelNestedExecution.resumeWithFuel_run_zero` | [`NestedExecution`](../../Solcore/ContractRuntime/NestedExecution.lean) | the same across calls and creation |
| Fuel in the driver | `HostDriverResult.resumeWithFuel_run`, `HostDriverResult.resumeWithFuel_run_add` | [`Internal/DriverLaws`](../../Solcore/ContractRuntime/Internal/DriverLaws.lean) | the same for any handler |
| The public entry | `BalancedTopLevelExecution.run_of_zero_value`, `BalancedTopLevelExecution.run_of_transfer_failure`, `BalancedTopLevelExecution.run_of_transfer_success` | [`BalancedExecution`](../../Solcore/ContractRuntime/BalancedExecution.lean) | a zero-value call goes straight to execution, a failed transfer rejects, and a successful one runs on the transferred world |
| Fuel at the public entry | `BalancedTopLevelExecution.resumeWithFuel_run`, `BalancedTopLevelExecution.resumeWithFuel_runWithEnvironment`, `BalancedTopLevelExecution.resumeWithFuel_run_zero` | [`BalancedExecution`](../../Solcore/ContractRuntime/BalancedExecution.lean) | splitting fuel never repeats the transfer |
| Call phases nest | `CallChainExecution.toCallResume_run_ofCallResume`, `CallChoiceExecution.run_ofChain` | [`CallPhases`](../../Solcore/ContractRuntime/CallPhases.lean) | a chain with no middle phases is the one-call convention, and a chain is a choice with one last finish phase |
| Call phases and the world | `CallResumeExecution.run_balance?`, `CallResumeExecution.run_code?`, `CallResumeExecution.run_finalWorld_of_ne_returned` | [`Internal/CallPhaseLaws`](../../Solcore/ContractRuntime/Internal/CallPhaseLaws.lean) | balances stay as they were, and a transaction that does not return commits the world before it |

The chain and choice conventions have the same three results as the last row, in the same file.

`HostDriverResult.resumeWithFuel_run_add` is the one main theorem outside the front: it rests on about
600 lines of `Internal/DriverLaws`, which is more than `Driver` should hold.

There is no separate file of main theorems here, as `Core/Safety` is for Core. Such a file would sit
above the old module paths, and tests name these theorems through those paths in `#check` and `example`.

Below these, a reader checking a proof will want `HostDriver.run_done_complete` in
`Internal/DriverLaws` and `WorldState.runCode?_ne_some_fault` in `Internal/WorldStateLaws`.

## Internal

Laws of the front, one file for each part of it, apart from the two splits explained below:

| File | Topic |
| --- | --- |
| [`ScalarLaws`](../../Solcore/ContractRuntime/Internal/ScalarLaws.lean) | Word bytes, and the bridge between addresses and words |
| [`ScalarText`](../../Solcore/ContractRuntime/Internal/ScalarText.lean) | The text encodings of scalars |
| [`WorldStateLaws`](../../Solcore/ContractRuntime/Internal/WorldStateLaws.lean) | Account fields under updates, conditional storage reads, code lookup |
| [`WorldStateDeltaLaws`](../../Solcore/ContractRuntime/Internal/WorldStateDeltaLaws.lean) | Balance and nonce lookup, and the queries of `WorldStateDelta` |
| [`FrameLaws`](../../Solcore/ContractRuntime/Internal/FrameLaws.lean) | Outcomes, journals, traces, continuation, resolution, checkpointed pairs |
| [`DriverLaws`](../../Solcore/ContractRuntime/Internal/DriverLaws.lean) | `HostDriver.run`: cases, typing, no faults, paths, stability, resumption |
| [`StorageDriverLaws`](../../Solcore/ContractRuntime/Internal/StorageDriverLaws.lean) | Input data, each request's response and effect, the storage driver's run |
| [`ContractLaws`](../../Solcore/ContractRuntime/Internal/ContractLaws.lean) | Word programs, profiles, checked contracts, registries, the environment |
| [`EntryOutcomeLaws`](../../Solcore/ContractRuntime/Internal/EntryOutcomeLaws.lean) | Exact recognition and decoding per profile, and decoded Word outcomes |
| [`TransactionLaws`](../../Solcore/ContractRuntime/Internal/TransactionLaws.lean) | The transaction journal, and the transaction driver |
| [`TopLevelLaws`](../../Solcore/ContractRuntime/Internal/TopLevelLaws.lean) | The top-level run, storage deltas, language results at the boundary |
| [`CreationLaws`](../../Solcore/ContractRuntime/Internal/CreationLaws.lean) | `WorldState.transferBalance` by cases, and the two preflights |
| [`NestedLaws`](../../Solcore/ContractRuntime/Internal/NestedLaws.lean) | The depth-one word call, transition steps, anchoring of reachable states |
| [`BalancedLaws`](../../Solcore/ContractRuntime/Internal/BalancedLaws.lean) | Projections of a balanced result |
| [`CallPhaseLaws`](../../Solcore/ContractRuntime/Internal/CallPhaseLaws.lean) | Balances, code and the final world across call phases |

Refinement layers, which tests use and the top-level runners do not:

| File | Topic |
| --- | --- |
| [`AddressBytes`](../../Solcore/ContractRuntime/Internal/AddressBytes.lean) | Exact-width address bytes, and their agreement with address text |
| [`CheckedCoreProgram`](../../Solcore/ContractRuntime/Internal/CheckedCoreProgram.lean) | Checked closed programs with no host capability |
| [`CodeExecution`](../../Solcore/ContractRuntime/Internal/CodeExecution.lean) | Running the code at a selected account |
| [`ParentIndexedFrames`](../../Solcore/ContractRuntime/Internal/ParentIndexedFrames.lean) | Frame contexts tied to one parent working pair |
| [`ParentIndexedExecution`](../../Solcore/ContractRuntime/Internal/ParentIndexedExecution.lean) | Parent-indexed selected execution and its sessions |
| [`SelectedWordExecution`](../../Solcore/ContractRuntime/Internal/SelectedWordExecution.lean) | Code selected by address and classified as Word code |

## What a reviewer should know

- **Definitions and laws are in separate files.** Old paths such as
  `Solcore.ContractRuntime.TopLevelExecution` are shims until consolidation, and they lead to the laws,
  because outside tests use the laws. So the definitions have new file names. Declarations and
  namespaces did not change: `TopLevelExecution.run` is still called that, and it is in `TopLevel`.
- **Three front files keep more proofs, because of `private`.**
  - `WorldState`: the constructors and fields of `Account` and `WorldState` are private, so the 510
    lines of laws that unfold them stay.
  - `NestedExecution`: `OneLevelNestedExecution.Result` has a private constructor, so the theorems that
    build one stay, 670 lines with the main theorems.
  - `BalancedExecution`: the same for `BalancedTopLevelExecution.Result`, 260 lines.
- **Other front files keep main theorems and the few a definition needs.** A definition can take a
  proof as an argument, so the theorem has to sit above it. `Contracts` has the most, 300 lines: the
  profile decoders are total on typed values, and `CoreContractEntryProfile.decode?_ne_none_of_hasType`
  and its companions show it. `Frames` and `Creation` hold under 50 lines. `StorageDriver` and
  `Transactions` hold none.
- **Front files can import proofs.** A front file imports an `Internal/` file of a lower family when one
  of its definitions needs a theorem. The front does not close on itself here as it does in Core,
  because checked contracts carry their typing evidence. The families form one chain, in the reading
  order above.
- **Files that look like one topic are separate on purpose,** because a `@[simp]` lemma reaches every
  module that imports any part of its file.
  - `WorldStateLaws` and `WorldStateDeltaLaws`, and `ContractLaws` and `EntryOutcomeLaws`: about 300
    modules reach the first of each pair and not the second.
  - `ScalarText` and `AddressBytes`: the Core wire codecs import the first, and the second would bring
    `ByteSelection` to them.
- **One copy was deleted.** `AddressBytesBE` and `AddressRepresentationCoherence` each declared the
  private `addressByteModulus`, with the same text. `Internal/AddressBytes` holds them both, so it keeps
  the first copy. `.refactor/deleted-r2.tsv` records this.
