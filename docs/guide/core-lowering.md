# Core lowering

`Solcore/SourceSemantics/CoreLowering/` proves that the Core code the native compiler generates means
what the [source semantics](source-semantics.md) says. Its theorems relate a compiled body's Core run
and an independent Source execution in both directions, including failures, control transfers and
the reached heap, and connect public compilation to sessions whose calls agree with Source. They
cover parts of the language: the theorem for the complete compiler is unfinished
([What remains](#what-remains)).

- **Input.** The actual compiler's results and receipts: `SourceCoreCompiler.compile`, the public
  `SourceCompiler.compile`, and the code that the lowering in `Solcore/Frontend/SourceCore/` emits
  ([Frontend](frontend.md)). On the Source side, mostly the staged traces of `Staging.Recursive`.
- **Builds on.** [Source semantics](source-semantics.md), [Frontend](frontend.md) (the lowering,
  sessions and the public API) and [Core](core.md) (evaluation and typing).
- **Built on by.** The tests. Also, the source semantics' compiled route (`CompiledBodies`,
  `Internal/Compiled`, `Internal/Prepared`) and `Staging/Internal/FaultCalls` import a few files of
  `Internal/`.

The umbrella is [CoreLowering](../../Solcore/SourceSemantics/CoreLowering.lean). It also imports the
parts of the source semantics that the SourceSemantics umbrella leaves out. A namespace names a section
of a file, not a file: `CellAwareInvocationAcceptedFlow` is a section of
[AcceptedStatements](../../Solcore/SourceSemantics/CoreLowering/AcceptedStatements.lean).

## Where things are

### Front

The files in route order: what the compiler did, the general route to the public root, the public
API, and families with a finite profile.

| File | Holds |
| --- | --- |
| [AcceptedTrees](../../Solcore/SourceSemantics/CoreLowering/AcceptedTrees.lean) | The receipts the compiler leaves when it accepts a named body: `AcceptedNamedBodyFlow.Tree`, `AcceptedNamedBodyFlow.Body`, and the write heads (`AcceptedBareAssignmentReceipt.Receipt`, …). Change it with the compiler's statement lowering |
| [ActualBodyInvocation](../../Solcore/SourceSemantics/CoreLowering/ActualBodyInvocation.lean) | `ActualBodyInvocation.Index`: one invocation, a named cache row or a materialized closure |
| [AcceptedStatements](../../Solcore/SourceSemantics/CoreLowering/AcceptedStatements.lean) | The statement closure: `CellAwareInvocationAcceptedFlow.Covered`, `correct`, `body_preserves`, `body_reflects`, and their inputs (`CellAwareInvocationAcceptedInputs.Expressions`, `Writes`, `Generalized`). A new statement branch goes here |
| [AcceptedExpressions](../../Solcore/SourceSemantics/CoreLowering/AcceptedExpressions.lean) | The first expression subset (`CellAwareInvocationAcceptedExpressionTrees.Subset`, `CellAwareInvocationAcceptedExpressions.Closed`) and the named-row entry |
| [AcceptedShapes](../../Solcore/SourceSemantics/CoreLowering/AcceptedShapes.lean) | A Source shape that implies `Covered` (`CellAwareInvocationAcceptedBodyShape.Shape`), and staged traces lifted from Source (`CellAwareInvocationAcceptedStatementLifting.body`) |
| [AcceptedCalls](../../Solcore/SourceSemantics/CoreLowering/AcceptedCalls.lean) | Direct calls at expression roots, and the closure of a family of rows by strong induction on the grade |
| [AcceptedPublicRoots](../../Solcore/SourceSemantics/CoreLowering/AcceptedPublicRoots.lean) | Accepted bodies at the actual public start |
| [PublicSupport](../../Solcore/SourceSemantics/CoreLowering/PublicSupport.lean) | `CompilerProgramStaticProfile.StaticProfile`, program support, `SelectedCompilationPublicSessionState.State` |
| [PublicSessions](../../Solcore/SourceSemantics/CoreLowering/PublicSessions.lean), [PublicSessionOutcomes](../../Solcore/SourceSemantics/CoreLowering/PublicSessionOutcomes.lean) | From actual compilation to an issued session, and one call of it in both directions |
| [PublicOutputs](../../Solcore/SourceSemantics/CoreLowering/PublicOutputs.lean) | Complete public values of closed staged bodies |
| [CellAwarePublicRoots](../../Solcore/SourceSemantics/CoreLowering/CellAwarePublicRoots.lean), [CellAwarePublicForward](../../Solcore/SourceSemantics/CoreLowering/CellAwarePublicForward.lean) | The named, lexical, faulting, imperative and materialized families at the unchanged public root, and their public outcomes |

### Internal

Each directory is one family, merged by topic; each file opens with a module doc.

| Directory | Holds |
| --- | --- |
| `Foundations/` | Heaps and location maps, Core evaluation and renaming, function values and calls, capture copies, primitive expressions, sizes of Source executions (`SourceExecutionSize`) |
| `Data/` | Payloads, places, patterns, mappings and equality on Core data; `DataHeap.EnvRepresents` |
| `Compatible/` | The source-compatible profile: expressions, places, matches, mappings, assignments, statements |
| `Statements/` | Statement, loop and match meaning on the typed and generic carriers; named and builtin calls |
| `Protected/` | Contracts that carry a state witness (`ProtectedStateTransition`) through expressions, statements and loops |
| `Diagnostics/` | Emitted diagnostic plans and reached fault paths |
| `Callable/` | Callable ancestry, coercions, lambda views, prepared methods, and indexed callables (lambda values, entries, parameters) |
| `Owned/` | Function values with immutable keys and reached pools; stored, chosen and contextual calls; lambda receipts |
| `OwnedAdmitted/`, `OwnedPrepared/`, `OwnedStaged/` | Graded interfaces of the recursive staged profile; receipts read from actual cached preparation; staged bounds by body shape and call form |
| `RecursiveNamed/` | The finite named-call catalog, the staged profile's primitives and calls, and their public results |
| `Generalized/` | Generalized local functions: compilation, formation, reads and body meaning |
| `Accepted/` | Accepted expressions and programs, invocation allocation, scoped Source bodies |
| `CellAware/` | Bodies over heaps that mix value cells and function descriptors: invocations, scopes, Source lifting, public handles |
| `Selected/` | Selected compilations: admission, calls, public steps, and lifting to staged Source |

**Words.** Names are systematic. *preserves* goes from Source to Core and *reflects* back; *bounds*
is a graded preservation and reflection contract; a *receipt* or *certificate* is static evidence
kept from the compiler, with no execution law; *selected compilation* is the requested roots, their
dependencies and the callable instances actually compiled; *staged* means `Staging.Recursive`;
*lifting* turns an ordinary Source trace into a staged one; *compatible* is the source-compatible
native profile; *protected* passes a state witness from child to child; *indexed* callables sit in a
fixed table; *owned* function values have immutable keys; *prepared* is read from actual cached
preparation; *cell-aware* heaps mix value cells and function descriptors; a *materialized* function
is a generalized local instantiated at a read.

## Definitions and theorems you build on

Each theorem's premises are part of its contract: a connected profile does not imply coverage of all
compiler-accepted syntax.

| Name | Reading | Used by |
| --- | --- | --- |
| `CellAwareInvocationAcceptedFlow.correct` | Induction over the accepted tree closes the statement flows that `Covered` admits | `body_preserves`, `body_reflects` |
| `CellAwareInvocationAcceptedFlow.body_preserves`, `body_reflects` | An accepted body of an `ActualBodyInvocation.Index` and a staged Source execution of its statements imply each other, with the result, the heap relation and the protocol state. Premises: `Expressions`, `Writes`, `Covered`, the compiler artifact, the checker run, fixed-control typing and Core typing of the body | `AcceptedExpressions`, `AcceptedCalls` |
| `CellAwareInvocationAcceptedExpressions.expressions`, `body_preserves`, `body_reflects` | `Closed` gives `Expressions` at every budget, so the body theorems hold without it for the first subset | `CellAwareInvocationAcceptedNamedInvocation.preserves_selected` |
| `CellAwareInvocationAcceptedCallFamily.preserves`, `reflects`, `expressions` | One strong induction on the grade closes a family of rows with direct calls | The call root in `AcceptedPublicRoots` |
| `CellAwarePublicAcceptedNamedRoot.checkpoint_has_sufficient_fuel_selected`, `checkpoint_reflects_selected` | A staged Source trace and the native completion of the actual public start imply each other | Test `Generalized/Export` |
| `SelectedCompilationRawPublicReceipt.of_compile` | A public compilation keeps its exact artifact, checking budget and prepared recipe in a `Receipt` | `Receipt.checker_bodies`, `checker_profiled`, `checker_initial_row` |
| `SelectedCompilationRawPublicReceipt.Receipt.checker_bodies` | The receipt gives validity of every cached body, through `SourceCompiledActualInitializerBarriers.compile_cached_bodies`; the profiled forms keep `StaticProfile` as a premise | The sessions |
| `SelectedCompilationCertifiedPublicSession.of_checked`, `of_checked_profile`, `Issued.forward_scalar`, `Issued.reflect_scalar_plain`, `Profiled.reflect_failure_plain` | A checked program issues a session; Source success reaches a later call's public result, and public results reflect to independent Dynamic applications | Tests in `Selected/` |
| `SelectedCompilationStageClosedOutputForward.initial`, `later` | Ordinary Source success determines the complete public value at the first and later calls | — |
| `CellAwarePublicNamedRoot.preserves_root`, `reflects_root` and the other families | The unchanged root relates a body to its native run | `CellAwarePublicForward`; tests in `Mixed/` use the imperative family's |

The statements use these definitions, all in `Internal/`:

| Definition | Reading | File |
| --- | --- | --- |
| `DataHeap.EnvRepresents` | A Source environment and its Core slots | `Data/HeapsAndBindings` |
| `GenericHeap.CellHeapRepresents`, `GenericHeap.HeapRepresents` | The heap relation, over whole cells or payloads | `Foundations/GenericHeaps` |
| `GeneralHeap.LocationMap.Extends`, `GeneralHeap.AdministrativePreserved` | The location map grows; administrative cells keep their values | `Foundations/Heaps` |
| `ProtectedStateTransition.Protocol` | A state witness carried from child to child | `Protected/StateAllocation` |
| `CallableIndexedOwnedFunctionValues.OwnedKey` | The immutable key of a function value | `Owned/FunctionValuesAndState` |
| `RecursiveStageMeaning.ResultRepresentsFor` | A Source result and its Core value | `RecursiveNamed/StageCalls` |

## Making changes

### When the source semantics or the compiler changes

Build the umbrella and work up from the lowest failing file: its importers fail with it. What breaks
depends on the change.

- **A new operator** (5b8c6e96d, e8d28e957). Most changed files changed by a line or two, in
  `Compatible/`, `Statements/`, `Diagnostics/`, `Protected/` and `Data/`.
  - `PrimitiveExpressions.strict_binary_value` (`Foundations/PrimitiveExpressions`) gains a case per
    strict operator; the integer case of `CompatibleExpressionPrimitives.BinaryProfile` takes
    `IntegerStrictBinaryOperator`, so a Word-only operator never reaches the integer bodies.
  - Compound assignment carries an assignment profile,
    `operator = .equal ∨ T = .word ∨ T = .integer ∧ operator.wordOnly = false`, restated in each
    file that needs it and in the receipts' `operatorType`. A new Word-only compound operator goes
    into `Syntax.ValueAssignOp.wordOnly`; `DataPlaceModifier.word_success` gains its case and
    `integer_success` refutes it.
  - The public-API tests go in [Foundations/Execution](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean);
    the `example` in `Tests.SourceCorePrimitiveExpressions` (`Foundations/Statements`) runs every
    `StrictBinaryOperator` through `PrimitiveExpressions.lowerExpression_preserves`.
- **A changed rule** (7ac75aea3, closures by value). Theorems whose statements mention the old
  premise are restated over the new one. Most changes were in `Owned/`, `CellAware/`, `OwnedStaged/`,
  `OwnedPrepared/`, `Callable/`, `Statements/`, `Generalized/`, `Selected/` and `Foundations/`.
  Change the sized copies in `Foundations/SourceExecutionSize` with the rule.
- **Different emitted code.** Receipts record the compiler's exact call and result
  (`AcceptedBareAssignmentReceipt.Receipt` keeps `accepted`, `generated` and `emitted`). A change in
  what the lowering emits breaks the inversions that build them
  (`AcceptedBareAssignmentReceipt.of_accepted`, `CompatibleBareAssignment.of_lower`) and the meaning
  proofs that read them.
- **Tests.** Runtime tests record native heap sizes and exact heaps, so a lowering that allocates
  differently changes their expectations, as the closure commit did.

### Extend the proved subset

As in f33466eaf (matches in the accepted-body closure), 762a6d4b1 (direct-call roots in the
expression subset) and 4d434af3a (the first expression subset):

1. Add the branch to the front file of its route, as a new section with its own namespace:
   statements in `AcceptedStatements` (a new `Covered` case), expressions in `AcceptedExpressions`,
   calls in `AcceptedCalls`.
2. Close it from the compiler's own receipts and the existing family heads of `Internal/`
   (f33466eaf also extended `Compatible/MatchPrefixes`). No expression or body execution law may be
   an input.
3. Carry it to a consumer of the real public API (`AcceptedPublicRoots`, the sessions), and update
   "Established proof connections" and "Remaining work" in the
   [design note](../design/core-runtime-unification.md), with the umbrella's module doc.

## Closures by value

The lowering mirrors the source rule of [closures by value](source-semantics.md#closures-capture-by-value)
allocation by allocation (7ac75aea3). Core's syntax and semantics, the Hull importer and the contract
runtime did not change.

**Lowering**, in `SourceCoreSourceCells` and `SourceCoreFunctions` of
[Frontend/SourceCore/Lowering](../../Solcore/Frontend/SourceCore/Lowering.lean):

- `copyScope` copies the slots that `CaptureBinders.copiedBinder?` selects (`copiedSlots`), then runs
  the body with each copied slot renamed to its copy (`scopeCopyRenaming`). `copyCell` loads the
  slot's optional payload and allocates an uninitialized or an initialized cell in the two branches
  of a `caseE`. Without an allocator a copy is a plain `newCell` (`copyScopePlain`).
- With the profile's allocator (`SourceCoreSourceCells.marked`) a copy is a marked source allocation
  whose references follow the convention of named inputs (`copyReferences`). Copies must be marked:
  the allocation ledger rejects a marker capture it does not record
  (`SourceCoreAllocationLedger.Error.unknownCaptureLocation`).
- The lambda lowering wraps the lowered lambda in `copyScope` at creation, when the policy's
  `snapshotLambda` holds, and wraps the raw body's parameter binding in `copyScope`, so each call
  copies again. A generalized declaration copies its scope once around its bundle
  (`letInitializedSnapshot`); its initializer's lambda takes no snapshot of its own, since
  `snapshotLambda` is false for it.

**Proofs:**

- `CaptureCopies.copies_prefix` (`Foundations/FunctionCalls`) and `CaptureCopies.marked_copies_prefix`
  (`Foundations/LambdaViewsAndMarkedCaptures`) relate the Core copies of a represented scope to the
  Source copies `Dynamic.EnvironmentCopies`: the heap relation extends, the scope's slots point at the
  copies, slots past the scope keep their values, and the copies agree with their continuation.
  `CaptureCopyRenaming` and `CaptureCopyTyping` hold the renaming and typing of a copy chain.
- `DataHeap.EnvRepresentsIn.internal` describes a Core slot that the Source environment does not bind
  by its typed Core cell.
- Formation: `CallableIndexedLambdaValues.formation` (`Callable/IndexedLambdaTyping`) gives a
  `CallableIndexedLambdaValues.Formed` record: the Source copies, the closure's capture layout over
  them, the extended heap relation and the Core evaluation. The closure is `formed.closure`, stated at
  `formed.finalMap` and `formed.finalWorld`, and its code is the creation code recaptured
  (`CallableIndexedLambdaValues.Code.recapture`). Consumers take a record as an argument or obtain one
  from an existence lemma such as `CallableIndexedOwnedLambdaFormationReceipts.formation_exists`;
  protocol states move to the formed state by administrative transport (`formedState` in
  `Owned/MethodLambdas` and `Owned/OrdinaryLambdas`). The non-indexed `FunctionValues.formation` and
  `ContractedFunctionValues.formation` conclude the copies directly.
- Calls: `CallableIndexedLambdaViewPrefix.Entry` records the copy of the captured cells
  (`Dynamic.EnvironmentCopies … function.captured …`) and then the parameter allocation. Protected
  protocols are rebound to the copied slots (`ProtectedStateTransition.Rebinds`).
- Generalized `let`: `CellAwareGeneralizedSnapshotCode` gives the emitted snapshot around the bundle,
  `CellAwareNamedGeneralizedPrefix.complete` follows it over the Source copies, and
  `ProtectedStateTransition.Bindings.rebind` rebinds the protocol state over the copied scope.

**Tests.** `Tests.SourceCoreExecution` in
[Foundations/Execution](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean)
runs #120's programs, a repeated call, a loop-carried capture and an adaptation of upstream's
`control-flow-capture-identity` fixture. Tests written for shared cells now expect by-value results:
closures created together or by different calls no longer share a capture cell, and a closure that
reaches itself through a local assigned after its creation copies that local uninitialized, so its
recursive call faults (`Callable/Ancestry`). Copies also change the native heap sizes that tests
record.

## What remains

The [Core runtime unification design](../design/core-runtime-unification.md) records the remaining
work, under "Remaining work for the second goal". In short:

- `StaticProfile` recognizes a strict subset on purpose. The general proof comes from the actual
  named and contextual compiler receipts, not from widening a recognizer or from a body-execution law.
- `Covered` still excludes writes and matches under contextual metadata views, and statements after an
  always-returning prefix in a non-Unit function.
- The expression closure covers a first subset and direct calls at expression roots. Calls inside
  other expressions remain, then indirect and builtin calls, methods, indices, tuples, constructors,
  generalized reads, closures and coercions. For call-containing rows at the public root, the
  reflection direction and the lifting of their Source traces remain.
- The proof target is a successful selected compilation, not the whole workspace and not checker
  acceptance alone. Each extension ends in a consumer of the real public API.

## Pitfalls

- **Premises are the contract.** A theorem over a recognized profile says nothing about other
  compiler-accepted syntax. Do not make a recognizer look universal, and do not add an execution law
  as a premise.
- **Lockstep with the semantics.** The copy decision is one function, `CaptureBinders.copiedBinder?`,
  for both sides, and `Foundations/SourceExecutionSize` restates every dynamic rule with a size.
- **The assignment profile is text, not a definition.** It is restated wherever it is needed; search
  for `wordOnly` to find every copy.
- **Bare names depend on imports.** `Foundations/CoreEvaluation` and `Callable/ViewWrappers` stay below
  the Source [Context](../../Solcore/SourceSemantics/Context.lean), because `Context` there is
  `Core.Context` through `open Core`. `Statements/GenericImperativeFor` and `TypedImperativeFor` keep
  their trees in separate files: they read `Scope` and `ValuesContext` through an `open`, and names of
  the same spelling in the tree files would win.
- **`@[simp]` reach.** `Statements/LoopLayouts` holds the `simp` lemmas `rename_insert` and
  `rename_insert_lift`, and `Statements/LoopRenaming` stays below it because they loop in its proofs
  at the `for` post edge.
- **Matchers.** Lean reuses an alpha-equal matcher within a file. `Callable/AncestryWorklists` stays
  apart from `Callable/Ancestry`, or the equations of `lists` would take their variable names from
  the matcher of `spines`; `Owned/DecodedCallFaults` stays apart from `Owned/ChosenOrdinaryCalls`, or
  `CallableIndexedOwnedPublicDecodedStagedCallFaults.faults` would stop being a namespace.
- **Private names, notations and instances.** The paired seeds live in `Callable/MethodOrigins`,
  because in `Callable/AncestryPaired` its private `bind_ok` would make their references ambiguous;
  `Callable/CoercionSpine` stays below `SourceCoreCallablePrincipals`, whose private `BEq TypedBinder`
  breaks its derived instances; `RecursiveNamed/PublicDirectClosureApplications` and
  `PublicDirectApplications` share three local notations, so they stay apart.
- **Import order picks instances.** The first two imports of `Callable/MethodOrigins` are in that
  order on purpose: they decide which equal-priority `DecidableEq` and `LawfulBEq` instances its
  validators use. Its module doc says which.
- **Isolation probes.** `#check_failure` lines in the tests assert what a file's imports must not
  reach. `Compatible/Payloads` stays below the compiler's encoder, and its tests check that
  `SourceCoreCompatibleValues.encode` is out of reach.
- **Some files sit below the compiled route.** The source semantics' compiled route imports
  `Selected/CatalogOrigins`, `Selected/MethodBodies` and some files of `Callable/`, `Generalized/` and
  `RecursiveNamed/`. They must not import `CompiledBodies`, `Internal/Compiled`, `Internal/Prepared`
  or `Staging/Preservation`.

## Testing

The tests are under [Solcore/Test/SourceSemantics/CoreLowering](../../Solcore/Test/SourceSemantics/CoreLowering),
by subject; [Tests](tests.md) lists them.

| Tests | Cover |
| --- | --- |
| [Foundations/Execution](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean), `Foundations/EntryPoints`, `Foundations/Snapshots` | The public API: compile, open a session, call, resume; closures by value, shifts, unchecked arithmetic |
| `Captured/`, `Callable/`, `Generalized/`, `Evidence/`, `Method/` | Closures and callables: captures, ancestry, indexed lambdas, generalized exports, evidence |
| `Compatible/`, `Data/`, `Mixed/`, `Named/`, `Recursive/`, `Chosen/`, `Closed/` | Profiles and families: places, assignments, matches, loops, named and recursive rows |
| [Selected/Profiles](../../Solcore/Test/SourceSemantics/CoreLowering/Selected/Profiles.lean), [Generalized/Export](../../Solcore/Test/SourceSemantics/CoreLowering/Generalized/Export.lean) | Instantiate the front's session and public-root theorems on fixtures |
| `UnifiedCorpus`, `UnifiedOperatorCorpus` | The unified runtime on canonical checked programs |

Lean checks the theorems and examples of a test file when it builds it, and `lake test` runs the
`IO` entry points registered in [Tests/Main.lean](../../Tests/Main.lean). Focused checks:

```sh
lake build Solcore.SourceSemantics.CoreLowering
lake build Solcore.Test.SourceSemantics.CoreLowering.Foundations.Execution
```

Then run the checks of [Workflow](workflow.md#before-you-commit).
