# Core lowering

`Solcore/SourceSemantics/CoreLowering/` proves that the Core code the native compiler generates
means what the [source semantics](source-semantics.md) says. Its theorems relate a compiled body's
Core run and an independent Source execution in both directions, including failures, control
transfers and the reached heap. They also connect public compilation to sessions whose calls agree
with Source. They cover parts of the language: the theorem for the complete compiler is unfinished
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
parts of the source semantics that the SourceSemantics umbrella leaves out. A namespace names a
section of a file, not a file: `CellAwareInvocationAcceptedFlow` is a section of
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
| [AcceptedShapes](../../Solcore/SourceSemantics/CoreLowering/AcceptedShapes.lean) | A Source shape that implies `Covered` (`CellAwareInvocationAcceptedBodyShape.Shape`, checked by `shapeWith?`), and staged traces of call-free bodies lifted from Source (`CellAwareInvocationAcceptedStatementLifting.body`) |
| [AcceptedCalls](../../Solcore/SourceSemantics/CoreLowering/AcceptedCalls.lean) | Direct calls at expression roots and their check on a compiled row |
| [AcceptedConversions](../../Solcore/SourceSemantics/CoreLowering/AcceptedConversions.lean) | The builtin conversions as compiler sites: the native check, the compiler's receipt, the dirty-integer revert's token law (`CellAwareInvocationAcceptedConversionFaults.DirtyToken`) and the head |
| [AcceptedNestedCalls](../../Solcore/SourceSemantics/CoreLowering/AcceptedNestedCalls.lean) | Direct calls and the builtin conversions inside expressions and as arguments (`CellAwareInvocationAcceptedNestedTrees.Nested`), their closure and check, and the closure of a family of rows by strong induction on the grade |
| [AcceptedCallLifting](../../Solcore/SourceSemantics/CoreLowering/AcceptedCallLifting.lean) | Staged traces lifted from Source for bodies with direct calls and the builtin conversions at any expression position, by strong induction on the size of the original derivation (`CellAwareInvocationAcceptedCallLifting.body`) |
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

**Words.** Names are systematic:
- *preserves* goes from Source to Core and *reflects* back; *bounds* is a graded preservation and
  reflection contract.
- A *receipt* or *certificate* is static evidence kept from the compiler, with no execution law;
  *prepared* is read from actual cached preparation.
- A *selected compilation* is the requested roots, their dependencies and the callable instances
  actually compiled. *Staged* means `Staging.Recursive`; *lifting* turns an ordinary Source trace
  into a staged one.
- *compatible* is the source-compatible native profile; *protected* passes a state witness from
  child to child; *indexed* callables sit in a fixed table; *owned* function values have immutable
  keys; *cell-aware* heaps mix value cells and function descriptors; a *materialized* function is a
  generalized local instantiated at a read.

## Definitions and theorems you build on

Each theorem's premises are part of its contract: a connected profile does not imply coverage of all
compiler-accepted syntax.

| Name | Reading | Used by |
| --- | --- | --- |
| `CellAwareInvocationAcceptedFlow.correct` | Induction over the accepted tree closes the statement flows that `Covered` admits | `body_preserves`, `body_reflects` |
| `CellAwareInvocationAcceptedFlow.body_preserves`, `body_reflects` | An accepted body of an `ActualBodyInvocation.Index` and a staged Source execution of its statements imply each other, with the result, the heap relation and the protocol state. Premises: `Expressions`, `Writes`, `Covered`, the compiler artifact, the checker run, fixed-control typing and Core typing of the body | `AcceptedExpressions`, `AcceptedCalls` |
| `CellAwareInvocationAcceptedExpressions.expressions`, `body_preserves`, `body_reflects` | `Closed` gives `Expressions` at every budget, so the body theorems hold without it for the first subset | `CellAwareInvocationAcceptedNamedInvocation.preserves_selected` |
| `CellAwareInvocationAcceptedCallFamily.preserves`, `reflects`, `expressions` | One strong induction on the grade closes a family of rows with direct calls and the conversions of a word at any expression position | The call root in `AcceptedPublicRoots` |
| `CellAwarePublicAcceptedNamedRoot.checkpoint_has_sufficient_fuel_selected`, `checkpoint_reflects_selected` | A staged Source trace and the native completion of the actual public start imply each other | Test `Generalized/Export` |
| `CellAwarePublicAcceptedCallRoot.checkpoint_has_sufficient_fuel_selected`, `checkpoint_reflects_selected`, `expressions_of_family` | The same for a call-containing body, whose expression meaning comes from a family of callee rows | Test `Accepted/OneCall` |
| `CellAwareInvocationAcceptedCallLifting.body`, `Callees` | An original execution of a shaped call-containing body is a sized staged trace, given the admitted callees' static receipts | Test `Accepted/OneCall` |
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

Build the umbrella and work up from the lowest failing file: its importers fail with it.

- **A new operator.** Most files change by a line or two, in `Compatible/`, `Statements/`,
  `Diagnostics/`, `Protected/` and `Data/`.
  - `PrimitiveExpressions.strict_binary_value` (`Foundations/PrimitiveExpressions`) gains a case per
    strict operator. The integer case of `CompatibleExpressionPrimitives.BinaryProfile` takes
    `IntegerStrictBinaryOperator`, so a Word-only operator never reaches the integer bodies.
  - An operator whose meaning differs at a fixed-width integer type takes its own `BinaryProfile`
    case and mode, such as `fixedChecked` or `fixedShift`, and its own body in
    `SourceCorePrimitive`, such as `checkedBinary`. The compiler's `binaryLowering` chooses the mode
    from the left operand's type and the operator, as the source semantics does. Division divides
    the magnitudes and restores the sign (`truncatedDivision`), since Core's `integerDiv` and
    `integerMod` are Euclidean.
  - A compound form carries the assignment profile, `WideAssignmentProfile`
    (`Foundations/FixedModifiers`): `AssignmentProfile` (`Foundations/AssignmentProfiles`) on the
    target's view, that is plain assignment or a compound one at a `Word` target or at an
    `integer` one whose operator is not Word-only, or `FixedCompoundAssignment` at a fixed-width
    target. A new Word-only compound operator goes into `Syntax.ValueAssignOp.wordOnly`;
    `DataPlaceModifier.word_success` gains its case and `integer_success` refutes it.
  - Fixed-width compound targets are compiled with the modified leaf wrapped to the type's width
    (`placeWrap`) and the operator's checks in `guard`
    ([design note](../design/integer-types-unchecked-shifts.md#row-1s-compound-assignments-checked-at-the-guard),
    [why the wrap belongs to the leaf](../design/integer-types-unchecked-shifts.md#row-1s-unchecked-compound-assignments-the-wrap-belongs-to-the-leaf)).
    The meaning proofs take them through `FixedCompoundAssignment`, except `<<=` and `>>=`,
    which `FixedCompoundAssignmentOperator` leaves out. A `Word` target's `<<=` and `>>=` are
    inside, with an amount of its own type (`AssignedRhsView`).
  - Public-API tests go in `Foundations/Execution`. The `example` in
    `Tests.SourceCorePrimitiveExpressions` (`Foundations/Statements`) runs every
    `StrictBinaryOperator` through `PrimitiveExpressions.lowerExpression_preserves`.
- **A new literal carrier.** The compiler's numeric branch picks the validator from the literal's
  type (`validateFixedIntegerLiteral`). `CompatibleExpressionLiterals.Literal` gains a case built
  from the validator's certificate, `NumericLiteralEvidenceReceipts` gains its construction, and the
  other files add the case to their splits over `Literal`. Numeric patterns at `uint256` have
  `LiteralCode.uint256` in both pattern-leaf codes (`DataPatternLeaves`, `CompatiblePatternLeaves`).
  `case uint256(p)` needs no leaf: a `uint256` value's Core value is its word, so it compiles as
  `p`'s matcher.
- **A new builtin function**, such as the conversions `uint256(w)`, `uintN(w)` and `intN(w)`. A
  builtin that is not a closure stays out of `BuiltinFunctionId.all`, so no program's globals,
  callable table or closure identities change, and `lowerExpressionWithPolicy` lowers it inline.
  On the accepted-body route the conversions are nested sites
  (`CellAwareInvocationAcceptedConversionSites.of_accepted`); the older families' builtin calls
  still take `function.conversion? = none` (`BuiltinCalls.call_of_accepted`).
- **A form only the compatible profile lowers**, such as row 4's arrays, slices and memrefs. The
  public compiler lowers through the compatible profile (`SourceCoreUnifiedCompilation`); the strict
  catalog (`SourceCoreDataCatalog`) still rejects these types, so their forms stay outside the
  proved subset.
  - A new type takes its Core representation in the compatible catalog
    (`SourceCoreCompatibleCatalog.Catalog.project`), whose inductions in `Compatible/` take its
    case. A slice `arraySlice<B>` projects to the product of `B`'s Core type and two words (its
    base, start and length), a memref `memref<T>` to that of `T[]`'s Core type and a word (its
    array and position).
  - A form takes cases in `lowerWithReasons` and `leafLowerer`, with its lowerer in
    [`SourceCoreDataExpressions`](../../Solcore/Frontend/SourceCore/DataExpressions.lean). An
    element write, plain, compound or in-place `~`, takes a branch of the place lowering
    (`SourceCoreCompatibleDataPlaces.lowerElements`) and of the fault-site pass
    (`SourceCoreCompatibleDataPlaceFaultSites.prepare`).
- **A changed rule**, such as closures by value. Restate the theorems whose statements mention the
  old premise, and change the sized copies in `Foundations/SourceExecutionSize` with the rule.
- **Different emitted code.** Receipts record the compiler's exact call and result
  (`AcceptedBareAssignmentReceipt.Receipt` keeps `accepted`, `generated` and `emitted`). A change in
  what the lowering emits breaks the inversions that build them
  (`AcceptedBareAssignmentReceipt.of_accepted`, `CompatibleBareAssignment.of_lower`) and the meaning
  proofs that read them.
- **Tests.** Runtime tests record native heap sizes and exact heaps, so a lowering that allocates
  differently changes their expectations.

### Extend the proved subset

1. Add the branch to the front file of its route, as a new section with its own namespace:
   statements in `AcceptedStatements` (a new `Covered` case), expressions in `AcceptedExpressions`,
   calls in `AcceptedCalls`.
2. Close it from the compiler's own receipts and the existing family heads of `Internal/`. No
   expression or body execution law may be an input.
3. Carry it to a consumer of the real public API (`AcceptedPublicRoots`, the sessions), and update
   "Established proof connections" and "Remaining work" in the
   [design note](../design/core-runtime-unification.md), with the umbrella's module doc.

## Closures by value

The lowering mirrors the source rule of
[closures by value](source-semantics.md#closures-capture-by-value) allocation by allocation. Core's
syntax and semantics, the Hull importer and the contract runtime did not change.

**Lowering**, in `SourceCoreSourceCells` and `SourceCoreFunctions` of
[Frontend/SourceCore/Lowering](../../Solcore/Frontend/SourceCore/Lowering.lean). `copyScope` copies
the slots that `CaptureBinders.copiedBinder?` selects, then runs the body with each slot renamed to
its copy. A lambda copies at creation, when the policy's `snapshotLambda` holds, and again at each
call; a generalized declaration copies its scope once around its bundle (`letInitializedSnapshot`).
With the profile's allocator (`SourceCoreSourceCells.marked`) a copy is a marked source allocation.
It must be: the allocation ledger rejects a marker capture it does not record
(`SourceCoreAllocationLedger.Error.unknownCaptureLocation`).

**Proofs.** `CaptureCopies.copies_prefix` and `CaptureCopies.marked_copies_prefix` relate the Core
copies of a represented scope to the Source copies `Dynamic.EnvironmentCopies`. Formation
(`CallableIndexedLambdaValues.formation`), calls (`CallableIndexedLambdaViewPrefix.Entry`) and
generalized `let` (`CellAwareNamedGeneralizedPrefix.complete`) record or follow these copies, and
protected protocols are rebound to them (`ProtectedStateTransition.Rebinds`).

**Tests.** `Tests.SourceCoreExecution` in `Foundations/Execution` runs #120's programs, a repeated
call, a loop-carried capture, an adaptation of upstream's `control-flow-capture-identity` fixture
and upstream's `closure-parameters` fixture where it needs no contract storage or inline assembly.
Tests written for shared cells expect by-value results: in `Callable/Ancestry`, a closure that
reaches itself through a local assigned after its creation copies that local uninitialized, so its
recursive call faults.

## What remains

The [Core runtime unification design](../design/core-runtime-unification.md) records the remaining
work, under "Remaining work for the second goal". In short:

- `StaticProfile` recognizes a strict subset on purpose. The general proof comes from the actual
  named and contextual compiler receipts, not from widening a recognizer or from a body-execution
  law.
- `Covered` still excludes writes and matches under contextual metadata views, and statements after
  an always-returning prefix in a non-Unit function.
- The expression closure covers a first subset, direct calls at any expression position and the
  builtin conversions. Indirect calls, the other builtin calls, methods, indices, tuples,
  constructors, generalized reads, closures and coercions remain.
- The proof target is a successful selected compilation, not the whole workspace and not checker
  acceptance alone. Each extension ends in a consumer of the real public API.
- Row 4's memory arrays, slices and memrefs compile through the compatible profile and stay
  outside `StaticProfile` and the meaning proofs
  ([decision 6](../design/memory-arrays-slices.md#6-meaning-proofs)). Relating array objects to
  their Core cells, and slices and memrefs to their Core products, is a later unit.

## Pitfalls

- **Premises are the contract.** A theorem over a recognized profile says nothing about other
  compiler-accepted syntax. Do not make a recognizer look universal, and do not add an execution law
  as a premise.
- **Lockstep with the semantics.** Both sides call one copy decision,
  `CaptureBinders.copiedBinder?`, and `Foundations/SourceExecutionSize` restates every dynamic rule
  with a size.
- **The assignment profile is named only at Source types** (`WideAssignmentProfile`, with
  `AssignmentProfile` on the view). The receipts' copies of the compiler's operator check at a
  Core leaf (`operatorValid`, `operatorType`), where a fixed-width leaf is `word`, and Frontend's
  `checkedCompound_of_profile` spell it out.
- **Bare names depend on imports.** `Foundations/CoreEvaluation` and `Callable/ViewWrappers` stay
  below the Source [Context](../../Solcore/SourceSemantics/Context.lean): `Context` there is
  `Core.Context` through `open Core`. `Statements/GenericImperativeFor` and `TypedImperativeFor`
  keep their trees apart, or names of the same spelling would win over the opened `Scope` and
  `ValuesContext`.
- **`@[simp]` reach.** `Statements/LoopRenaming` stays below `Statements/LoopLayouts`, whose `simp`
  lemmas `rename_insert` and `rename_insert_lift` loop in its proofs at the `for` post edge.
- **Matchers.** Lean reuses an alpha-equal matcher within a file. `Callable/AncestryWorklists`
  stays apart from `Callable/Ancestry`, or the equations of `lists` would take their variable names
  from `spines`' matcher; `Owned/DecodedCallFaults` from `Owned/ChosenOrdinaryCalls`, or
  `CallableIndexedOwnedPublicDecodedStagedCallFaults.faults` would stop being a namespace.
- **Private names, notations and instances.** The paired seeds live in `Callable/MethodOrigins`,
  since `Callable/AncestryPaired`'s private `bind_ok` makes their references ambiguous.
  `Callable/CoercionSpine` stays below `SourceCoreCallablePrincipals`, whose private
  `BEq TypedBinder` breaks its derived instances. `RecursiveNamed/PublicDirectClosureApplications`
  and `PublicDirectApplications` share three local notations, so they stay apart.
- **Import order picks instances.** The first two imports of `Callable/MethodOrigins` decide which
  equal-priority `DecidableEq` and `LawfulBEq` instances its validators use (see its module doc).
- **Isolation probes.** `#check_failure` lines in the tests assert what a file's imports must not
  reach, such as `SourceCoreCompatibleValues.encode` from `Compatible/Payloads`.
- **Some files sit below the compiled route.** The source semantics' compiled route imports
  `Selected/CatalogOrigins`, `Selected/MethodBodies`, `RecursiveNamed/HeadersAndPrograms` and some
  files of `Callable/`, `Generalized/` and `RecursiveNamed/`. They must not import
  `CompiledBodies`, `Internal/Compiled`, `Internal/Prepared` or `Staging/Preservation`.

## Testing

The tests are by subject under
[Solcore/Test/SourceSemantics/CoreLowering](../../Solcore/Test/SourceSemantics/CoreLowering);
[Tests](tests.md) lists them and says how they run.

| Tests | Cover |
| --- | --- |
| [Foundations/Execution](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean), `Foundations/EntryPoints`, `Foundations/Snapshots` | The public API: compile, open a session, call, resume; closures by value, shifts, unchecked arithmetic |
| `Captured/`, `Callable/`, `Generalized/`, `Evidence/`, `Method/` | Closures and callables: captures, ancestry, indexed lambdas, generalized exports, evidence |
| `Compatible/`, `Data/`, `Mixed/`, `Named/`, `Recursive/`, `Chosen/`, `Closed/` | Profiles and families: places, assignments, matches, loops, named and recursive rows |
| [Selected/Profiles](../../Solcore/Test/SourceSemantics/CoreLowering/Selected/Profiles.lean), [Generalized/Export](../../Solcore/Test/SourceSemantics/CoreLowering/Generalized/Export.lean) | Instantiate the front's session and public-root theorems on fixtures |
| `UnifiedCorpus`, `UnifiedOperatorCorpus` | The unified runtime on canonical checked programs |
| `Accepted/Fixture`, `Accepted/OneCall` | A compiled program with its inventory, family rows and callees' receipts; the call root's theorems in both directions at a direct call, at a call whose argument is a call, at a conversion and at `Typedef.rep` of a conversion, and in reflection at dirty words |

```sh
lake build Solcore.SourceSemantics.CoreLowering
lake build Solcore.Test.SourceSemantics.CoreLowering.Foundations.Execution
```

Then run the checks of [Workflow](workflow.md#before-you-commit).
