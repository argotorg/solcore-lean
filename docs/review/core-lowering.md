# Source-to-Core correspondence: review guide

`Solcore/SourceSemantics/CoreLowering/` proves that generated Core code means what
its independent Source semantics says. The proof covers parts of the language.
The theorem for the complete compiler is unfinished; the
[Core runtime unification design](../design/core-runtime-unification.md) records
the state of that work.

Read this area from its [umbrella](../../Solcore/SourceSemantics/CoreLowering.lean)
and the front files below. Everything else is in `Internal/`.

A namespace names a section of a file, not a file. For example,
`CellAwareInvocationAcceptedFlow` is a section of
[AcceptedStatements](../../Solcore/SourceSemantics/CoreLowering/AcceptedStatements.lean).
Each section starts with the marker `-- leanmerge: from <module>`, so searching for
that marker or for the namespace finds it.

## Front

| File | Holds | Why it is in the front |
| --- | --- | --- |
| [AcceptedTrees](../../Solcore/SourceSemantics/CoreLowering/AcceptedTrees.lean) | The compiler's accepted trees and write receipts | The accepted-body theorems are stated over them; the design note names `AcceptedNamedBodyFlow.Tree` |
| [ActualBodyInvocation](../../Solcore/SourceSemantics/CoreLowering/ActualBodyInvocation.lean) | One body invocation: a named row or a materialized closure | The design note starts the general route from `ActualBodyInvocation.Index` |
| [AcceptedStatements](../../Solcore/SourceSemantics/CoreLowering/AcceptedStatements.lean) | The statement closure | Cited by the design note |
| [AcceptedExpressions](../../Solcore/SourceSemantics/CoreLowering/AcceptedExpressions.lean) | The first expression closure and the named-row entry | Cited by the design note |
| [AcceptedShapes](../../Solcore/SourceSemantics/CoreLowering/AcceptedShapes.lean) | A checkable Source shape, and staged traces lifted from Source | Cited by the design note |
| [AcceptedCalls](../../Solcore/SourceSemantics/CoreLowering/AcceptedCalls.lean) | Direct calls and the family closure | Cited by the design note |
| [AcceptedPublicRoots](../../Solcore/SourceSemantics/CoreLowering/AcceptedPublicRoots.lean) | Accepted bodies at the public root | Cited by the design note; the last theorems of this route |
| [CellAwarePublicRoots](../../Solcore/SourceSemantics/CoreLowering/CellAwarePublicRoots.lean) | The public root of each cell-aware family | Dependency roots; the accepted route uses the same unchanged root |
| [CellAwarePublicForward](../../Solcore/SourceSemantics/CoreLowering/CellAwarePublicForward.lean) | Public outcomes of each cell-aware family | Dependency roots |
| [PublicSupport](../../Solcore/SourceSemantics/CoreLowering/PublicSupport.lean) | `StaticProfile`, program support and session state | The session theorems are stated over them; the design note names `StaticProfile` |
| [PublicSessions](../../Solcore/SourceSemantics/CoreLowering/PublicSessions.lean) | From actual compilation to an issued session | Cited by the design note |
| [PublicSessionOutcomes](../../Solcore/SourceSemantics/CoreLowering/PublicSessionOutcomes.lean) | One session call, in both directions | Dependency roots |
| [PublicOutputs](../../Solcore/SourceSemantics/CoreLowering/PublicOutputs.lean) | Complete public values of closed staged bodies | Dependency roots with the largest closures in the area |

**How these were chosen.**
- `README.md`, "Proof status", claims the source-to-Core correspondence proved so far.
- The design note cites 30 modules of this area, and all of them are in the front.
- A query over the environment lists the theorems no other declaration of the area
  uses. There are 3,680, far too many to read. 148 modules hold one that depends on at
  least 5,000 constants, and most of those state a public result.
- 50 of those 148 modules are in the front, through the routes above. The rest are
  listed under [Other public results](#other-public-results) or are body-level steps
  that those results build on.

Merging is limited by the import graph. A group of modules can become one file only
if no import path leaves the group and comes back. Every front file meets this: the
31 accepted-body modules, for example, have no module of any other family between
them.

## Reading order

1. **What the compiler did.** `AcceptedNamedBodyFlow.Tree` in
   [AcceptedTrees](../../Solcore/SourceSemantics/CoreLowering/AcceptedTrees.lean) and
   `ActualBodyInvocation.Index` in
   [ActualBodyInvocation](../../Solcore/SourceSemantics/CoreLowering/ActualBodyInvocation.lean).
2. **The general route.** The `Accepted*` theorem files in the order of the table, then
   [AcceptedPublicRoots](../../Solcore/SourceSemantics/CoreLowering/AcceptedPublicRoots.lean).
3. **The public API.** [PublicSupport](../../Solcore/SourceSemantics/CoreLowering/PublicSupport.lean),
   [PublicSessions](../../Solcore/SourceSemantics/CoreLowering/PublicSessions.lean),
   [PublicSessionOutcomes](../../Solcore/SourceSemantics/CoreLowering/PublicSessionOutcomes.lean)
   and [PublicOutputs](../../Solcore/SourceSemantics/CoreLowering/PublicOutputs.lean).
4. **Finite families.** The two `CellAwarePublic*` files state the same results for
   bodies that a finite profile recognizes.

## Main theorems

Each theorem's premises matter: a connected profile does not imply coverage of all
compiler-accepted syntax. The design note lists what remains.

### The accepted-body route

| Theorem | Reading |
| --- | --- |
| `CellAwareInvocationAcceptedFlow.correct` | Induction over the accepted tree closes the mixed-cell statement flows. |
| `CellAwareInvocationAcceptedFlow.body_preserves`, `CellAwareInvocationAcceptedFlow.body_reflects` | A body means its Source execution in both directions, including failures, control transfers and the reached heap, given `Expressions`. |
| `CellAwareInvocationAcceptedExpressions.expressions` | `Closed` gives `Expressions` at every budget. |
| `CellAwareInvocationAcceptedExpressions.body_preserves`, `CellAwareInvocationAcceptedExpressions.body_reflects` | The body theorems without the `Expressions` premise, for the first subset. |
| `CellAwareInvocationAcceptedNamedHeaders.static_inputs` | An actual prepared header gives Core typing, fixed-control typing and the result projection. |
| `CellAwareInvocationAcceptedNamedInvocation.preserves_selected`, `CellAwareInvocationAcceptedNamedInvocation.reflects_selected` | The subset's body theorems run through the actual named entry and restore the caller. |
| `CellAwareInvocationAcceptedDirectCalls.preserves`, `CellAwareInvocationAcceptedDirectCalls.reflects` | The direct-call head, with the application of the selected closure as an input below the call's grade. |
| `CellAwareInvocationAcceptedNamedApplication.preserves`, `CellAwareInvocationAcceptedNamedApplication.reflects` | That input follows from the callee's own accepted body. |
| `CellAwareInvocationAcceptedCallFamily.preserves`, `CellAwareInvocationAcceptedCallFamily.reflects` | One strong induction on the grade closes a family of rows. |
| `CellAwarePublicAcceptedNamedRoot.checkpoint_has_sufficient_fuel_selected`, `CellAwarePublicAcceptedNamedRoot.checkpoint_reflects_selected` | A staged Source trace and the native completion of the actual public start imply each other. |
| `CellAwarePublicAcceptedNamedForward.first_value_selected` | A staged trace that returns a value reaches a successful public resumption, with the exported value and physical history. |
| `CellAwarePublicAcceptedCallRoot.preserves_root_selected` | The same preservation for a call-containing row. |

### Public sessions

| Theorem | Reading |
| --- | --- |
| `SelectedCompilationRawPublicReceipt.of_compile` | A public compilation keeps its exact artifact, checking budget and prepared recipe. |
| `SelectedCompilationRawPublicReceipt.Receipt.checker_bodies`, `SelectedCompilationRawPublicReceipt.Receipt.checker_profiled`, `SelectedCompilationRawPublicReceipt.Receipt.checker_initial_row` | That receipt gives body validity and the profiled session; `StaticProfile` stays a premise. |
| `SelectedCompilationCertifiedPublicSession.of_checked`, `SelectedCompilationCertifiedPublicSession.of_checked_profile` | A checked program issues a session. |
| `SelectedCompilationCertifiedPublicSession.Issued.forward_scalar`, `SelectedCompilationCertifiedPublicSession.Issued.forward_function` | Source success reaches the public result of a later call. |
| `SelectedCompilationCertifiedPublicSession.Issued.reflect_scalar_plain`, `SelectedCompilationCertifiedPublicSession.Profiled.reflect_failure_plain` | A public result reflects to independent Dynamic application at the same session state. |
| `SelectedCompilationStageClosedPublicForward.scalar`, `SelectedCompilationStageClosedInitialForward.scalar` | Ordinary Source success reaches public output, at later and first calls. |
| `SelectedCompilationStageClosedOutputForward.initial`, `SelectedCompilationStageClosedOutputForward.later` | The same for the complete public value, with its metadata and retained callable leaves. |
| `SelectedCompilationCertifiedPublicSession.Initial.forward_data_output_plain` | Initial calls accept structurally typed data inputs. |

### Cell-aware public roots

This table shows the `Named` family. `Lexical`, `Faulting` and `Imperative` state
theorems of the same kinds, and `Materialized` states the direction from Source.

| Theorem | Reading |
| --- | --- |
| `CellAwarePublicNamedRoot.preserves_root`, `CellAwarePublicNamedRoot.reflects_root` | The unchanged root relates a body to its native run. |
| `CellAwarePublicNamedRoot.checkpoint_has_sufficient_fuel`, `CellAwarePublicNamedRoot.checkpoint_reflects` | The same at the actual checkpoint. |
| `CellAwarePublicNamedForward.first_value`, `CellAwarePublicNamedContinuation.after_value` | A Source trace reaches public output at the first and later calls. |
| `CellAwarePublicNamedFailureForward.first_fault`, `CellAwarePublicNamedFailureContinuation.after_fault` | The same for faults. |
| `CellAwareCheckedPublicRetainedMaterializedForward.source_success` | A Source application reaches public success through a retained function handle. |

## Definitions the statements use

The definitions a theorem is stated over reach well beyond the front. The statements
of the front's theorems mention 334 other definitions directly, in 172 modules. With
the definitions those use, that is 732 declarations in 228 modules. These modules are
mostly proofs: in 169 of them, under a quarter of the declarations are this
vocabulary. They also sit at every depth of the import graph, so whole files cannot
form a front layer. They stay in `Internal/`, and this table lists the ones used most.

| Definition | Reading | Topic in `Internal/` |
| --- | --- | --- |
| `CallableIndexedOwnedFunctionValues.Header`, `CallableIndexedOwnedFunctionValues.Key`, `CallableIndexedOwnedFunctionValues.OwnedKey` | A catalog header, and the immutable key of a function value | `Owned/FunctionValuesAndState` |
| `CallableIndexedOwnedFunctionState.State` | The reached pool as a protected state witness | `Owned/FunctionValuesAndState` |
| `CallableIndexedOwnedPublicFaultReceivers.Receiver` | Metadata and a diagnostic table, without an execution result | `Compatible/PlaceDiagnostics` |
| `FunctionCalls.FaultRep` | How a failure is represented | `Foundations/FunctionCalls` |
| `RecursiveNamedCatalog.Header` | One row of the finite named-call inventory | `RecursiveNamed/CatalogAndSpecialization` |
| `RecursiveNamedPublicSpecializationMeaning.Prepared` | A prepared named row | `RecursiveNamed/CatalogAndSpecialization` |
| `RecursiveNamedPublicRootMeaning.RootSelection` | The stored root that a public start selects | `RecursiveNamed/PublicRoots` |
| `CallableIndexedParameterMeaning.Arguments` | How arguments are represented | `Callable/IndexedParameters` |
| `CompatiblePayload.FunctionModel` | How function values are represented in payloads | `Compatible/Payloads` |
| `GenericHeap.CellHeapRepresents` | The heap relation over whole cells | `Foundations/GenericHeaps` |
| `LambdaMetadataViews.MetadataView` | A Source view of runtime metadata | `Foundations/LambdaViewsAndMarkedCaptures` |
| `ProtectedStateTransition.Index` | The index of a protected state | `Protected/StateAllocation` |

## What `Internal/` holds

Each directory is one family of supporting proofs, merged by topic. Files name their
topic, and each opens with a module doc.

| Directory | Holds |
| --- | --- |
| `Foundations/` | Heaps, Core evaluation and sizes, function values, basic expressions and statements |
| `Data/` | Payloads, places, patterns, mappings and equality on Core data |
| `Compatible/` | Lowering of the source-compatible profile: expressions, places, matches, mappings, statements |
| `Statements/` | Statement, loop and match meaning on the `Typed` and `Generic` carriers, named and builtin calls |
| `Protected/` | Contracts that carry an actual state witness through expressions, statements and loops |
| `Diagnostics/` | Emitted diagnostic plans and reached fault paths |
| `Callable/` | Callable ancestry, coercions, lambda views, prepared methods and indexed callable carriers |
| `Owned/` | Function values with immutable keys and reached pools |
| `OwnedAdmitted/` | Graded interfaces of the supported recursive staged profile |
| `OwnedPrepared/` | Receipts read from actual cached preparation |
| `OwnedStaged/` | Staged bounds of bodies, closures, methods and calls |
| `RecursiveNamed/` | The finite named-call catalog, and its public results |
| `Generalized/` | Generalized local functions: instances, materialization and reads |
| `Accepted/` | Accepted expressions, program completion and body invocations |
| `CellAware/` | Bodies over heaps that mix value cells and function descriptors |
| `Selected/` | Selected compilations: admission, calls, public steps and lifting to staged Source |

### Other public results

These are correspondence theorems too, for particular families of bodies. They stay
in `Internal/` to keep the front short, and a review of one of these families should
start here.

| Results | Topic in `Internal/` |
| --- | --- |
| `RecursiveNamedPublicHistoryFrontdoor.public_run_succeeded_collects` and the other `public_run_*` and `public_invoke_*` theorems | `RecursiveNamed/Public*` |
| `CallableIndexedOwnedPreparedStagedInitializedPublicBounds.public_run_succeeded_reflects` and the other staged public bounds | `OwnedStaged/InitializedPublicBounds` |
| `CertifiedPublicSession` and its outcomes, over recursive named rows | `Selected/CertifiedPublicSessions` |

### Words

The names are systematic. These words recur.

| Word | Meaning |
| --- | --- |
| preserves, reflects | Source to Core, and Core back to Source |
| bounds | A graded preservation and reflection contract |
| receipt, certificate | Static evidence kept from the compiler; it holds no execution law |
| meaning | A theorem that closes preservation and reflection for a form |
| selected compilation | The requested roots, their dependencies and the callable instances actually compiled |
| staged | The recursive staged Source semantics, `Staging.Recursive` |
| lifting, inversion | Turning an ordinary Source trace into a staged one; reading a derivation back |
| compatible | The source-compatible native profile, with authenticated metadata in Core data |
| typed, generic | Statement meaning on the typed carrier, and on the carrier generic in its payload model |
| protected | A contract that passes an actual state witness from child to child |
| indexed | Callable carriers in a fixed table, with ghost ancestry kept apart |
| owned | Function values with immutable keys; live authority stays in a reached pool |
| admitted | Graded interfaces of the supported recursive staged profile |
| prepared | Read from actual cached preparation |
| physical, canonical | The physical cache layer; canonical callers also keep every global reference |
| terminal, discard, mixed, finite | Body shapes: one terminal statement, discards before it, any of those, a fixed finite family |
| cell-aware | Over heaps that mix value cells and generalized function descriptors |
| generalized local | A local function with its own type parameters |
| materialized | A generalized local function instantiated at a read |
