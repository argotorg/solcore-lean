# Core runtime unification and semantic preservation

Status: The first goal (runtime unification on Core) is complete. Implementation and proofs for the second goal (preserving meaning across the full compilation pipeline) are ongoing.

Created: 2026-09-30. Updated: 2026-10-09.

## Current Implementation Status

| Item | Status |
| --- | --- |
| Removal of direct runtime evaluation | Completed in `a3168382` (2026-10-01). The public SourceCompiler uses a shared Core artifact, Value, Session, and Checkpoint. |
| Preservation of meaning across the full compilation pipeline | Ongoing. The estimate based on work completed is about 70%. The final theorem connecting general function values, call bodies, and all passes to the public entry point is incomplete. |
| Latest implementation commit | `783a716f`. The accepted fixture now retains one actual public Recipe preparation and bootstrap completion, then constructs the named parameter Receipt at that same completed store. The original hook installation and parameter producer retain their actual state and ContinuationAgreement. |
| Latest verification of all registered modules | Verified on 2026-10-09 at `783a716f`: registered Solcore and Tests.Main build (5603 jobs), strict audit of 15836 cumulative declarations, all 152 declarations of four added modules, and 45 signatures. Complete private types and axiom arrays match literally. Authentic censuses show 152 additions, no prior overlap and no removals, including one helper whose actual module owner was independently checked. Source/object and protected-file guards pass. One positive public bootstrap check succeeds at fuel 10000 with a two-cell initialized store; full registered executions remain those at `3ff3daf4`. |
| Working implementation | Apply the existing body correspondence ports at the actual public parameter Receipt. The complete public Session association, stronger ReachedExit interfaces, measured mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and final theorem remain incomplete. |
| Next phase | Unify the comptime evaluator on Core and connect new source contract/storage/external-call support to ContractRuntime. |

Anyone resuming implementation should first read the current status and the handoff at the end of the [implementation record](core-runtime-unification-progress.md). Public API users should consult the [API migration record](core-runtime-unification-api.md); see the [T0 audit](core-runtime-unification-audit.md) for the initial compatibility and semantics investigation.

Design approach: Combine a small number of Core extensions with helper libraries implemented using ordinary Core data types and functions.

Reading order:

- Review the approach: Sections 1 and 3
- Implement Core: Sections 4 and 5
- Develop proofs: Sections 6 and 7
- Choose a task to resume: The implementation status above and Sections 8, 9, and 12
- Assess completion: Sections 10 and 11

## 1. Goals and Agreements

This design has two goals, in priority order.

1. **Remove direct runtime evaluation of typed-source and unify the runtime backend on Core.**
2. **Prove that compilation from typed source to Core preserves the meaning of execution relative to an independent `SourceSemantics`.**

Typed source remains as an intermediate representation in the compiler. The runtime evaluator is what is removed.
Core safety proofs alone do not establish compilation correctness, so the second goal is treated as a separate deliverable.

### 1.1 Conditions Confirmed with the User

| Item | Decision |
| --- | --- |
| Functional compatibility | Preserve every feature executable through typed-source at the start of migration through Core before removing the old evaluator. |
| Strength of the proof | Prove correspondence of execution results and state changes with independent `SourceSemantics`, in addition to type preservation. |
| New contract integration | Defer new connections for source contract methods, persistent storage, and external calls to the next phase. |
| comptime | This phase removes direct runtime evaluation. Unifying the existing direct comptime evaluator on Core is deferred to the next phase. |
| Termination | Successful termination of all programs is not a requirement. Allow general recursion and use execution with finite fuel. |
| Core size | Do not add Core types or instructions for each source feature. Prefer representations using existing features and helper libraries; decide additions by recording comparisons and reasons. |

If these conditions change, consult the user rather than reducing the feature scope solely at the implementer's discretion.
The specific module names and internal data structures below are design recommendations, distinct from the agreements above.

### 1.2 Scope of This Phase

- Preserve the current closed roots, finite specialization plans, and currently supported range of trait evidence.
- Preserve the behavior of existing Core, Core Wire, HostRunner, and ContractRuntime.
- Changes to existing ContractRuntime required by Core syntax or state changes are in scope.
- Designing acceptance, ABI, or storage layout for new source contracts is out of scope.
- Compilation of every type-checked program, unlimited specialization, and new open dictionary support are not required.
- Exact equality of source and Core fuel counts, heap indices, internal cell counts, or diagnostic strings is not required.
- Preserve existing computational results, shared state, evaluation order, and language failures. Track compatible diagnostic categories and source locations in the migration table as well.

### 1.3 How to Pursue the Two Goals

Completing every proof for the second goal is not a prerequisite for completing the first goal.
However, design the representation relations and main theorem first, and develop Core extensions, compilation, and basic lemmas in parallel.
The complete proof can still be finished against `SourceSemantics` after the old runtime evaluator is removed.

Use agreement tests with the old evaluator for checks during migration. Do not use the old evaluator as the definition of semantics or as a permanent proof assumption.

### 1.4 Record of the Initial Implementation and Audit (2026-09-30)

This section preserves the initial results and the scope that was incomplete at that time. Do not read "current" or "incomplete" below as the latest status. See the opening status and the [implementation record](core-runtime-unification-progress.md) for subsequent implementation, completion of the first goal, and the latest proof boundaries.

As of 2026-09-30, the [T0 audit material](core-runtime-unification-audit.md) contains migration tables for expressions, statements, values, evaluation order, failures, public inputs, and comptime.
Reachable missing-default examples, migration destinations for all features, and failure regression checks still needed confirmation; creating this list alone did not complete T0 or the first goal.

Positive missing-default fault rules were added for expression indexing, reads during place resolution, and latest-root updates after the RHS.
They make the successful prefix and its heap explicit, and prove that pure path failure is exclusive with successful execution of the same read / update.
This change does not cover other rules for invalid shapes, type mismatches, or similar conditions, or failure coverage and determinism for all source executions.

The [StagedValue correspondence proof](../../Solcore/SourceSemantics/CoreLowering/StagedValue.lean) is implemented.
For the existing `SourceStagedValue.toCoreExpr`, it proves structural correspondence with independent source values, typing on both sides, successful Core checking, preservation and reflection of evaluation, store invariance, and the connection to execution with fuel.
This proves **embedding a staged value that has already been obtained**. It does not yet prove that the pre-evaluator computed that value correctly, lowering of all typed source expressions, shared heaps, or preservation of the meaning of recursion.

The [Literals correspondence proof](../../Solcore/SourceSemantics/CoreLowering/Literals.lean) also connects to lowering actual source expressions.
Its scope is finite trees recursively combining unit, Bool, in-range Word, and two-element products, with explicit uniqueness of occurrences, exact type information, and empty requirements / coercions.
Using an internal wrapper for the existing lowerer and the existing `Resolved.Expr.lower?`, it proves successful lowering with a sufficient compilation budget, successful Core checking, correspondence of finite successful results in both directions with independent `Dynamic.ExpressionEvaluates`, and heap/store invariance on both sides.
Sufficient execution fuel is derived from finite source evaluation and distinguished from the traversal budget for compilation. General expressions, failures, staging, and correctness of whole-function compilation are outside this proof's scope.

The full build, all tests, and kernel policy checks passed with both proof files included. These results are distinct from completion of T3 and T6, and can be used by later source expression / comptime proofs.

The pure Core machine's `StateHasType` now uses the world-dependent `RuntimeStoreHasTypes`.
`BoundedSafety` handles world extension for execution steps and finite step sequences, typing of suspended states, and runtime typing of completed values.
Type preservation for finite evaluation also moved to the same store relation, and cell payload restrictions were removed from checker and frame typing. Constructor payloads admit general well-formed types.
The unconditional normalization proof for all Core was removed, and APIs deriving completion and sufficient fuel now require actual finite `Evaluates` evidence.
The old `StoreHasTypes` remains in limited theorems requiring first-order inputs or literal equality of final stores.

[CoreGeneralCells](../../Solcore/Test/CoreGeneralCells.lean) proves infinite execution of a self-referential closure accepted by the checker, with typed suspension and resumption for all fuel.
[CoreRecursiveCells](../../Solcore/Test/CoreRecursiveCells.lean) also validates handwritten Core examples of terminating self-recursion, mutual recursion, function arguments, and shared captures. It checks exact step counts, final values, references and stores, type preservation, suspension, and resumption.
These examples initialize cells with placeholder functions, so handling of uninitialized reads was supplied by later implementation.
The added [OptionalCell](../../Solcore/Core/OptionalCell.lean) stores any well-formed Core payload type in `sum unit T`, allowing allocation without constructing a placeholder payload.
[LanguageResult](../../Solcore/Core/LanguageResult.lean) represents success and language failure with ordinary `sum Word T`, and proves typing, short-circuiting bind, and safe observation and decoding of finite runs.
The [ContractRuntime adapter](../../Solcore/ContractRuntime/CoreLanguageResult.lean) passes successful payloads to the existing entry codec and connects language failures to frame traps and top-level rollback. Fuel exhaustion is not terminal.
The new [local-read lowerer](../../Solcore/Frontend/SourceCoreLocalCell.lean) and [LocalCell correspondence proof](../../Solcore/SourceSemantics/CoreLowering/LocalCell.lean) cover initialized reads and uninitialized failures for ordinary unit/bool/word/product values.
They prove successful actual compilation, independent source outcomes, structural correspondence of both heaps, completion with sufficient fuel, and reflection of values and stores for every completed Core run.
[SourceCoreBasic](../../Solcore/Frontend/SourceCoreBasic.lean) composes these reads into ordinary monomorphic let, `=` to a bare local, expression statements, explicit return, and trailing expressions.
The type scope remains unit/bool/word/product; it does not yet handle evidence for functions, blocks, loops, mappings, or Integer literals.
[HeapMutation](../../Solcore/SourceSemantics/CoreLowering/HeapMutation.lean) proves correspondence of allocation, writes, and lexical environments. [BasicExpressions](../../Solcore/SourceSemantics/CoreLowering/BasicExpressions.lean) derives correspondence of actual compilation, typing, independent source success and uninitialized failure, and finite Core execution from structural expression proofs.
[BasicStatements](../../Solcore/SourceSemantics/CoreLowering/BasicStatements.lean) contains lemmas composing statement sequences and full correspondence for the uninitialized failure of `let x:T; return x;`. A successful `let Bool; = true; return` example was also validated using actual compilation output.
For general statement sequences, the proof assumes correspondence proofs for child expressions and continuations, and evaluation in the actual environment containing inserted temporary Core binders. It does not prove preservation of meaning for every accepted statement sequence.
At that time, `SourceCoreControl` added conditional expressions, if/block, scope restoration, and early return; `SourceCoreBasicEntry` added typed startup and resumption. The public compiler tries this route after the old direct Core route.
The ordinary-read reason/site table preserves expression IDs, binders, and spans, and reconstructs diagnostics from language failures. Expression proofs from actual compilation, extraction of Core typing for statement sequences, and preservation of meaning for whole sequences from a static statement-sequence Tree without external child-evaluation assumptions were also added.
This still excludes semantic correspondence for the origin and input/output layout of actual entries, whole if/block constructs, the full source failure table, captures, and recursion.
It does not settle the recursion approach for all source programs or complete T1. Details and integrated verification are recorded in the [implementation record](core-runtime-unification-progress.md).

## 2. Current State and Reasons for the Change

### 2.1 Current Path for Unification on Core

The public `SourceCompiler` re-exports `SourceCoreExecution`. `SourceCoreCompiler` and `SourceCoreUnifiedCompilation` validate plans and prepare Core code, then create bootstrap, session, and checkpoint from a shared artifact. Root execution and calls to returned functions use cached Core bodies and `Core.runStateful`. Backend preference, automatic fallback, and choosing between `runCore` / `runTyped` have been removed.

Typed source remains as an IR for preparation, compilation, and authentication. `SourceRuntimeValues` and similar modules retain the `SourceTypedRuntime` namespace as a value, observation, and validation carrier, rather than a runtime evaluator for expressions, statements, or calls. Existing direct comptime evaluation remains in the preparation phase.

The existing pure `SourceProgramExecution → SourceCoreDirectLinking` path remains as a focused adapter that generates Core. Its cell allocation differs from the public unified path, so distinguish where proofs apply (Section 6.6.1).

### 2.2 Implemented Representations and Remaining Proofs

- General cells, constructor payloads, world-dependent store typing, finite safety, suspension, and resumption are implemented.
- Uninitialized cells use the `OptionalCell` sum; language failures use the `LanguageResult` sum. Public diagnostics and the existing ContractRuntime trap/rollback adapter are connected.
- Recursion and mutual recursion use existing closure / apply and optional function cells. No new Core function definition table was added.
- Arbitrary-precision Integer was added as a Core scalar with operations. Mappings and proxies use ordinary Core data and helper functions.
- Execution of return, break, continue, while/for, non-tail statements, match, local instantiation, selected methods/coercions, and helpers has migrated to Core.

Registered regression checks confirmed functional compatibility for the first goal. Do not infer preservation of meaning for all source programs from these implementations or Core type safety. Actual provenance of function values, all captured environments, dynamic AuthorityPool and general bodies, composition of all passes, and the final main theorem from public inputs remain for the second goal.

### 2.3 Limits of the Current Proof Assets

Reuse Core proofs of type preservation, progress, and correspondence between execution and declarative evaluation.
The successful Core checker evidence returned by the current lowerer establishes typing of generated code, rather than preservation of source meaning.

`SourceSemantics` has values, heaps, and execution relations independent of the evaluator.
It also has type preservation proofs for successful finite execution, so use it as the reference for compilation proofs.
However, some bridging theorems from the source checker to declarative semantics still have explicit assumptions.
This document does not assume that correctness from raw source through execution has already been proved.

## 3. Target Architecture

```text
CheckedProgram / TypedSource
    |
    | SourceCompilationPlan / SourceSpecializationWorklist
    | Validate root, staging, evidence, and reachability; required existing comptime calculations
    v
SourceCompiler / SourceCoreExecution
    |
    | SourceCoreCompiler / SourceCoreUnifiedCompilation
    | Compile types, functions, local instantiations, control, and state to Core; run checker
    v
Shared Artifact + source locations, public types, and authentication catalogs
    |
    | Validate public inputs and prefix; Bootstrap / Session
    | cached Core body / Core.runStateful
    v
Successful completion / language failure / typed Checkpoint
```

ContractRuntime uses the host-aware execution form of the same Core. New connections for source contract methods, persistent storage, and external calls belong to the next phase.

### 3.1 Conditions on the Execution Path

- Core execution does not refer to the `TypedSource` node table.
- Core execution does not call the type inferencer, trait solver, or specialization worklist.
- Core closure bodies are Core code.
- Core instructions do not call the old typed-source evaluator.
- Diagnostic source correspondence tables are separate from executable code.
- Moving specialization or validation to another module must not leave a runtime interpreter there.

The existing pure Core machine and host-aware machine may remain as execution forms of the same Core language.
What is prohibited here is retaining a separate backend that evaluates source syntax.

### 3.2 Separating Compilation Work

The following work has been separated from the runtime evaluator into `SourceCompilationPlan`, `SourceSpecializationWorklist`, and the Core preparation layer.

- Canonical revalidation of specialization plans
- Collection of selected operator/coercion methods and their helper frontier
- Collection of first-class function references and concrete uses of locally polymorphic functions
- Validation of stage conditions and evidence
- Determination of public roots and signatures

Compilation plans retain functions, types, required methods, local instantiations, and source correspondence.
Their success conditions include "every call or reference destination exists."
Agreement with rerunning the plan does not replace a proof that it covers all semantically reachable targets.

### 3.3 Boundary Between the Core Kernel and Helper Libraries

The Core specification contains typed functions and application, a mechanism for recursion, general cells, products, sums, nominal data, scalar operations, general failure results, and the existing host boundary.
The default approach is to compile source-specific behavior into Core code written with these features.

| Feature | Default placement |
| --- | --- |
| Recursion and mutual recursion | The adopted closure / apply and optional function cells (Section 4.1). |
| Mutable captures | General typed cells and existing closure / apply. |
| Uninitialized variables | Represent initialization state with a sum and check it with ordinary branching. |
| mapping dictionaries | Entry sequences and Core helper functions for lookup, update, key comparison, and defaults for each type. |
| proxy | Tags in ordinary data types. Do not add dedicated type-reflection instructions. |
| loop, return, break, continue | Compilation using recursive functions and sums. Do not add dedicated source-statement instructions. |
| trait, evidence, local polymorphism | Compile-time instantiation and compilation to Core functions and records. |
| Integer | The adopted arbitrary-precision Core scalar and operations. See Section 4.4.1 for the comparison and reasons for adoption. |
| Diagnostics | Retain source locations and source-specific failure categories in correspondence tables. |

Helper libraries are ordinary Core code checked by the Core checker.
They do not directly evaluate mappings or similar features with special host functions or interpret the source IR.
Their execution uses the same evaluator, typing, and fuel rules as other code.

### 3.4 Criteria for Adding Core Features

Before adding a new Core type, value, instruction, or special evaluation rule, compare and record the following.

1. A representation using existing functions, sums, data, cells, and helper libraries.
2. An addition as a Core primitive.
3. The scope of changes to the specification, checker, type safety, host, and Wire for both options.
4. The impact of both options on compilation, helper libraries, preservation-of-meaning proofs, and generated code size.
5. Measurements of representative examples if performance is a reason for the decision. Do not rely on unmeasured speedups.

The goal is not merely to minimize the number of Core syntax forms.
Assess the combined burden of Core safety proofs and correctness proofs for libraries and compilation.
A primitive may be chosen for a feature such as Integer if a data-structure representation would require extensive arithmetic implementation and proofs.
Do not add dedicated mapping or proxy types or instructions by default; if that changes, retain the comparison and reasons for adoption described above.

Based on the T0 candidates and T1/T3 implementation and proofs, recursion uses existing mechanisms and Integer uses a scalar extension. Public API and Wire compatibility were validated. Record the same comparison if further additions become necessary.

## 4. Core Representation and Execution

### 4.1 Representation of Recursion (Adopted)

Decision on 2026-10-01: **Use existing closure / apply and optional function cells.** Source compiler regressions passed for self-recursion, mutual recursion, higher-order arguments, returned lambdas, and shared mutable captures, maintaining execution and checkpoint type safety without adding a Core function definition table.

1. Allocate optional function cells for all globals first.
2. Compile each body to Core code and create closures capturing shared global references and required cells.
3. Store the closures in their cells and call them with existing `apply`.
4. Treat calls and iterations of generated loops as ordinary machine transitions that consume fuel.

Represent uninitialized values with sums and propagate read failures through explicit language results. Do not construct placeholder function payloads. Tie suspended states to the same generated code and store. Source self-cell recursion uses the same closure / cell combination.

The initial proposal for `FunctionId`, signatures, a function definition table, and dedicated calls was considered for comparison and was not adopted. No other recursion instructions such as `fix` / `letrec` were added. Runtime body inlining is not required.

Type safety of generated code is implemented, but preservation of meaning connecting arbitrary captures, caller/lexical history, catalog permissions during calls, and all source bodies remains ongoing under the second goal.

### 4.2 General Cells and Cyclic References

Remove the `CellPayload` restriction and handle storability through Core type well-formedness and world-dependent value typing.
Align the constraints on nominal constructor payloads as well.
This checker admission, finite safety, uninitialized-value compilation, and source-recursion compilation are implemented. Semantic correspondence with arbitrary Source heaps and capture history remains ongoing under the second goal.

The central type-safety structure has the following form (definition names are pseudonotation).

```text
D                       Core data definitions
Σ                       Declared type of each cell
ValueTyped D Σ v T      Value type under data definitions D and cell types Σ
StoreTyped D Σ H        Each cell value has a type under the same D and Σ
StateTyped D Σ state R  Type of execution state, including continuations
```

Typing a cell reference `loc` only checks `Σ[loc] = T`.
Closure typing does not recursively reread heap contents.
Typing every heap cell separately under the same `Σ` handles closure → cell → closure cycles.

The required basic lemmas are type-world extension, allocation, read, write, environment extension, and type preservation for closure creation and application.
Type preservation alone does not require introducing a step-indexed definition that traverses the whole heap.
If semantic correspondence between higher-order source and Core values requires another technique, introduce it in that proof layer.

### 4.3 Uninitialized Cells

The adopted `OptionalCell` represents a mutable source cell `T` as Core `cell (sum unit lower(T))`.

- `inLeft unit`: Uninitialized
- `inRight value`: Initialized
- Reads branch and produce the prescribed failure if the cell is uninitialized.

This lets the Core store itself retain a structure in which every cell always contains a value.
Preserve the current treatment of an uninitialized mapping as an empty mapping, distinguishing it from ordinary uninitialized reads.

The proposal to change Core store values to `Option Value` was not adopted. If this representation changes in the future, update the comparison in Section 3.4 together with heap correspondence and public input validation.

### 4.4 Data Types, Integer, mapping Dictionaries, and proxy

In this document, `mapping` refers to the source language's dictionary type `mapping(K => V)`.
For example, in `let table: mapping(Word => Word); table[7] = 42;`, it is the type of `table`.
It does not mean a correspondence from source to Core or a connection to persistent contract storage.

| Feature | Adopted implementation | Conditions to preserve |
| --- | --- | --- |
| nominal data | Associate instantiations of closed source types with Core data type IDs. Allow general well-formed payloads. | Constructor identity, payload order and types, and pattern-matching order. |
| Integer | Added an arbitrary-precision Core scalar and operations. See Section 4.4.1 for the comparison and reasons for adoption. | Arbitrary-precision operations, signs, comparisons, bitwise operations, and Word conversions. |
| mapping dictionaries | Represent entry sequences for each concrete key and value type with existing data types, and generate lookup, update, and similar operations as ordinary Core functions. Do not default to a dedicated `Core.Ty.mapping` or mapping instructions. | Key comparison, insertion and replacement order, defaults, nested updates, and the distinction between copying and sharing. |
| proxy | Represent with ordinary nominal data. The public compatibility path retains authenticated raw metadata IDs in Word payloads. Core does not interpret source `Ty`. | Type identity and behavior as mapping keys. |

The mapping helper library implements entry sequences, lookup, and update for each concrete `K` and `V` as ordinary Core code. Its basic structure is shown below. This is design pseudonotation, rather than a proposal to add polymorphic types to Core.

```text
EntryList_KV = Nil | Cons(lower(K), lower(V), EntryList_KV)
keyEqual_K   : lower(K) × lower(K) → Bool
lookup_KV    : EntryList_KV × lower(K) → sum unit lower(V)
insert_KV    : EntryList_KV × lower(K) × lower(V) → EntryList_KV
default_V    : unit → sum unit lower(V)
```

Entry sequences use existing nominal data and recursive data definitions.
Lookup misses and absent defaults return explicit values; compilation of source index operations handles applying defaults or producing the prescribed failure.
Insert preserves current insertion order and replacement rules. Nested updates reconstruct the required outer values and ultimately write back to the original local cell.
These bodies are entirely Core code, rather than wrappers calling old runtime operations.

Do not optimize all proxies away to unit until unchanged observable behavior has been proved.
Even when source types lower to the same Core representation, do not merge types distinguished by proxy comparison into the same tag.
Changing mapping values to independent reference objects could change assignment and copy semantics, so do not do this in the initial implementation.

Do not assume general mathematical map laws unconditionally for key comparison.
The original `valueEqual` does not consider ordinary closures or mapping values equal to one another; for global functions it compares specialization keys and evidence.
Prove correspondence between the old comparison and Core operations for each supported key type. The compatibility carrier retains authenticated IDs for raw type metadata and function provenance/evidence to reconstruct comparison and defaults. These IDs are not a general Core function-equality instruction.
Generate this comparison from the type-specific `keyEqual_K`. Retain provenance and evidence identity needed for function-key comparison as ordinary data in the value representation.
Do not choose a function representation that loses this identity or solve the problem by adding a general Core function-equality instruction.
Do not replace this with generic Core value equality or assume reflexivity or `lookup(insert(k,v),k)=v` for all keys without checking the specification.

Mapping lookup and update consume multiple Core steps by executing helper functions. Their fuel counts do not match the old runtime.
Integer is a primitive, but an operation taking one Core step does not necessarily have constant computational cost.
Fuel in this phase is an evaluator transition budget, rather than EVM gas or an upper bound on total computation.

### 4.4.1 Comparison and Adoption of Integer Representations (2026-10-01)

Integer has been added as an arbitrary-precision Core scalar. Mappings and proxies use ordinary data and functions.

| Option | Scope of changes and proof burden |
| --- | --- |
| Sign and Word limb sequences in ordinary Core | Can be represented without changing existing kernel, host, or Wire syntax. However, normalization, carry/borrow, multiplication, Euclidean div/mod, signed bitwise operations, and Word conversions must be implemented anew, and agreement with the original Int operations must be proved for sequences of arbitrary length. |
| native Integer | Add Ty/Value/literal and operations, and update exhaustive branches in the checker, CEK, evaluation correspondence, type safety, renaming, host transitions, and Wire. Use existing Lean Int operations and prove agreement with independent source primitives for each operation. |

Reading the existing code suggested that the native option would change about 25–35 production/proof modules, including about 8–10 Wire modules. This was an estimate before implementation, rather than a measured diff size. File counts, generated code size, and speed for the limb option were not measured.

The reason for adoption is to avoid reimplementing and proving an arbitrary-precision arithmetic library while limiting the added Core specification to one scalar and its operations. Speed is not a basis for the decision. Keep host storage and external-call ABIs based on Word, with explicit conversions as needed. Do not add a dedicated source interpreter, mapping primitive, or proxy primitive.

Preserve current source semantics. Both div and mod return 0 on division by zero; nonzero cases use Lean Int Euclidean operations. Bitwise operations follow the current rules, including combinations of positive and negative operands; Integer→Word is modulo 2^256. Preserve old Wire tags and decoding, and extend representation of new syntax through new explicit tags and budget accounting. Projection to the old format returns unrepresentable instead of silently discarding Integer.

### 4.5 Locally Polymorphic Functions

In the currently supported scope, quantified local binders are limited to lets initialized directly by lambdas, and assignment to such binders is rejected.
Use this constraint and collection of use sites by the existing worklist to keep Core monomorphic by default.

- Determine concrete code from the outer specialization, lambda location, accumulated type substitution, and handling of required evidence.
- Generate code for each reachable usage type.
- Instantiations belonging to the same activation share the same captured cells.
- Do not re-execute initializer expressions or duplicate captured values or heaps.
- Local cells allocated for each function call are fresh and specific to that call.
- Do not assume the source cell of a generalized descriptor corresponds to a single Core cell.

Validate and prove that the catalog of local instantiations covers every use site.
If this catalog is incomplete, fix compilation rather than adding fallback to the source evaluator.

### 4.6 Trait Evidence, Operators, and Coercion

Compile selected implementation methods to Core functions.
Where the required implementation differs by call, pass dictionary arguments using Core function values or typed records.
Statically fixed cases can use direct function references.

Do not interpret source predicates, requirement IDs, or the trait solver during Core execution.
Retain them as compile-time validation evidence and source correspondence information.

Check the following reachability in particular.

- Helpers called by selected methods
- First-class function references first discovered inside methods
- Evidence captured by function values
- Evidence specific to each use site of locally polymorphic functions
- Coercion order and coercion of the full argument list for indirect calls

### 4.7 Statements, Control, and Evaluation Order

Conceptually, statement compilation returns a typed control result distinguishing `fallthrough`, `returned R`, `break`, and `continue`.
The implementation uses existing Core sums and generated recursive functions.

- A statement sequence executes the next statement only on fallthrough.
- Return does not execute the rest of the statement sequence.
- While returns to condition evaluation on continue.
- For executes the post part after continue, then returns to the condition.
- Break is consumed by the innermost loop.
- Scope exit removes local names but retains cells reachable from closures.
- Preserve handling of values from trailing expressions and the presence or absence of semicolons.
- Short-circuit operations and conditional branches do not execute side effects of unselected expressions.

Fix the evaluation order of function values, arguments, assignment-target indices, right-hand sides, and coercions in a table based on `SourceSemantics` and existing behavior.
Do not introduce changes such as evaluating the same index expression twice in compound assignment.

After resolving the target and indices, compound assignment retains the **leaf value from before RHS evaluation** as the operation's left operand.
The final structural write uses the **latest root value after RHS evaluation**, preserving changes that the RHS made to other fields or mapping entries.
The current `ResolvedPlace.selected` retains the former. Do not reread the leaf from the new root as the left operand or write back the entire old root.
Typing, compilation, and proofs handle the state at target resolution separately from the state after the RHS.

## 5. Execution Results, Fuel, and Public Inputs

### 5.1 Result Categories

| Category | Treatment |
| --- | --- |
| Successful completion | Return a value and final store. |
| Language failure | Return the failure category and state up to that point. |
| Fuel exhaustion | Retain a well-typed intermediate state that can be resumed. |
| Internal error | Invalid instructions, type inconsistencies, and similar conditions. Prove that these do not arise from checked code and valid inputs. |
| Public input rejection | A boundary error before execution, distinct from language failure during execution. |
| Insufficient compilation budget | A compilation error in plan creation, staged evaluation, or similar work, distinct from runtime fuel exhaustion. |

The adopted representation is an explicit language-failure result using existing Core `sum Word T`.
`inLeft reason` is failure, `inRight value` is success, and `LanguageResult.bind` propagates failure and suppresses subsequent processing.
Expression, function, and statement-sequence lowering interprets and composes these results. It must not use ordinary `letE` alone to continue processing after failure.
Do not confuse this with existing `MachineFault`. Core syntax, machines, and runner result types have not changed.
Restore source locations from correspondence tables without introducing a source-syntax dependency into Core.

The host-aware runner and HostDriver retain the carrier as an ordinary completed value, and the `ContractRuntime.CoreLanguageResult` adapter interprets the outer sum.
Connect failure to the existing frame's trapped outcome and TopLevelExecution rollback; do not treat it as success or pending resumption.
On success, pass only the envelope payload to the existing entry codec. Preserve entry-outcome conventions based on return values.
Do not route it to current unreachable internal-fault branches. On fuel exhaustion, retain the typed state/context without finalizing.
The reason is a Word argument to helpers; the actual compilation fault/site table and public `diagnostic` / `handleDiagnostic` reconstruct the source category and location. Preservation and reflection of all independent Source failures remain for the second goal.

Even typed source can encounter uninitialized reads and similar failures.
It is therefore not claimed that every input produces only successful completion or fuel exhaustion.

### 5.2 Termination Guarantees

Completion and sufficient-fuel APIs such as `checked_runStateful_has_sufficient_fuel` now require actual finite `Evaluates` evidence. The unconditional normalization proof for general Core has been removed. Returning a result with finite fuel and successfully terminating are treated as separate guarantees.

The guarantees retained for general Core are as follows.

- The execution function returns a result for finite fuel.
- Types are preserved at each step.
- Correct code and state do not produce internal errors.
- Fuel-exhausted states are also typed.
- Additional fuel for the same suspended state corresponds to execution with the total fuel.
- Given a terminating semantic execution, finite fuel exists that realizes it.

Do not introduce unbounded recursion that consumes no fuel in Core helpers or implementations of calls and loops.
Do not change ContractRuntime to commit fuel exhaustion as a successful transaction.

### 5.3 Public Inputs and API

The public `SourceCompiler` boundary is unified around one opaque artifact, Value, Session, Outcome, and Checkpoint. `BackendPreference`, automatic fallback, two result carriers, and the old session implementation have been removed.

Functions in public Values use handles with ownership. Authenticate artifact, session, export generation, and slot; reject different ownership, unknown handles, and type mismatches before execution. This supports named / builtin inputs, repeated calls to returned functions within the same session, and repeated state updates.

Input validation goes beyond checking the outer tag.

- Validate payloads, heaps, captures, and code provenance under the same type world.
- Convert ordinary initial data to a sealed prefix with `SourceCoreHeapInput`.
- Validate historical raw heaps containing closures through explicit `SourceCoreLegacyHeapImport`. This process does not execute Source expressions or statements.
- Handle snapshots carrying evidence of actual allocation and capture through restoration or `exportPrefix`. Implicit transfer to another artifact is not provided.

See the [API migration record](core-runtime-unification-api.md) for actual API signatures, execution and observation budgets, source/native snapshot cell counts, and ownership constraints. Do not confuse internal compatibility carriers in old namespaces with continued existence of the old public execution path.

### 5.4 Core Wire Compatibility

The adopted format retains the fixed `schema` string `solcore-semantic-core`. No separate version field or Core function table was added. The Program codec retains its 4 existing required fields.

- Preserve old tags, decoding, and existing roundtrips.
- Extend native Integer types, values, and operations with explicit tags, accounting for decode depth, node, and byte budgets.
- Generated code for mappings, proxies, and closures uses existing data, function, and cell representations without dedicated Wire tags.
- Projection to the old representation is a partial conversion that checks representability and does not silently discard Integer or similar constructs.
- Codec, Core conversion, budget, and roundtrip proofs and rejection tests have been updated.

The initial `solcore-semantic-core-v2` and new function-table proposals were not adopted. If required fields change in the future, design identification of compatible formats at that point. Wire is an external representation, rather than an additional runtime backend.

## 6. Proof of Meaning Preservation

### 6.1 Reference and Scope

The main subject is typed source with valid declarative typing and stage conditions, and its execution.
Use `SourceSemantics.Dynamic.ProgramEvaluates` and associated failure relations as the reference.
The final theorem's input `S` is typed source before specialization and comptime pre-evaluation/substitution.
Theorems concerning only residual code after specialization and staging are intermediate results.

Do not redefine semantics as "the generated Core behaves this way" or embed old evaluator return values into semantics.
If existing semantics lacks rules, supply them with source-language reasons and examples.

Distinguish full correctness from parsing and name resolution of raw source from this compilation theorem.
Track the connection that supplies declarative assumptions from executable checking / stage analysis as separate theorems.

### 6.2 Correspondence Relations

Define at least the following. The names are provisional.

```text
ProgramRel       Correspondence of source definitions and instantiations with actual generated code and closure inventory
Representation   Correspondence information for types, locations, generated code, and local instantiations
ValueRel         Correspondence of source values and Core values
HeapRel          Correspondence of source heaps and Core stores
EnvironmentRel   Correspondence of source local environments and Core environments
OutcomeRel       Correspondence of successful results or prescribed failures and the state at that point
```

Requirements:

- Make correspondence for scalars, products, nominal data, mappings, and proxies explicit.
- Represent closure code correspondence and sharing of captured locations.
- Allow one generalized source closure to correspond to multiple monomorphic Core bodies.
- Allow extension of location correspondence upon allocation.
- Handle source descriptor cells, erased staged cells, and Core helper cells.
- Do not assume equality of entire heaps or one-to-one correspondence of all cells.

### 6.3 Shape of the Main Theorem

The following is mathematical pseudonotation describing the proof contract, rather than a currently existing Lean API.

Assumptions:

```text
compile(S, root) = ok C
SourceAdmitted(S)
EntryValid(S, root, sourceInputs, sourceHeap)
InputsRelated(ρ₀, sourceInputs, sourceHeap, coreInputs, coreStore)
```

Successful `compile` includes plan validation, compilation, and successful Core checking.
Do not make the main theorem trivial by requiring callers to supply proof fields that assume meaning preservation itself.

**A. Preservation of Successful Execution**

```text
SourceEvaluates(S, root, sourceInputs, sourceHeap, v, H)
  → ∃ fuel, vC, HC, ρ₁,
      CoreRun(C, coreInputs, coreStore, fuel) = done(vC, HC)
      ∧ Extends(ρ₀, ρ₁)
      ∧ ValueRel(ρ₁, v, vC) ∧ HeapRel(ρ₁, H, HC)
```

**B. Reflection of Successful Execution**

```text
CoreRun(C, coreInputs, coreStore, fuel) = done(vC, HC)
  → ∃ v, H, ρ₁,
      SourceEvaluates(S, root, sourceInputs, sourceHeap, v, H)
      ∧ Extends(ρ₀, ρ₁)
      ∧ ValueRel(ρ₁, v, vC) ∧ HeapRel(ρ₁, H, HC)
```

`ρ₀` is the initial representation relation; `ρ₁` is the final relation, including allocation during execution and similar changes.
`Extends` expresses preservation of existing correspondences and sharing, with the ability to add correspondence for new locations and similar entities.

**C. Preservation and Reflection of Prescribed Failures**

Provide bidirectional failure theorems corresponding to A and B.
Relate the side effects and state before failure as well as the failure category.
Because internal representations of types and locations differ, literal equality of error values is not required.

**D. Safety of Finite Execution**

No internal type inconsistency occurs for any fuel.
Successful results, prescribed failures, and suspended states each retain the required typing invariants.

A and B guarantee that compilation does not introduce divergence into terminating source or produce successful termination absent from the source.
However, they do not by themselves prove equivalence of infinite traces or overall source progress.
If an independent theorem for infinite execution or correspondence with the source prefix at fuel exhaustion is required, design additional small-step / coinductive semantics separately.
The finite observations in this phase do not require new source small-step semantics from the outset.

### 6.4 Decomposing the Proof

| Layer | Required results |
| --- | --- |
| Core | Soundness of the extended checker, type preservation, progress, result categories, and fuel/resumption laws. |
| Basic representation | Correspondence of types, values, heaps, environments, primitives, and allocation/read/write. |
| Helper libraries | Core typing and semantic correspondence for type-specific generated entry sequences, key comparison, lookup, update, defaults, and proxy tags. |
| Expressions | Correspondence for variables, calls, closures, operations, coercions, constructors, and mappings. |
| Statements | Correspondence for statement sequences, scopes, early return, loops, break/continue, and match. |
| Specialization | Preservation of type substitutions, local instantiations, evidence, and reachability. |
| comptime | Correctness of pre-evaluation, constant replacement, and branch elimination actually performed. |
| Whole pipeline | Theorems A–D connecting roots, arguments, initial states, and compilation artifacts. |
| Public boundary | Executable validation supplies the main theorem's initial conditions. |

Develop preservation by induction on source big-step derivations.
For reflection, use generated-code and continuation structure and invariants of the correspondence relations.
Extend the existing correspondence theorems between Core declarative evaluation and the machine with fuel, and connect concrete fuel theorems.

Reuse general Core safety through typing of helper functions.
This alone does not establish mapping or similar specifications, so separately prove correspondence of lookup results, insertion order, defaults, comparison, failures, and state changes.
Show that helper generators can apply these lemmas for each accepted type and representation.
Also establish finite lookup and insert execution on valid finite entry sequences, preventing correspondence from being satisfied vacuously by functions that fail to terminate successfully.
Maintain the same proof contract for keys containing function values or proxies, and do not take old runtime equality as an unproved callback.

### 6.5 Specialization Proofs

Separate specialization revalidation from semantic coverage.

- Revalidation: The supplied plan can be reconstructed from the program and has not been altered.
- Coverage: Functions, methods, and local instantiations reachable at runtime within the supported scope exist in the plan.
- Preservation: Execution based on original types and evidence corresponds to execution of instantiated bodies.

If plan creation does not finish within budget, a compilation error is acceptable.
A runtime path back to source is not permitted to compensate for omissions in a successful plan.

### 6.6 Treatment of comptime

Retain the existing direct comptime evaluator in this phase.
The final theorem from typed source to Core concerns source before pre-evaluation, so correctness of the pre-evaluation actually applied is also required.

- The returned staged value is also obtained by declarative evaluation.
- Constant replacement and embedding of the value in Core preserve correspondence relations.
- Branch and short-circuit choices are correct.
- Eliminated computations do not remove runtime-observable side effects.
- For staged computations with heaps, make the relation between their state and residual code explicit.

New pre-evaluation optimizations are not required in this phase. Do not add constant folding that is unnecessary for moving existing features to Core execution.
Do not retain existing runtime evaluation by relabeling it "for comptime."

Intermediate composition lemmas may assume `StagingCorrect` or similar conditions.
The final result for the second goal must connect theorems showing that the passes actually applied supply those assumptions.

### 6.6.1 State Correspondence for Erased comptime Cells

Inspection of the implementation on 2026-10-05 confirmed that replacing comptime expressions with constants can produce cells existing only in source execution.

- `SourceCoreElaboration.lowerExpressionFuelWith` replaces accepted comptime function calls or whole conditional expressions with `SourceStagedValue.toResolved`. Independent Source execution may allocate function arguments and locals while generated Core does not allocate them.
- In `lowerStatementsFuelWith`, the monomorphic Integer `let` branch adds the value to the compile-time environment and returns only the body. The Source `let` cell is erased.
- Staged `let` for Word, Bool, and similar types retains a value binding through `.letE` even when its initializer becomes a constant. `Resolved.Evaluates.letE` and `Core.Evaluates.letE` extend the value environment without allocating physical cells. Retaining a syntactic binding alone does not preserve Source cell allocation.

Distinguish allocation by execution path. The pure `SourceCoreElaboration.lowerFunctionBody → BodyDraft.finalize → Resolved.Expr.lower?` path also passes inputs in the value environment, and `Resolved.Evaluates.store_eq` establishes store invariance. The public `SourceCompiler.compileChecked → SourceCoreUnifiedCompilation.prepare` path uses `SourceCoreSourceCells.bindParameters` / `letInitialized`. The current indexed allocator allocates a snapshot, marker, and payload for each Source cell; the existing heap relation associates payload locations with Source cells.

The current public artifact is generated from the original specialized `TypedSource` and does not apply the pure Integer `let` erasure or constant replacement above. `prepareContexts` authenticates local evidence and does not pre-evaluate expressions. Pure erasure reaches `elaborateFunction` and the existing `SourceProgramExecution → DirectLinking` path. State each actual path's proof scope, and do not claim complete state correspondence for the public compiler from `Resolved.Evaluates.toCore` alone. Introducing new erasure into the public path is not added as a required task for this phase.

The current `GenericHeap.HeapRepresents` / `GeneralHeap.HeapRepresents` associate each Source cell with a Core cell. Their `length_eq` requires the length of the location correspondence table `LocationMap` to equal the number of Source heap cells. This is a proof table relating cell locations, distinct from the language's `mapping<K,V>`.
Existing "whole heap invariance" theorems for expression evaluation alone cannot connect the full compilation pipeline, which includes argument and `let` allocation described above.

**Implemented relation:** [SourceStagingHeapRelation.HeapRel](../../Solcore/SourceSemantics/CoreLowering/SourceStagingHeapRelation.lean) in the comptime-pass proof layer relates the complete Source heap before compilation to the Source heap of residual code. Reuse the existing all-cell relation for correspondence from residual code to Core. Adding Core syntax or execution rules is not a condition for solving this problem.

This relation and the pass theorems must satisfy at least the following.

1. Preserve all initial heap cells and the contents, sharing, and references of retained cells. Changes in locations caused by subsequent allocation must also be reflected consistently in values, environments, and closure references.
2. Identify erased cells from the actual accepted pass and the original Source evaluation derivation. Do not arbitrarily remove cells merely believed to be unreachable.
3. For erased Integer bindings and similar cases, maintain equality between values in the actual staged environment and original Source cells. Prove that erased locations do not leak into return values, captures of remaining closures, update targets, public handles, or similar places.
4. Relate retained side effects and states at failure. Supply successful evaluation of erased computations as independent Source derivations from acceptance by the actual evaluator.
5. Retain the original complete heap and evaluation derivation without changing Source semantics to fit residual code. Do not add equality of Source/Core cell counts or internal indices as a final-theorem condition.

The first unit covers actual Integer `let` and argument allocation in accepted staged functions. Supply local-variable validity and freshness from independent Source typing. `8f356765`, `7740d7aa`, and `618cd059` connect the structural relation, actual let erasure, residual Word/Bool computations, and pure function outputs. General staged computations, remaining closures, failures, and composition of all passes remain.


#### Implemented Proof Units and Their Scope

The first `SourceStagingHeapRelation` unit assigns an `Option` target to each Source location. The targets of retained locations enumerate all residual heap positions `0, …, n-1` in their original allocation order; candidate erased locations have no target. Retained values relate all product, constructor, and language-mapping elements and their order. Closures and generalized closures retain code, context, evidence information, and every location in their captured environments. Erasure candidates are limited to initialized ordinary Integer cells. This is a structural location correspondence relation; correctness of erasure decisions by the actual pass is proved separately.

The first application theorem uses acceptance by actual `evaluateStagedIntegerFunction` and the original execution derivation obtained from independent Source typing. It shows that Integer cells for inputs and selected `let` bindings are appended in order to the complete initial heap, and that the result is an Integer value containing no references. Preservation of reads for every initial heap cell is shown for arbitrary heaps. Where needed, derive from `HeapWellTyped` and typing of values and captured environments that initial closures do not capture locations appended later. Do not add rules permitting captures of erased locations or unproved body-execution laws to the relation.

`7740d7aa` extracts the accepted initializer expression, updated staged environment, code for only the recursively lowered body, and requirement-consumption order from the actual `lowerStatementsFuelWith` Integer `let` branch. [SourceStagedIntegerResidualMeaning](../../Solcore/SourceSemantics/CoreLowering/SourceStagedIntegerResidualMeaning.lean) in `618cd059` connects actual acceptance of pure `elaborateFunction` with Word/Bool inputs and computations, Integer let, block, if, and return to independent original Source execution including the complete heap and actual Resolved/Core results. Reflection of finite completion of the original Core uses determinism and existing machine correspondence.

This result preserves meaning in the pure path and does not add Integer erasure to the public unified path. Code and captures of general remaining closures, all staged-value functions, states up to failure, and correspondence of the full public compiler remain subsequent obligations.

Distinguish Source input cells erased by replacing entire function calls with constants from paths retaining Core argument values even when known staged inputs are used. Do not infer cell allocation from retained argument values; check derivations of the actual allocator and correspondence of value environments. Tie every erasure plan to actual lowering branches.

## 7. Specification Audit and Known Gaps

### 7.1 Failure Rules

`SourceSemantics.Dynamic.Fault` defines failures with structural grounds.
It does not guarantee coverage of every case, uniqueness of failures, or a first-fault policy for arbitrary malformed carriers.

First list the following for the valid source programs in scope.

- Successful execution rules
- Prescribed execution failures
- Invalid inputs rejected at compile time
- Invalid values/heaps rejected at the execution boundary
- Internal validation errors found only in the old evaluator

Prove required determinism and exclusivity with failure for the supported scope.
Do not promote every defensive error of the old evaluator to language semantics.

### 7.2 Resolved Gaps and Remaining Boundaries

For missing mapping keys whose value type also lacks a default, positive failure rules for indexing, place reads, and latest-root updates after the RHS have been added to independent `Dynamic.Fault`. They retain successful evaluation prefixes and heaps, and prove exclusivity with success of the same read / update. Core regressions also preserve diagnostics for absent defaults and evaluation order.

Do not treat this change as establishing coverage or uniqueness of all failures, or preservation and reflection for all syntax. The final theorem including stage guards, arity, general call bodies, methods/coercions, and all passes remains ongoing.

The old `RuntimeBoundaryAccepts` / `RuntimeExpressionEvaluatesOutcome` cover a narrow historical runtime representation boundary. Connect to independent Source through the actual compiler's value, heap, and outcome relations rather than accepting current Core values unconditionally.

### 7.3 Coexistence with Proofs in Progress

At the time this design was written, source inference and parser proofs had uncommitted changes.
Recheck `git status` and the relevant files when implementation starts, and preserve other work.
If subsequent work discharges bridging-theorem assumptions, inspect the actual theorems and update this design's assumption list.

## 8. Current Module Structure

| Responsibility | Implementation entry points |
| --- | --- |
| Core types, general cells, finite safety | `Core/Syntax.lean`, `Core/Safety.lean`, `Core/BoundedSafety.lean`, `Core/OptionalCell.lean`. |
| Explicit language failures and Integer | `Core/LanguageResult.lean`, `Core/IntegerPrimitives.lean`, and the existing checker, machine, host, and Wire. |
| Compilation plan validation and closure | `Frontend/SourceCompilationPlan.lean`, `SourceSpecializationWorklist.lean`. |
| Core compilation for public execution | `Frontend/SourceCoreCompiler.lean`, `SourceCoreUnifiedCompilation.lean`, `SourceCoreCompatibleFunctions.lean`, and feature-specific generators. |
| Ordinary Core helpers and cells | `Frontend/SourceCoreMappingWithDefault.lean`, `SourceCoreCompatibleDataEquality.lean`, `SourceCoreSourceCells.lean`, and similar modules. |
| Representation relations and meaning preservation | `SourceSemantics/CoreLowering.lean` and `SourceSemantics/CoreLowering/`. The independent spec umbrella does not import frontend. |
| Public API | `Frontend/SourceCompiler.lean` re-exports `SourceCoreExecution.lean`. `SourceCoreIndexedSession.lean` manages ownership, state, and checkpoints. |
| comptime and pure lowering | `Frontend/SourceCoreElaboration.lean`, `SourceCoreDirectLinking.lean`. State allocation differences from the public unified path explicitly. |

The initial `Core/Functions.lean`, `SourceCoreLowering.lean`, and `SourceCoreLibrary/` are not adopted filenames. New proof units should reuse existing relations and induction, and be added after checking actual placement.

### 8.1 Files to Read First

Links are relative to this document. Line numbers change, so search for the names below.

| File | Definitions and uses to focus on |
| --- | --- |
| [SourceCompiler](../../Solcore/Frontend/SourceCompiler.lean) / [SourceCoreExecution](../../Solcore/Frontend/SourceCoreExecution.lean) | `compileChecked`, `compileEntry`, `compileStaticWord`, `Compiled.open`, and the shared public API. |
| [SourceCoreCompiler](../../Solcore/Frontend/SourceCoreCompiler.lean) / [SourceCoreUnifiedCompilation](../../Solcore/Frontend/SourceCoreUnifiedCompilation.lean) | Actual plan validation, preparation, and cached Core code. |
| [SourceCoreIndexedSession](../../Solcore/Frontend/SourceCoreIndexedSession.lean) | Artifact, Bootstrap, Session, Outcome, Checkpoint, snapshot, and ownership. |
| [SourceCompilationPlan](../../Solcore/Frontend/SourceCompilationPlan.lean) | Revalidation of plans, evidence, and specialization. |
| [SourceCoreElaboration](../../Solcore/Frontend/SourceCoreElaboration.lean) | `lowerType`, `BodyDraft.finalize`, `evaluateStaged*`. |
| [SourceCoreDirectLinking](../../Solcore/Frontend/SourceCoreDirectLinking.lean) | `validatePlan`, `linkWithStagingFuel`, `evaluateStagedIntegerFunctionFuel`, `evaluateStagedValueFunctionFuel`. |
| [SourceRuntimeValues](../../Solcore/Frontend/SourceRuntimeValues.lean) | Compatibility carriers for values, state, and observations, rather than a runtime expression/statement evaluator. |
| [SourceCoreHeapInput](../../Solcore/Frontend/SourceCoreHeapInput.lean) / [SourceCoreLegacyHeapImport](../../Solcore/Frontend/SourceCoreLegacyHeapImport.lean) | Validation of initial data and explicit raw prefix migration. |
| [SourceSpecialization](../../Solcore/Frontend/SourceSpecialization.lean) | `SpecializedFunction` and the allowed scope of locally quantified variables. |
| [SourceSpecializationWorklist](../../Solcore/Frontend/SourceSpecializationWorklist.lean) | `Plan`, `collectContextualLocalLambdaInstances`, `closeLocalLambdaInstancesAux`, `run`. |
| [Core Syntax](../../Solcore/Core/Syntax.lean) | `Ty`, `CellPayload`, `Expr`, `Value`. |
| [Core Data](../../Solcore/Core/Data.lean) | `ConstructorPayload`. |
| [Core Safety](../../Solcore/Core/Safety.lean) | `RuntimeValueHasType`, `RuntimeStoreHasTypes`, the old `StoreHasTypes`, type preservation, progress, and completion assuming finite evaluation evidence. |
| [Core BoundedSafety](../../Solcore/Core/BoundedSafety.lean) | Type safety of finite execution, world extension, and typed suspension. |
| [Core Correspondence](../../Solcore/Core/Correspondence.lean) | `runStateful_evaluation_sound`, `evaluation_runStateful_complete`. |
| [Staged value proofs for Core lowering](../../Solcore/SourceSemantics/CoreLowering/StagedValue.lean) | Implemented value-embedding correspondence. `toCoreExpr_infers`, `toCoreExpr_evaluates_iff`, `toCoreExpr_run_complete`, `toCoreExpr_run_sound`. |
| [Core FuelResumptionProperties](../../Solcore/Core/FuelResumptionProperties.lean) | `runStateful_resume`. |
| [SourceSemantics Dynamic Program](../../Solcore/SourceSemantics/Dynamic/Program.lean) | `ProgramEntryValid`, `ProgramEvaluates`, `ProgramEvaluates.preserves`. |
| [SourceSemantics Dynamic Value](../../Solcore/SourceSemantics/Dynamic/Value.lean) | Values, closures, and failures independent of the evaluator. |
| [SourceSemantics Dynamic Evaluation](../../Solcore/SourceSemantics/Dynamic/Evaluation.lean) | Independent big-step rules for expressions, statements, and calls. |
| [SourceSemantics Dynamic Fault](../../Solcore/SourceSemantics/Dynamic/Fault.lean) | Failure and side-effect propagation, and the old runtime boundary. |
| [SourceInferenceProgramBridge](../../Solcore/SourceSemantics/SourceInferenceProgramBridge.lean) | Check bridging assumptions requiring `InferStatementsFuelSoundness` and similar conditions. |
| [CheckedCoreProgram](../../Solcore/ContractRuntime/CheckedCoreProgram.lean) | Completion guarantees from finite evaluation evidence and type safety of finite execution and checkpoints. |
| [HostDriver](../../Solcore/ContractRuntime/HostDriver.lean) | Connection between Core state and host suspension. |
| [TopLevelExecution](../../Solcore/ContractRuntime/TopLevelExecution.lean) | `TopLevelRunResult`, fuel exhaustion, resumption, finalize. |
| [Core Wire](../../Solcore/Core/Wire.lean) | External representation, codec, and fixed host boundary. |
| [SourceStagedIntegerResidualMeaning](../../Solcore/SourceSemantics/CoreLowering/SourceStagedIntegerResidualMeaning.lean) | Preservation and reflection between original Source execution of pure staged Integer functions and actual Core completion. |
| [CallableIndexedAuthorityPool](../../Solcore/SourceSemantics/CoreLowering/CallableIndexedAuthorityPool.lean) | Preservation of owner keys, shared frames, and all records. |
| [CallableIndexedLambdaTemplatePermission](../../Solcore/SourceSemantics/CoreLowering/CallableIndexedLambdaTemplatePermission.lean) | Derive static template permission from actual receipts. |
| [RecursiveNamedExpressionCompilerCertificates](../../Solcore/SourceSemantics/CoreLowering/RecursiveNamedExpressionCompilerCertificates.lean) | Connect ordered additional child expressions to the same compiler-fuel induction. |

## 9. Implementation Tasks and Dependencies

For each task, record changed APIs, proved claims, remaining assumptions, and verification results.
"Complete" below includes passing the build for the relevant code without introducing proof escape hatches.

| Task | Current assessment |
| --- | --- |
| T0 | Audit of migration scope, representation decisions, and regression scope is complete. Proof obligations for all semantics continue under T6. |
| T1 | Core foundations, adopted recursion representation, and host/Wire updates are complete. |
| T2 | Separation from the runtime evaluator and revalidation of plans are complete. Connect semantic coverage under T6. |
| T3/T4 | Runtime features in scope have migrated. Partial preservation and reflection proofs are implemented; composition for all syntax and general bodies continues under T6. |
| T5 | Public unification and removal of the old evaluator for the first goal are complete. |
| T6 | Ongoing. The overall claims of the second-goal checklist are incomplete. |

The deliverable lists below define implementation and proof scope. Completion of runtime migration for T3/T4 does not mean completion of all correspondence proofs.

### T0: Audit of Features and Semantics in Scope

Dependencies: None.

Initial findings are recorded in the [T0 audit material](core-runtime-unification-audit.md). Update the table by tying each item to concrete migration destinations and regression checks.

Deliverables:

- Feature-by-feature inventory of existing runtime/compiler tests and their Core migration destinations.
- Classification table for successful execution, prescribed failures, input rejection, and insufficient budgets.
- Confirmation of evaluation-order, sharing, and mapping-default specifications.
- A design expressing this document's main theorem and assumptions as Lean types.
- An explicit list of work remaining in comptime.
- A comparison of candidate Core extensions and representations using helper libraries. Record effects on specifications, safety proofs, compilation proofs, generated code, fuel, and Wire/host.
- Decisions on the recursion mechanism, mapping/proxy helpers, and whether to adopt Integer.

Completion criteria: Every unimplemented or unproved item is listed, leaving no room to silently discard old evaluator features.
For each candidate addition, distinguish changes to Core specifications from work placed in compilation and helpers.

### T1: Foundations for Core Cells, Functions, and Results

Dependencies: T0 representation and failure policies.

Deliverables:

- General cells, the adopted closure / apply and optional function cells, and representation of prescribed failures.
- Updates to the Core checker, typing, machine, runner, and basic declarative evaluation.
- Type-world extension and type preservation/progress for read/write, closure, and call.
- Review of unconditional termination theorems and their uses.
- Compatibility and conversion for host, ContractRuntime, and existing Wire, with updates to Core fixtures. Finalizing extended Wire and the public API is excluded.

Completion criteria: Handwritten Core programs execute recursion, mutual recursion, shared captures, and self-cell recursion, with type safety and fuel-resumption laws passing.
Dedicated mapping, proxy, or source-statement instructions have not been added as prerequisites for these foundations.

Current status: Implemented and verified together are checker admission for general cells, finite-execution type safety, a self-referential closure that suspends for all fuel, and terminating self-recursion, mutual recursion, and shared-capture examples.
Uninitialized cells and language-failure results using ordinary sums, allocation of function payloads without placeholder values, and the ContractRuntime failure/rollback adapter are also implemented and verified together.
Source failure envelopes, reason/site tables, recursion selection, and compilation are implemented, so the T1 Core foundations are considered complete. Preservation of meaning for all source programs remains under T6.

### T2: Independent Compilation Plans

Dependencies: T0. Can partly proceed in parallel with T1.

Deliverables:

- Move plan validation, method reachability, first-class references, and local instantiation to an independent compilation layer.
- Deterministic ID assignment for types, functions, and instantiations.
- Registration and deduplication of generated helper functions and data definitions. Include dependencies in the plan and track budgets required for generation.
- Preserve existing rejection of externally forged plans.
- Expose invariants needed to prove coverage.

Completion criteria: New runtime lowering can obtain a complete input plan without importing the old evaluator.

### T3: Minimal source → Core Path and Correspondence Proofs

Dependencies: Required parts of T1 and T2.

Scope:

- Scalars and products
- Let, assignment, conditional branching, return
- Calls using adopted closure / apply and optional function cells
- Closures capturing mutable cells and self-cell recursion
- A small prototype handling lookup and update for `mapping(Word => Word)` and proxy tags with ordinary Core data and functions

Deliverables: In addition to an executable path, establish `ValueRel` / `HeapRel` and basic preservation/reflection lemmas for this small scope.
For the mapping prototype, check helper typing and lookup/update correspondence without first fixing native mapping types or instructions.

Completion criteria: Confirm that shared-heap and recursion representations support the proofs. Result-agreement tests alone do not complete this task.
Assess the implementation and proof burden of helper representations, providing evidence for comparison with candidate Core extensions.
This is the minimum condition for starting to finalize Wire and public API formats.

### T4: Extending Feature Coverage

Dependencies: T3.

Scope:

- Nominal data, match, and Integer in the adopted representation
- Helper generation for mapping, proxy, key comparison, and defaults, with typing and semantic correspondence
- While / for, break / continue, non-tail control, scope
- Locally polymorphic functions, nested instantiation, first-class function values
- Trait evidence, operators/coercions, and their helper frontier
- Stage boundaries and connection to existing comptime work
- Public inputs containing function values and existing heaps

Add representation, compilation, Core type checking, tests, and correspondence lemmas together for each feature.
If native mapping/proxy support or similar changes are considered necessary, update the comparison in Section 3.4 before changing the implementation.
State the associated scope of changes to Core, host, Wire, and proofs.

Completion criteria: Core can execute every typed-source runtime feature available at the start of migration, with no successful cases exclusive to the old path.
For T0 prescribed failures, also check compatibility through regressions for categories, evaluation order, and side effects up to failure.

### T5: Unify the Public API and Remove the Old Evaluator

Dependencies: T4 and verification of all features, including T0 prescribed failures and side effects up to failure as well as successful results.

Deliverables:

- Consolidate backend selection and duplicate carriers in `SourceCompiler`.
- Move deep input validation and code-ownership validation to the new Core boundary.
- Migrate tests, proofs, and umbrella imports depending on the old runtime.
- Remove `SourceTypedRuntime` execution features and public types specific to the old runtime.
- Update README, public API migration examples, and treatment of Core Wire format changes.
- Finalize the extended Wire format and public API based on T3 verification and T4 extension decisions.

Completion criteria: Satisfy the first-goal checklist in Section 10.

### T6: Complete Meaning-Preservation Proofs for the Full Compilation Pipeline

Dependencies: T3/T4 lemmas. May begin before T5.

Deliverables:

- Preservation and reflection of successful execution and failures for all syntax.
- Connect typing and semantic correspondence of generated helper libraries to the full compilation theorem.
- Correspondence of specialization substitution, reachability, and evidence.
- Correctness of comptime transformations actually applied.
- A connection enabling use of the main theorem from successful public compilation and input validation.
- A final theorem leaving no unproved pass correctness as external assumptions.

Completion criteria: Satisfy the second-goal checklist in Section 10.

### Division of Work

Multiple contributors must not independently change Core representations. Assign Core type, store, and result representations to one owner.
After fixing that boundary, work on data operations, control compilation, specialization/evidence, and correspondence proofs can be divided.
Changes to the Core kernel and changes to helper libraries generating ordinary Core code are separate responsibilities.
Agree on shared type and theorem signatures first, and avoid concurrent editing of the same foundational files.

## 10. Completion Criteria

### First Goal: Remove Direct Runtime Evaluation

- [x] The T0 feature inventory contains no item executable only through the old path.
- [x] Regression checks pass for failure categories, evaluation order, and side effects up to failure for T0 prescribed failures.
- [x] All runtime expressions, statements, and calls execute through Core.
- [x] The Core evaluator contains no `TypedSource` interpretation or calls to the old evaluator.
- [x] Helper libraries are ordinary Core code and conceal no separate host-side evaluator for mappings or similar features.
- [x] Every Core addition has a comparison and reasons for adoption, with no duplicated mechanism for recursion or source control.
- [x] Mappings and proxies use helper functions and data, or the comparison and reasons for dedicated features are recorded.
- [x] Runtime values retain no closures interpreting the source node table.
- [x] No values, states, or results specific to `SourceTypedRuntime` remain in the public API.
- [x] Validation of public-input references, heaps, and closures is preserved.
- [x] Specialization and preparation are separated from the old evaluator.
- [x] The direct-evaluation work retained as comptime is explicitly listed.
- [x] Core checker, bounded safety, host, ContractRuntime, and Wire are updated.
- [x] Before finalizing Wire and the public API, type safety and meaning-preservation lemmas for the minimal path and comparisons of extension candidates have been checked.
- [x] Tests for existing features, the build, and kernel policy pass.

First-goal assessment (2026-10-01, `a3168382`): Complete. An independent re-audit of the dependency paths and actual definitions of public `SourceCompiler` / `SourceCoreExecution`, registration of existing T0 test groups, and the public initial-heap/snapshot/handle boundaries found no concrete unresolved items. Full `lake test` passed with 8338 jobs and all execution tests, and kernel policy passed. See the [implementation record](core-runtime-unification-progress.md) and [API migration record](core-runtime-unification-api.md) for details.

This assessment concerns the TypedSource runtime backend and public execution path. An independent old `Syntax.Expr/Term` evaluator for fragment proofs remains in an isolated module, unreachable from the shared public compiler / Current dependency paths. The agreed comptime evaluator remains in compilation preparation. Meaning preservation across the full pipeline for the second goal remains ongoing.

### Second Goal: Meaning Preservation Across the Full Compilation Pipeline

- [ ] Preservation and reflection of successful execution are proved against independent semantics.
- [ ] Correspondence of prescribed failures in scope and states at those failures is proved.
- [ ] A heap relation including shared captures, allocation, and local instantiation is defined and proved.
- [ ] Correctness of specialization, evidence, and actual comptime transformations is connected.
- [ ] For mapping key comparison, lookup, update, defaults, and proxy representation, semantic correspondence of helper libraries or adopted Core primitives is connected.
- [ ] The final theorem does not require callers to assume unproved meaning preservation of passes themselves.
- [ ] Malformed raw `CheckedProgram` values or arbitrary input closures are not trusted unconditionally.
- [ ] The relationship between declarative input validity and conditions guaranteed by the executable public boundary is explicit.
- [ ] The document does not incorrectly claim proofs of equal fuel, successful termination of all programs, or equivalence of infinite traces.
- [ ] The build and kernel policy pass without proof escape hatches.

## 11. Verification

### 11.1 Priority Regression Cases

- Recursion, mutual recursion, fuel exhaustion, and resumption with additional fuel.
- Self-cell recursive closures and multiple closures updating the same variable.
- Use of locally polymorphic functions at different types and shared captured state.
- Returned closures and validation in initial heaps, accepted global / builtin function arguments, rejection of unsupported closure arguments, and rejection of invalid function handles from different artifacts.
- Higher-order values in nominal data, pattern matching, and payload types.
- Mapping copies, nesting, defaults, proxy keys, and update order.
- Type-specific mapping key comparison, proxy types that must remain distinct despite representation changes, and registration/reuse of helper functions.
- Arguments with side effects, assignment-target indices, coercions, and short-circuit expressions.
- For continue and post, break, early return, and captures after scope exit.
- First-class constrained functions, globals discovered inside selected methods, and helper frontiers.
- Integer signs, bitwise operations, Word conversions, and comptime acceptance/rejection.
- Uninitialized reads, mappings without defaults, and altered boundary inputs.
- Existing host, transactions, commit/rollback, suspension, and resumption.

Differential tests during migration compare values, observable state, and failure categories.
Do not judge by equal fuel or string equality of entire raw heaps.
Repeated executions with different fuel are supplementary tests and do not replace meaning-preservation proofs.
When comparing Core primitives and helper libraries, record generated code size, execution steps, and elapsed time separately for the same examples.
Do not conclude that total burden is smaller merely because there are fewer syntax forms.

### 11.2 Basic Commands

Run from the repository root.

```sh
lake build
lake test
node scripts/check-kernel.mjs
```

Lean warnings are treated as errors.
Kernel policy rejects `sorry`, `admit`, `partial`, `unsafe`, `axiom`, and similar constructs in semantic modules.
Do not fill unproved declarations with escape hatches even at intermediate stages. Record unfinished claims in the design/tasks, and add lemmas as they are proved.

Main tests to migrate:

- [SourceCompiler](../../Solcore/Test/SourceCompiler.lean)
- [SourceTypedRuntime](../../Solcore/Test/SourceTypedRuntime.lean)
- [SourceTypedRuntimeStateInteractions](../../Solcore/Test/SourceTypedRuntimeStateInteractions.lean)
- [SourceTypedRuntimeOperators](../../Solcore/Test/SourceTypedRuntimeOperators.lean)
- [SourceTypedRuntimeFirstClassEvidence](../../Solcore/Test/SourceTypedRuntimeFirstClassEvidence.lean)
- [SourceStagedRecursion](../../Solcore/Test/SourceStagedRecursion.lean)
- [Tests/Main](../../Tests/Main.lean)

Tests may be renamed or split, but removing tests from imports alone does not complete feature migration.

## 12. Procedure for Resuming Implementation

1. Check this document's current implementation status, the opening and latest additions of the [implementation record](core-runtime-unification-progress.md), applicable AGENTS.md, and `git status`. Preserve other inference/parser work.
2. Use the latest committed verification point in the current status table and inspect subsequent proof changes. Shared registrations and owned Values/Entries/State are committed; rerun appropriate checks for later changes.
3. Thread the concrete reached state through ordered expressions, actual marked allocations, lexical tails and five-way imperative flow. Reuse the existing static Tree/CatalogSites and Source/Core size proofs.
4. Retain actual SourceReceipt, complete type substitution and capturePrefix, and the same Source/Core value model and Entry. Do not force actual general captures of nested lambdas into existing theorems limited to prefix0.
5. Call restoration installs saved frames in the reached AuthorityPool. Preserve records added during callee, argument, or body evaluation, shared and distinct frames, all captures, and snapshots.
6. Connect the actual lowerer's callee and ordered arguments, original Source derivations, and strict child sizes in original Core to the existing single mutual induction. Static child-expression authentication and template permission do not replace body meaning preservation.
7. Integrate general indirect calls, lambdas, methods/coercions, and local instantiations into the same relation, and supply final assumptions from actual specialization, evidence, and staging passes.
8. From public compilation success and input validation, complete preservation of successful results, language failures, and all state against independent Source before pre-evaluation, together with reflection of finite completion of the original Core. Leave no unproved body/pass laws in the final theorem.
9. Complete required verification and shared registration for each logical unit, then commit. Reflect proof scope, remaining assumptions, and actual completion results in the progress record. Do not mark complete until the second goal in Section 10 is satisfied.

If implementation changes the design, record the reasons, affected theorems, compatibility, and verification results in this document or adjacent records.
If reducing the goals, removing existing features, or introducing new source-language semantics becomes necessary, state these as matters to confirm with the user.
