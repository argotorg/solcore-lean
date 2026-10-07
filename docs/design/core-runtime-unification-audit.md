# Core unification: T0 audit of features, semantics, and proof boundaries

Initial audit: 2026-09-30. Last updated: 2026-10-08.

This document preserves the initial audit for the [implementation design](core-runtime-unification.md) and subsequent dated investigations. Sections 1–9 record the state on 2026-09-30; later sections record the state on their respective dates. References to the "current" implementation, "unfinished" work, "next steps," or old API names describe that historical state.

Runtime Core unification was completed in `a3168382`. See the [API migration record](core-runtime-unification-api.md) for the current public entry points. The [implementation record](core-runtime-unification-progress.md) and the final section, "2026-10-08: Current status," describe the latest commits, validation, and uncommitted work.

Compilation preparation has been separated into `SourceCompilationPlan`. The historical investigations below refer to definition names at the time rather than line numbers.

## 1. Feature migration table

Coverage is measured against `ExpressionForm`, `StatementForm`, and `ForItemForm` in `SourceInference.TypedIR`, together with the old runtime's values and public boundary.
The target is the closed roots and finite plans supported by the compilation and execution boundary, rather than every source program accepted by the type checker.
Tests that pass modified carriers to `runTrusted` do not establish what the public boundary accepts.

### 1.1 Expressions and values

| Subject | Behavior to preserve | Initial Core approach | Implementation and test references |
| --- | --- | --- | --- |
| `literal` | Convert the natural number denoted by the literal to Word by modular reduction. | Existing Word constant. | `LiteralConstructs`, `WordLiteral`, `evaluate`. |
| `integerLiteral` | Construct Word or Integer according to the resolved type and Int evidence. | Word constant / Integer representation to be selected after comparison. | `ResolvedIntegerLiteralConstructs`, `validateIntegerLiteralResolutionWith`. |
| builtin boolean reference | Return a Bool value. | Bool constant. | `builtinBoolean` in `evaluate`. |
| local reference | Read a cell by stable local ID and observe subsequent updates. An uninitialized mapping can be read as empty. | Local ID → Core binder / cell correspondence. | `initialRootValue`, `testClosuresOrderProxyAndFuel`. |
| declaration reference | A first-class function with the exact generic instantiation and evidence. | Function-table reference and required dictionary values. | `testConstrainedGlobalValue`, `testPredicateReordering`. |
| builtin function reference | Retain a builtin as a first-class value. | Typed Core function value. | `applyBuiltin`, `BuiltinFunctionId`. |
| `group` | The same value and effects as the enclosed expression. | Lower the enclosed expression. | `ExpressionFormEvaluates.group`. |
| `tuple` | Evaluate left to right and construct the same product tree with `Value.pack` / `ValuesPack`. | Existing pair/unit. | `testNestedMatchingAndCalls`. |
| `unary` | Bool not, Word / Integer bit-not, or a method selected by evidence. | Core primitive or compiled method call. | `applyUnary`, `executeUnaryOperatorMethod`. |
| `binary` | Word / Integer operations and comparisons, selective equality, short-circuiting, and selected trait methods. | Core primitive / branch / method call. | `applyBinary`, `testSelectedOperatorMethods`. |
| `conditional` | Evaluate the condition, then only the selected branch. | Core if. | Conditional rule in `ExpressionFormEvaluates`. |
| `lambda` | Capture cell locations and evidence from that activation, rather than a snapshot of their values. | Core lambda / generated function with captured cell references. | `testGenericRecursiveClosure`, `testRecursiveClosureSelfCellAndEvidence`. |
| direct call | Enter the type-specialized declaration body, including recursive and mutually recursive calls. | Function-table reference and call. | `testNominalConstructionAndRecursiveCalls`. |
| builtin call | Preserve the 7 builtins below, their types, and argument order. | Primitive or small Core function. | `applyBuiltin`. |
| indirect call | Callee, arguments, argument-bundle coercion, body, then result coercion. | apply and explicit coercion calls. | `testIndirectArgumentCountMetadata`, `testIndirectEndpointMetadata`. |
| `constructor` | Nominal identity, type arguments, payload order, and payload types. | Closed source type → Core data ID; relax payload restrictions. | `testNominalConstructionAndRecursiveCalls`, `testNominalInputValidation`. |
| `member` | Return the selected payload from a base evaluated once. | Core data decomposition and projection. | `ValueAt`, `updateResolvedValue_member_*`. |
| `proxy` | Identify the retained closed type. Proxy keys of the same type match. | Type tag that does not interpret source `Ty`. | `testGenericProxyMappingKey`. |
| `index` | Evaluate the base before the key. Return an existing entry's value, or the value type's default if absent. | Entry sequence represented by Core data, with ordinary lookup/update functions. | `MappingLookup`, `DefaultValue`, `testAssignmentsMappingsAndControl`. |
| locally polymorphic lambda | Instantiate a single principal initializer at each use site. All instances share the same captured cells. | A set of monomorphic code instances with a shared environment. | `testLocalLetPolymorphism`, `testContextualLocalGenericCalls`. |
| qualified locally polymorphic lambda | Relate template requirements to concrete use-site evidence. | Instantiated code and dictionaries. | `testQualifiedLocalLetPolymorphism`, `testQualifiedLocalAliasEscape`. |
| expression output coercion | After obtaining the raw value, execute methods in the recorded order and retain their effects. | A chain of typed functions. | `executeCoercionPath`, `testStatefulCoercionMethod`. |

The builtins are `integerSub`, `wordFromInteger`, `integerAdd`, `integerEq`, `integerLt`, `integerMul`, and `wordToInteger`.
Word → Integer produces a nonnegative mathematical integer. Integer → Word reduces modulo `2^256`, including negative inputs.
Word and Integer division and remainder return 0 for a divisor of 0. Do not introduce a new division-by-zero failure.
Integer bitwise operations follow infinite two's-complement behavior. Fix their correspondence with Lean's signed division and remainder operations as well.

`valueEqual` is not a general decision procedure for equality of all values. Closures and mappings are not comparable values.
Do not replace equality for global / builtin functions, proxies, nominal payloads, and products with a comparison of outer Core type tags.

### 1.2 Statements, scope, and heap

| `StatementForm` / related feature | Behavior to preserve | Migration target and checks |
| --- | --- | --- |
| `letDecl`, without initializer | Allocate a fresh cell. Reading an uninitialized non-mapping cell fails. | Explicit uninitialized representation such as `cell (sum unit T)`. |
| `letDecl`, with initializer | Allocate a fresh cell after the initializer's effects. | Relation between `Heap.Allocates` and Core allocation. |
| generalized let | Create the principal descriptor once and instantiate it at each use site. | Do not equate a descriptor cell with a single monomorphic cell. |
| `returnStmt` | Return a value or unit; do not execute the remaining statements. | Returned branch of a typed control result. |
| `expression` | Execute effects. An expression without a semicolon at the end of a function is an implicit return. | Final-statement rule in `executeFunctionSequence`. |
| `assignValue` | Resolve the target and evaluate indices, then evaluate the RHS, then update the target. | See the evaluation-order table below. |
| compound assignment | `+= -= *= /= %= &= ^= \|=`. Distinguish the value selected during target resolution from the root at write time. | `assignmentBinary?`, `ResolvedPlace.selected`, `updateResolvedValue`. |
| `assignBitNot` | Apply bit-not to the resolved place's current value. There is no RHS. | `SourcePlaceBitNotExecutes`. |
| `ifThen` | Execute only the branch selected by the condition. The else branch is optional. | Distinguish fallthrough from return. |
| `block` | Restore lexical names. Retain allocated cells for closures that capture them. | Relate environments and heaps separately. |
| `matchWith` | Evaluate the scrutinee once; handle the hidden binding, arms in source order, pattern bindings, and default. | Constructor / tuple / binder / literal patterns. |
| `whileLoop` | Condition → body. continue returns to the condition; break exits the loop. | Generated recursive function and control result. |
| `forLoop` | Initializer → condition → body → post. continue also executes post. | Handle every let / expression / assign / bit-not form in `ForItemForm`. |
| `breakStmt` / `continueStmt` | Consumed by the innermost loop; cannot escape the function. | Loop-control typing and correspondence of runner outcomes. |
| recursive closure | Allocate the function cell first, then store a closure that captures that cell. | Core safety for self-cells and mutual sharing. |
| mapping update | Resolve the index path once, reconstruct inner values, and update the root cell. | Do not turn mappings into new shared reference objects. |

The old heap is a sequence of cells with a type and `Option Value`. Closures capture cell locations.
Mappings, nominal data, and products are value structures; do not unconditionally turn them into shared mutable objects.
New mapping entries are appended; replacing an entry preserves its original position.

## 2. Evaluation-order contract

| Construct | Order |
| --- | --- |
| tuple / constructor / argument list | Left to right in source order. A fault or fuel exhaustion returns the heap at that point. |
| direct call | Validate metadata for the synthetic declaration callee, evaluate arguments, then enter the body. The synthetic reference introduces no extra effects. |
| indirect call | Callee → arguments → pack → coercion of the argument bundle → unpack → body → expression output coercion. |
| strict binary | Left → right → primitive or selected method. |
| logical and / or | Do not evaluate the right operand if the left determines the result. |
| conditional / if | Condition → the single selected branch. |
| indexing | Base → key → lookup or default. |
| assignment | Resolve root / projection indices → RHS → reread current root → update path → write root. |
| compound assignment | Use the leaf selected after target resolution and before the RHS as the operation's left operand. Structural writeback uses the latest root after the RHS and preserves unrelated changes. Do not reevaluate resolved indices. |
| coercion path | Pass each stage's result and heap to the next. Retain method side effects. |
| match | Scrutinee → hidden binding → arm selection → binder allocation → body. |
| for continue | Move from the body to post, then back to the condition. |

Assignment proofs must not identify the heap used to resolve the place with the heap after the RHS.
Carry the `ResolvedPlace.selected` snapshot forward: the operation uses the old leaf, while reconstruction uses the new root.
Retain `assignmentOrder` from `testClosuresOrderProxyAndFuel` and the state-interaction coercion cases as regressions.

## 3. Outcome and failure classification

This classification preserves failure meaning and state, rather than requiring exact diagnostic names.
Every constructor of the runtime's `RuntimeError` at the time must map to one of these categories during migration.

| Category | Examples | Treatment at the new boundary |
| --- | --- | --- |
| Specified source failure | Uninitialized read of a non-mapping local; mapping read / projected update with no available default. | Typed trap or specified failure result. Preserve effects before failure. |
| Invalid program / plan | Missing / duplicate specialization, ownership errors, noncanonical plan, missing / duplicate call/reference edge. | Reject during compilation. Do not call a solver or worklist during Core execution. |
| Invalid typed metadata | Indirect arity / endpoint, declaration mismatch, malformed literal/pattern, result type mismatch. | Make unreachable from checked lowering; reject forged carriers at the boundary. |
| Invalid evidence | Duplicate / missing requirement, goal mismatch, selected implementation mismatch, local scheme template/actual mismatch. | Reject in compilation-plan and external function-handle validation. |
| Stage constraint | Runtime-dependent comptime argument, invalid stage of a comptime result, unsupported staged input. | Preserve the existing accepted scope and distinguish compile/input rejection from source failure. |
| Invalid external value / heap | Dangling cell, nominal payload mismatch, forged closure code/evidence, handle from a different artifact. | Reject before execution; leave the initial heap unchanged on rejection. |
| Insufficient compilation resources | Specialization / method-frontier budget, executable-plan closure fuel, comptime depth. | Compilation outcome; separate from runtime outOfFuel. |
| Insufficient input-validation budget | `inputValidationFuelExhausted` and similar errors. | Validation outcome; separate from execution fuel. |
| Insufficient execution budget | `outOfFuel`. | Preserve typed machine state and continuation. |
| Defensive internal runtime diagnostic | expectedBool / Function / Product, invalid primitive, controlEscapedFunction, deep final-state rejection. | Prove these cannot arise from valid artifacts and inputs. Revisit classification if a legal reachable example is found. |

### 3.1 Known specification gaps

`SourceSemantics.Dynamic.Fault` has positive fault derivations. Its current description alone does not establish determinism or complete failure coverage for every well-formed execution.

When a mapping entry is absent and its value type has no default, the old evaluator returns `typeMismatch valueType none`.
For expression indexing, `SemanticFault.missingMappingDefault valueType` and
`ExpressionFormFaults.indexDefaultUnavailable` were added. Successful evaluation of the base and then the key, the key's type,
`MappingAbsent`, and the absence of an independent `Defaultable` derivation produce a fault with the heap at that point.
The observation correspondence is `missingMappingDefault valueType` → the old `RuntimeError.typeMismatch valueType none`.
No restriction was added to type checking of mappings with non-defaultable value types.
`Solcore/Test/SourceMappingDefaultFault.lean` checks an empty mapping of function values, the heap after evaluation,
and matching diagnostics from the old default computation and projected update.

Independent rules were also added for place reads and updates:

- `ProjectionsFaults` in `Dynamic/Place.lean` is a pure path failure restricted to missing defaults. It explicitly records each index's type check and the successful prefix through existing entries, defaults, and members.
- `ProjectionsFaults.excludes_read` and `excludes_update` prove incompatibility with a successful read or update of the same root and path. `ProjectionsUpdate.readable` shows that a successful update implies readability of the leaf on that path.
- `SourcePlaceFaults.projectionRead` reads the current root in the heap **after evaluating all index expressions** and derives a pure path fault. It returns the post-index heap; the RHS has not yet been evaluated.
- `SourcePlaceAssignmentFaults.structuralUpdate` derives a fault from the **latest root** after successful target resolution and RHS evaluation, returning the post-RHS heap unchanged. It checks that the root type matches. Structural traversal precedes the leaf modifier, so a missing default is observed first even if the operation on the old selected leaf would fail.
- `SourcePlaceAssignmentFaults.operands` requires a latest-root read, matching type, initialized value, and successful path read. It does not skip structural traversal to derive an operand fault. In the missing-default case, the exclusion lemma prevents the read premise for the same root/path.
- BitNot has no intervening RHS. `SourcePlaceResolves.excludes_projection_fault` proves that a missing default cannot newly arise after successful target resolution in the same post-index heap. No unreachable additional fault constructor was introduced.

Regression proofs check successful index/default/member prefixes, preservation of post-index / post-RHS heaps, structural faults preceding invalid snapshot operands, and read/update exclusion.
They also check that the actual `updateResolvedValue` and `writeResolvedPlace` return the existing `typeMismatch valueType none` before calling any leaf modifier, without changing the heap. This includes prioritizing the missing default even when a modifier explicitly returns `invalidAssignmentOperands`.
The new source rules and regression proofs passed a combined Lean check in a temporary file without updating shared artifacts. Ordinary module builds are deferred to integration validation.

The following specification gaps remain separate:

- Invalid projection shapes, wrong key types, out-of-range members, post-RHS uninitialized roots, dangling locations, root-type mismatches, and failed type checks of leaf / rebuilt-root values are outside this pure path-fault relation.
- The existing success relation `ProjectionsRead` itself does not require the index key type. Adding a read premise to the operand fault does not cover the runtime's type checks for arbitrary invalid keys.
- The new rules derive faults from explicit successful prefixes. They do not collectively establish complete failure coverage, determinism, first-fault agreement, or reachability from the checker for all well-formed source programs.
- The current `ValueRuntimeType` and index key-type fault rules compare source types directly.
  Agreement with the old runtime's recursive comptime erasure is a separate obligation; the unstaged Word-key regression does not supply it.

The old `RuntimeBoundaryAccepts` is a small unit/bool/word/product residualization boundary, rather than an admission test for general source values.
Passing the new Core Integer, mapping, closure, and nominal values through it unchanged would incorrectly produce stagingViolation.

Removal criteria include regression checks of legal failures, their classification, evaluation order, and heaps up to failure, in addition to successful examples.
When source rules and the old evaluator disagree, record the difference, its language-level justification, and compatibility implications rather than defining semantics directly from old behavior.

## 4. Actual public-input scope

Inspect `runWithValidationFuel` and `runDeepCertifiedWithValidationFuel` separately.
The latter checks shallow input validation, the prepared plan, the deep initial heap, and deep arguments, then rechecks the heap/value of successful results.
The guarantee is stronger than equality of the outer `Value.type?` tag.

- `Value.validateTypeFuel` checks nominal declarations/payloads, products, mapping entries, and proxy types.
- External function arguments currently have global / builtin branches. Do not assume arbitrary lexical closures are already accepted as public arguments.
- Closures created during execution or present in the initial heap participate in deep checks of code provenance, capture cells, and evidence.
- The old `runTrusted` differs from the public boundary. Do not automatically promote trusted-only tests of forged inputs into new API feature requirements.
- New API input certificates tie the code table, nominal table, store typing, references, and evidence to the same artifact.
- Function handles must preserve the existing public-input admission scope. Accepting arbitrary external closures is not required by this migration.

Provide a theorem deriving the relation's initial conditions from successful public validation, rather than merely requiring external callers to assume them.
Conversely, do not require every hand-written Core value without source provenance to have a corresponding source value. Keep the contracts of standalone Core APIs and source-compiler APIs distinct.

## 5. comptime and retained evaluation

The following direct evaluation can remain separately from the runtime interpreter being removed:

- `SourceCoreElaboration.evaluateStagedInteger*`, `evaluateStagedWord*`, and `evaluateStagedBool*`.
- `SourceCoreElaboration.evaluateStagedValue*` and statement / binding helpers.
- `SourceCoreDirectLinking.evaluateStagedIntegerFunctionFuel` / `evaluateStagedValueFunctionFuel` and staged callbacks for selected methods and coercions.
- The unit/bool/word/product carrier of `SourceStagedValue` and its reification into Core.

`SourceStageAnalysis` is a sidecar classifying occurrence stages, rather than a residualizer with a proof of execution meaning.
The final theorem targets **admitted TypedSource before specialization and pre-evaluation**.
Required proofs cover correspondence of actual pre-evaluation with source evaluation, constant embedding, branches/short-circuiting, effects, erased staged cells, and the runtime heap.
Intermediate lemmas may assume `StagingCorrect`; the final theorem must supply that proof from success of the actual pass.

Do not retain runtime stage validation from the typed runtime, together with its runtime AST interpreter, merely by renaming it comptime.
Complete evidence resolution and helper-frontier construction for compilation plans during compilation as well.

## 6. Representation and proof contract

### 6.1 Representation relations

`Representation` includes at least type instances, Core code IDs, local lambda instances, and a correspondence between source locations and Core cells.

- Extend the relation on allocation without relocating existing locations or breaking aliases.
- Do not require a one-to-one correspondence for source descriptor cells, erased staged cells, and Core administrative cells.
- Relate nominal payloads and mapping entries structurally.
- A generalized closure may correspond to multiple monomorphic Core code instances, but they share the captured mutable cells.
- The closure relation requires registered code and its corresponding capture environment, rather than mere function-type equality.
- Initially represent monomorphic locals with explicit cells wherever possible. Consider eliminating unnecessary cells after proving the correspondence.

General Core safety is stated under code table `Δ` and store typing `Σ`.
cellRef checks its type in `Σ`; separately typing the store, including closures, under the same `Σ` supports cyclic heaps.
Type preservation does not require a definition that recursively traverses heap contents without bound.

### 6.2 Initial premises of the final theorem

```text
compile(S, entry) = Ok C
SourceAdmitted(S)
EntryValid(S, entry, sourceInputs, sourceHeap)
ProgramRel(S, C, R0)
InputRel(R0, sourceInputs, sourceHeap, coreInputs, coreStore)
```

`ProgramRel` is a separate proof result constructed from compilation success and admitted source, rather than a hole requiring the caller to assume meaning preservation.
It records definition provenance and structural correspondence of types, specialization, and code, rather than equality of final execution results themselves.
Construct the required typed-input / store conditions from successful public input validation.
Keep proofs for the entire raw parser / resolver separate from the main lowering theorem. Record remaining source-checker bridge premises as unfinished until their actual proofs exist.

### 6.3 Preservation and reflection of finite observations

For normal completion in both directions, existentially quantify an `R1` extending the same initial relation `R0`.

```text
SourceEvaluates(S, entry, sourceInputs, sourceHeap, v, H)
  → ∃ fuel, vC, HC, R1,
      Extends(R0, R1)
      ∧ CoreRun(C, coreInputs, coreStore, fuel) = Done(vC, HC)
      ∧ ValueRel(R1, v, vC) ∧ HeapRel(R1, H, HC)

CoreRun(C, coreInputs, coreStore, fuel) = Done(vC, HC)
  → ∃ v, H, R1,
      Extends(R0, R1)
      ∧ SourceEvaluates(S, entry, sourceInputs, sourceHeap, v, H)
      ∧ ValueRel(R1, v, vC) ∧ HeapRel(R1, H, HC)
```

Relate specified faults and their heaps in the same way.
Translate failure reasons containing source locations through `R1` and the diagnostic map rather than requiring raw index equality.
Prove absence of internal MachineFault for arbitrary finite fuel, type preservation of suspended states, and resumption with additional fuel in the Core layer.

This correspondence of finite observations in both directions does not require new source small-step semantics.
It prevents compilation from introducing divergence for terminating source executions or normal completions absent from the source.
It does not automatically establish equivalence of infinite traces, overall source progress, or correspondence with a source prefix leading to outOfFuel.

### 6.4 Completion checks against circular premises

- Source semantics must not define results using the old evaluator or generated Core.
- Compilation success alone must not define source validity.
- Plan replay equality must not substitute for complete dynamic reachability coverage.
- Core checker success must not substitute for meaning preservation.
- The outcome relation must not be so weak that lowering can discard an entire admitted program.
- Do not relate every scalar to the same value. Function values must constrain code and captures.
- Do not leave unproved `StagingCorrect` / `SpecializationCorrect` or caller-supplied simulation in the final theorem.
- Check success/fault exclusion, required determinism, and rules for reachable legal faults over the target scope.

## 7. Dependencies of the Core safety change (initial implementation record)

Dependencies found at the start of the audit and their state after general-cell admission was implemented:

- `CellPayload` remains as a first-order helper predicate, but was removed from the premises of `HasType.newCell/loadCell/storeCell` and the executable checker.
- `ConstructorPayload` corresponds to general `Ty.WellFormed`, allowing functions and general cells.
- The pure machine's `StateHasType` and finite `evaluation_preserves_type` use `RuntimeStoreHasTypes`. `BoundedSafety` covers world extension and typing of suspended states and completed values.
- `ReducibleValue` / `ReducibleEnvironment` and the unconditional normalization proof were removed from `Core.Safety`. Completion and sufficient-fuel APIs for closed/Program execution require finite `Evaluates` evidence.
- The sufficient-fuel API of `ContractRuntime.CheckedCoreProgram` also requires finite evaluation evidence. Guarantees for arbitrary fuel use bounded safety and resumption.
- The old `StoreHasTypes` remains in conditions for first-order input and exact-store lemmas. General heap correspondence with changing closure captures does not require literal equality of final stores.
- Full builds and tests validated the corresponding changes to host state, frontend, ContractRuntime, and existing Core Wire. Language-trap propagation and validation of the new public input format remain unfinished at this point.

Individual Lean checks of `CoreGeneralCells` proved checker acceptance of a program that constructs a self-referential closure from an empty store, a 7-step cycle, absence of finite successful evaluation, and typed suspension/resumption for all fuel.
The example uses a `Unit → Unit` cell with a placeholder initial value, so it does not resolve uninitialized cells or a general source-recursion representation.
`CoreRecursiveCells` also checks terminating self-recursion and mutual recursion, use as a function argument, a counter shared across calls, returned references and captures, exact fuel, and typed resumption.
Uninitialized cells, recursive initialization for arbitrary source types, and language traps remain; T1 is unfinished at this point.

## 8. Scope of the first proof unit

New module: `Solcore/SourceSemantics/CoreLowering/StagedValue.lean`.

The implemented small scope covers:

- Interpretation of existing `SourceStagedValue.Value` as an independent source value.
- The scalar/product source–Core representation relation, its range, and uniqueness.
- Source-value typing under arbitrary source heaps and contexts.
- The actual `toCoreExpr` returning the corresponding value without changing any Core store.
- Preservation and reflection of that declarative execution, and completion/reflection for execution with fuel.

This proves correctness of **staged-value reification**.
It does not prove that the staged evaluator computed the value correctly, or correctness of arbitrary source-expression lowering, shared heaps, recursion, or failure.
Reuse it as the first connection between independent SourceSemantics and the existing implementation.

Validation: `lake env lean Solcore/SourceSemantics/CoreLowering/StagedValue.lean` succeeded.

## 9. Actual lowering from literal trees

Added module: `Solcore/SourceSemantics/CoreLowering/Literals.lean`.
Internal proof wrappers and computation rules for unit / Bool / Word / pair were added to existing `SourceCoreElaboration`, reusing its expression traversal unchanged.
No new lowering algorithm or public source API was introduced.

`Literals.Tree` is an independent finite-tree grammar for actual source occurrences.
It includes empty tuples, builtin Booleans, compatibility Word literals within range, and recursive combinations of two-element tuples.
It requires exact type information for every node, empty requirements / coercions, and global occurrence uniqueness.
The Word premise matches existing strict lowering; agreement with the source's modulo semantics was separately proved for values within range.

The proofs establish:

- With sufficient traversal budget, the existing expression lowerer and `Resolved.Expr.lower?` actually return the corresponding Core expression.
- Core checker success for that output.
- Construction of an independent `Dynamic.ExpressionEvaluates` derivation, with the same value and final heap for every successful derivation of the same source tree.
- Correspondence in both directions between the actual generated Core expression and finite successful source results, without changing either heap/store.
- Sufficient execution fuel from finite source evaluation, and reflection of source evaluation from a completed Core execution.

Compiler success is not a grammar premise. Evidence for `ExpressionLowers` is constructed before composition theorems that assume it.
General source determinism, staged-evaluation correctness, and source-inference soundness are not used as unproved assumptions.
This scope does not cover general expressions, Integer literals, groups, arbitrary tuple arity, shared cells, failures, staging computations, or whole-function lowering.

Validation: the affected Lean files, `lake build`, `lake test`, and the kernel-policy check succeeded.
The lowering-proof umbrella is registered in `Tests/Main.lean`; the independent specification umbrella does not import the frontend.

## 2026-10-01: Grouped root-tuple observation mismatch and approved fix

At the time of this investigation, the parser/checker and explicitly selected typed-source compiler accepted the following program.

```solidity
function main(left: Word, right: Word) returns (Word) {
  match ((left, right)) {
    case ((x, y)) { return x; }
    default { return 99; }
  }
}
```

For inputs 7 and 8, the old evaluator returned 99. The validation log is
`/private/tmp/solcore-grouped-tuple-runtime-audit-2.log`.
The tuple branch of `SourceTypedRuntime.matchPattern` reads elementCount only when `pattern.source` is directly `.tuple`; it uses 0 for `.group`. Unpacking the tuple value fails and selects the default arm.

Independent SourceSemantics treats groups transparently, so this match binds x=7 and y=8 and returns 7.
On 2026-10-01, the user approved aligning the implementation with the independent semantics. The new Core lowerer recurses through groups, and the old runtime also reads tuple arity through groups. The old runtime's internal nested-pattern search bound was changed to 2 times the instruction count + 1.

At the time, `Test.SourceCoreGroupedTuple` checked multiple parentheses, nested tuples, Unit, literal arm selection, and side effects using actual checked programs in both Core and the old runtime. Registered tests now use public and internal Core paths. Repeated Core execution and resumption from a zero-fuel checkpoint were also checked. `DataPatternCertificates` and `Test.SourceCoreDataPatternProofs` prove static extraction of grouped roots, independent PatternMatches, finite execution of authenticated binder values, and reflection. The log is `/private/tmp/solcore-grouped-tuple-fixed-run-4.log`. No change to checker/staging acceptance conditions was needed.

## 2026-10-01: Additional audit of staging and public closure boundaries

`SourceCoreStageContracts` authenticates original analyzer outputs and parameter/result flags for named, lambda, and contextual-lambda functions. `SourceCoreStageCodebook` assigns a contract ID to each owned origin and preserves the existing validator's decision at each indirect callsite. The ID is independent of function identity.

The old indirect execution order is callee → stage guard → arguments/coercions → applyCallable arity check → parameter allocation → body. An effectfulStaging caller skips the stage guard but keeps the arity check. An effectful fixture accepted by the public parser/checker/forced typed compiler passes two scalar arguments to one tuple parameter and returns argumentArityMismatch 1 2 after both arguments modify the trace. No parameter cells are allocated, and heap typing is preserved. Reproduction: `/private/tmp/solcore-staged-arity-public-audit.lean`. The original applyCallable checks arity before bindValues; bindValues also checks value types before allocation.

The independent `Dynamic` indirectCall/argument fault rules at this point lack the stage guard's acceptance premise and stage-fault rules. Metadata agreement with an existing validator does not complete independent source meaning preservation.

Internal DeepSafety does not distinguish missing or renamed captures. Public `Value.validateTypeFuel`, however, rejects raw closure/instantiated-closure values even inside products, data, and mappings. Public function inputs resolve from global/builtin references. A clarification question based on inferring public-input scope from internal checks was withdrawn; no approval to reduce features was sought.

A malformed closure that passes internal DeepSafety can be placed in an unused initial-heap prefix; that prefix remains after a successful global call. A global's initial lexical environment is empty, and input allocation begins after the prefix. Public inputs provide no constructor that refers to a prefix location. The full unreachability theorem and observation preservation for opaque prefixes are next steps. Rejecting every prefix does not establish preservation of old features.

### Output metadata for generalized locals and nested lambdas

`directLambdaLetBinder?` detects only polymorphic binders. Do not add a new `.instantiated` wrapper to local reads of monomorphic lambdas.
Even when the same generalized initializer is read at the same concrete type multiple times, `ownWitnesses.actualRequirement` differs at each read occurrence.
The native code ID for `(initializer, cumulative substitution)` alone therefore cannot reconstruct the old wrapper's own substitution/witnesses.
Preserve occurrences using cached `CallableViews` and ordinary Core lambda wrappers retaining descriptor/anonymous identity.

When the body invoked through such a wrapper creates a nested lambda, the old runtime also rewrites original Source requirement IDs according to the read occurrence.
Authentication of a static parent receipt and exact native lambda template cannot by itself recover this dynamic difference.
Connect the following metadata transport separately from completion of template authentication:

- Represent callable ancestry with ordinary Core recursive nominal data. Distinguish named boundaries, ancestry at lambda creation, and local-read views.
- Give the artifact a single administrative context cell. Do not add it to the source allocation ledger.
- A local-read wrapper saves the view frame immediately before invoking the original payload, then restores the caller frame on both success and language failure. Fuel exhaustion retains it within the Core checkpoint.
- A lambda captures its lexical ancestry at creation through a pure let. Calls use that snapshot and add only the immediately preceding view frame for the same lambda.
- A named call uses its own metadata boundary. Do not apply unrelated caller local views to principal source metadata.
- Authenticate output by checking owned views/templates, exact native bodies, global slots, capture ledgers, and ancestry correspondence, rather than a word alone.

This connection is in progress at this point. Restoration of the whole source heap, including lambdas/principals, and switching public typed-source routing are not yet complete.
These changes do not add Core kernel syntax or machine instructions.

## 2026-10-01: Public source values with raw metadata

The actual `checkProgram` → forced typed compile → public `runTyped` path showed that the old public boundary accepts raw metadata equivalent under `runtimeType`. Reproduction: `/private/tmp/solcore-public-source-boundary-audit.lean`.

- A `.proxy (comptime Word)` key in `mapping(@Word => Word)` is accepted by type validation. `table[@Word]` does not match that key and returns default 0; a canonical `.proxy Word` key returns the stored value 7.
- Constructor metadata `Box<comptime Word>` is accepted as a `Box<Word>` input and remains in an echo result. A canonical `Box<Word>` pattern does not match a value with different raw metadata and selects the default arm. The number of allocated pattern binders also differs.
- An empty `mapping(Word => @Word)` with raw valueType `proxy(comptime Word)` is accepted. A missing lookup returns `.proxy (comptime Word)`. The default is built from the actual mapping header's valueType rather than the static expected type.
- Scalar globals in the plan and the builtin `wordToInteger` are accepted as function inputs. Initial-heap prefixes containing existing valid closures and uninitialized `.error` cells are also accepted and retained in the result heap.

Strict raw-metadata equality in `SourceCoreDataValues` / the owned session codec is therefore insufficient to finish the adapter for old public values. The compatibility profile retains authenticated raw-metadata Word IDs in Core carriers at canonical runtime types. Nominal matching, proxy-key equality, result restoration, and source-cell restoration use these IDs. A mapping carrier retains a raw-header ID, authenticated optional default, and ordered entry sequence; updates preserve the header/default. Missing-default diagnostics use a token that recovers the raw valueType and callsite.

A hidden match scrutinee is an actual old-source heap cell and must be exported. Keep it distinct from administrative cells for globals, loops, comparisons, and mapping helpers. Its type is the runtime type of the old runtime value; do not restore the raw expression annotation directly as the cell type.

Preserving these differences does not require Core kernel extensions. The new registry/helpers use ordinary Word, product, sum, data, and function representations. Their connection to the public runtime and typing/meaning correspondence are validated separately.


## 2026-10-08: Current status

### Execution and public boundary

The first goal was completed on 2026-10-01 in `a3168382`. `SourceCompiler` reexports `SourceCoreExecution`. Common artifacts and sessions execute cached Core code prepared by `SourceCoreCompiler → SourceCoreUnifiedCompilation`. Backend preferences, fallback, the old session implementation, and runtime typed-source expression/statement/call evaluators have been removed.

The raw metadata, grouped tuples, stage/arity evaluation order, callable views/ancestry, inert initial-heap prefix, and distinction between source allocations and administrative cells found in the initial audit have been incorporated into compatibility carriers, public ownership, snapshots/full prefixes, and regression tests. Public Value does not expose source closures or arbitrary native references; function calls authenticate owned handles. Historical raw heaps migrate through the explicit `SourceCoreLegacyHeapImport` boundary.

The `SourceTypedRuntime` namespace remains for compatibility values, observations, and validation data. The namespace and tests named after old features do not demonstrate survival of a runtime evaluator. Existing comptime direct evaluation remains in preparation as agreed. Unifying that evaluator with Core and adding source contract/storage/external-call connections belong to the next phase.

### Latest proofs and validation scope

| Commit | Proved scope | What this unit alone does not complete |
| --- | --- | --- |
| `618cd059` | Connects acceptance of pure `elaborateFunction` with staged Integer lets to the full original Source heap, actual Resolved/Core results, and reflection of original finite Core completion. | The full-state theorem for the public unified path. No Integer-let erasure was added to that path. |
| `85da3f04` | AuthorityPool invariants for ordered ownership keys with duplicates, shared physical frames, and retained snapshots/records. | Pool integration with function values and general call bodies; no coverage claim for all physical heap snapshots. |
| `a3e0f4ab` | Derives lambda template permission from actual prepared inventory, the same full source/table row, and compiler receipts. | Runtime catalog authority and body meaning preservation; static permission does not imply them. |
| `0bb0c9ee` | Connects additional children to the same compiler induction, preserving original policy, predecessor fuel, independent Source typing, duplicates, and order. | Mutual induction closing the execution meaning of callees, arguments, and general bodies. |

Shared registration, concrete ownership and actual lexical/imperative producers are committed. The latest implementation point is `4521c209`. The CatalogSites fold, origin-neutral body kernel and named body family consume actual states. Named and anonymous parameter prefixes, frame installation, invocation and caller restoration retain the body's exact reached record vector. Actual ordinary/direct call heads pass ordered argument states into live Capture acquisition. A proof wrapper carries original canonical slots through lexical prepend/restore and genuine marked allocation.

Data, builtin and tuple producers now forward actual child posts through the unchanged expression Tree fold. The closed named body/caller family derives strict callee callbacks internally from authentic static profiles; its final public methods take no expression/body meaning premise. Runtime mode retains full evidence and the requirement ledger. Formal consumers exercise complete Header-based ordinary/direct calls and an ordered tuple containing a call with nonempty Source/native Boolean arguments. Selected accepted indirect lambda calls now retain the complete callee receipt and the actual argument, parameter, body and restored posts, including argument faults. Actual method invocation is connected, and builtin method bodies close internally. A concrete anonymous empty-Unit consumer also closes its body internally. Arbitrary indirect dispatch and general method/coercion bodies remain incomplete.

Original `Prepared.HeaderAt.layouts` provides full layout equality. Canonical slot receipts come from authentic Header bootstrap construction, actual input Entry globals or complete Capture coherence. Pool authority alone does not prove a canonical slot. Selected-frame `BodyAuthorizationAt` retains the original owned-id, Carries and code receipts while adding the actual physical frame equality, from which concrete allocation readiness is proved. Raw Source capture declarations and generalized storage metadata also require genuine Source validity; native type projection cannot supply them.

The latest proof-umbrella and `Tests.Main` build passed **5173 jobs**, all registered `lake test` executions passed, and the latest strict audit checked **4100 declarations** using only the permitted standard axioms. Fresh inventories cover **219 declarations** in nine modules. All **105 original declarations** have exact raw type/axiom matches and independent original literal Expr.eqv/axiom checks; no helper was relocated. All **49 signature probes**, semantic policy and whitespace checks passed. **5019 original files** outside explicit owned changes remained unchanged. Records: `/private/tmp/solcore-owned-functions-resume-20261007/catalog-body-ready-validation.json` and its logs.

The shared measured family supports a separate protocol and dependent record type for each genuine origin. Actual lambda and method parameter continuations wrap authentic canonical slots at the exact entry. Selected indirect calls retain the actual caller protocol independently of the selected closure's captured owner/prefix. The same actual body pool is restored and wrapped at the caller's original scope and captures. Receipt-aware named and indirect caller bridges now return stronger formation packets at the same actual body post using genuine cumulative effects. The named entry factory authenticates its original Source seed from the actual Header record and carried history.

Actual named lambda views and genuine nested formation leaves are registered. They retain original frame references, bundle tags, Source captures and metadata from reached own Current receipts and real physical reads. Their static helper boundary explicitly retains capture prefix zero and caller prefix one. The packet survives genuine lexical allocation, restoration and named calls. Actual nested expression head callbacks consume the packet at real child inputs. The same original expression Tree and measured shared family now close nested named bodies and expressions without outside body/expression execution laws. Actual anonymous parameter entries retain their genuine full capture spine and expose pointwise continuations. Nested anonymous bodies now close expression and named callee meanings internally through the original kernel and closed named family. A genuine named-body formation consumer is registered. The original formation producer supplies a selected ClosureAt with exact owner, prefix one, complete captures and Source seed; arbitrary ValueRep inversion does not recover that receipt. General indirect/method branches and all static factories remain incomplete.

Complete outer Source adapters and a closed full indirect expression consumer construct actual callee reads, a Boolean argument, singleton Source allocation and the nil body internally. A selected method consumer now also derives genuine typed bootstrap capture and whole empty Source heap relation, full Source admission at the same marked allocation, and internally closed builtin Source/native invocation. Internally closed actual method coercion steps compose an ordered path through the existing folds, threading real intermediate and final states through the actual protocol relation. A fault retains the reached pool and skips subsequent steps. These consumers retain actual returned pools and independent grades. The whole outer method operator, live caller transport, nonempty initial Source prefixes and general body families remain unfinished.

Authentic method principals now retain independent TraitMethodInstantiates, the complete selector/dictionary and cached Source body. Genuine hook history authenticates the emitted method seed at actual parameter posts. The new generic origin packet requires no ordinary Header and retains the same real pool, reads and complete records. A Boolean parameter consumer derives actual Source admission and preserves strict native children and the original saved-frame write. The compiler's synthetic function does not establish top-level Source function authority. Existing lambda static support still requires an ordinary Header; method-produced lambda origins remain a separate unproved model extension.

The authentic method continuation providers now consume the exact hook history and parameter packet. Builtin method bodies and complete invocation close internally through the existing shared measured family using real marked allocation. A typed-bootstrap Boolean consumer retains the same restored pool and every ordered record observation. General method-produced lambda support and live caller transport remain separate.

Raw Source capture validity follows from genuine Source formation, typing or whole Source expression preservation. Actual parameter admission for named functions and selected methods derives the complete original Source certificate internally from genuine instantiation/selection and whole-program validity. Initial Source heap and raw argument validity remain explicit, and their extraction at the actual public boundary is unfinished. No Core type projection is used to infer Source declarations or dictionaries.

Literal indirect call selection now uses the authentic formation producer at the same caller state, retaining the exact emitted callee and its full closure receipt. A separate closed continuation specialization consumes the real argument pool through the existing named/anonymous body grammar. The Source/native parent still requires genuine pointwise input admission and already closed ordered argument meaning. New admitted expression contracts derive successful value and deep heap typing from real Source traces at the exact reached state; the two-child packing consumer passes that actual successful admission to its next child. Faults retain the actual pool and all-row stable history. No deep Source heap typing or uniform input admission is inferred from administrative metadata extension or a bare selected-row packet. The admitted ordered sequence now instantiates the same indirect call providers at the real callee post. Actual selected literal Head callbacks retain that admitted input and successful post. The complete shared mixed family remains necessary.

Authentic named, lambda and method Source parameter receipts now wrap the complete original body Entry with genuine heap typing and all-row history. Real carried hook installation and parameter effects preserve that same pool. The existing complete FunctionStatements preservation core derives successful body value and heap typing, including the implicit final expression. Faults retain stable rows without a deep heap-typing claim. These wrappers strengthen already closed producers; the general CatalogSites/kernel still require admitted child inputs. Original parent typing supplies an ordered argument/value row independently of native types. Actual absent and initialized lexical allocation now preserve the complete original allocator output while deriving deep heap typing from genuine Source allocation and raw value typing. The same reached state is admitted in its genuine next Source context. Composition, tuple and builtin Head adapters now derive raw Source operand rows from genuine parent typing and consume admitted children at actual inputs. Their shared original cores retain the real guarded builtin environment, left-to-right order, short circuits and selected branches. Source success admits the exact returned witness; faults retain stable rows. Admitted constructor/member/index providers now retain actual child states and genuine parent typing. The existing lexical Tree folds consume authentic contextual Source syntax, actual initializer/allocation posts and restoration at the same reached state. Suffix facts are requested only after genuine fallthrough, preserving accepted dead code. Named invocation now requests its body continuation at the actual parameter state. The same five-way control proof cores now consume actual readiness and authentic Source facts, retaining the real tail or selected-branch input. Named ordinary/direct Heads select invocation continuations after actual argument evaluation. Genuine Source declaration typing, argument preservation, Header certificates and actual arity derive the raw callee context and argument types. Full actual named parameter receipts now construct pointwise admitted entries. Internally closing their body callbacks and connecting assignment, loops and match through CatalogSites remain in progress.

Shared expression dispatch now consumes genuine parent typing and admitted child providers at actual inputs. Bare assignment uses the actual RHS snapshot and written or fault prefix, preserving the real seven-slot native continuation. Successful Source assignment derives admission at the actual written heap. Ordered place key providers retain every Source occurrence and use the pointwise sequence producer at the real protected root input. Source projection typing derives the independent raw key row, and genuine resolution admits the same reached getter heap. The admitted projected assignment adapter now consumes the actual whole-key and getter/RHS producers. A shape dispatcher retains the same actual bare or projected write/fault output and strict native continuation. The same while proofs now carry actual readiness at condition, body and recursive posts. High while factories now retain actual Source condition/body facts and admitted posts. Authentic same-code body Trees derive their reflection control restriction. For/match readiness and general imperative closure remain unfinished.

The admitted named adapter retains the full actual parameter BodyState, original globals, selected physical hook and carried history. Its canonical and nested entries keep the same Source receipt and rows. Body callbacks target that exact computed entry; they still need internal discharge by the shared family. A generic typed BodyEntry alone supplies neither canonical global slots nor the named Source seed. Imperative facts now retain original Source assignment legality, Boolean while conditions and complete ForItems judgments independently of compiler syntax. Suffix typing is transported only after actual fallthrough by the existing dynamic final-context proof.

A closed no-expression named receipt consumer now proves that pointwise body callbacks can be constructed internally at authentic full parameter receipts. It uses the real marked producer and existing singleton mutual family, retaining the exact original entry and body pool. Its bounded grammar does not close general mixed, indirect or method bodies. Generic while reflection retains its original control-fault restriction; an authentic same-code body compiler Tree can discharge it through the existing control-shape theorem.

The restricted admitted expression Tree now closes ordinary/direct named callees internally from authentic full parameter receipts, real marked producers and the existing singleton mutual family. Its callee grammar has no executable expression leaves; this does not establish the general mixed body family. Match admission helpers derive raw Source case/default typing and preserve deep heap typing through genuine hidden and binder allocations at actual states. The selected-prefix/body execution composition still requires the next readiness cut.

For iteration now retains the actual condition/body/post states, readiness and real recursive self-cell reads. Genuine ForItems traces establish Source heap typing at both original and static final contexts through actual Source preservation and runtime context fields. Function finish preserves the same reached flow witness and converts escaped controls to fault history without rebuilding state. A literal-false while consumer closes its Source/native completion and nil-body proof internally, retaining real physical reads. For header/post, full match readiness and general CatalogSites/body closure remain in progress.

The match cores now carry actual readiness through scrutinee, selected prefix, body and restoration. High Source admission uses real hidden and pattern allocations at a single actual selection post, without a fabricated intermediate protocol state. Genuine cases and body typing remain independent of Core representation. Faults retain actual stable rows, and restoration retains the same returned body pool. High parent adapters and the existing CatalogSites/body closure remain in progress.

High match endpoints now derive original scrutinee/cases/default typing from the actual parent Source judgment and occurrence uniqueness. Their actual selected-body callbacks retain compiler and Source receipts separately. Actual bit-not snapshot/write traces now establish reached heap admission through already proved Source preservation; no external expression execution law is assumed. These receipts still need composition into the original CatalogSites fold and general mixed body family.

For headers now retain readiness through actual initializer children, allocations, assignment and snapshot writes, and the exact tail. Genuine Source item typing selects facts only at visited contexts. Successful initializer traces identify runtime/static final contexts and retain deep Source heap typing in both contexts. Post restoration uses the actual tail state, genuine Source binder restoration and real loop progress. High for endpoints retain the original parent Source judgment and independent condition/body/post facts; the same-code compiler body Tree derives the reflection control restriction. General ready CatalogSites/body closure remains in progress, including the authentic normalized initializer receipt. No administrative metadata rule is used to derive deep Source heap typing.

Original actual parameter Source receipts now construct genuine body typing beside a separate authentic compiler syntax receipt. A closed false-for consumer with nil initializer/body/post constructs both Source and native completions internally, retaining the actual reached readiness, every ordered row and real physical self/frame reads. Its native witness is the original self-cell producer; Source preservation identifies the same store by evaluation determinism. This consumer does not establish general loop bodies or mixed dispatch. The original ready CatalogSites folds and body flow/finish compositions are integrated. Their complete original entries, actual Source facts, reached readiness and ordered pools are retained. The ready measured family and complete mixed dispatch remain in progress.

The same two CatalogSites folds now carry genuine facts through lexical, allocation, assignment, snapshot and five-way control producers. Finite while/for/match recipes retain authentic static receipts and only smaller child goals. The genuine initializer judgment follows original contexts to the nil continuation, retaining its loop facts and inclusive loop bound. The callable body composes that actual flow post with the original finish proof, retaining ReachedExit and readiness at the same returned state. Legacy APIs have exact original types. Ready origin entries retain the complete actual original Entry and pair independent Source typing with authentic compiler syntax. No extra execution or Tree induction is introduced. Closing these contracts in the measured family and deriving complete public origin factories remain unfinished.

### Remaining audit and proof obligations

- Preserve full captures, original named/lambda Source provenance, caller/lexical frames, and the actual AuthorityPool under the same function-value and heap model.
- Connect callees, arguments, general bodies, methods/coercions, local instances, and application views to the same mutual induction. Actual indirect continuations now select the real argument post; final mixed closure must supply them internally from strictly smaller body obligations. Retain records added during calls through restoration.
- Relate specified failures and all preceding state as well as normal results. Positive missing-default rules have been added, but whole-syntax/whole-failure coverage and the final theorem remain unfinished.
- Compose actual specialization, evidence, and pre-evaluation passes to prove preservation and finite completion reflection from independent Source before pre-evaluation to actual public Core execution. Correctness of current passes belongs to the second goal even though comptime backend unification is deferred.

The old temporary Values and Entry fragments have been replaced by committed modules. Ordered expressions, ordinary/marked allocation, lexical restoration, all assignment outcomes, finite while/for, headers, five-way control, selected match and function finish retain actual post-witnesses. The outer imperative fold and origin-neutral body kernel now carry actual states. Named body/caller expression families reuse the measured mutual fold, and actual parameter/restoration consumers use real allocator receipts. Closing general indirect/method/coercion dispatch, every static factory and the full compiler theorem remains incomplete. A generic prefix transition does not establish exact fresh snapshot membership; that claim requires the concrete allocator receipt for the same execution. See the [implementation record](core-runtime-unification-progress.md) for the current boundary and validation scope.

The language's `mapping(K => V)` in this audit is a dictionary type. `SourceStagingHeapRelation.LocationMap` and similar definitions are proof tables relating cell locations; they are a different subject. Do not count ordinary Core administrative cells, retained Source cells, and Integer cells erased by pure staging as the same set of cells.
