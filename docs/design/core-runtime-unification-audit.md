# Core unification: T0 audit of features, semantics, and proof boundaries

Initial audit: 2026-09-30. Last updated: 2026-10-09.

This document preserves the initial audit for the [implementation design](core-runtime-unification.md) and subsequent dated investigations. Sections 1–9 record the state on 2026-09-30; later sections record the state on their respective dates. References to the "current" implementation, "unfinished" work, "next steps," or old API names describe that historical state.

Runtime Core unification was completed in `a3168382`. See the [API migration record](core-runtime-unification-api.md) for the current public entry points. The [implementation record](core-runtime-unification-progress.md) and the latest dated audit section describe the latest commits, validation, and uncommitted work.

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

Shared registration, concrete ownership and actual lexical/imperative producers were verified at the earlier `4521c209` checkpoint. The CatalogSites fold, origin-neutral body kernel and named body family consume actual states. Named and anonymous parameter prefixes, frame installation, invocation and caller restoration retain the body's exact reached record vector. Actual ordinary/direct call heads pass ordered argument states into live Capture acquisition. A proof wrapper carries original canonical slots through lexical prepend/restore and genuine marked allocation.

Data, builtin and tuple producers now forward actual child posts through the unchanged expression Tree fold. The closed named body/caller family derives strict callee callbacks internally from authentic static profiles; its final public methods take no expression/body meaning premise. Runtime mode retains full evidence and the requirement ledger. Formal consumers exercise complete Header-based ordinary/direct calls and an ordered tuple containing a call with nonempty Source/native Boolean arguments. Selected accepted indirect lambda calls now retain the complete callee receipt and the actual argument, parameter, body and restored posts, including argument faults. Actual method invocation is connected, and builtin method bodies close internally. A concrete anonymous empty-Unit consumer also closes its body internally. Arbitrary indirect dispatch and general method/coercion bodies remain incomplete.

Original `Prepared.HeaderAt.layouts` provides full layout equality. Canonical slot receipts come from authentic Header bootstrap construction, actual input Entry globals or complete Capture coherence. Pool authority alone does not prove a canonical slot. Selected-frame `BodyAuthorizationAt` retains the original owned-id, Carries and code receipts while adding the actual physical frame equality, from which concrete allocation readiness is proved. Raw Source capture declarations and generalized storage metadata also require genuine Source validity; native type projection cannot supply them.

That earlier proof-umbrella and `Tests.Main` build passed **5173 jobs**, all registered `lake test` executions passed, and the latest strict audit checked **4100 declarations** using only the permitted standard axioms. Fresh inventories cover **219 declarations** in nine modules. All **105 original declarations** have exact raw type/axiom matches and independent original literal Expr.eqv/axiom checks; no helper was relocated. All **49 signature probes**, semantic policy and whitespace checks passed. **5019 original files** outside explicit owned changes remained unchanged. Records: `/private/tmp/solcore-owned-functions-resume-20261007/catalog-body-ready-validation.json` and its logs.

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

The same measured callable family now consumes genuine Ready inputs and actual Source runtime origins. The finite Catalog and body adapters retain the full original actual entry and reached state. A closed named false-while consumer constructs Source execution internally and separately reflects the original measured native completion through that family, including real parameter/frame observations. This establishes the bounded false-while body; general call and formation dispatch remains unfinished. Verification at `5da8a5bb` passed the 5179-job normal build, all registered tests, strict kernel audit of 4241 declarations, fresh inventories of 148 declarations, all seven original literal/type/axiom checks, 39 signature probes and the kernel policy. The 5019 protected original files are unchanged.

Finished mixed body closure requires the authentic canonical or nested protocol at the same parameter entry. A base owned pool has no caller Globals or captured Source seed. Those facets must be retained from actual Header globals, complete capture spines or genuine method principal/history receipts, then projected away at the same returned pool. No administrative metadata rule supplies deep Source heap typing.

The public session keeps valid inert prefixes separately from its empty active Source bootstrap heap. Existing heap migration proves reconstruction and prefix preservation, without a whole execution correspondence. A theorem executing Source over a nonempty initial prefix therefore needs an authentic complete heap relation or a proved prefix execution relation. The existing fresh public root entry is constructible for the empty active Source heap.

Actual named parameter receipts now choose the complete static family index internally from their original profile, member, Source runtime validity and independent Syntax. The actual canonical entry supplies global slots; the original admitted expression Tree consumes strict family children for arbitrary authentic ordinary/direct named callee profiles. Runtime literal meanings come from the real requirement ledger. Actual lambda/method wrappers retain genuine captured or principal packets beside the same Source receipt and all-row history, then forward the same returned pool. These adapters reuse the existing folds and do not establish joint mixed dispatch.

Method lambda sites now retain original Source provenance, graph uniqueness, genuine carried history and emitted descriptor from the actual selected method principal. The owned lambda StaticSupport remains Header-based; a method-only principal requires an explicit support alternative before the current value model can represent it. No ordinary Header or FunctionInstantiates is inferred from synthetic compiler code.

Verification at `ed314136` passed the 5190-job normal build, all registered tests, strict kernel audit of 4375 declarations, fresh inventories of 71 declarations in six new modules, 37 signature probes and the kernel policy. No original proof module changed in this unit, and the 5019 protected original files are unchanged. General named closure, joint origin factories, mixed dispatch and the compiler/public theorem remain unfinished.

The general ordinary/direct named family now closes its own body and recursive expression obligations through the existing measured family and original admitted expression Tree. The runtime expression endpoints assume only the genuine static and Source receipts, deriving literal meanings internally. They carry no outside completed expression or body execution law. Actual lambda and method entries construct the matching dependent family index at their original parameter post; strict continuations return the identical underlying pool and full exit. Genuine method occurrence typing now proves the exact lambda closure frame without an ordinary Header.

Verification at `6d4bfd65` passed the 5195-job normal build, all registered tests, strict kernel audit of 4474 declarations, fresh inventories of 99 declarations in five new modules, 29 signature probes and the unchanged kernel policy. No original proof module changed in this unit, and the 5019 protected original files are unchanged. Joint origin factories and expression dispatch, method-generated lambda support, static public extraction and the compiler/public theorem remain unfinished.

Genuine method-principal lambda support now exists as an additive alternative to the ordinary Header-based model. It retains the same compiled Code, full captures, carried history and independent Source method origin. Original representations lift forward into the new model; erasing a new representation does not recover an ordinary Header. Authentic principal packets derive lambda formation history, the captured bundle and the real frame slot. The admitted formation leaf preserves the exact packet, Source heap and native store and reflects completion with an independently constructed Source size.

The extended joint Family reuses the existing measured closer for named, ordinary lambda, method, nested named and method-lambda origins. Actual parameter continuations select only their genuine dependent index. In particular, an ordinary lambda entry supplies the original full layout equality at that actual selection; a universal transport for arbitrary standalone static lambda indices is not assumed. The mixed expression dispatcher remains incomplete.

The public ordinary/direct named runtime connector derives layouts from the original prepared Header and uses the actual compiler bundle prefix. The closed named family supplies all body execution meanings internally. The endpoint still needs genuine interpreted static output receipts and independent Source Syntax. An arbitrary receipt's diagnostic predicate cannot be inferred from native typing or compiler acceptance; the actual producer's emitted diagnostic shape must be retained and proved.

Verification at `773d5836` passed 5200 build jobs, all registered tests, a strict audit of 4623 declarations, fresh inventories of 149 declarations and 40 signatures. Verification at `37d10587` passed 5208 jobs, all tests, 4811 strict declarations, 188 fresh declarations and 59 signatures. Verification at `ec287604` passed 5213 jobs, all tests, 4864 strict declarations, 53 fresh declarations and 25 signatures. The semantic kernel policy remains unchanged. Every final source passed parent and two independent exact-source reviews. No original proof source or runtime/fuel/Tree induction changed in these units; the 5019 protected original files remain unchanged.

Ordinary formation now reconstructs the actual capture/code/history witness from a genuine ranked static certificate. Selected ordinary and method formation keep distinct actual protocols. A selected method-lambda call retains independent raw Source argument typing, ordered argument fault/success posts, its strict dependent body continuation and the actual saved-frame restoration. Every returned packet retains the same reached pool and full ordered record vector. Method used-prefix capture projection changes no underlying heap, world, store or pool.

Concrete static method formation and selected-call heads construct their runtime receipts at each input. The existing expression support fold and actual runtime literal producer now consume these heads. No arbitrary compiler body certificate is identified with the constructed Tree. The supported expression grammar and selected literal call are narrower than complete mixed dispatch or arbitrary stored/returned callee selection.

Verification at `23d60439` passed 5216 normal build jobs, all tests, 4874 strict declarations, 10 fresh declarations and 10 signatures. Verification at `3ff3daf4` passed 5220 jobs, all tests, 5075 strict declarations, 201 fresh declarations and 37 signatures. Verification at `666f95b0` passed 5222 jobs, 5164 strict declarations, 89 fresh declarations and 16 signatures; the registered tests were unchanged by its two proof modules and passed at the preceding checkpoint. All final sources passed parent and two independent exact-hash reviews. The kernel policy remains unchanged, no runtime/fuel/Tree induction was added, and 5019 protected original files remain unchanged.

The actual for-header and statement/match static folds now retain emitted diagnostic plans and exact equations to their original predicates. The finite plan interpreter consumes genuine local Source/fault receipts and follows only the retained scoped requests. Terminal cases preserve the original unused suffix. Cached/public profile extraction uses the actual returned plan rather than an arbitrary interpreted output. This does not yet derive every public local fault token or the global prepared operand typing condition.

Verification at `145bdc6e` passed the 5229-job normal build, 5386 strict declarations, fresh inventories of 224 declarations across nine added/modified modules and 43 signature probes. The two original modules preserve all old theorem headers and unchanged source prefix/suffix. Original compatibility covers 68 raw type/axiom matches plus one relocated compiler-generated matcher checked against an independently saved original literal `Expr.eqv` and exact axioms in both private and normal objects. Both original static Syntax inductions remain unique. The unchanged registered executions passed at `3ff3daf4`; the new changes affect static proofs and certificate extraction. All three exact-source reviews, the kernel policy and whitespace checks passed. The two intentional original fold changes are excluded from the **5017 other protected original files**, which remain unchanged.

The `356a4871` checkpoint added genuine unrestricted ordinary support, exact Source-origin entries and a shared owned function relation that embeds prior method values forward. Same-model formation/selected calls retain all actual heaps, argument/body posts and caller restoration. Prepared unary/binary operators with empty output coercions retain the independently selected Source dictionary and original raw grades. Public named endpoints interpret their own actual emitted plans. Verification passed 5238 normal jobs, 5546 strict declarations, 160 fresh module-attributed declarations and 60 signatures.

The `6db08194` checkpoint connects the same-model method-lambda heads to runtime Trees and composes actual named/direct named and method-lambda calls at one genuine method caller packet. Ordinary formation uses authentic accepted Sites with unrestricted same-Code bodies and full actual capture/Source history. The compiler prefix changes only slot evidence, while the underlying pool, records, Source seed and restoration remain identical. Original expression/body folds and runtime literal producers are reused. Verification passed 5244 normal jobs, 5626 strict declarations, 81 fresh module-attributed declarations and 36 signatures. All source reviews, policy and whitespace checks passed; 5017 other protected original files remain unchanged. Registered native and interpreted tests passed at `3ff3daf4`; later units change proofs and static certificates and rebuild the test target.

At `c271f222`, actual table unary entries, for-header items and scoped statement/match children retain their owning Source sites and emitted tokens through the original static folds. Their prepared table internally supplies unary/operand interpretation; remaining place laws concern only actual assignment atoms. Verification passed 5252 normal jobs, 5782 strict declarations, 322 fresh declarations and 35 signatures. Of 187 originals, 186 raw types/axioms match exactly; one relocated matcher passes an independently saved original literal `Expr.eqv` and exact axiom check in private and normal objects. Original traversal counts and explicit headers remain unchanged.

At `b3d58921`, the same shared model retains authentic principal prefix-one globals and the leading bundle through actual formation, extension, key embedding and exact selection. Unrestricted ordinary literal calls use genuine same-Code Support, the real argument post and original strict body family. Public named runtime bounds interpret their own actual tokens internally. Verification passed 5256 normal jobs, 5858 strict declarations, 109 fresh module declarations and 46 signatures. All 27 original non-recursor model/selection types and all 33 original axiom arrays remain exact; six recursors intentionally gain a case. Every source passed three exact full-source reviews; kernel policy, whitespace and 5015 other protected original-file checks passed. Registered executions passed at `3ff3daf4`; subsequent units add proofs/static certificates and rebuild the test target.

The principal and unrestricted ordinary branches retain their actual invocation facets. Legacy prior method/ranked branches keep their original arbitrary prefixes. Assignment tables also do not justify universal missing-default/uninitialized laws over arbitrary raw types and bare roots. General stored-callee invocation, typed reachable assignment faults, full Source diagnostic typing and all-pass composition remain separate obligations. No weaker native relation or externally supplied completed body law establishes them.

At `6d74be1f`, actual public compilation retains the identical raw program diagnostic producer and exact selected specialization. Its own Header receives the corresponding assignment preparation. The unit passed 5257 normal jobs, 6028 strict declarations, 170 fresh module-attributed declarations and nine signatures; all 116 original program-fault raw types and axiom arrays remain exact.

At `08991147`, genuine ordinary lambda and principal mixed heads connect to the same original expression support fold and finite dispatcher. Actual nested captures, independent Source argument typing, parameter entry and restored pool remain intact. Runtime literals come from the actual Source ledger. Public named endpoints derive the selected assignment table internally from the retained producer. Verification passed 5263 normal jobs, 6131 strict declarations, 103 fresh declarations across six new modules and 34 signatures. All final sources passed three exact full-source reviews; policy, whitespace and 5014 other protected original-file checks passed. Runtime and registered tests remain unchanged since their actual native and interpreted executions at `3ff3daf4`.

The runtime fault audit found correct emitted categories for absent bare compound assignments, unary bit-not, nonmapping projections and compatible mapping defaults. The proof obstruction is broader quantification: the unused bare projection token is zero, while missing-default laws currently admit unrelated raw mapping headers. The next proof cut retains authentic prepared paths, actual ordered arguments and root representations at the reached key/RHS/fault states. Bare heads need only the operand law. No zero-token reinterpretation or broader fault relation is justified. Full original Source body typing and graph closure, rather than runtime validity alone, must also supply all-occurrence assignment typing.

At `5e90dffd`, full original Source body certificates and graph closure derive unary and assignment operand typing for actual ordinary and selected trait bodies. Public endpoints derive those conditions internally. Actual successful callee representation exposes complete selection; raw Source argument packing, binder-bundle equality and genuine arity recover the closure binder row at the same argument-post heap. Stored ordinary/principal payload application retains the current owner row, distinct captured history, original strict body continuation and identical restored caller pool. Verification passed 5269 normal jobs, 6218 strict declarations, 89 fresh declarations and 28 signatures.

At `d35929c6`, projected fault receipts retain the actual key/getter or RHS/live-root phase and the same terminal state, prepared path, ordered represented arguments, raw root and existing fault tree. Bare heads require only operands. Original finite cores are factored once; legacy wrappers erase receipts. Actual caller admission derives raw closure inputs internally, and map/world extension preserves the unchanged full invocation association. Verification passed 5272 normal jobs, 6250 strict declarations, 109 fresh declarations across seven new or modified modules and 29 signatures. Original compatibility covers 72 exact raw type/axiom matches plus five relocated helpers independently checked against original literal expressions in private and normal objects; all 59 explicit theorem headers remain verbatim. Three exact source/diff reviews, policy, whitespace and 5014 other protected-file checks passed. Runtime code and registered tests remain unchanged since their actual native and interpreted executions at `3ff3daf4`.

Actual public projected-fault interpretation remains open: it must associate the reached terminal metadata with the precise prepared missing-default row, including normalized raw key/value checks and reserved token range. General stored-call parent expressions still need actual argument/stage/coercion and compiler binding receipts. Bundle type equality alone does not imply Source arity. Neither native type vectors nor an arbitrary fault relation can supply these facts.

At `69e3f120`, actual Source call prefixes retain independent callee/argument typing and real heap extensions; actual codebook preparation exposes the selected generated request and count. Original stage acceptance remains an independent receipt. The missing-default producer retains authenticated emitted rows, and the original path-fault core exposes the actual terminal index and raw mapping fields. Verification passed 5278 normal jobs, 6329 strict declarations, 79 fresh declarations and 36 signatures. The original path-fault theorem retains its exact raw type and axioms against Root's independently saved actual original objects.

At `eb7851c3`, genuine equal arity and independent Source/native bundle equalities derive the original binder argument representation. The indirect parent and payload application suffixes preserve the exact native grade, body, captures, argument and stores through finite inversion. Verification passed 5280 normal jobs, 6345 strict declarations, 21 fresh declarations and 11 signatures. All source reviews, policy, whitespace and 5013 other protected-file checks pass. Actual compiler pack provenance, whole-parent composition and coherent public diagnostic lookup remain incomplete; row membership and packed type equality do not replace those obligations.

At `f3a8bc11`, actual native binder packs, accepted stored-call invocation and terminal provider provenance passed 5283 normal jobs, 6409 strict declarations, 64 fresh declarations and 31 signatures. All 16 original prepared-path raw types and axiom arrays match independently saved original normal objects exactly.

At `8d187247`, strict callee bounds construct the actual reached state and retain complete selection; callee faults close the original parent at that same state. Actual contextual lambda generation retains the genuine binder policy and Source monomorphic projections. Original diagnostic preparation supplies all range, fixed and escaped exclusion conditions for coherent raw-error lookup at a genuine MissingSite member. Verification passed 5287 normal jobs, 6628 strict declarations, 223 fresh module-attributed declarations and 17 signatures. All 59 original lambda-generation types and axioms remain exact. Three exact source/diff reviews, kernel policy, whitespace and 5011 other protected-file checks passed. Runtime and registered tests remain unchanged since their actual native and interpreted executions at `3ff3daf4`.

Terminal-to-inventory membership and catalog Source type closure remain separate static obligations. Header occurrence graph closure does not establish type closure. Successful stored-call composition currently requires genuine strong ordinary/principal provenance, same-Code body syntax, actual guard acceptance and independent raw Source bundle/count facts. It does not cover every legacy, rejected or coerced call.

At `108f6af3`, the same original registration fold retains closed Source entries, and actual factory/projection/description proves the concrete assignment gate. The genuine lambda Site identifies the native binder pack, while concrete ordinary/principal receipts build invocation association at the actual callee post. Actual route collection and Source projection typing associate the reached mapping terminal with its precise MissingSite/base and raw table error. Verification passed 5294 normal jobs, 6800 strict declarations, 186 fresh module-attributed declarations and 27 signatures. All 48 original registration-prefix raw types and axioms remain exact against independently saved original normal objects. Three exact source/diff reviews, policy, whitespace and 5010 other protected-file checks passed. Runtime and registered tests remain unchanged since their actual native and interpreted executions at `3ff3daf4`.

The public adapter must still produce its authentic selected catalog factory and full Source inventory membership from actual compilation. The terminal proof now closes for a real collected prepared assignment, while Source projection typing, actual extended raw metadata and the same generated path remain genuine inputs. Stored-call raw Source bundle/count/result production, full rejection/coercion/stage coverage and all-pass composition remain unfinished.


At `0f829f4e`, actual public compilation supplies the selected catalog and complete Source inventory. Missing terminals and uninitialized projected roots retain their actual prepared paths and first table rows. Actual callable preparation supplies arity diagnostics before and after argument effects. Empty output coercions and genuine successful callee traces derive the raw Source result used by the ordinary/principal continuation adapters. The original assignment and Header static folds retain their selected preparation; admitted projected endpoints consume the actual reached diagnostic packet.

Verification passed 5314 build jobs, 7186 strict declarations, 221 fresh module-attributed declarations and 29 signatures. All seven original Header raw types and axiom lists are exact against independently saved normal objects. The preceding assignment checkpoint independently checked all eight saved literal expressions and axiom lists; seven raw types are exact, with one hygienic matcher-name difference. Source/diff reviews, policy, whitespace and 5009 protected-file checks passed. Runtime and registered tests are unchanged since their actual executions at `3ff3daf4`.

At that checkpoint, preparation still needed a structural connection to the exact assignment in the emitted Tree. Equality of diagnostic predicates or emitted code does not recover the chosen head. Actual raw table observations also require a precise interpretation into the semantic fault relation, especially the reached uninitialized location. Existing uniform profile/Catalog fault requirements remain a separate consumer obligation. Stage rejection, nonempty coercions, public Source admission and all-pass composition remain incomplete.

At `744c1c40`, the actual compiler's original Header/match Syntax traversals retain joint Tree/Plan receipts. Each assignment shares the chosen head with its real preparation and Source occurrence; the match receipts retain the actual requests, child contexts and terminal materialization. Original theorem types remain available. Public projected endpoints derive their reached diagnostics internally. First-stage rejection and callee-fault adapters retain the genuine staged outcome, same reached pool, strict child callbacks and actual full native completion bound.

At `744c1c40`, the proof umbrella and `Tests.Main` build passed **5323 jobs**. Strict `--trust=0` verification checked **7430 declarations** against the three permitted standard axioms. Fresh inventories cover **301 module-attributed declarations** across six new or modified modules, with **65 signatures**. All **88 original declarations** retain their types and axiom lists: 81 keep their names and exact raw types, six private generated helpers have explicit relocation mappings and exact raw types, and one retained matcher alias differs only in a hygienic bound name. Seven independently regenerated literal Lean-expression checks pass against saved original normal objects. Eight public generated declarations retain their names and raw types while their owning module moves to the finite adapter. Every final source passed parent and two independent reviews; both modified original modules passed complete diff review. Kernel policy, whitespace and **5009 other protected original files** pass. Runtime code and tests remain unchanged since their actual native and interpreted executions at `3ff3daf4`.

At that checkpoint, the existing ready Header/Catalog fault and reflection proofs still consumed their older uniform laws. The subsequent Header checkpoint below shares its semantic branches between derived legacy and joint recursor adapters.

At `c9078fd2`, Header fault and reflection proofs each use one common six-branch semantic core. Legacy wrappers derive their structural recursor from original error laws; coupled endpoints derive it from the genuine Tree/Plan receipt and its actual prepared assignment payload. The original successful-prefix proof is unchanged. Public assignment readiness derives the bare operand law internally and retains precise reached interpretations for projected heads.

Strict callee induction now constructs the actual stored-call post from the full native completion, closing the earlier successful-child reflection premise. Accepted first gates feed actual ordered argument evaluation. Argument failures retain genuine Source/staged outcomes, cumulative state and all-row stable history. Successful arguments retain the complete fourth-bind bound beside the application projection. Physical arity, the gate after arguments and general body invocation remain the next boundaries.

At `c9078fd2`, the proof umbrella and `Tests.Main` build passed **5330 jobs**. Strict `--trust=0` verification checked **7505 declarations** against the three permitted standard axioms. Seven new or modified modules account for **102 fresh module-attributed declarations**, with **26 signatures**. All **49 original Header declarations** preserve their types and axiom lists: 38 exact same-name raw types and 11 explicitly mapped helpers checked independently against saved original literal Lean expressions. Parent and two independent final reviews, complete original-module diff reviews, policy, whitespace and **5009 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

At `a1bb3536`, the public Header supplies actual per-context assignment providers and derives unary typing and issued tokens internally. The stored-call gate after arguments uses genuine physical arity. Rejection retains the actual argument post and true Source/staged arity failure; acceptance returns the original argument receipt and complete fourth-bind bound. The combined checkpoint with `676743ef` passed **5332 build jobs**, **7520 strict declarations**, **15 fresh declarations** and **seven signatures**. No original source module changed. Three exact full-source reviews, policy, whitespace, hashes and **5009 protected-file checks** passed.

A legacy Tree or diagnostic predicate does not yield PreparedAt. Catalog integration must retain actual initializer code, loop post-header receipts and genuine match catalog/context fields. The current coupled match receipt omits its full solved-row identity; emitted code cannot recover unused rows. Unary token interpretation, interpretation of reached table entries as semantic faults, later phases, nonempty coercions and recursive staged semantics remain separate obligations. Public Source admission and all-pass compiler closure remain incomplete.

At `31bf3d35`, genuine public Source program facts derive catalog well-formedness, and strict child induction composes the stored-call parent prefixes at one real callee post. That checkpoint passed 5334 jobs, 7532 strict declarations, 12 fresh declarations and six signatures. The accepted body continuation still needs the callee-to-argument effects retained from the same ordered argument traversal.

At `5faa387e`, the proof umbrella and `Tests.Main` build passed **5338 jobs**. Strict verification checked **7702 declarations**, with **326 fresh module-attributed declarations** across seven new or modified modules and **55 signatures**. All 156 original declarations retain their types and axiom arrays: 154 have exact same-name raw types, and two generated matchers pass independently regenerated literal Lean-expression checks against saved original normal objects. Every final source and all three modified original-module diffs passed parent and two independent reviews. Policy, whitespace, final source hashes and **5009 protected original-file checks** pass.

The Catalog common cores preserve actual initializer code and continuation and exact loop post-header receipts. The compiler extraction carries genuine Source signatures and full solved-row ledger identity through binder and selected-child contexts. Prepared endpoints consume that same static receipt internally; a bare coupled receipt still needs an explicit match-field supplier. Prepared Head/loop providers, precise diagnostics, strict general body closure and all-pass/public-entry composition remain separate obligations. No runtime code or tests changed; actual executions remain those at `3ff3daf4`.

At `4e9cd0ae`, the proof umbrella and `Tests.Main` build passed **5344 jobs**. Strict verification checked **7767 declarations**, with **89 fresh module-attributed declarations** across eight new or modified modules and **16 signatures**. All 24 original declarations have exact same-name raw types and axiom arrays against independently saved normal objects. Every final source and both modified original-module diffs passed parent and two independent reviews. Policy, whitespace, final source hashes and **5009 protected original-file checks** pass.

Public Catalog extraction now retains the exact generated flow, finish equation and chosen compiler receipt at the actual ordinary BodyState. Prepared for-header adapters keep genuine Source typing, reached readiness and the original static payloads. The same measured closer is publicly reusable without a new induction.

Accepted stored-call adapters retain the real callee-to-argument effects from one ordered argument proof and use only strict body induction. They derive genuine Source and staged outcomes and preserve the complete body pool through caller restoration. The original 15 argument declarations and nine measured-family declarations retain exact raw types and axiom arrays. The whole parent must still pass the stronger receipt to these adapters; accepted intermediates do not establish complete callee classification.

Prepared Head/loop production, public flow/finish family closure, precise diagnostics, nonempty coercion and stage routes, Source admission and all-pass compiler closure remain incomplete. Runtime code and tests are unchanged; actual native and interpreted executions remain those at `3ff3daf4`.

At `0a3ab594`, the proof umbrella and `Tests.Main` build passed **5349 jobs**. Strict verification checked **7843 declarations**, with **148 fresh module-attributed declarations** across ten new or modified modules and **55 signatures**. All 72 original declarations retain exact same-name raw types and axiom arrays against independently saved normal objects. Every final source or complete original-module diff passed parent and two independent reviews. Policy, whitespace, final source hashes and **5009 protected original-file checks** pass. This checkpoint changes proofs; the most recent actual native and interpreted executions remain those at `3ff3daf4`.

Prepared initializer/Head/loop providers now construct genuine reached header results and exact post receipts internally. Their legacy wrappers and the three post restorations share the existing finite proof bodies. Public Source-site inputs and successful Source heap typing retain the actual original body receipt. Whole stored-call reflection retains ordered argument effects and the actual callee post through accepted ordinary/principal body invocation; its provenance callback does not establish a complete classifier. All 72 original declarations have exact raw types and axiom arrays.

Next: connect the actual public flow through the existing function finish and named callbacks carrying genuine parameter receipts into the same measured family. Prove that typed Source bodies cannot let break or continue escape the function, and retain actual lambda formation provenance through stored values. Precise reached diagnostic interpretation, complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished. Semantic child callbacks must come from strict mutual induction.

### Remaining audit and proof obligations

- Preserve full captures, original named/lambda Source provenance, caller/lexical frames, and the actual AuthorityPool under the same function-value and heap model.
- Connect callees, arguments, general bodies, methods/coercions, local instances, and application views to the same mutual induction. Actual indirect continuations now select the real argument post; final mixed closure must supply them internally from strictly smaller body obligations. Retain records added during calls through restoration.
- Relate specified failures and all preceding state as well as normal results. Positive missing-default rules have been added, but whole-syntax/whole-failure coverage and the final theorem remain unfinished.
- Compose actual specialization, evidence, and pre-evaluation passes to prove preservation and finite completion reflection from independent Source before pre-evaluation to actual public Core execution. Correctness of current passes belongs to the second goal even though comptime backend unification is deferred.

The old temporary Values and Entry fragments have been replaced by committed modules. Ordered expressions, ordinary/marked allocation, lexical restoration, all assignment outcomes, finite while/for, headers, five-way control, selected match and function finish retain actual post-witnesses. The outer imperative fold and origin-neutral body kernel now carry actual states. Named body/caller expression families reuse the measured mutual fold, and actual parameter/restoration consumers use real allocator receipts. Closing general indirect/method/coercion dispatch, every static factory and the full compiler theorem remains incomplete. A generic prefix transition does not establish exact fresh snapshot membership; that claim requires the concrete allocator receipt for the same execution. See the [implementation record](core-runtime-unification-progress.md) for the current boundary and validation scope.

The language's `mapping(K => V)` in this audit is a dictionary type. `SourceStagingHeapRelation.LocationMap` and similar definitions are proof tables relating cell locations; they are a different subject. Do not count ordinary Core administrative cells, retained Source cells, and Integer cells erased by pure staging as the same set of cells.

### 2026-10-08: actual parameter and public body checkpoint

At `85983792`, the proof umbrella and `Tests.Main` build passed **5353 jobs**. Strict verification checked **7912 declarations**, including **67 declarations** in four new proof modules, and **32 signatures**. Each module passed parent and two independent source reviews. Policy, whitespace, exact final source hashes and **5009 protected original-file checks** pass. The most recent actual native and interpreted executions remain those at `3ff3daf4`.

The new parameter receipts retain actual argument typing, installed frame, captured history and full reached pool. Public body bounds use the actual compiler flow and the existing function finish, and derive successful Source admission from the genuine Source receipt. All semantic child callbacks remain strict; the complete mutual family and final public compiler theorem remain unfinished.

### 2026-10-08: Source control and prepared named family checkpoint

At `75075048`, the proof umbrella and `Tests.Main` build passed **5356 jobs**. Strict verification checked **8052 declarations**, including **224 module-attributed declarations** in six new or modified modules, and **28 signatures**. All final sources or complete original-module diffs passed parent and two independent reviews. Policy, whitespace, final source hashes and **5008 protected original-file checks** pass. The most recent actual native and interpreted executions remain those at `3ff3daf4`.

Typed Source statement summaries now retain possible fallthrough, break and continue transfers through the existing mutual preservation proof. Loops consume break and continue, and a genuinely typed function body cannot let either transfer escape. The original explicit preservation APIs remain available. Function finish uses that actual Source trace to discharge the escaped-control condition, including lambda contexts whose internal reason is zero. Nested callee faults retain their original reason and token.

`CallableIndexedOwnedPublicPreparedNamedFamilyClosure` closes prepared ordinary/direct named bodies through the existing measured family. It consumes actual parameter receipts, the same public Header and generated flow, and strict callee body callbacks. It retains genuine Source typing, administrative effects, the complete reached record pool and independent Source/native grades. Prepared read/place diagnostic interpretation and static child associations remain explicit; this does not establish the final public compiler theorem.

Compatibility checks preserve exact raw types and axiom arrays for all 42 explicitly declared original Source APIs and all 29 original function-finish declarations. Across the three modified modules, 73 same-name raw types and 105 surviving original axiom arrays match. Strengthening the Source mutual proof changes 32 compiler-generated private matcher types and removes eight generated helpers; the validation record enumerates those generated changes separately.

Next: retain actual contextual lambda formation provenance through storage and later selection. Replace uniform read/index fault premises with policies at the genuine reached Source read and mapping lookup, then connect them to the actual public diagnostic receiver. Complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished. Semantic child callbacks must come from strict mutual induction.

### 2026-10-08: reached diagnostics and contextual lambda provenance checkpoint

The checkpoint comprises `d1d76443`, `61ff6e28`, `7866b408` and `fd8f7c94`.

Read and mapping index fault policies now consume Source witnesses at the actual reached environment and heap. The existing four terminal proof bodies are shared with their legacy wrappers. Source preparation supplies each local read's exact canonical function, occurrence, binder, span and globally issued token. Retokening retains row identity, and actual assignment ranges and function boundary tokens establish separation in the original program table.

Contextual ordinary and principal lambda formation retains its original compiler producer, binder policy and full Source body syntax. The additive value relation and selection cases keep that packet through storage, map/world extension and later selection. Principal evidence retains its original dictionary and method receipt. The existing runtime expression heads still need to select the stronger formation endpoints and feed them into typed invocation.

Public fault observation uses the actual completion's registry, rebuilt diagnostic table, filtered callable append, failed native token/store and accepted heap export. The ordinary-read packet retains the actual read certificate. It currently retains the whole Source failure and primitive read separately: their occurrence path through the same failure must be constructed by the existing semantic joins. Read/index priority, extra-source preparation ranges and successful table rebuilding remain explicit producer obligations. These proof definitions and preparation certificates do not establish the final compiler theorem.

At `fd8f7c94`, the proof umbrella and `Tests.Main` build passed **5366 jobs**. Strict verification checked **8787 declarations**, including **913 declarations attributed to nineteen new or modified modules**, and **82 signatures**. All final sources or complete original-module diffs passed parent and two independent reviews. Policy, whitespace, final source hashes and **5002 protected original-file checks** pass. The most recent actual native and interpreted executions remain those at `3ff3daf4`.

Compatibility checks preserve exact same-name raw types for 509 of 515 original declarations and exact axiom arrays for all 515. The six changed types are the generated `rec`, `recOn` and `casesOn` eliminators of the two lambda representation/selection relations; they reflect two additional contextual lambda cases. All original declarations remain present. The normal validation record lists these changes.

Next: use the retained contextual lambda packet at actual runtime expression heads and connect typed body continuations for the exact emitted Code to the original parameter, invocation and restoration proofs. Carry actual primitive fault origins through the same existing ordered-expression, call and imperative proof joins, and derive diagnostic priority and reserved registry ranges from the actual preparation. Public Session lookup and failure completion must retain their actual table and state receipts. Complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished. Semantic child callbacks must come from strict mutual induction.

### 2026-10-08: actual Session receipts, typed lambda invocation and failure paths

The latest implementation checkpoint is `9e0e3da8`, following `2363f329`, `70b62780`, `6532c642`, `2766ef4c`, `a194a050` and `10fef624`.

Public Session lookup now retains the actual registry extension and the table selected by the original lookup. Failed native completion retains the actual returned Session, weakened slots, values and ownership. The failure observer uses those receipts and the original diagnostic lookup; it does not assume equality between the exported Source heap and the native store.

Typed lambda invocation uses the actual parameter installation and a genuinely typed Source body. The original invocation proof supplies allocation, the body post, restored caller frame and complete returned pool. Source control facts discharge escaped break and continue at function finish. Contextual ordinary and principal formation now supplies typed body syntax and the actual binder policy for the emitted Code. The runtime heads and the mixed body family still need to consume these stronger static and invocation receipts together.

Expression sequences and the five existing composition branches share their original preservation and reflection proofs with stronger failure posts. These posts retain the origin of an uninitialized local read or a missing default in a mapping through the actual selected child path, retaining the final Source heap and token. Primitive terminal providers still need to construct these posts from the actual Core completion and bind the mapping leaf to the emitted token base. Call, imperative and remaining expression branches must retain that path through the same existing folds.

Actual missing-diagnostic generation now retains each emitted row's Source site, registry entry, checked one-based header, runtime type views and nonwrapping token. Rebuilding a table retains the actual generated rows and fixed prefix. This proves where accepted rows came from. It does not yet prove that every required row exists or that the public decoder selects it. Preparation ranges, priority among read, fixed and callable rows, and contextual Source occurrence agreement remain separate producer obligations.

At `9e0e3da8`, the proof umbrella and `Tests.Main` build passed **5442 jobs**. Strict verification checked **10724 declarations**, including **469 declarations attributed to nine new or modified modules**, and **50 signatures**. All **213 original declarations** retain exact same-name raw types and axiom arrays against saved normal objects. Every final source or complete original-module diff passed parent and two independent reviews. Policy, whitespace, source hashes and **4997 protected original-file checks** pass.

The preceding checkpoint for typed lambda invocation and failed completion at `6532c642` passed **5437 build jobs**, **10255 strict declarations**, **1563 module-attributed declarations** and **24 signatures**; all 1491 original raw types and axiom arrays match. Session diagnostic lookup at `2363f329` passed **5366 build jobs**, **10189 strict declarations**, **1404 module-attributed declarations** and **4 signatures**; all 1393 original raw types and axiom arrays match. These checkpoints add proofs and static receipts. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

Next: derive concrete primitive failure posts from the original read/index terminal proofs and retain the actual model through their semantic joins. Strengthen the existing preparation range proof once to retain actual base acceptance, final token bounds and read/fixed separation; use those receipts with the real table rebuild and filtered callable append. Retain coupled Catalog/structural body extraction at actual contextual lambda formation, then connect the stronger runtime heads and typed invocation through strict mutual induction. Complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-08: primitive failure posts and actual public diagnostic priority

The latest implementation checkpoint is `7c110570`, following `9cede6ab` and `c7f6e67a`.

The original read and mapping index terminal proofs now construct primitive failure posts internally. A lifted pointwise policy retains the actual witness, then projects the original result, heap and effects alongside the concrete Source path. The same catalog and function model remain associated with that origin. The upper read/index adapters and the remaining expression, call and imperative folds still need to carry this post through their actual children.

The existing diagnostic preparation loop now retains its actual accepted base, generated rows, final token bounds and separation of original reads from fixed and reserved diagnostics. The old range theorem projects the same proof. Actual callable preparation places its checked unknown token at or above the supplied minimum; the existing filtered append preserves earlier diagnostics.

Public read and missing-default endpoints use the actual rebuilt table and callable allocation at the preparation's final token boundary. They derive decoder priority from these producer receipts. Read decoding preserves the exact binder, occurrence and span. Missing-default decoding preserves the raw error; a duplicate token keeps the first selected row's span.

Actual public preparation, selected callable identity, receiving registry and site membership remain required receipts. The compiler must supply them and relate the same Source occurrence to the issued row. Arbitrary extraSources can reuse a key and expression ID with a different form, so accepted generic preparation alone does not establish Source ownership. The next producer work retains the genuine contextual substitution and canonical occurrence facts.

At `7c110570`, the proof umbrella and `Tests.Main` build passed **5446 jobs**. Strict verification checked **10787 declarations**, including **194 declarations attributed to five new or modified modules**, and **26 signatures**. Every final source or complete original-module diff passed parent and two independent reviews. Policy, whitespace, source hashes and **4997 protected original-file checks** pass.

All 124 surviving original preparation declarations retain exact same-name raw types and axiom arrays. Seven generated proof/simplification helpers move from prepare_ranges to prepare_reserved_receipt: four retain exact raw types, and three have recorded raw binder-name differences. All 131 original axiom arrays match using those explicit relocation pairs. The normal record preserves both raw hashes; it makes no normalized-type compatibility claim and introduces no obsolete aliases. These changes add proofs and static receipts. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

Next: connect the stronger primitive posts to actual emitted read/index constructors and early child failures through the existing folds. Derive query-specific diagnostic Source ownership from the real contextual factory and canonical occurrence uniqueness, retaining provenance in the same preparation loop. Retain coupled Catalog/structural lambda body extraction and connect the stronger runtime heads and typed invocation through strict mutual induction. Complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-08: actual read/index ports and authentic public diagnostic factories

The latest implementation checkpoint is `f0ddfaa3`, following `834f69b6` and `61824c61`.

Actual certified local reads retain their lexical binding and current cell witness through the concrete primitive post. Scalar and general mapping index adapters evaluate the actual ordered children, including the hidden key slot, then call the original terminal proof at the emitted reasonAt id. They preserve the same Source outcome, native result, final heap, map, world and effects. Extended paths retain early base and key failures; the existing full index folds still need to carry those posts.

The real contextual factory retains full-key singleton selection, the selected original Source, its active substitution and the exact ordered extraSources passed to diagnostic preparation. The original local catalog remains separate from its later callable rewrite. Local-read and index constructors, occurrence IDs and spans survive substitution. General forms and types are not equated; canonical occurrence uniqueness remains a genuine Source receipt. The same preparation loop still needs to retain actual index issuer provenance and coverage before these views establish the public reasonAt association.

The actual compatible, automatic and sealed factories now supply optional callable allocation at the issued preparation endpoint. Sealed read and missing-default decoder endpoints derive preparation and callable priority internally. Actual receiving table identity, selected read or MissingSite, raw metadata and runtime type views remain required. Read decoding retains the exact binder, occurrence and span; missing-default decoding retains the raw error and the original first selected duplicate span.

At `f0ddfaa3`, the registered Solcore modules and `Tests.Main` build passed **5451 jobs**. Strict verification checked **10910 declarations**, including **123 declarations attributed to five new modules**, and **45 signatures**. Each exact full source passed parent and two independent semantic reviews. Policy, whitespace, source hashes, regular normal objects and **4997 protected original-file checks** pass. This checkpoint adds only new proof modules and umbrella imports; existing runtime and semantic implementation modules remain unchanged. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

Next: carry early index posts through the original scalar and general folds once. Retain unconditional actual index issuer and selector coverage in the same preparation proof, then derive query-specific ownership from the genuine contextual views. Complete joint contextual lambda Catalog/structural body extraction and connect it to typed invocation through strict mutual induction. Complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-08: index failure folds, actual diagnostic issuers and joint lambda static bodies

The latest implementation checkpoint is `32cbe6b1`, following `250c2d61` and `9b670b52`.

The original scalar and general index preservation/reflection proofs now retain failure posts at the actual base or key child. Key failures retain the successful base trace and its exact middle heap. Concrete terminal adapters use the emitted reasonAt id and genuine Header, key and ordered child receipts. The original semantic result, final heap, map, world, store and effects stay paired with the primitive origin. The scalar/general fragment suppliers and larger expression/body folds still need to carry this stronger post internally.

Diagnostic preparation retains literal index issuers, per-key uniqueness and coverage of the actual ordered source/node prefixes in its existing loops. This receipt accepts arbitrary extra sources. Only finite contextual queries add the real factory's Source views and canonical occurrence uniqueness; they derive no-index priority for local reads and the first selected index's canonical form and span. Substituted issuer types remain distinct from canonical types. Public reasonAt/receiver composition and the selected MissingSite's own Source association remain separate work.

Contextual lambda generation retains the actual body-lowering recipe and binder policy. Shared static transport moves prepared assignment, unary, header and match packets with their exact mapped trees. A post tree retains its chosen Plan and tokens. The real view collector runs once, yielding a canonical typed body and prepared structural elimination. Genuine local views, reachability, both syntax certificates, the actual compiler children, native body typing and the complete ledger remain inputs. Connecting this joint static receipt to typed invocation through the same measured family is the next runtime proof unit.

At `32cbe6b1`, the registered Solcore modules and `Tests.Main` build passed **5457 jobs**. Strict verification checked **11194 declarations**, including **477 declarations attributed to eleven new or modified modules**, and **71 signatures**. Every final source or complete original-module diff passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4994 protected original-file checks** pass. This checkpoint factors five existing proof modules and adds six proof modules. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **271 original axiom arrays** match against saved actual normal source and regular objects. **259 same-name raw types** match exactly. Twelve generated helpers have explicit relocation pairs: nine raw types match exactly, and three retain enumerated raw binder-name differences. Comparisons preserve the complete literal types and axiom arrays; no normalized comparison or obsolete generated alias is used.

Next: derive the stronger scalar Members fragment from its actual literal/read producers through the five original support cores. Compose real contextual reasonAt/receiver observations, retaining MissingSite/metadata authority. Consume the joint contextual lambda prepared body in the existing strict measured family. Complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: scalar failure origins, prepared lambda execution and Session diagnostic observations

The latest implementation checkpoint is `52999450`, following `bd7f9250` and `7cf8c705`.

The five original scalar expression proof modules now retain primitive failure posts in their existing preservation and reflection inductions. Actual grouping, ordered products, primitive operations, conditional branches, constructor arguments and member bases carry the same failure token, reached heap, map, world, store and model association. Concrete literal and read adapters supply their stronger results internally. The scalar index fold consumes this stronger fragment and preserves the successful base prefix when a key fails. Larger general, builtin, recursive and named expression folds remain to be connected.

Contextual lambda execution now consumes the actual joint prepared body. The owning Source's real assignment and diagnostic preparations supply finite operand and projected-fault laws. Genuine Source typing and reached readiness feed the original head, loop and flow producers. The actual prepared eliminator yields bounded flow preservation and reflection; strict admitted expression children then yield typed parameter-entry and body-finish continuations with independent Source and native grades. Precise reached-table interpretation remains an input. The actual function formation, storage and selection path must still retain this stronger body receipt inside the shared mixed family.

Public and Session diagnostic observations now compose the genuine contextual factory and callable allocation bounds with the actual receiving registry and rebuilt table. Local reads retain the exact diagnostic binder, identifier and span. Missing-index observations retain the first literal index issuer and the raw missing-type error. A sealed Artifact's real compiler authority is extracted only into a proof proposition. The selected MissingSite's membership, provider base, receiving metadata and runtime views remain genuine inputs; decoding alone does not establish a Source fault origin or heap association.

At `52999450`, the registered Solcore modules and `Tests.Main` build passed **5469 jobs**. Strict verification checked **11491 declarations**, including **297 declarations attributed to seventeen new or modified modules**, and **97 signatures**. Every final new source and complete original-module diff passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4989 protected original-file checks** pass. This checkpoint factors five existing proof modules and adds twelve proof modules. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **141 original axiom arrays** match saved actual normal source and regular objects. **131 same-name raw types** match exactly. Ten generated support matchers move to the strengthened proof cores and have genuinely changed raw types, recorded in explicit pairs. The comparison retains complete literal types and axiom arrays without normalization, renamed binders or obsolete generated aliases.

Next: retain the joint prepared lambda body through actual function formation, local storage and selected invocation, then close its strict expression children in the shared measured family. Retain the actual selected MissingSite and its Source/type-mapping issuer in the original diagnostic preparation. Connect the stronger scalar post to larger general, builtin, recursive and named folds. General callee classification, rejection/coercion and staging coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: recursive failure posts, missing issuer ownership and prepared ordinary lambda invocation

The latest implementation checkpoint is `09e65b60`, following `e7b74177` and `554c65df`.

The original recursive expression preservation and reflection folds now retain primitive failure posts through their existing inductions. Concrete literal, read and scalar-member providers are assembled internally. Ordered child traces retain the actual intermediate Source heap and the complete native result, map, world, store and model association. General, builtin and named folds remain to be connected.

The actual missing-diagnostic preparation now retains accepted expression suffixes and place routes in the same original proof cores. Each appended missing row keeps its literal Source issuer, mapping and result type views, selected key and provider reason. Checked fresh allocations prove both index reason ownership by full specialization key and separation from place reasons. Ordered coverage supplies missing membership and provider bases internally. Genuine contextual Source views and canonical uniqueness then identify the occurrence and span of actual expanded receiving rows. Public and Session observations still need to consume these stronger receipts; decoding alone does not establish a runtime Source fault or heap association.

Prepared ordinary lambda support now survives actual formation, capture, model extension, key embedding and exact value selection. The original stronger contextual producer selects one Site with its policy and body recipe. The same owning Source and joint prepared body stay indexed by that Code through recapture. Finite formation heads construct the actual nested Header packet, global frame reference and captured history. Genuine physical arity and independent raw and native bundles align the selected parameter vector. Strict children of the same expression family supply the prepared flow and typed body finish; the original invocation and apply proofs restore the current caller's complete pool with independent Source and native grades. The new model explicitly retains prior General alternatives. Their prepared-body population, generic stored-call parent composition, principal formation and shared mixed-family closure remain unfinished. Precise reached-table interpretation and outer stage/coercion routes remain genuine inputs.

At `09e65b60`, the registered Solcore modules and `Tests.Main` build passed **5476 jobs**. Strict verification checked **11783 declarations**, including **427 declarations attributed to nine new or modified modules**, and **75 signatures**. Every final new source and complete original-module diff passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4988 protected original-file checks** pass. This checkpoint factors two existing proof modules and adds seven proof modules. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **175 original axiom arrays** match saved actual normal source and regular objects. **145 same-name raw types** and **four relocated raw types** match exactly. Twenty-three generated declarations move to the strengthened proof cores with genuinely changed raw types. Three existing private wrapper types also change because their generated constants belong to the new cores; their literal source headers remain identical. Every delta is recorded using complete literal types and axiom arrays, without normalization, renamed binders or obsolete generated aliases.

Next: connect the stronger recursive post to the original General fold and its actual index terminal. Consume internally derived missing membership and provider bases in public and Session observations, including the actual first row's span. Connect the exact prepared function model to the stored-call parent and shared measured family, and populate the remaining ordinary/principal routes. General callee classification, rejection/coercion and staging coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: General failure posts and exact public/Session missing diagnostics

The latest implementation checkpoint is `7167660d`, following `fe7c0b09`.

The original General expression preservation and reflection folds now retain primitive failure posts through their two existing support inductions. Concrete literal, read, proxy, recursive and index providers are assembled internally. Index base and key failures keep their actual ordered Source prefix, intermediate heap and complete native result, map, world, store and model association. The terminal case retains the genuine Header, lookup form, base/key representations and exact `reasonAt`. Generic reflection has no added uniqueness assumption; concrete read and missing policies remain genuine pointwise inputs. Builtin, named, call and imperative joins remain to be connected.

Public and Session missing-diagnostic observations now derive missing membership and provider bases internally from the actual accepted preparation. Canonical base lookup and runtime mapping views, together with the genuine receiving metadata representation, identify the raw key and value views. Reserved ranges and fixed-row separation select the actual first rebuilt additional row. Full specialization-key ownership, Source views and occurrence uniqueness fix its raw error, occurrence and span. The same sealed allocation, table rebuild, registry and filtered callable append transfer the exact diagnostic to public and Session observations. A diagnostic observation alone does not provide a runtime Source fault, heap or event association.

Prepared ordinary lambda formation, storage, selection and invocation remain available from the preceding checkpoint. Connecting that exact function model to the stored-call parent and shared measured family remains unfinished. The proposed next factor retains the existing finite callee, guard, ordered argument and application proofs while making their model explicit. Genuine prior General alternatives, principal prepared population, initial and captured heap coverage, precise reached-table interpretation and outer stage/coercion routes remain separate obligations.

At `7167660d`, the registered Solcore modules and `Tests.Main` build passed **5479 jobs**. Strict verification checked **11851 declarations**, including **68 declarations attributed to four new or modified modules**, and **21 signatures**. All final sources and the complete original-module diff passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4987 protected original-file checks** pass. This checkpoint factors one existing proof module and adds three proof modules. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **49 original axiom arrays** match saved actual normal source and regular objects. **43 same-name raw types** and **four relocated raw types** match exactly. Two generated matcher declarations move to the strengthened support cores with genuinely changed raw types. Four existing compatibility aliases point to the actual relocated helpers and retain their exact raw types and axiom arrays. Every delta is recorded using complete literal types and axiom arrays, without normalization, renamed binders or new obsolete generated aliases.

Next: connect the exact prepared function model to the stored-call parent through the existing finite prefix proofs, then assemble the shared measured family and remaining ordinary/principal population. Carry the stronger General fault post through builtin and larger named/call/imperative joins. Runtime Source failure and heap attribution, general callee classification, rejection/coercion and staging coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Builtin argument failure origins and reached mapping diagnostics

The latest implementation checkpoint is `cd5a61ab`, following `387cbe06`.

Builtin expression preservation and reflection now carry primitive failure posts through the original two support inductions and the two existing finite builtin-head proofs. Actual argument-list failures retain their Source evaluation prefix beneath the two inserted native slots, their failing child and their complete result, map, world, store and model association. Concrete literal, read, proxy, General and index providers are assembled internally. Successful represented builtin inputs exclude the actual builtin application-fault branch. Generic reflection adds no uniqueness assumption. Named, call and imperative fault joins remain unfinished.

A reached mapping-index failure now supplies the canonical mapping view and receiving metadata from its actual leaf fields, Source lookup and raw key/value runtime views. The genuine specialization and Source/reason issuer receipt, occurrence uniqueness and receiving-registry extension remain explicit. Existing first-row reconstruction, sealed public allocation and Session registry receipts then derive the exact raw missing-value diagnostic, occurrence and Source span. This observation does not establish a whole-program Source fault or identify the restored runtime heap or events.

Prepared ordinary lambda formation, storage, selection and invocation remain available. The stored-call prefix proofs are being factored to retain that exact function model. A compiler producer for a chosen contextual Site is also being connected to the existing static body collector. Genuine prior General alternatives, ordinary/principal population, initial and captured heap coverage, precise reached-table interpretation and outer stage/coercion routes remain separate obligations.

At `cd5a61ab`, the registered Solcore modules and `Tests.Main` build passed **5483 jobs**. Strict verification checked **11994 declarations**, including **143 declarations attributed to six new or modified modules**, and **38 signatures**. All final sources and complete original-module diffs passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4985 protected original-file checks** pass. This checkpoint factors two existing proof modules and adds four proof modules. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **73 original axiom arrays** match saved actual normal source and regular objects. **67 same-name raw types** and **four relocated raw types** match exactly. Two generated matcher declarations have recorded literal type changes. The four existing compatibility aliases retain their exact raw types and axiom arrays while pointing to the strengthened helpers. Comparisons use complete literal types and axiom arrays, without normalization, binder substitution or new obsolete generated aliases.

Next: connect the exact prepared function model to the stored-call parent through the existing finite prefix proofs, retain the actual compiler factory and chosen Site, then assemble the shared measured family and remaining ordinary/principal population. Carry fault posts through larger named/call/imperative joins. Runtime Source failure and heap attribution, general callee classification, rejection/coercion and staging coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Prepared stored-call reflection, compiler ownership and reached read diagnostics

The latest implementation checkpoint is `219b4b63`, following `75d980c6`.

Stored indirect stage, callee, argument, application and parent prefixes now share their original proofs through an explicit function model. The existing General interfaces remain finite wrappers. The prepared parent retains the selected ordinary closure, its immutable captured history and the actual callee and argument posts. A new application reflection endpoint uses physical argument counts, the original whole fourth-bind bound and strict child body continuations. It restores the caller once from the actual argument state and retains the complete pool, cumulative effects and independent Source and native grades. Its forward preservation connection remains unfinished.

The contextual ordinary-lambda compiler producer now invokes the existing generation and joint static body collector once. Its receipt keeps the literal owning Compilation, diagnostics, emitted named code, chosen Site, complete solved ledger and body recipe. The actual mixed compiler factory, initial and captured heap coverage, prior General and principal branches, shared measured family and pointwise policy population remain separate obligations.

Admitted builtin outcomes retain the reached primitive fault path, its actual native evaluation and token, and the Source post admission. A finite determinism bridge aligns the same returned value because the generic expression post omits it. A reached read certificate also derives the exact binder, location and Source span in public and Session diagnostics. Genuine issuer, Source lookup, receiver registry and first-row receipts remain explicit; these observations do not establish whole-program Source failure or restored heap attribution. Larger sequence, named-call and imperative fault joins remain unfinished.

At `219b4b63`, the registered Solcore modules and `Tests.Main` build passed **5489 jobs**. Strict verification checked **12184 declarations**, including **261 declarations attributed to twelve new or modified modules**, and **42 signatures**. All final sources and complete original-module diffs passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4985 protected original-file checks** pass. This checkpoint changes six existing proof modules and adds six proof modules. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **71 original axiom arrays** match saved actual normal source and regular objects. **57 raw types at their original names** match exactly. Fourteen declarations retain their names but have recorded literal lambda-binder name changes; these are counted as raw type changes, with separate Lean-expression equivalence evidence. Every original explicit declaration header remains unchanged. Comparisons use complete literal types and axiom arrays, without normalization, binder substitution, relocation or generated compatibility aliases.

Next: connect forward preservation of prepared stored applications and authentic indirect compiler leaves, then assemble the shared measured family and remaining ordinary/principal population. Retain actual expression fault posts through readiness sequences, named calls, invocation restoration and imperative joins. Runtime Source failure and heap attribution, general callee classification, rejection/coercion and staging coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Prepared stored-call preservation, actual compiler policy and reached argument faults

The latest implementation checkpoint is `51626f35`, following `3dc12014`.

Prepared stored indirect calls now have a forward preservation endpoint alongside the existing reflection endpoint. The shared finite suffix proof invokes the prepared body from strict children and restores the caller once at the actual argument state. The body-child and physical-count obligations apply only to the called suffix; an argument fault needs neither. The endpoint retains immutable captured history, the complete current argument pool, cumulative effects, genuine Source typing and independent Source and native grades. It still requires authentic selected closure, support, stage and caller receipts.

Ordinary closure facts now derive the original Source function type and closure frame from actual Source typing, runtime validity and evidence coverage. Indirect compiler receipts retain the owning Compilation, diagnostics, emitted named code, solved ledger and exact contextual special-body callback. Finite metadata producers derive the indirect pointwise policy agreement from that same selection. Actual initializer absence and empty raw requirements, node coercions and argument coercions remain genuine inputs. These additions do not establish a complete mixed compiler factory.

Admitted expression sequences now retain the reached fault post through their original readiness and reflection cores. Named argument-fault endpoints join that same ordered argument failure to the actual named call and emitted slot, retaining the primitive fault path, literal native token, Source outcome, current heap, cumulative effects and post admission. They do not cover named body failure or invocation restoration. The generic expression post still omits the returned native value, so an actual evaluation witness and determinism align the literal fault token; no inverse fault relation is assumed.

At `51626f35`, the registered Solcore modules and `Tests.Main` build passed **5498 jobs**. Strict verification checked **12500 declarations**, including **411 declarations attributed to eleven new or modified modules**, and **82 signatures**. The checkpoint changes two existing proof modules and adds nine proof modules. All final sources and complete original-module diffs passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4985 protected original-file checks** pass. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **95 original axiom arrays** match authentic saved normal Source and regular objects. **91 same-name raw types** match exactly. Three generated reflection helpers have explicit relocations and literal type changes. One declaration keeps its name with a recorded literal lambda-binder name change; its separate saved-original Lean-expression equivalence check also passes. All **63 original explicit declaration headers**, including the stored-call completion inductive, remain unchanged. Comparisons use complete literal types and axiom arrays, without normalization, binder substitution or generated compatibility aliases.

Next: populate the mixed compiler factory using the same selected policy at every child budget, then close the shared measured expression and body family. Retain reached named body faults through real invocation restoration and imperative joins. Initial and captured heap coverage, prior General and principal selection, general callee classification, physical rejection, coercion and staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Same-policy callable leaves, named body fault restoration and prepared primitive family members

The latest implementation checkpoint is `b3557065`, following `0d4387a9`.

The contextual compiler now produces ordinary-lambda and indirect-call leaf receipts under one actual root policy. It retains the owning Compilation, selected special-body callback, body recipe, allocator, raw body and expression hooks, callable profile, projector and solved ledger. Each leaf uses the actual generic child acceptance at its original child budget. Lambda selection and joint static extraction occur once at the same chosen Site. The original Generation entry remains available with its exact declaration header. Complete mixed compiler-tree population remains unfinished.

Named invocation now retains a body fault post through actual caller restoration. The original finite preservation and reflection cores are shared with compatibility wrappers. The receipt keeps the genuine parameter/body entry, literal native fault token, Source outcome and heap, cumulative effects, complete current pool and actual pre-restoration body store. Restoration runs once at that body post; the fault predicate is not assumed invariant under arbitrary stores. Source and native body grades remain independent. Producing the post from the full imperative body and carrying it through outer expression heads are subsequent obligations.

Prepared primitive bodies now derive admitted expression preservation and reflection internally from their actual support certificate and builtin compiler tree. Ordinary literal context validity, read policies and missing policies remain genuine pointwise static inputs at the same certified context. The resulting expression family supplies actual flow and typed Source/native parameter continuations. Native flow reflection uses the original strict bound at size+1 without equating it to a Source grade. Finite smaller-member extraction reuses the existing measured family interface; the full mixed recursive family remains unfinished.

At `b3557065`, the registered Solcore modules and `Tests.Main` build passed **5504 jobs**. Strict verification checked **12670 declarations**, including **268 declarations attributed to eight new or modified modules**, and **47 signatures**. The checkpoint changes two existing proof modules and adds six proof modules. All sources and complete original-module diffs passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4985 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

All **98 original axiom arrays** match authentic saved normal Source and regular objects. **96 same-name raw types** match exactly. Two generated named-invocation helpers have recorded relocations and literal type changes. All **36 original explicit declaration headers** remain unchanged. Comparisons use complete literal types and axiom arrays, without normalization, binder substitution or generated compatibility aliases.

Next: populate the actual mixed compiler Tree from the same-policy leaf receipts, then close the shared measured expression and body family. Carry named body fault posts through the outer named-call heads and derive them from actual imperative body producers. Initial and captured heap coverage, prior General and principal selection, general callee classification, physical rejection, coercion and staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Mixed compiler trees, named-call body posts and actual prepared formation

The latest implementation checkpoint is `2de0da30`, following `4434e246`.

Compiler extraction now combines named calls, ordinary lambdas and indirect calls in one finite call-head family. Lambda parent metadata and Source frame facts come from the same accepted branch and genuine Source typing. Indirect calls retain their physical callee and ordered argument entries, including duplicates. Static metadata covers actual admitted extra nodes before acceptance; native typing and collector inputs apply to successful accepted lambda children. The existing compiler induction builds the mixed Tree once under the same root policy and body recipe. This result covers the canonical caller Source and native prefix; mixed coverage of each selected body's own certificate factory remains unfinished.

Named call expressions now retain the selected body post through their original finite preservation and reflection cores. The route distinguishes actual argument failure from invocation after successful arguments. Invocation retains the live argument-state capture, original ReturnedAt receipt at bodyStore, complete reached pool and literal equality from the outer caller restoration. Source and native grades remain independent. The original outer named/direct dispatcher is unchanged; forwarding this stronger route there and deriving body posts from real imperative producers remain subsequent work.

Prepared formation now attaches its literal ordinary body index to the actual formed closure. The producer calls the original formation once at identity inclusion in the unchanged prepared model. Its returned relation supplies native typing; the known captures, Code, Support and history construct membership directly. Finite map/world and key transports retain the same body and captured history. All prior model cases remain available. Carrying this receipt through actual storage, reads and returns, and covering initial/prior/principal closure population, remain unfinished.

At `2de0da30`, the registered Solcore modules and `Tests.Main` build passed **5509 jobs**. Strict verification checked **12808 declarations**, including **172 declarations attributed to six new or modified modules**, and **40 signatures**. This checkpoint changes one existing proof module and adds five proof modules. All final sources and complete original-module diffs passed parent and two independent semantic reviews. Policy, whitespace, exact Source hashes, regular normal objects and **4985 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

All **34 original same-name raw types and axiom arrays** match authentic saved normal Source and regular objects exactly. All **28 original explicit declaration headers** remain unchanged. Replacing only the two factored call cores and removing their new providers/import reconstructs the original Source byte for byte. The raw comparison uses complete types and axiom arrays, without normalization, binder substitution or generated aliases. The mixed compiler inventory uses actual imported module indices, including eight deferred Head equation declarations generated in the Certificates module.

Next: attach mixed compiler coverage to each actual selected body factory, carry formed membership through real storage/read/return producers, and populate the runtime mixed heads from strict shared-family children. Forward named body posts through the outer named/direct dispatcher and derive them from actual imperative producers. Initial and captured heap coverage, prior General and principal selection, general callee classification, physical rejection, coercion and staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Selected body factories, primitive named body fault producers and finite mixed runtime branches

The latest implementation checkpoint is `a6896205`, following `d7ae55e9` and `94413e52`.

The selected lambda compiler receipt now retains its actual collector inputs, certificate factory, read fuel and body entry. Mixed body certificates use these same inputs under the original root policy and body recipe. At the current Source context and scope, the existing compiler induction derives trees for named calls, ordinary lambdas and indirect calls, including the physical callee and ordered arguments. Recaptured support keeps the same factory. Source admission, metadata, native typing and assignment readiness remain explicit requirements; this does not yet establish runtime meaning for every body.

A named function whose body is one primitive expression, either a trailing expression or an explicit return, now has preservation and reflection of its body fault post. The proof derives the fault path from the actual child execution and runs the original builtin expression proof once. It retains the literal native token, Source fault and reached heap, and the actual store when the body finishes. Source and native grades are independent. These producers feed the existing named body-post interfaces; they do not cover arbitrary imperative bodies or return an additional native-bound packet.

Finite runtime adapters now connect the actual mixed named and lambda constructors to their existing proofs. Lambda adapters use the same chosen receipt and compiler fields. Named adapters obtain body continuations from strictly smaller members at the actual parameter receipt. Selected prepared ordinary calls obtain expression continuations from the actual captured body index; the original ordered argument effects, whole fourth-bind bound and caller restoration remain intact. The full prepared function model, including prior alternatives, is unchanged. These adapters do not close the mixed runtime family or recover formed membership from an opaque stored value.

At `a6896205`, the registered Solcore modules and `Tests.Main` build passed **5514 jobs**. Strict verification checked **13048 declarations**, including **242 declarations attributed to six new or modified modules**, and **45 signatures**. This checkpoint changes one existing proof module and adds five proof modules. All final sources and the complete modified-module diff passed parent and two independent semantic reviews. Policy, whitespace, exact Source hashes, regular normal objects and **4985 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

Both original declarations in the modified module retain their complete same-name raw types and axiom arrays. Both explicit declaration headers, original imports and the indirect-call implementation remain unchanged. The comparison uses authentic saved normal Source and regular objects, without normalization, binder substitution or generated aliases. Inventories attribute declarations by their actual imported module indices.

Next: use the retained body factories and finite runtime branches to populate and close the shared measured family. Carry formed membership through actual storage, reads and returns. Extend named body fault producers to imperative bodies and forward their posts through the outer named/direct dispatcher. Initial and captured heap coverage, prior General and principal selection, general callee classification, physical rejection, coercion and staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Chosen body runtime, initialized stored members and sequential named fault posts

The latest implementation checkpoint is `1d2aea21`, following `4ec24148` and `eb30a3e4`.

Lambda formation now retains a positive receipt for the chosen compiler factory at its actual ordinary body index. The original formation proof runs once; the same capture, code, support and prepared body remain attached to its result. Preservation and reflection of expressions in that support use the existing admitted runtime fold at the actual owning caller. This bounded domain excludes indirect calls throughout the Source graph and still requires strictly smaller named-family members and the current static compiler and diagnostic policies. It does not close the full mixed family or connect the base parameter carrier to nested body continuations.

A known prepared ordinary function now remains qualified through actual initialized allocation, writes and local reads. Allocation retains the real three native cells and capture/frame receipts. Read qualification uses the actual binder, Source cell and native optional payload; the nominal cell type stays separate from the reported occurrence type. The original callee post and parent prefix retain their native and Source grades, gate and conditional resolver. Future heap/store transport requires actual reads of the same payload. Broad heap representation does not recover membership or the stronger chosen-factory receipt, and prior, principal and global alternatives remain open.

Named bodies containing a discarded builtin expression followed by a trailing expression or explicit return now derive their fault posts from their actual executions. A fault in the first expression stops before the suffix. A successful first expression supplies the reached middle heap, native store, admitted state and all stable rows used by the next expression. Each executed child uses the original builtin proof once. The Source fault path and native prefix share the same middle witness and final primitive origin, token and body store. Source and native grades remain independent. General imperative bodies and forwarding these posts through the outer dispatcher remain unfinished.

At `1d2aea21`, the registered Solcore modules and `Tests.Main` build passed **5520 jobs**. Strict verification checked **13122 declarations**, including **74 declarations attributed to six new proof modules**, and **38 signatures**. All six complete sources passed parent and two independent semantic reviews. Policy, whitespace, exact Source hashes, regular normal objects and **4985 protected original-file checks** pass. Existing proof-module sources are unchanged; inventories use actual imported module indices, including generated declarations. Actual native and interpreted test executions remain those at `3ff3daf4`.

Next: connect typed nested body continuations to the actual chosen runtime factory and shared measured family. Retain the stronger chosen receipt through actual stored values and construct selection from known ordinary members. Extend named body fault producers to imperative bodies and forward their posts through the outer named/direct dispatcher. Initial and captured heap coverage, prior General and principal selection, general callee classification, physical rejection, coercion and staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Chosen nested continuations, retained factory selection and outer named body posts

The latest implementation checkpoint is `ac58faf5`, following `eb8d42b0` and `9f194b00`.

A chosen ordinary lambda now derives its nested body continuations from its actual compiler Support. Genuine parameter packets, Source typing and all stable rows supply the same nested state. The existing runtime fold feeds the original prepared flow and typed finish proofs. Their result retains the actual packet, complete pool, exit and readiness; the base continuation projects that same returned state. This domain still excludes indirect calls throughout the Source graph and requires strictly smaller named-family members and pointwise compiler, model and diagnostic policies.

The positive receipt for the chosen factory now survives actual initialized allocation, writes and local reads at the known ordinary index. Callee qualification retains the same original post and parent prefix, including the actual Source closure and native payload, map/world extensions, separate grades, gate and conditional resolver. The actual lexical occurrence and compiler read type construct ordinary selection. Coverage of initial closures and the prior, global and principal alternatives, physical arity and complete dispatch remain separate obligations.

The outer named/direct dispatcher now retains the actual selected low call route beside its root outcome. Its two finite cores are shared with the original wrappers. Bodies containing a single builtin, or a discarded builtin followed by a final builtin expression or return, obtain their parameter Source receipt and all stable rows from the actual successful arguments. Their proofs retain the body fault post through the existing invocation and caller restoration. The post remains at the actual body store; root Source, low call and native grades remain independent. General imperative body paths and the full measured family remain unfinished.

At `ac58faf5`, the registered Solcore modules and `Tests.Main` build passed **5525 jobs**. Strict verification checked **13248 declarations**, including **164 declarations attributed to five new proof modules and one modified module**, and **53 signatures**. All six complete sources and the complete modified-module diff passed parent and two independent semantic reviews. All **38 original complete raw types and axiom arrays** and **32 original explicit declaration headers** remain unchanged. Comparisons retain every line of each literal type without normalization or aliases. Policy, whitespace, exact Source hashes, regular normal objects and **4985 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

Next: feed positive chosen ordinary members into actual accepted invocation and close the shared measured family. Extend concrete named fault paths to broader imperative bodies. Initial and captured heap coverage, prior General and principal selection, general callee classification, physical rejection, coercion and staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.
