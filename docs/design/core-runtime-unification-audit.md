# Core unification: T0 audit of features, semantics, and proof boundaries

Initial audit: 2026-09-30. Last updated: 2026-10-10.

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


## 2026-10-09: Current status

### Execution and public boundary

The first goal was completed on 2026-10-01 in `a3168382`. `SourceCompiler` reexports `SourceCoreExecution`. Common artifacts and sessions execute cached Core code prepared by `SourceCoreCompiler → SourceCoreUnifiedCompilation`. Backend preferences, fallback, the old session implementation, and runtime typed-source expression/statement/call evaluators have been removed.

The raw metadata, grouped tuples, stage/arity evaluation order, callable views/ancestry, inert initial-heap prefix, and distinction between source allocations and administrative cells found in the initial audit have been incorporated into compatibility carriers, public ownership, snapshots/full prefixes, and regression tests. Public Value does not expose source closures or arbitrary native references; function calls authenticate owned handles. Historical raw heaps migrate through the explicit `SourceCoreLegacyHeapImport` boundary.

The `SourceTypedRuntime` namespace remains for compatibility values, observations, and validation data. The namespace and tests named after old features do not demonstrate survival of a runtime evaluator. Existing comptime direct evaluation remains in preparation as agreed. Unifying that evaluator with Core and adding source contract/storage/external-call connections belong to the next phase.

### Latest proofs and validation scope

The latest implementation checkpoint is `06f2635c`. Genuine strong parameter Receipt contracts supply the original body entry, full administrative context, lexical exit and body PostAdmission to the generic invocation. Pure restoration uses genuine context support, saved stable rows and the actual restored frame to keep caller admission inside the same causal returned-state witness. The accepted initial/completed factory derives its static and input facts internally without replaying bootstrap or parameters; Source and native grades remain independent. Faults retain stable rows.

Normal verification passes 5618 build jobs, two empty strict Source logs, all 27 private/normal literal TYPE/AXIOMS blocks (10 generic / 17 accepted) and 20 signatures, using only the standard three axioms. Cumulative 16297 adds 27 names to 16270 with no overlaps or removals. The 5549-row pre-install snapshot, exact 2295-module environment, two changed existing object pairs (`Tests.Main` / `CoreLowering`), four-module cone and four actual rebuilds pass. All 4985 protected artifacts remain unchanged. No IO or runtime/Core specification change is added.

The 165-line public root and 242-line program exit companions remain uncompiled drafts. The next unit connects the same strong result to actual root completion and successful export; general mixed bodies, failure/export-error correspondence, specialization/evidence/comptime composition and the all-pass compiler theorem remain unfinished. The earlier dated `8d2289c5` factor audit remains below.

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

### 2026-10-09: Chosen invocation, accepted argument receipts, conditional body posts and local formation

The latest implementation checkpoint is `4246eb3d`, following `350a2921`, `30d7b328` and `b55a5b86`.

Invocation of a positively chosen ordinary closure now uses the original typed invocation proof with continuations derived from its actual compiler Support. The source and native endpoints retain the same owner, capture, history, live heap, argument packet and complete returned pool. Their finite application adapters preserve the original Source and native grades. The body domain still excludes indirect calls throughout its Source graph and requires strictly smaller named-family members and pointwise static and diagnostic policies.

Selected-call receipts retain the exact callee post, genuine first-stage acceptance, physical arity, dispatch row and successful ordered arguments. Qualification consumes one actual success step; its fourth-bind bound, argument effects and current admission stay attached to the same chosen closure. It does not construct a complete parent invocation or classify arbitrary function values.

Conditional named bodies now retain the fault from the actual condition or selected return branch. Both directions follow the real compiler finish, sequence, conditional and fallthrough wrappers, including the empty tail. The unselected branch is not evaluated. The post keeps the same primitive origin, body store, Source heap and token. Connecting this producer to the outer dispatcher and extending it to broader imperative bodies remain separate steps.

Ordinary closure formation now has a shared core accepting a static membership constructor for the same actual closure and its independently obtained native typing. Existing public wrappers retain their exact types and headers. Each direction uses one actual formation tuple, keeping the full heap, packet, post and effects. This enables a stronger function model to retain the positive chosen factory; it does not populate that model by itself.

At `4246eb3d`, registered Solcore modules and `Tests.Main` built successfully (**5529 jobs**). Strict verification checked **13354 declarations**, including **149 declarations attributed to four new proof modules and one modified module**, and **47 signatures**. All complete sources and the modified-module diff passed parent and two independent semantic reviews. All **43 original complete raw types and axiom arrays**, including generated declarations, and **12 original explicit declaration headers** remain unchanged. The comparisons include every line of each literal type. Policy, whitespace, exact Source hashes, regular normal objects and **4985 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

Next: assemble the actual accepted stored-call parent from the chosen callee and argument receipts, populate a function model retaining the positive chosen factory, and connect conditional fault producers to the outer named dispatcher. The shared mixed family, initial and captured heap coverage, prior General and principal selection, general callee classification, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Chosen function model, accepted stored parent and outer conditional fault posts

The latest implementation checkpoint is `529e4c2c`, following `04c98460`, `af5f8ef7`, `f8f9b774` and `0718b79e`.

The function value model now retains the actual chosen compiler factory, capture index, history and independently typed closure. Its prior branch retains the existing General representation. Forward forgetting is available; recovering a factory from an arbitrary prior value is still unproved. Actual formation receipts populate the positive branch through the shared formation core. Source and native expression heads use the same model and retain the complete heap, packet, post and effects.

The accepted stored-call adapter composes the real selected callee, ordered arguments, physical arity and current argument state with the chosen invocation proof. Both directions retain the original body continuation and full returned pool. Native reflection uses the authentic successful argument step and whole fourth-bind bound. The owning Source domain still excludes indirect calls, and strict callee induction and arbitrary callee classification remain separate obligations.

Conditional fault producers now feed the outer named dispatcher. Actual compiler acceptance derives the finish/sequence/conditional/return/fallthrough envelope, including the empty tail. The original argument and parameter receipts keep body-entry admission, stable rows and the same causal primitive fault, heap and token. Each direction uses the original conditional producer and outer call core once. Broader imperative bodies and complete static policy population remain open.

At `529e4c2c`, registered Solcore modules and `Tests.Main` built successfully (**5535 jobs**). Strict verification checked **13508 declarations**, including **155 declarations in separate inventories of six new proof modules**, and **54 signatures**. The separate inventories share one generated lemma, counted once in the combined audit. Every complete source passed parent and two independent semantic reviews. No original proof modules changed in this checkpoint. Policy, whitespace, exact Source hashes, regular normal objects and **4985 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

Next: generalize the existing body and invocation proofs to the chosen function model, connect strict callee induction to accepted stored parents, and extend outer fault posts to broader imperative bodies. The sole mixed-family closure, initial and captured heap coverage, prior General and principal selection, general callee classification, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Receiving function models, strict callee posts and lexical named-body faults

The latest implementation checkpoint is `ae0f3086`, following `9b8510f9`, `ad21b5c2`, `d35da032`.

The existing body, nested-continuation and invocation proofs now accept the receiving function model. They retain genuine formation membership, parameter Source receipts, current admission, the complete row pool and the actual selected body factory. Existing prepared-model APIs forward to these shared cores with their original types. The chosen model still retains the genuine General prior branch; these proofs do not recover a chosen factory from an arbitrary prior value.

The actual strict callee child now supplies its complete reached post and the model's selection at that same tuple. A callee fault retains the actual child post and stops before arguments. Accepted stored-call adapters receive the selected current model, complete ordered argument post and genuine physical dispatch receipts. Their body and caller-restoration proofs run once. The selected body's owning Source domain still excludes indirect calls; it remains distinct from the parent call's Source. Arbitrary callee qualification and the full mixed-family closure remain open.

The original lexical Tree, control and function-finish cores now carry a causal fault witness alongside their usual result. Their existing wrappers keep their exact APIs. The witness follows actual allocation, condition, branch, prefix and block joins and retains the current heap, all stable rows, native token, independent Source/native grades and final body store. A concrete named-body producer derives its builtin expression ports internally and uses those same Tree and finish proofs. Its current domain is finite discarded-expression prefixes ending in a final expression or an explicit return. Empty bodies, allocation prefixes and broader imperative producers remain separate work.

At `ae0f3086`, all registered Solcore modules and `Tests.Main` built successfully (**5540 jobs**). Strict verification checked **13762 cumulative declarations**, **450 declarations attributed to 14 new or modified proof modules**, and **166 signatures**. All **197 original declarations**, including generated helpers, retain their complete same-name literal types and axiom arrays. One original generated helper belongs to an already imported formation module; the normal audit checks its actual global declaration without counting it twice. The cumulative increase is 254 declarations.

All 14 frozen Sources passed strict compilation with warnings treated as errors. Two independent reviewers read every complete Source and all original-module diffs. The parent read all complete Sources outside the three original lexical modules, every added lexical proof region, and all four new lexical modules. Separate parent installation guards checked the exact reviewed hashes, authentic normal snapshots and complete literal original types. The integrated normal audit confirms actual imported modules, regular Source and object files, policy, whitespace, English text and **4985 protected original-file checks**. This checkpoint changes nine existing proof modules, adds five proof modules and updates the aggregation imports. Actual native and interpreted test executions remain those at `3ff3daf4`.

Next: derive the positive chosen-model callee post from a real initialized local read, connect that post to the actual accepted indirect parent, and extend the concrete named-body producer to an absent local allocation followed by its supported suffix. Keep the sole measured family induction. Initial and captured heap population, prior General and principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Chosen storage/read posts, strict indirect prefixes and absent local allocation

The latest implementation checkpoint is `3c770d21`, following `9469886c` and `5def781c`.

Actual initialized writes and marked allocations now retain the chosen receiving function model and the same known ordinary member. The existing heap producers run once. Allocation retains the capture, frame, marker, optional payload and literal map/world extension. An actual initialized local read keeps that positive member and constructs selection from independent occurrence and nominal-type receipts. Its callee endpoint derives the complete value post, Source admission and current pool. A separate same-post association endpoint identifies an already produced callee post using the real read witness; it does not run another read producer.

The strict callee child now supplies a conditional accepted indirect-parent resolver at its exact reached tuple. Both directions retain the actual chosen closure, original physical dispatch and stage facts, ordered arguments, argument faults, body effects and full returned pool. Native reflection also retains the original whole fourth-bind bound and successful prefix. Callee faults stop before arguments. The genuine positive chosen index and compiler/type/dispatch receipts remain required; arbitrary prior values are not classified by these endpoints.

The lexical named-body producer now exposes the same shared proof through additive `StaticBodyInputs`, without the earlier discard/return profile restriction. The original `BodyInputs`, public headers and wrappers remain unchanged. A concrete producer constructs a genuine absent local declaration followed by the supported discard/return suffix, then invokes the original lexical Tree and finish proofs once. It retains the allocated middle heap, current frame and all rows, causal fault, independent grades and actual final body store. Initialized declarations and forwarding these lexical body posts through the outer named/direct dispatcher remain next steps.

The accepted chosen invocation still requires `NoIndirect` over its entire owning Source. The parent call's Source may be distinct. This is a real domain restriction: when the actual parent and selected body use the same owning Source, the parent's indirect occurrence contradicts that hypothesis. The current endpoints therefore do not close a same-Source mixed runtime family. The next domain factor must use genuine static body/support coverage while retaining the actual chosen factory, nested bodies and strict children.

At `3c770d21`, all registered Solcore modules and `Tests.Main` built successfully (**5544 jobs**). Strict verification checked **13832 cumulative declarations**, **124 declarations attributed to five new or modified proof modules**, and **32 signatures**. All **54 original declarations**, including generated helpers, retain their complete same-name literal types and axiom arrays. All 124 private declaration blocks also match the normal compiled declarations literally. The cumulative increase is 70 declarations. Actual module ownership includes the generated `extendIndex.congr_simp` helper in the stored-post module; it is counted once.

All five complete Sources and the full 313-line original-module diff passed parent and two independent semantic reviews. Separate parent installation guards checked exact reviewed Source and regular object hashes, authentic before snapshots and actual compiled imports. The normal audit confirms **2225 actual project imports**, regular Source and both object files, policy, whitespace, English text and **4985 protected original-file checks**. This checkpoint changes one existing proof module, adds four proof modules and updates aggregation imports. Actual native and interpreted test executions remain those at `3ff3daf4`; this checkpoint changes proofs only.

Next: replace the whole-Source exclusion with genuine body/support coverage at the existing proof cores, connect initialized-read callee receipts to nonvacuous mixed runtime leaves, and forward lexical/absent-allocation body posts through the existing outer named/direct dispatcher. Keep the sole measured family induction. Initial and captured heap population, prior General and principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Invocation proofs with body domains and lexical outer call posts

The latest implementation checkpoint is `30658fc4`, following `13eb4e17` and `d97e6b75`.

The new chosen invocation path requires `NoIndirectOn` only for the expressions approved by the selected body factory. An indirect parent elsewhere in the same retained Source no longer contradicts this condition. Compiler coverage retains the actual approved occurrence on extra leaves and derives the non-indirect form of named leaves from their real receipts. The existing compiler fold and runtime head, tree and support proofs each run once. The legacy `NoIndirect`, certificates, public types and wrappers remain unchanged.

That restriction now passes through the actual nested continuation, payload application, ordered argument state and accepted stored parent. The scoped static inputs retain the same chosen factory, captures and diagnostics when map/world proofs extend. The source and native indirect endpoints build the strict callee post internally and keep prior alternatives, physical dispatch, argument faults, the whole fourth bind and the exact restored caller pool. These remain conditional producers: an actual chosen member, accepted compiler/dispatch receipts and supported body inputs are required. They do not construct those inputs automatically or close the complete mixed family.

A concrete outer named-call producer now obtains lexical body ports from the existing discard/return and absent-allocation producers. Actual argument evaluation constructs the real named parameter receipt, Source admission and stable rows. The original outer-call core then carries the same body result, causal fault, native token, final body store, independent execution grades and reached caller tuple through one physical restoration. Argument faults retain their real outer route. Initialized declarations, arbitrary blocks and branches are outside these concrete producers' current domain.

At `30658fc4`, all registered Solcore modules and `Tests.Main` built successfully (**5545 jobs**). Strict verification checked **13930 cumulative declarations**, **400 declarations across eight audited proof modules**, and **73 signatures**. One audited selected-call module is unchanged. All **302 original declarations** and all 400 private declaration blocks retain their complete same-name literal types and axiom arrays. Generated declarations are included and counted once under their actual module ownership; no supplements were needed. The cumulative increase is 98 declarations.

Each of the seven changed or new source files and every original-module diff received at least two complete reviews independent of its author. The parent read the two compiler/runtime files, the new outer-call producer, both complete diffs and the stored-parent parameter block; its independent guards verified all reviewed hashes, original types, regular source/object files and actual import closures. The normal audit confirms **2224 actual project imports** against the recursive compiled import graph and **4985 protected original-file checks**. Two unchanged-source consumers rebuilt their `.olean` files after their affected imports changed; their original Source and `.ilean` bytes remain exact, and the guards record the actual build and import paths. This checkpoint changes six existing proof modules, adds one proof module and updates the aggregation import. Actual native and interpreted executions remain those at `3ff3daf4`; this checkpoint changes proofs only.

Two parent metadata checks were corrected during verification: one omitted the audit's separate `COUNT` records; the other treated the two expected dependent rebuilds as unexpected changes. Final metadata checks pass. No proof changes or compiler reruns were required for these corrections.

Next: populate the chosen factory and supported body domain from actual accepted compiler results, starting with the checked literal-return lambda and its same-Source indirect parent. Use these genuine receipts to close the shared measured family. Extend the concrete body producers for initialized declarations and broader imperative bodies. Initial and captured heap population, prior General and principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Mixed lexical call posts and an accepted literal lambda fixture

The latest implementation checkpoint is `3c2026ca`, following `7e66e744`, `adb7db57`, `712e95bb` and `8ef65a35`.

The mixed lexical body producer now derives causal Source/native body posts from genuinely smaller expression children. Actual arguments construct the named parameter receipt, Source admission and stable rows. The outer named expression adapters consume these internally constructed body ports and the original ordered argument producer once. They retain the actual body store, independent execution grades, fault origin, restored caller pool and strict native completion bound. Static body typing, compiler receipts and the strict child induction remain genuine inputs.

Literal lambda static facts are derived from an independent Source lambda typing judgment and the actual compiler/frame receipts. A literal-root receipt retains one original contextual selector, its authentic plan record and the fixed read budget of the prepared compiler. The literal body shell constructs parameter entry, return syntax and native body typing internally. Its local domain excludes indirect calls only at the approved literal occurrence; an indirect parent elsewhere in the same Source is allowed. Source typing, runtime/Covers, constructor/profile coverage and broader builtin static facts remain explicit inputs to this conditional construction.

The new accepted fixture uses the actual parser, checker, worklist and public preparation for `accepted()`, whose local lambda returns `7` and whose indirect parent calls it with `(1, 2)`. It retains the untouched Source, original named slot, cached code, contextual compilation equations, numeric requirements and their valid evidence. The parent output is proved at the same selected initializer root using pointwise ordinary-branch equality. The proof keeps the original initializer budget 499, parent budget 498 and fixed read budget 500. It derives no equality between policies at different budgets.

A computable finite graph receipt derives the original occurrence-graph invariants: unique occurrence IDs, owned nodes/roots and existence of roots/child edges. Together with the real numeric ledger and declaration-context fields, it supplies `SourceRuntimeValid` for the fixture. Genuine lambda typing and the association of that context with the actual public Header remain to be constructed. Chosen factory/support population, whole mixed-family closure and Source/Core execution equivalence for the fixture remain open.

At `3c2026ca`, all registered Solcore modules and `Tests.Main` built successfully (**5553 jobs**). Strict verification checked **14618 cumulative declarations**, **691 declarations attributed to nine new or modified modules**, and **74 signatures**. All 691 private declaration blocks and all **three original declarations** retain their complete same-name literal types and axiom arrays. Only the three permitted standard axioms occur. The cumulative increase is 688 declarations. The newly registered fixture checker was executed successfully against the normal cache; it checks actual compiler and metadata receipts. The existing full registered test executions remain those at `3ff3daf4`.

All nine complete Sources passed strict compilation with warnings treated as errors, and each received at least two full semantic reviews independent of its author. Normal installation copied Source files only. Independent guards confirmed the reviewed Source/object hashes, **2225 pre-install Source/object pairs**, and exact agreement between **2221 actual compiled project imports** and the Lean environment. Two unchanged-source consumers rebuilt their `.olean` files after the original body-post module changed; their Source and `.ilean` bytes remain exact, and actual build/import paths explain those rebuilds. Policy, English text, registration, whitespace and **4985 protected original-file checks** pass. The checkpoint changes one existing proof module, adds seven proof modules and one test module, and updates the proof umbrella and test import/runner.

Next: construct independent lambda Source typing and actual public Header/context receipts for the accepted fixture, then populate its literal shell/domain and chosen factory from those genuine inputs. Feed those receipts into the sole measured mixed family. Initial/captured heap population, prior General/principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Accepted literal Source typing and original public Header

The fixture retains the original accepted specialization, lambda initializer and indirect parent in one unchanged Source. Finite metadata checks now prove absence of matches, empty coercion rows, the actual parameter inventory and successful Core projection of the literal return type. Independent declarative Source rules construct the lambda's parameter context, numeric literal typing, return statement, body typing and completion summary. Core typing is not used to infer these Source judgments.

The public Header association comes from the original specialization worklist, exact cached row, original compilation and genuine Source frame validity. It retains the Source owner, assumptions, parameter layout, body roots, ledger, contextual policy and actual compiler acceptance. This constructs the Header/context correspondence and runtime validity without a body execution or whole-program well-formedness premise.

The literal shell now requires equality of place diagnostics rather than equality of the entire program metadata. Installing the callable root table changes that metadata but preserves the actual places and their diagnostic reasons. The construction still uses genuine Source typing, compiler/frame receipts, runtime coverage and static builtin/constructor facts. The older shell remains unchanged.

Implementation commits: `2cacd8e1` (body metadata), `ca33552c` (independent lambda typing), `c7273ade` (original Header and checker registration), and `67a50253` (place-diagnostic shell and proof registration).

At `67a50253`, all registered Solcore modules and `Tests.Main` built successfully (**5557 jobs**). Strict verification checked **14863 cumulative declarations**, **245 unique declarations attributed to four added modules**, and **59 signatures**. All **246 private declaration occurrences** have exactly the same complete literal types and axiom arrays as the normal build. The generated `Tests.SourceCoreChosenOrdinaryAcceptedFixture.initialScope.eq_1` helper belongs to both isolated private inventories for BodyMetadata and Header, but to BodyMetadata in the combined normal inventory. Both occurrences match exactly. Only the three permitted standard axioms occur. The cumulative increase is 245 declarations.

All four complete Sources passed strict compilation with warnings treated as errors and received at least two independent full semantic reviews. Installation copied Source files only. Guards confirmed **2221 unchanged pre-install Source/object pairs**, exact agreement between **2211 actual compiled project imports** and the Lean environment, regular Source/olean/ilean files, and **4985 protected original files**. English, policy, registration and whitespace checks pass. Three newly registered checkers ran successfully; they validate actual compiler and static receipts, and do not establish Source/Core execution equivalence. Full registered executions remain those at `3ff3daf4`.

Next: construct independent typing of the outer let/indirect-call body, populate the literal shell/domain and chosen factory from these actual receipts, and connect them to the sole measured mixed family. Initial/captured heap population, prior General/principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Accepted outer body typing and literal Source input population

Independent declarative typing now covers the actual outer let, its fresh local binder and paired requirement tables, both numeric argument literals, their physical pair, the indirect call and the return. The complete body and completion summary are transported to the original public Header using its actual inferred result and context. All node types, numeric evidence and Source rows remain unchanged.

A finite check identifies every retained Source node through actual lookup receipts. It proves absence of unary assignments, value assignments, for-header assignments and constructors, and identifies the five numeric/local-reference/tuple rows in the builtin fragment. The original root's read and special callbacks retain their actual ordinary and generalized-local gates at each child scope and budget. The constructor law holds at the genuine residual context through form absence.

The selected compilation's diagnostic row and original preparation now construct an IssuedSource with the actual assignment table and place providers. The same-Produced callback retains its diagnostics, code and Compilation identities. The accepted Header, lambda typing and body metadata supply the literal shell's remaining local Source fields. Genuine issuer and policy/view identity inputs are retained by that shell adapter; automatic population of the entire chosen factory is still incomplete.

Implementation commits: `7124d2d6` (original diagnostic issuer), `6f6a199e` (outer Source typing), `494a8a8d` (full finite static inventory), and `c2ec5a7a` (literal Source inputs and test registration).

At `c2ec5a7a`, all registered Solcore modules and `Tests.Main` built successfully (**5561 jobs**). Strict checks verified **15036 cumulative declarations**, **173 declarations across four added modules**, and **53 signatures**. All 173 private complete literal types and axiom arrays match the normal build; only the three permitted standard axioms occur. Every Source passed strict compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2225 pre-install Source/object pairs** and **4985 protected original files**; **2215 actual compiled project imports** match the Lean environment exactly. Registration, English, policy and whitespace checks pass.

The two new finite checkers executed successfully against the normal cache. They check actual compiler/static fields and do not establish Source/Core execution equivalence. Full registered executions remain those at `3ff3daf4`.

Next: derive native typing of the actual initializer before Site selection, construct singleton catalog order and SourceTypes from original specialization/signature receipts, and populate the chosen literal factory without an external body execution premise. Then feed this support into the sole measured mixed family. Initial/captured heap population, prior General/principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Native typing and automatic selection of the literal body factory

The actual initializer now has Core typing before a lambda Site is selected. Its original accepted certificate supplies the real parameter compiler and literal body callback. The singleton parameter projection determines the packed native bundle; the unchanged native prefix supplies the frame cell, and the original expression hook supplies the callable descriptor. The proof uses no Produced, Site or completed body execution law as an input.

Original worklist specialization and executable checker interface receipts now determine the singleton Header catalog's raw parameters and specialized result. They construct SourceTypes in the genuine receiving context using its signature equality. Lexical variables and residual mode remain unchanged. The finite Source inventory supplies builtin read/special callbacks and constructor/coercion facts at each actual child scope.

The fixture now constructs the original diagnostic issuer, literal body inputs and shell internally. Its initializer selects one lambda Site, retaining the same Compilation, policy, body recipe, Source view and reason provider. The approved domain is fixed to literal occurrence 3 before collection. The chosen factory retains the actual collector inputs, certificate family and body entry. Its read budget is the original indexed budget 500; the initializer's lambda certificate uses compiler fuel 498. The independent static read index changes no generated code or execution budget.

`chosen_initializer` obtains the original named compilation and initializer root internally. `globals_at` and `domain_at` construct the literal compiler domain from the actual catalog, inventory and Source inputs. The Source still contains the outer indirect call at occurrence 5. This checkpoint constructs the chosen static factory and domain; the same recaptured Support's runtime meaning and the complete measured mixed family remain unfinished.

Implementation commits: `69b301b2` (original catalog SourceTypes), `bec71734` (native typing before Site selection), `22b4f9e0` (original issuer and body inputs), and `024a3491` (chosen initializer factory, literal domain and test imports).

At `024a3491`, all registered Solcore modules and `Tests.Main` built successfully (**5566 jobs**). Strict checks verified **15093 cumulative declarations**, **57 declarations across five added modules**, and **34 signatures**. Every complete private literal type and axiom array matches the normal build; only the three permitted standard axioms occur. All five complete Sources passed strict compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2229 pre-install Source/object pairs** and **4985 protected original files**. **2219 actual compiled project imports** match the Lean environment exactly. English, policy, registration and whitespace checks pass.

The five added modules are proof connections and add no executable checker. Existing full registered executions remain those at `3ff3daf4`; earlier finite fixture executions remain recorded at their original checkpoints. The work estimates remain about 70% for the second goal and about 85% overall; declaration counts are not progress percentages.

Next: derive each current-context domain and the local absence of indirect calls from the same chosen and recaptured Support, then prove the literal body meaning from its original expression and finish receipts. Retain the outer indirect parent and genuine capture, parameter and heap identities. The complete mixed family, initial/captured heap population, prior General/principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Selected literal return semantics

Original singleton return receipts now retain the compiler's actual child, emitted finish and callback budget. The literal factory derives its current-context domain and expression coverage from the same selected Support. Its approved domain remains literal occurrence 3; the unchanged outer Source contains the indirect parent at occurrence 5. The indexed read budget 500, initializer compiler fuel 498 and independent Source/native execution grades remain separate.

The actual Word node and its selected numeric evidence prove admitted expression preservation and finite-completion reflection. Both use the existing literal producer and retain the same initial heap, store, mapping, world and complete ordered record vector. No whole-program well-formedness or finished body semantics is assumed.

The body proof derives the certified child and return flow from the actual expression tree and Source syntax. Genuine parameter admission supplies the reached entry, Source receipt and all rows. The original finish transfers the return once; Source control establishes that break and continue cannot escape this body. Source/native continuations retain the same reached pool and returned value. Fixture helpers obtain the original body inputs, compiler receipt and Word facts internally.

Implementation commits: `ca7b7b57` (original singleton return compiler receipts), `d620422d` (admitted Word literal semantics), `b4dbc7db` (selected literal domain and coverage), `8a170eac` (literal body continuations and proof imports), and `77f71db7` (accepted compiler receipt connections and test imports).

At `77f71db7`, all registered Solcore modules and `Tests.Main` built successfully (**5571 jobs**). Strict checks verified **15161 cumulative declarations**, **68 declarations across five added modules**, and **37 signatures**. All 68 complete private literal types and axiom arrays match the normal build; only the three permitted standard axioms occur. Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2235 pre-install Source/object pairs** and **4985 protected original files**. **2225 actual compiled project imports** match the Lean environment exactly. English, policy, registration and whitespace checks pass.

These proof modules add no executable checker. Full registered executions remain those at `3ff3daf4`; earlier finite fixture executions retain their original checkpoints. The estimates remain about 70% for the second goal and about 85% overall. Declaration counts do not measure progress.

Next: derive the remaining current body ledger, capture/global, argument and deep Source heap receipts from actual initialization and invocation. Connect these literal continuations through the real stored-callee parent and caller restoration. The complete mixed family, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and final compiler theorem remain unfinished.

### 2026-10-09: Literal invocation and finite Source admission

The selected literal Support now supplies its body ledger and runtime validity internally. Its original body continuation feeds the actual frame installation and marked parameter allocations. The body finishes once, and invocation restores the saved caller in the same reached pool. Application uses that invocation directly; reflection retains the original strict child bound and independent Source/native grades.

Initialized callee admission now follows from the actual Source occurrence typing, initialized cell, environment correspondence and deep heap typing. The original read producer supplies the callee value relation at the same heap and complete ordered records. This finite connection does not require whole-program well-formedness or a broad runtime coverage premise.

The actual numeric argument occurrences 7 and 8 evaluate in order to the physical pair at occurrence 6. Their selected evidence excludes missing-evidence, coercion and literal faults. The resulting pair has raw parameter typing in any receiving Source context. Its actual trace and administrative effects establish successful admission at the same reached heap and transfer every stable record row.

The accepted fixture derives the literal parameters, result, body context, Word facts and original return receipts internally. Its invocation and application ports retain genuine dynamic captures, history, Source origin, captured globals, reference authority, Source heap typing, raw arguments and represented native arguments.

Implementation commits: `ef031a04` (actual paired Source argument admission), `0353c372` (initialized callee admission), `a6fcef3f` (literal invocation, application and proof imports), and `e55949f5` (accepted fixture invocation and test imports).

At `e55949f5`, all registered Solcore modules and `Tests.Main` built successfully (**5575 jobs**). Strict checks verified **15194 cumulative declarations**, **33 declarations across four added modules**, and **26 signatures**. All 33 complete private literal types and axiom arrays match the normal build; only the three permitted standard axioms occur. Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2245 pre-install Source/object pairs** and **4985 protected original files**. **2234 actual compiled project imports** match the Lean environment exactly. English, policy, registration and whitespace checks pass.

These proof modules add no executable checker. Full registered executions remain those at `3ff3daf4`; earlier finite fixture executions retain their original checkpoints. Estimates remain about 70% for the second goal and about 85% overall. Declaration counts do not measure progress.

Next: connect the actual paired Core argument tree, stored-callee dispatch, sidecar and selected codebook to the new invocation proofs at parent occurrence 5. Initial/captured heap population, the complete mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Accepted parent, paired arguments and stored application

The accepted fixture now retains the actual indirect parent compiler receipt under the same chosen root, policy, body lowerer, read budget and Header. Its callee is occurrence 9, its physical argument list is the singleton occurrence 6, and the parent is occurrence 5. Header equality transports these original receipts without selecting another root.

The actual parent acceptance derives the pair compiler tree and its two numeric children. Their original literal and tuple producers prove argument preservation and finite-completion reflection, including raw Source typing, deep heap admission and every ordered record row. No child execution law or whole-program well-formedness is supplied.

The selected function's genuine stage and physical parameter count derive the actual dispatch row's acceptance. Application uses the existing selected literal invocation once, preserving captures, history, reference authority and the reached pool. Independent Source inversion of the real call allocation and singleton return derives final heap typing and successful result admission. The original physical caller restoration occurs once.

Reflection of the original fourth bind retains its full SuccessPrefix, SuccessStep and PassedAt witnesses, then constructs the real parent Source outcome with an independent Source grade. The complete native callee and argument prefix still needs to be derived from whole parent completion. Actual sidecar, dispatch, stored-member and capture associations remain genuine inputs to this finite endpoint.

Implementation commits: `782d7013` (selected-row acceptance), `4cbfb0e3` (original parent compiler receipt), `646de0f0` (closed paired argument semantics), and `fdf51087` (stored application, actual call outcome and test imports).

At `fdf51087`, all registered Solcore modules and `Tests.Main` built successfully (**5579 jobs**). Strict checks verified **15311 cumulative declarations**, **119 declarations across four added modules**, and **35 signatures**. All 119 complete private literal types and axiom arrays match the normal build; only the three permitted standard axioms occur. The cumulative increase is **117**: the actual inventories also include two deferred `RecursiveNamedLoopContracts.ExecutesAt` equations already counted in the prior cumulative environment. Independent prior/current name censuses show no removals, and both complete original equation types and axiom arrays match literally.

Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2250 pre-install Source/object pairs** and **4985 protected original files**. **2236 actual compiled project imports** match the Lean environment exactly. English, policy, registration and whitespace checks pass. No executable checker was added; full registered executions remain those at `3ff3daf4`.

Next: derive the same chosen parent's actual sidecar, lambda origin, dispatch and selected codebook from its static receipts. Connect the original initialized stored read and closed pair argument tree to whole native parent completion. Initial/captured heap population, the complete mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished. The work estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

### Chosen dispatch and whole native parent prefixes (2026-10-09)

| Module | Proven connection |
| --- | --- |
| `CallableIndexedOwnedChosenOrdinaryArgumentBundles` | The actual callee value relation and known chosen carrier identify native parameter and result types. Original parameter alignment consumes actual argument values at the reached map and world. Source arity and raw binder types remain independent inputs. |
| `CallableIndexedOwnedChosenOrdinaryCallDispatchReceipts` | The positive chosen member and original Prepared callsite supply the real sidecar, lambda origin, complete codebook rows, dispatch and selection. Runtime association to the actual callee post remains explicit. |
| `CallableIndexedOwnedStoredIndirectPurePrefixBounds` | Whole Core parent completion aligns the native callee child with the supplied genuine callee value post and extracts the ordered argument post, cumulative effects, successful prefix, successful step and full fourth bind. It uses genuine callee admission, accepted guards, strict argument children and finite Source argument fault exclusion. The measured application child remains for the existing application theorem. |
| `SourceCoreChosenOrdinaryAcceptedParentEntryReceipts` | The same accepted parent receipt supplies the initialized callee trace and value post and the original pair tree with all-size preservation and reflection. Initial heap, environment, stored lookup, native typing and admission retain their original authority. |

Implementation commits: `c236c562` (native argument bundles), `e57a93d5` (actual chosen dispatch), `5cc73e36` (whole native prefix and production imports), and `49f420e0` (accepted parent entry producers and test import).

At `49f420e0`, all registered Solcore modules and `Tests.Main` built successfully (**5583 jobs**). Strict checks verified **15402 cumulative declarations**, **91 declarations across four added modules**, and **25 signatures**. Every complete private literal type and axiom array matches the normal build; only the three permitted standard axioms occur. Authentic prior/current name censuses show **91 additions**, no prior overlap and no removals. Generated helpers are counted by the actual Lean module index.

Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2256 pre-install Source/object pairs** and **4985 protected original files**. The four audited modules' **2233 actual project imports** match their compiled closure and Lean environment exactly. Independent stored Source snapshots also retain their original hashes. English, policy, registration and whitespace checks pass. No executable checker was added; full registered executions remain those at `3ff3daf4`.

Next: compose these producers and the existing literal application theorem into preservation and reflection for the accepted whole parent, deriving the callee post, argument meanings, fault exclusion, dispatch and native bundle internally. Initial/captured heap population, the complete mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished. The work estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

### Accepted whole parent preservation and reflection (2026-10-09)

| Module | Proven connection |
| --- | --- |
| `CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport` | Genuine Source equality transports the original compiler sidecar, lambda origin, dispatch and selected rows at the same chosen root. |
| `SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes` | Independent sized Source traces fix the actual singleton pair values and heap and exclude argument faults. |
| `SourceCoreChosenOrdinaryAcceptedParentPreservationBounds` | The whole Source parent derives its actual callee and pair producers, selected guards and native bundle internally, then uses the literal application proof once to construct Core evaluation and the full returned result. |
| `SourceCoreChosenOrdinaryAcceptedParentReflectionBounds` | Whole Core parent completion yields the real successful prefix. One unpack of its successful step retains the same argument state and cumulative effects; the original application reflection runs once, and the independent Source parent is reconstructed. |

Both directions retain the original compiler, receiving function model, positive chosen carrier, closure capture, history and physical caller restoration. Final value and heap relations, mapping/world extensions, administrative preservation, Source heap metadata and returned caller admission are composed at the same actual intermediate witnesses. Initial heap, environment, stored-cell authority, native typing and input admission remain genuine inputs. These proofs assume no completed child/body execution law or whole-program well-formedness.

Implementation commits: `48f9dc42` (actual Source transport) and `3a99ac67` (whole parent preservation/reflection, argument outcomes and test imports).

At `3a99ac67`, all registered Solcore modules and `Tests.Main` built successfully (**5587 jobs**). Strict checks verified **15455 cumulative declarations**, **53 declarations across four added modules**, and **20 signatures**. Every complete private literal type and axiom array matches the normal build; only the three permitted standard axioms occur. Authentic prior/current name censuses show **53 additions**, no prior overlap and no removals. Generated helpers are attributed by actual Lean module index.

Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2260 pre-install Source/object pairs** and **4985 protected original files**. The four audited modules' **2249 actual project imports** match their compiled closure and Lean environment exactly. Original Source snapshots retain their hashes. English, policy, registration and whitespace checks pass. No executable checker was added; full registered executions remain those at `3ff3daf4`.

Next: derive the actual initialized-let allocation and outer-return flow from original named-body acceptance, then connect real lambda formation and one marked allocation to the proved parent. Initial/captured heap population, the complete mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished. The work estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

### Accepted initialized allocation and finite outer-body ports (2026-10-09)

| Module | Proven connection |
| --- | --- |
| `SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts` | Original body acceptance supplies the initializer, marked Allocation/Annotated receipts and exact initialized-let/return flow and finish under the same selected root. |
| `SourceCoreChosenOrdinaryAcceptedInitializerAdmission` | Actual lambda typing, frame coverage and captured-environment agreement derive the same receipt's raw closure typing, pure Source outcome and unchanged-state admission. |
| `CallableIndexedOwnedChosenOrdinaryInitializedAllocationState` | One original stateful marked allocation retains every reached-state output and attaches positive `ChosenStoredAt` for the actual initialized cell in the receiving model. |
| `SourceCoreChosenOrdinaryAcceptedOuterBodyBounds` | Actual native initializer, allocation and parent traces compose value/fault completion. Whole completion yields a genuine strict parent child; finite Source body inversion retains the initializer, allocation and parent outcome. |

The allocator keeps actual environments, Source/native heaps, mappings, worlds, frame references and metadata, every ordered row, and reached-state admission. The finite native ports retain the literal final body store and fault token. Source inversion retains its own execution grades independently of native child grades. These are concrete composition ports; complete whole-body preservation and reflection with admission have not yet been assembled.

Implementation commits: `5121afc3` (positive initialized allocation state) and `b024dfd3` (actual compiler receipts, initializer admission, finite outer-body ports and registrations).

At `b024dfd3`, all registered Solcore modules and `Tests.Main` built successfully (**5591 jobs**). Strict checks verified **15541 cumulative declarations**, **87 declarations across four added modules**, and **42 signatures**. Every complete private literal type and axiom array matches the normal build; only the three permitted standard axioms occur. Authentic name censuses show **86 additions** and no removals. The one prior overlap, `Tests.SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason.eq_1`, has exact complete type/axiom agreement with an independent probe of the original imports. Generated helpers are attributed by actual Lean module index; the four private inventories have no shared declaration names.

Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2266 pre-install Source/object pairs** and **4985 protected original files**. The four audited modules' **2255 actual project imports** match their compiled closure and Lean environment exactly. Original Source snapshots retain their hashes. English, policy, registration and whitespace checks pass. No executable checker or IO runner was added; full registered executions remain those at `3ff3daf4`. Validation records: `/private/tmp/solcore-owned-functions-resume-20261007/accepted-outer-body-ports-checks.json` and its actual command receipts.

Next: retain the actual Header constructor's empty evidence, compose formation, one marked allocation and the initialized parent at the same reached state, and align the parent child with whole native completion by reconstruction and determinism. Complete preservation and reflection of that body with admission, initial/captured heap population, the shared mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished. The work estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.


### Accepted whole outer-body preservation and reflection (2026-10-09)

| Module | Proven connection |
| --- | --- |
| `SourceCoreChosenOrdinaryAcceptedHeaderEvidence` | The same original Header constructor retains `HeaderAt` and genuine empty evidence; no equation is inferred from emitted code. |
| `SourceCoreChosenOrdinaryAcceptedInitializedEntry` | One original formation and one stateful initialized allocation retain the actual admitted parent entry, positive stored member and original formation history. |
| `SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction` | Actual initializer execution, Source allocation and parent outcome construct the original initialized-let/return body with independent Source grades. Raw admission transports to Γ0 at the same reached state. |
| `SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds` | `preserves_body` and `reflects_body` compose the admitted parent internally and retain the full final body result, cumulative effects, actual restored caller and all rows. |

Preservation inverts the original Source body, obtains its real allocation, and runs the initialized parent at the same reached state. Reflection constructs a genuine Source allocation independently of a Source execution premise, extracts the original strict native parent child, and reflects that child once. The resulting parent evaluation reconstructs whole native execution; determinism identifies both its final value and final store with the supplied whole completion. The finite Source constructors then build the independent body trace. Source and native grades remain independent.

The returned result keeps the actual final heap/store, mapping and world extensions, administrative preservation, Source heap metadata, restored caller pool and every ordered row. Successful raw value and deep heap typing transport from the local binder context to the original Γ0. Lexical scope restoration preserves the same reached pool and records.

Initial Source environment `[]`, actual captures and history, raw/native heap correspondence, native environment typing, frame/global references and reads, genuine allocator readiness and initial all-row admission remain explicit. These finite body ports contain no completed child/body law or whole-program well-formedness premise. The actual Header evidence equation remains explicit in the body ports and is available from the authentic Header constructor.

At `57485ac4`, all registered Solcore modules and `Tests.Main` built successfully (**5595 jobs**). Strict checks verified **15605 cumulative declarations**, **64 declarations across four added modules**, and **18 signatures**. Every complete private literal type and axiom array matches the normal build; only the three permitted standard axioms occur. Authentic prior/current name censuses show **64 additions**, no prior overlap and no removals. Generated helpers are attributed by actual Lean module index; the four private inventories have no shared declaration names.

Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2270 pre-install Source/object pairs** and **4985 protected original files**. The four audited modules' **2259 actual project imports** match their compiled closure and Lean environment exactly. Original Source snapshots retain their hashes. English, policy, registration and whitespace checks pass. No executable checker or IO runner was added; full registered executions remain those at `3ff3daf4`. Validation records: `/private/tmp/solcore-owned-functions-resume-20261007/accepted-outer-body-preservation-bounds-checks.json` and its actual command receipts.

The work estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

Next: connect these finite body ports to the public BodyState interface and populate the genuine initial heap, captured environment, frame and complete rows. The shared mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, composition of all passes and the final compiler theorem remain unfinished.

### Accepted body correspondence at the actual parameter state (2026-10-09)

At `0a48ccf2`, four additive modules connect the accepted whole-body proofs to the original named parameter Receipt. BodyStatePorts derives the actual empty Source entry, captures, global references, native typing, readiness and admission. InitialBodyAdmission derives deep heap typing and all rows from real empty-parameter allocation and singleton hook effects. HeaderRuntimeEvidence retains the actual global count and empty evidence. BodyStateCorrespondence supplies preservation, reflection and the existing SourceBodyAt/NativeBodyAt interfaces at the same reached state.

The full returned pool, cumulative effects and successful raw PostAdmission are retained. No completed body law or ProgramWellFormed premise is added. Complete catalog and zero-prefix receipts remain genuine inputs. Stronger ReachedExit/LexicalResult witnesses are not asserted.

The registered build passed 5599 jobs. Strict checks verified 15684 cumulative declarations, all 79 declarations of the four new modules and 32 signatures. Complete private/normal types and axiom arrays match literally; only the three permitted standard axioms occur. Authentic name censuses show 79 additions, no prior overlap and no removals. Normal Source/object guards and all 4985 protected-file checks pass. No executable fixture checker was added in this checkpoint.

Next: retain the actual successful public Recipe preparation, bootstrap constructor fields and concrete store/capture association, then join the same singleton pool, hook and parameter producer to this Receipt. Public Session association, the shared mixed family and all-pass compiler correctness remain unfinished.

### Accepted public bootstrap and actual parameter Receipt (2026-10-09)

| Module | Proven connection |
| --- | --- |
| `RecursiveNamedCatalogPreparedInitializationReceipts` | `stored_capture` and `entry_with_constructor` retain the prescribed initialized capture and actual initialization authority, with frame zero, empty current/ghost ownership and no records. |
| `SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt` | `prepare_public` retains one actual Recipe.prepare equation. `complete_bootstrap` retains one original runStateful completion; `completed_store` identifies its initialized store without rerunning either producer. |
| `SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence` | The same authentic Header constructor retains runtime evidence, layout equality and empty Source captures. Native captures remain the actual installer data. |
| `SourceCoreChosenOrdinaryAcceptedPublicParameterEntry` | Derives the singleton checker ledger, Complete and initial state at the actual completed store, then uses the original hook installation and parameter action once to return the same Receipt and ContinuationAgreement. |

The unchanged accepted fixture has one named row. Its positive public bootstrap checker succeeds at fuel 10000 and observes a two-cell initialized store. The symbolic receipt retains the original Recipe acceptance and exact machine completion.

The parameter entry derives native store typing, the empty Source heap relation, every initial stable row and the prescribed live capture from that same initialization constructor. Original named hook history and real frame installation feed `parameters_with_state` once. The returned parameter Receipt keeps the actual BodyState, reached pool, ordered records, Source admission and complete prefix/body ContinuationAgreement. The parameter proof uses the retained Recipe acceptance, machine completion and Header evidence; its function model and metadata registry remain parameters. It assumes no completed body law or ProgramWellFormed premise.

At `783a716f`, all registered Solcore modules and `Tests.Main` built successfully (**5603 jobs**). Strict checks verified **15836 cumulative declarations**, all **152 declarations across four added modules**, and **45 signatures**. Every complete private literal type and axiom array matches the normal build; only the three permitted standard axioms occur. Authentic censuses show **152 additions**, no prior overlap and no removals. Generated helpers are attributed by actual Lean module index.

The initial normal validation passed Source, type/axiom, signature and fixture checks, then failed because its cumulative census omitted `Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization.environment.eq_1`. An independent probe of the same environment identifies its actual owner as `RecursiveNamedPublicBootstrapGlobals` and confirms complete literal type/axiom agreement. The corrected census includes that one genuine helper. The original failure is preserved; only the cumulative stage was rerun, and the original successful bootstrap execution remains the single new checker run.

Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2278 pre-install Source/object pairs** and **4985 protected original files**. The four audited modules' **2267 actual project imports** match their compiled closure and Lean environment exactly. Original Source snapshots retain their hashes. English, policy, registration and whitespace checks pass. Validation records: `/private/tmp/solcore-owned-functions-resume-20261007/accepted-public-parameter-entry-checks.json` and its actual command receipts.

One positive bootstrap IO call is newly registered. Existing full registered executions remain those at `3ff3daf4`. The work estimates stay about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

Next: compose the existing admitted body preservation/reflection and SourceBodyAt/NativeBodyAt interfaces at this actual public Receipt. Association with a returned public Session, stronger ReachedExit/LexicalResult witnesses, general mixed bodies, all-pass composition and the final public compiler theorem remain unfinished.


### Accepted public body, invocation and ready Session receipts (2026-10-09; `46df219c`)

| Module | Proven connection |
| --- | --- |
| `SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence` | One actual public parameter receipt supplies BodyAtReceipt, admitted whole-body preservation/reflection and the existing SourceBodyAt/NativeBodyAt interfaces. |
| `SourceCoreChosenOrdinaryAcceptedPublicInvocation` | Genuine public initial state and capture supply each original named invocation. Its own parameter child is packaged as the actual receipt, with body meaning derived internally and caller restoration retained. |
| `SourceCoreIndexedSession` | Erased RecipeAt/InitialAt receipts share original artifact mint and session construction. Actual ready inversion retains native completion and the same Session authority, world/store, full prefix, physical registry and initial metadata context. |
| `SourceCoreChosenOrdinaryAcceptedPublicSessionEntry` | The retained actual ready equation supplies CompletedBootstrap proof-only. Body and invocation ports use the same actual Session native world/store and checked static registry. |

The body proof retains its full admitted returned result and successful raw PostAdmission. The low invocation proof retains original parameter execution, caller restoration, returned pool and cumulative effects; it does not assert stronger invocation post-admission or ReachedExit/LexicalResult. Header, Source typing, inventory and genuine compiler/root receipts remain inputs. Source and native execution grades remain independent.

The original Recipe.open, Artifact.bootstrap and bootstrapFresh operational types remain exact. The shared receipt producers perform one artifact mint and one session-authority creation. Original finish/resume validation, error, fuel-exhaustion and impossible native-fault branches remain unchanged. NativeDone alone does not establish readiness: resume_ready_receipt requires the actual successful ready equation. BootstrappedFrom retains the entire supplied prefix; metadata RegistryAt is distinct from the physical handle registry.

Strict normal Source checks are empty and use warningAsError. The 117-line public body module has a full audit of 13 declarations and 8 positive API checks; the 250-line public invocation module has 28 declarations and 11 API checks. The 2315-line Session module has 1441 declarations and 20 API checks. That whole-module count includes the original declarations and is not a net-addition count. The 158-line public Session consumer has 39 declarations and 10 API checks, plus an actual ready IO run. The complete four-module audit has 1521 declarations and 49 API checks, with no cross-module shared names. The private before union covers 2282 Source/object pairs, and the complete normal pre-install snapshot covers 5526 modules, including the Tests.Main registration cone.

Complete unnormalized original/current comparison reports 1412 exact original declaration types and axiom arrays, one explicitly approved generated-helper change and no missing original names. The genuine generated Artifact.bootstrap._proof_1 changes from native initial-state typing to Recipe reflexivity after factoring. Its original 2750-byte TYPE/AXIOMS block appears literally unchanged at the new generated Artifact.bootstrapWithReceipt._proof_1. The exact old/new same-name blocks and movement were independently reviewed; raw comparison failures are preserved. No helper alias, type normalization, deleted declaration or extra axiom is used.

The newly registered normal Session check prepares the unchanged fixture and Recipe once, opens one artifact, creates one fresh checkpoint and resumes it once at fuel 10000. It actually returns ready with two native cells and zero physical handles. Its proof-only receipt retains the same initialization store. This test exercises public bootstrap readiness; it does not execute a public root call or authenticate a successful exported program result. The Session consumer uses the retained completion directly, without first running a standalone bootstrap and then resuming it again.

The code checkpoint is `46df219c`. The registered normal build passed 5606 jobs. Strict checks verify 15944 cumulative declarations, all 1521 current declarations, 49 signatures and complete literal private/normal TYPE/AXIOMS agreement using only the standard three axioms. The cumulative census adds 108 names, overlaps 1413 prior names and removes none; the overlap retains 1412 exact originals and the one explicitly approved generated-helper change. The actual compiled closure equals the 2270-module Lean environment. All 49 changed existing object pairs are covered by the original reverse dependency cone and actual successful build records; independent Source/paired-object snapshots and all 4985 protected original files pass. The new registered public Session runner executes once in normal validation and returns ready at fuel 10000 with two native cells; its exact log is 113 bytes. Two existing registered regression units pass separately with a 163-byte log. This does not claim execution of every registered test. The preceding committed verification sections remain historical records. The estimates stay about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

Next: connect actual public root start/call and native completion, Source program admission/staging, and authentic success/export receipts to the pointwise invocation bounds. Stronger invocation post-admission/ReachedExit/LexicalResult, arbitrary mixed bodies, prior General/principal qualification, general dispatch, rejection/coercion routes, all-pass composition and the final public compiler theorem remain unfinished.

### Accepted public program outcomes and Word exports (2026-10-10; `7b0f562f`)

| Module | Proven connection |
| --- | --- |
| `SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission` | Finite full-catalog equality retains the original singleton checked function and absence of methods. Original checker typing and actual stage analysis derive ProgramWellFormed and ProgramHasStages without a global inference-soundness premise. |
| `SourceCoreChosenOrdinaryAcceptedPublicRootStart` | The actual successful Session.start selects the singleton Header. The original global/capture read and invocation give preservation and reflection at the same native checkpoint and initialization store. |
| `SourceCoreChosenOrdinaryAcceptedPublicResultObservation` | The receiving chosen model gives exact Word equality or the genuine language-fault relation from the full invocation result. |
| `SourceCoreIndexedSession` | One resumeWithReceipt shares the original runStateful and completion action. Actual success/failure inversion retains decoding, slots, the full store/prefix and authority; requested raw Source typing and Word export facts remain tied to the real checkpoint. |
| `SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome` | One StaticReceipt collector and actual public action chain derive admitted independent ProgramOutcome, sufficient native fuel and identical successful Word export. The same full low returned-state relation remains. |

For the retained accepted fixture, the same public Session root start and actual resume receipt now connect independent Source ProgramOutcome to native completion and the identical exported Word. Original checker typing and the actual stage analysis establish program admission internally. Reflection uses the successful public decoder equation; a Source Word result crosses the same boundary with sufficient native fuel and a positive export budget. The full low invocation result retains final heap correspondence, the restored owned pool and cumulative effects. Source and native budgets remain independent.

The static collector checks originalCatalog once on the same retained fixture. Full original checked-function equality, the original checker budget of 1024, genuine body typing and actual stage analysis establish Source admission. It does not assume global checker soundness or accept a completed body/pass law. The original empty Source heap and nil raw argument typing are derived at the actual Header context.

The public collector keeps the original ready Session, starts its selected root once and resumes that root checkpoint once. Native completion reflects to a genuine Source ProgramOutcome. An independent Source completion yields sufficient native fuel for that same checkpoint. Actual successful export excludes the native language-fault branch by its retained decoder equation and returns the identical Source Word and raw result type. Source Word preservation requires a positive export budget. This unit does not claim general correspondence for public failed/export-error outcomes.

The erased completion receipt shares the original resume/mint action. Original operational signatures and finish branches remain exact. The whole Session baseline comparison reports 1440 original same-name literal TYPE/AXIOMS matches and one explicitly reviewed generated resume-helper migration. Its moved proof has two generated binder-label differences; the literal blocks and original comparison failure are retained. No type normalization or manual alias is used. All 1678 current private/normal TYPE/AXIOMS blocks match literally in normal validation.

All five private packets are frozen. Their full audits contain 1551 Session declarations, 19 original-program declarations, 18 root-start declarations, 10 result-observation declarations and 80 consumer declarations; the corresponding positive API counts are 58, 12, 8, 7 and 16. The independent normal audit verifies 1678 unique declarations, equal to the private occurrence total; the cumulative net growth is recorded separately. The authentic private consumer run returns public Word 7 at native fuel 10000 with a 127-byte log. It also measures originalCatalog acceptance on that same fixture. The separately recorded first normal-environment run also returns Word 7 with a 127-byte log; the declaration-name census repair retains both successful execution receipts.

The code checkpoint is `7b0f562f`. The registered normal build passed 5610 jobs. All five strict Source checks produced empty logs. The normal audit verifies 16181 cumulative declarations, all 1678 current declarations and 101 signatures, using only the standard three axioms. Every current private/normal TYPE/AXIOMS block matches literally. The cumulative census adds 238 names and removes the single reviewed generated resume helper, for net growth of 237; all 1440 prior/current overlapping declarations remain literal exact. The pre-install snapshot retains 5539 original Source/object triples. The actual compiled closure equals the 2287-module Lean environment; all 35 changed existing object pairs have successful rebuilds within the original dependency cone. All 4985 protected original files remain unchanged. The first normal public program runner returns Word 7 at fuel 10000 with a 127-byte log. Two existing Session and packed-invocation regression units pass separately with a 163-byte log, covering suspension/resumption, shared writes, handles, stage checks and language-fault state. These executions do not cover the full registered suite. Successful IO, Source and full/API audit receipts were retained during the bounded declaration-name census repair.

Stronger invocation PostAdmission and actual lexical ReachedExit/LexicalResult remain unfinished. General mixed bodies, prior General/principal qualification, general dispatch, rejection/coercion routes, specialization/evidence/comptime composition and the final theorem for the complete public compiler remain unfinished. The estimates stay about 70% for the second goal and about 85% overall; declaration counts do not measure progress. The existing dated checkpoints remain historical records.

### Accepted public program post-admission (2026-10-10; `4aa849f8`)

| Module | Proven connection |
| --- | --- |
| `CallableIndexedOwnedNamedProgramAdmission` | Genuine ProgramOutcome supplies successful raw value and deep heap typing in the actual Header function context. Saved stable rows follow the final administrative frame at the same returned state. |
| `CallableIndexedOwnedBodyRestorationAdmission` | The original caller restore runs once and retains its complete tuple. Saved rows and the actual restored frame retain every returned history; successful typing moves only through genuine TypeContextSupports. |
| `SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission` | The existing native/Source and Word-export proof producers run once. The enriched ResultAt keeps the original six effects, same returned State, Relates and PostAdmission. |

For the retained accepted fixture, preservation and reflection now retain successful raw Source value typing, deep heap typing and every returned row's own stable history at the same actual restored caller state. The companion keeps the original heap correspondence, cumulative effects and returned pool. It consumes each existing program/export producer once and retains independent Source and native budgets. Faults retain stable rows without claiming successful value or deep heap typing.

The generic proof derives the actual Header body identity and successful typing from the original admitted program outcome. It accepts no arbitrary body law or ProgramWellFormed premise. `after_program_transition` eliminates the original transition once and retains that same witness. The optional restoration helper keeps the body's raw heap and the returned pool's exact records. Fault post-admission requires stable rows, with no successful value/deep heap claim. The public companion changes proof interfaces only; it performs no execution action.

The code checkpoint is `4aa849f8`. The registered normal build passed 5613 jobs. All three strict Source checks produced empty logs. The normal audit verifies 16201 cumulative declarations, all 20 declarations of the three added modules and 16 signatures, using only the standard three axioms. Every complete current private/normal TYPE/AXIOMS block matches literally. Authentic name censuses show 20 additions, no prior overlap and no removals. The pre-install snapshot retains 5543 original Source/object triples. The actual compiled closure equals the 2290-module Lean environment. The two changed existing object pairs are covered by the five-module dependency cone and five actual successful rebuilds. All 4985 protected original files remain unchanged. This checkpoint adds no runner and executes no IO or test suite; the public Word 7 and two existing regression receipts at `7b0f562f` remain historical evidence.

Validation records: `/private/tmp/solcore-owned-functions-resume-20261007/accepted-public-program-post-admission-checks.json` and its actual command receipts.

Genuine lexical ReachedExit/LexicalResult and their propagation through general body finish and caller restoration remain unfinished. General mixed bodies, prior General/principal qualification, general dispatch, rejection/coercion routes, specialization/evidence/comptime composition and the final theorem for the complete public compiler remain unfinished. The estimates stay about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

Next: retain genuine lexical exit from the actual outer body finish, populate the stronger named parameter Receipt body ports, and propagate that witness with admission through the original caller restoration.

### Accepted body lexical exit at the actual public parameter Receipt (2026-10-10; `f0274543`)

| Module | Proven connection |
| --- | --- |
| `SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit` | The real initialized binder and parent Source outcome produce genuine lexical exit at the same final map/world. Both whole-body ports retain the original represented result, returned pool and admission. |
| `SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts` | The actual BodyState supplies the full lexical administrative context, authentic capture/packet/readiness and Source admission. One outer-body proof in each direction fills the existing strong parameter Receipt result. |
| `SourceCoreChosenOrdinaryAcceptedPublicBodyExitReceipts` | One original public parameter entry retains the same initial state, actual Receipt and ContinuationAgreement, then supplies both strong body contracts for every size. |

The accepted initialized body now preserves and reflects genuine lexical exit and LexicalResult with the same represented result, cumulative effects, returned pool and PostAdmission. The BodyState adapter uses the actual parameter Receipt's full administrative environment; creator capture remains separate. One public parameter entry supplies the same initial state, Receipt and ContinuationAgreement and both strong body contracts at independent grades.

Lexical exit comes from the actual Source body/control constructors and represented reached binder environment. The BodyState administrative context is `packTypes (caller.bindings.map Prod.snd) :: receipt.administrative`; the shorter creator capture is not used to identify that suffix. Header scope/source/context and the genuine empty parameter environment are transported while every dynamic index remains fixed. Native reflection retains its independently constructed Source grade and actual whole-body value/store alignment. The public factory reuses the existing receiving chosen model and actual completed bootstrap. It does not replay a parameter, bootstrap or execution action and assumes no completed body law or ProgramWellFormed premise.

The registered normal build passed 5616 jobs. All three strict Source logs are empty. The normal audit covers 60 unique declarations and 17 signatures; complete private/normal TYPE/AXIOMS blocks match literally and use only the standard three axioms. The cumulative census is 16260, up from 16201: 59 new names, one exact prior overlap and no removals. The overlap is `Tests.SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captures_at_entry.congr_simp`; its saved-before TYPE/AXIOMS block matches the current block literally. The pre-install snapshot retains 5546 original Source/object triples. The compiled closure equals the actual 2271-module Lean environment. The sole changed existing object pair, `Tests.Main`, is covered by the four-module dependency cone and exactly four successful rebuilds. All 4985 protected original files remain unchanged.

The complete normal full log is 81655504 bytes, the API log 60583 bytes, the saved-before overlap log 792345 bytes and the cumulative log 1841739 bytes. These are retained successful command receipts. No declaration or imported namespace is omitted from the census.

No runtime/Core specification changes, runner or IO are added. The earlier public Word 7 and existing regression executions remain historical evidence. This checkpoint does not establish a stronger public Session or generic invocation theorem.

Generic named invocation must still carry this same body exit and admission through caller restoration. The existing low interfaces discard these fields, and a protocol Transition or successful PostAdmission cannot supply lexical exit. General mixed bodies, prior General/principal qualification, general dispatch, rejection/coercion routes, specialization/evidence/comptime composition and the final all-pass compiler theorem remain unfinished. The estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

Next: retain the same strong body result through the original invocation callback and actual caller restoration, preserving the genuine lexical witness and admission without projecting through the low body interface.

### Generic named invocation retains the same body fact through caller restoration (2026-10-10; `8d2289c5`)

| Module | Proven connection |
| --- | --- |
| `NamedInvocationFaultPostContracts` | A dependent BodyExtra and the actual restored frame are retained inside the original causal existential. Forgetting preserves every original entry, state, trace, history and effect witness. |
| `CallableIndexedOwnedInvocationBounds` | Both directions consume the real body callback once, keep its same completed state and perform the original caller restore once. Legacy post-only ports wrap the same witness with TrivialExtra. |

Generic named invocation now retains a supplied `BodyExtra` at the same actual body entry, parameter state and completed body state. Preservation and reflection keep that fact inside the original causal receipt, together with the actual restored frame. Each core consumes its original body callback once and performs the original caller restore once. Source and native grades remain independent. Legacy post-only interfaces attach `TrivialExtra` to the same body witness and forget the added fields.

The next unit connects genuine strong named parameter Receipt results to this retained family, then uses `restore_post` with saved stable rows, the actual restored frame and genuine context support to add caller admission. The generic factor does not itself derive lexical exit or successful admission. Neither follows from a protocol Transition. General mixed bodies and the final all-pass compiler theorem remain unfinished.

All 50 retained same-name original TYPE/AXIOMS blocks match literally. Two generated proof helpers move from the legacy `with_post` cores to `with_extra`; the reviewed differences are their generated names and hygienic binder labels. All other TYPE fields and complete axiom arrays are retained. These moves are recorded separately from the same-name matches.

Normal verification passed: 5616 build jobs, two empty strict Source logs, 62 declarations (15 lower / 47 upper) and 36 signatures (26 retained / 10 new), with all private/normal TYPE/AXIOMS blocks literally equal and only the standard three axioms. The cumulative census is 16270 from 16260: 12 additions, two reviewed generated-helper removals and 50 retained overlaps, for net growth of 10. The 5549-row before snapshot and 1954-module import environment passed; 10 changed existing object pairs are covered by the 360-module reverse dependency cone and 360 actual rebuilds. All 4985 protected artifacts remain unchanged. Registrations are unchanged, and this factor adds no IO or runner. Earlier public Word 7 and regression executions remain historical evidence.

The two reviewed generated moves are `invocation_preserves_bounded_at_with_post._proof_1_1` to `invocation_preserves_bounded_at_with_extra._proof_1_1` and the corresponding reflection helper, within `CallableIndexedOwnedInvocationBounds`. The public legacy declarations remain at their original names and signatures. The private original census has 52 declarations: 50 exact same-name matches and these two expressly reviewed moves. The measured cumulative census has 12 additions, these two reviewed removals and 50 retained overlaps; net growth is 10.

No stronger public Session, successful caller admission or new lexical-exit derivation follows from the uninterpreted retained family alone. The downstream strong Receipt adapter and its accepted public companion remain uncompiled W-only drafts. General mixed bodies, prior General/principal qualification, general dispatch, rejection/coercion routes, specialization/evidence/comptime composition and the final all-pass compiler theorem remain unfinished. The estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

Next: use the genuine universal strong body callbacks and pure restore_post to retain lexical exit, body admission and caller admission at the same returned pool, without another restoration.

### Strong Receipt exit and caller admission in one named invocation (2026-10-10; `06f2635c`)

`CallableIndexedOwnedPreparedNamedInvocationAdmission` preserves the actual parameter Receipt, full body administrative context, lexical exit and PostAdmission through the generic core. The pure restoration proof uses genuine caller-context support, saved stable rows and the actual restored frame at the same causal witness; the fault path needs frame/row transport. `SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission` closes these inputs for the accepted initial/completed pair without replaying bootstrap or parameters. Public root/program exit companions remain uncompiled drafts.

The Source hashes are `09fe9750` and `89b3a705`; Source creation followed a 2293-module before capture. Normal verification at `06f2635c` passed 5618 registered build jobs, two empty strict Source logs, 27 complete declarations (10 generic / 17 accepted) and 20 signatures. Every private/normal TYPE/AXIOMS block matches literally and uses only the standard three axioms. The cumulative census is 16297 from 16270: 27 additions, no prior overlaps and no removals. The 5549-row pre-install snapshot and actual 2295-module import environment passed. The two changed existing object pairs, `Tests.Main` and `CoreLowering`, are covered by the four-module dependency cone and four successful rebuilds. All 4985 protected artifacts remain unchanged. The unit adds two Source modules and two registration imports, with no IO or runner. Runtime/Core specifications and public execution actions are unchanged; no IO is added. Generic mixed bodies, specialization/evidence/comptime composition and the final all-pass theorem remain unfinished. The 70% / 85% estimates and earlier dated checkpoints retain their scope.
