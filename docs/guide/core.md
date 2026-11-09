# Core

`Solcore/Core` is the typed language that every program compiles to: its syntax, typing and checker,
a big-step evaluator, a CEK machine with fuel, host requests, and the safety proofs. The
[umbrella](../../Solcore/Core.lean) imports all of it except two parts: the JSON boundary
[`Wire`](../../Solcore/Core/Wire.lean), and `Internal/LocalLoopCorrespondence`, which only the Rust
Hull import uses.

- **Builds on.** Nothing in `Solcore`, except that the wire codec imports `Util/Json` and
  `ContractRuntime/Internal/ScalarText`.
- **Built on by.**
  - [ContractRuntime](contract-runtime.md) runs checked Core contracts and answers their host
    requests.
  - [Frontend](frontend.md): the native compiler emits Core and rechecks it with `infer?`; the Rust
    Hull import translates Hull into Core.
  - [Core lowering](core-lowering.md) proves, for part of the language, that compiled Core agrees
    with the source semantics. It works over `Evaluates` and the conventions below.
  - `Resolved` lowers resolved expressions to Core, and `Abi` generates a Core dispatcher
    ([Foundations](foundations.md)).
  - [Synthesis](synthesis.md) generates Core programs and exchanges them as wire JSON.

Most language changes need no Core change. Shifts compile to the existing `wordShl` and `wordShr`
([Adding a language feature](adding-a-feature.md)).

## Where things are

The front is the specification and the main theorems:

| File | Holds | Edit it when you add |
| --- | --- | --- |
| [`Syntax`](../../Solcore/Core/Syntax.lean) | `Ty`, `Expr`, `Value`, `Program`, the operator types, `HostFunction` with its order (`HostFunction.all`, `HostFunction.index`), the hand-written `Expr.equal` and `Value.decEq` | a type, expression, value, operator or host function |
| [`Data`](../../Solcore/Core/Data.lean) | data lookups, `Ty.WellFormed`, `DataEnvironment.WellFormed` | a type former |
| [`Primitive`](../../Solcore/Core/Primitive.lean) | word and integer arithmetic, `UnaryOp.apply`, `BinaryOp.apply`, `TernaryOp.apply` with their typing theorems, `Expr.weakenAt`, derived forms such as `Expr.wordLt` and `Expr.boolAnd` | an operator or a derived form |
| [`Typing`](../../Solcore/Core/Typing.lean) | `HasType`, `infer?`, `Program.WellTyped`, `Program.check`, and the proofs that unfold `infer?`'s private helpers | an expression form |
| [`Check`](../../Solcore/Core/Check.lean) | `inferDetailed`, `Program.checkDetailed`, `CheckError`, `CheckPath` | an expression form or a diagnostic |
| [`Eval`](../../Solcore/Core/Eval.lean) | the store and `Evaluates` | an expression form |
| [`Machine`](../../Solcore/Core/Machine.lean) | `Frame`, `Transition`, `advance`, `Steps`, `runStateful`, `run`, `MachineFault` | an expression form |
| [`Host`](../../Solcore/Core/Host.lean) | `hostContext`, `hostEnvironment`, `Program.checkHost` | nothing: they follow `HostFunction.all` |
| [`HostMachine`](../../Solcore/Core/HostMachine.lean) | `HostRequest` with `Response`, `responseType` and `responseValue`, `HostSuspension`, `hostAdvance`, `HostTransition`, `HostRequestEmission` | a host function |
| [`RuntimeTyping`](../../Solcore/Core/RuntimeTyping.lean) | `ValueHasType`, `RuntimeValueHasType`, `StoreHasTypes`, `FrameHasType`, `StateHasType`, without host values | a value form or a frame |
| [`HostTyping`](../../Solcore/Core/HostTyping.lean) | the same relations with host functions as values | a value form or a frame |
| [`Safety`](../../Solcore/Core/Safety.lean) | preservation, progress and finite execution safety | proof cases for new rules |
| [`Correspondence`](../../Solcore/Core/Correspondence.lean), [`Fuel`](../../Solcore/Core/Fuel.lean) | evaluator against machine; exact fuel and resumption | rarely |
| [`HostRunner`](../../Solcore/Core/HostRunner.lean) | `hostRun`, `HostRunResult`, `HostSteps`, and their safety | a host function |
| [`LanguageResult`](../../Solcore/Core/LanguageResult.lean) | language failures as ordinary Core sums | a change to how failures are carried |
| [`Conventions`](../../Solcore/Core/Conventions.lean), [`Mappings`](../../Solcore/Core/Mappings.lean) | how compiled code encodes source constructs, such as `OptionalCell`, `LocalLoop`, `CallableContract`, `WordMapping` | a convention |
| [`Wire/Syntax`](../../Solcore/Core/Wire/Syntax.lean), [`Wire/Conversions`](../../Solcore/Core/Wire/Conversions.lean), [`Wire/Codec`](../../Solcore/Core/Wire/Codec.lean), [`Wire/Host`](../../Solcore/Core/Wire/Host.lean) | wire syntax, maps to and from Core, budgeted JSON codecs, the frozen host table | a form that must cross the JSON boundary |

`Internal/` holds the supporting lemmas. A new lemma goes in the file of its topic:

| File | Topic |
| --- | --- |
| [`EvaluationLaws`](../../Solcore/Core/Internal/EvaluationLaws.lean) | store laws, determinism of `Evaluates`, store growth, the cell-free fragment |
| [`MachineLaws`](../../Solcore/Core/Internal/MachineLaws.lean) | `advance` against `Transition`, the runners against `Steps` |
| [`Simulation`](../../Solcore/Core/Internal/Simulation.lean) | both directions between `Evaluates` and `Steps` |
| [`Preservation`](../../Solcore/Core/Internal/Preservation.lean) | laws of the `RuntimeTyping` relations, result types of the primitives |
| [`Renaming`](../../Solcore/Core/Internal/Renaming.lean) | the type `Renaming`, `Expr.rename`, weakening, appended data definitions |
| [`PrimitiveLaws`](../../Solcore/Core/Internal/PrimitiveLaws.lean) | value, application and evaluation laws of single operators, one section each |
| [`WordComparisons`](../../Solcore/Core/Internal/WordComparisons.lean), [`ByteSelection`](../../Solcore/Core/Internal/ByteSelection.lean), [`DerivedForms`](../../Solcore/Core/Internal/DerivedForms.lean) | word comparisons; byte selection; conversions and derived comparisons |
| [`LocalFragment`](../../Solcore/Core/Internal/LocalFragment.lean) | `Expr.LocalFragment`: typing, inference, evaluation, cost under insertion, termination |
| [`HostLaws`](../../Solcore/Core/Internal/HostLaws.lean) | host lookups, `Program.checkHost`, each request's response, `HostSuspension.resume`, `hostAdvance` against its relations |
| [`HostPreservation`](../../Solcore/Core/Internal/HostPreservation.lean) | laws of the `HostTyping` relations, preservation and progress with host requests |
| [`ConventionLaws`](../../Solcore/Core/Internal/ConventionLaws.lean), [`MappingLaws`](../../Solcore/Core/Internal/MappingLaws.lean) | typing and evaluation laws of `Conventions` and `Mappings`, one section per convention |
| [`LocalLoopCorrespondence`](../../Solcore/Core/Internal/LocalLoopCorrespondence.lean) | stage-by-stage evaluation bridges for `LocalLoop` |

## Definitions and theorems you build on

These are the statements other code uses. Keep them proved, or change them deliberately. `Safety`
states what README's Proof status claims for Core.

| Declarations | Reading | Used by |
| --- | --- | --- |
| `HasType`, `infer?`, `infer_sound`, `infer_complete` | the typing judgment and its decision procedure | the native compiler, which rechecks the Core it emits; Core lowering |
| `Program.check`, `Program.checkHost` | whole-program checks, closed and with host capabilities | `checkHost`: ContractRuntime's `CheckedHostCoreProgram`, the Abi dispatcher, Synthesis |
| `Evaluates`, `evaluation_deterministic` (`Internal/EvaluationLaws`) | big-step evaluation with an explicit store, and its single result | Core lowering, throughout |
| `evaluation_preserves_type` | a typed evaluation gives a typed value and store in an extended world | Core lowering |
| `runStateful_evaluation_sound`, `evaluation_runStateful_complete_with_sufficient_fuel` | a finished run is an evaluation; an evaluation is reached with enough fuel | Core lowering, Frontend tests |
| `steps_from_initial_sound` (`Internal/Simulation`), `advance_next_iff`, `runStateful_sound` (`Internal/MachineLaws`) | lower-level forms of the same | `Frontend/Fragments` and its tests |
| `runStateful_resume`, `Steps.resumed_done_iff` | continuing an exhausted run is one larger run | Frontend tests, `Frontend/Fragments` |
| `Program.checked_run_never_faults`, `Program.checked_runStateful_has_type`, `well_typed_runStateful_has_type`, `well_typed_runStateful_resume_has_type` | finite execution safety: no fault, and every result typed, a checkpoint included | README's claim; the native compiler, Rust Hull, tests |
| `UnaryOp.apply_total_of_type`, `BinaryOp.apply_total_of_types`, `TernaryOp.apply_total_of_types`, and each `apply_result_type` | an operator returns a value of its result type on every operand of its declared types | `state_progress` and host progress |
| `hostRun`, `hostRun_hasType`, `hostRun_never_faults`, `hostRun_done_sound`, `hostRun_suspended_sound` | runs that stop at host requests, and their safety | ContractRuntime's `HostDriver` |
| `HostRequest.Response`, `HostRequest.responseValue_hasType` (`Internal/HostPreservation`) | each request fixes the type of its answer | why every `HostHandler` keeps states typed |
| `LanguageResult`, `Conventions`, `Mappings` | language failures and compiled-code conventions | the native compiler emits them, Core lowering proves over them, the Rust Hull import uses some |
| `Wire.decodeProgram`, `Wire.encodeProgram` | the canonical JSON form | Synthesis generators |

## Faults, language failures and fuel

These are the ways a run can end; a language failure is a kind of completion. Keep them distinct.

| Outcome | What it is | How it shows |
| --- | --- | --- |
| Completion | `advance` returns `.done` | `RunResult.done`, `StatefulRunResult.done value store` |
| Language failure | a completion whose value is the left side of `LanguageResult.resultType type = .sum .word type`, carrying a Word reason | `LanguageResult.run` gives `.failed reason store`; at a contract boundary an entry profile reads results as returned, reverted or trapped |
| Out of fuel | the budget ran out before the next step | `.outOfFuel state`, a typed checkpoint that `runStateful_resume` continues exactly |
| Suspension | the program applied a host function | `hostRun` gives `.suspended suspension remainingFuel`; a handler answers |
| Fault | the machine is stuck, a `MachineFault` | `.fault error state` |

- A fault is what the safety theorems exclude for a checked program. A source-level error, such as
  an uninitialized read or a fall-through, must be a language failure, and a revert an ordinary
  result that the entry profile reads as reverted. Neither may be a stuck state: a typed stuck state
  breaks `state_progress`.
- Operators are total on typed operands. `Word.udiv` and `Integer.divide` return zero for a zero
  divisor, and `Word.shiftLeft` returns zero for an amount of 256 or more. An `apply` that returns
  `none` on typed operands breaks `UnaryOp.apply_total_of_type` and progress.
- A failure keeps the effects before it: `LanguageResult.bind_failure` returns the computation's
  final store without running the body.
- `LanguageResult.Observation` keeps fuel exhaustion (`.outOfFuel`) apart from faults
  (`.internalFault`, which `LanguageResult.checked_run_ne_internalFault` excludes).
- `hostRun` charges one unit of fuel for an ordinary step and one for reaching a host request.

## Making changes

### Add an operator

When `wordClz` was added, only `Syntax` and `Primitive` changed (30f241621), and its laws came next
(22b71d803). The integer operators of 0ce7c5f07 also crossed the wire.

1. `Syntax`: add the constructor to `UnaryOp`, `BinaryOp` or `TernaryOp`, and its case in
   `operandType` and `resultType` (`leftType`, `rightType`, `resultType` for binary operators).
   Every operator today takes and returns scalars (bool, word, integer), and proofs rely on it:
   `binary_apply_result_has_runtime_type` in `Internal/Preservation` needs a `CellPayload` result
   type, and the private `BinaryOp.apply_related` in `Internal/Renaming` closes each case with
   `exact .bool _`, `.word _` or `.integer _`. `TernaryOp`'s type functions are all `.word`.
2. `Primitive`: define the computation, for example `Word.clz`, and add the `apply` case, total on
   operands of the declared types. `apply_total_of_type` and `apply_result_type` are proved by case
   analysis and normally re-check.
3. Nothing else in the specification changes: typing, evaluation and the machine use `op.apply` and
   the type functions generically. The proofs that split on `op` in `Internal/EvaluationLaws`,
   `Internal/Preservation` and `Internal/Renaming` close each case by automation, so a scalar
   operator needs no new proof there.
4. `Internal/PrimitiveLaws`: add a section with value lemmas, an `@[simp]` `apply` lemma and an
   evaluation lemma, as `Word.clz_zero`, `UnaryOp.apply_wordClz` and `Evaluates.wordClz` do.
5. `Wire`, only if the operator must cross the JSON boundary: the constructor in `Wire/Syntax`,
   `toCore` and `ofCore?` in `Wire/Conversions`, and the name in `Wire/Codec`'s encoder and decoder
   (`encodeUnaryOp` and `decodeUnaryOpAt`, or the binary and ternary ones), including the decoder's
   `expected` list.
6. Tests: a section of `Test/Core/Primitives.lean` with an `IO` entry point, called from
   `Tests.run` in `Tests/Main.lean`, as `testCoreCountLeadingZeros` is; wire round trips in
   `Test/Core/Wire.lean`.
7. Build the whole library. When 0ce7c5f07 made `BinaryOp.leftType` a case split, proofs in
   `Abi/StaticWord` that ran `simp [BinaryOp.leftType]` had to change. The Core program generator
   uses only the operators in its fixed catalogs (`unaryOps`, `binaryOps` and `ternaryOps` in
   `Synthesis/Core/Fragment`).

### Add an expression form or a value form

0ce7c5f07 added `Ty.integer`, `Expr.integer` and `Value.integer` across Core, host safety and Wire.

1. Specification:
   - `Syntax`: the constructor; `Expr.equal`, `Expr.equal_sound` and `Expr.equal_self`, or
     `Value.decEq` and `Value.type`; `CellPayload` and `Ty.isCellPayload` for a new type.
   - `Data`: `Ty.WellFormed` and `Ty.isWellFormed` for a new type.
   - `Primitive`: `Expr.weakenAt`.
   - `Typing`: the `HasType` rule, the case of the private `inferWithDefinitions?`, and the proofs
     beside it.
   - `Check`: a `CheckPathStep` per child, the private diagnosis, `inferDetailed_iff_infer`.
   - `Eval` and `Machine`: the `Evaluates` rules; the `Frame`s for pending children, the
     `Transition` rules and `advance` cases, and a `MachineFault` for each wrong shape an
     elimination can meet.
   - `RuntimeTyping` and `HostTyping`: `ValueHasType`, `RuntimeValueHasType` and
     `HostRuntimeValueHasType` for a value; `FrameHasType` and `HostFrameHasType` for a frame.
2. Proofs: `Safety` (`evaluation_preserves_type`, `transition_preserves_state_type`,
   `state_progress`), `HostRunner` (`hostAdvance_done_iff`), and in `Internal/` `MachineLaws`,
   `Simulation`, `EvaluationLaws`, `Preservation`, `Renaming`, `HostLaws` and `HostPreservation`.
   Many proofs list every value constructor (`| unit | bool | word | integer | hostFunction | …`); a
   new value form joins each list.
3. `Wire`, if the form crosses the boundary: `Wire/Syntax`, `Wire/Conversions`, and the sections of
   `Wire/Codec` for scalars, types, expression encoding, measure, decoding and budgets.
4. Other areas: build everything. A match with a wildcard compiles silently, so check those by
   hand: `acceptsAt` in `Synthesis/Core/Fragment` and the shrinker in `Synthesis/Core/Shrink`
   match on `Wire.Expr`, and `SourceCoreDataEquality.ReadOnly` on Core's `Expr`.
5. Tests: `Test/Core/Primitives.lean` or `Test/Core/DataAndCells.lean`, and `Test/Core/Wire.lean`;
   0ce7c5f07's tests are now the `Tests.CoreIntegers` and `Tests.CoreWireInteger` sections.

### Add a host function and its request

The log capability came in Core commits for the function (8eb8c3dde), the suspension (4d48eacca),
the safety cases (bad9d383e) and the wire table (456a94a77, d2b9b03dd).
[ContractRuntime](contract-runtime.md#add-a-host-effect) continues from there.

1. `Syntax`: append the constructor to `HostFunction`, with `parameterType` and `resultType` cases
   and their `@[simp]` lemmas. Append it to `HostFunction.all` and give it the next
   `HostFunction.index`, with its `index_…` lemma.
2. `HostMachine`: the `HostRequest` constructor with its `Response`, `responseType` and
   `responseValue`; the `hostAdvance` case, which faults with `invalidHostArgument` on a wrong
   argument shape; the `HostRequestEmission` constructor.
3. `Internal/HostLaws`: the lemmas each function has, such as `hostContext_emitLogWord`,
   `HostRequest.responseValue_emitLogWord`, `HostSuspension.resume_emitLogWord`,
   `hostAdvance_suspend_emitLogWord` and `hostAdvance_invalid_emitLogWord_argument`, and the cases
   of the proofs against the relations.
4. `Internal/HostPreservation`: the case of `HostRequest.responseValue_hasType`, and a progress
   lemma like `typed_emitLogWord_emits` with its case in `typed_hostApplication_emits`.
   `HostRunner`: the case in `hostAdvance_done_iff`.
5. `Wire/Host` writes its table out on purpose. `Wire.Host.functions_eq_current` (by `rfl`) says it
   equals `HostFunction.all`, and `functions_prefix_current` is proved from it. Either extend
   `functions`, `context`, `environment` and their length and `…_firstUnbound` lemmas, or prove the
   prefix relation directly.
6. ContractRuntime: its handlers and its scheduler match on every request.
7. Tests: `Test/Core/HostMachine.lean` (`testCoreHostMachine`) and `Test/Core/Wire.lean`
   (`testCoreWireHost`).

### Add a convention of compiled code

A convention is a function that builds ordinary `Expr`. It needs no new syntax, typing rule or
machine rule, and the safety theorems cover it unchanged. Examples: `CallableContract` (4c1b86b6a),
`LocalAssignment` and `WordMapping` (e92def549), `LanguageResult` and `OptionalCell` (cbd0e5565).
Each was one module then; its definitions are now in the front and its laws in `Internal/`.

1. Define it in a new section of `Conventions`, `Mappings` or `LanguageResult`, with its own
   namespace.
2. Prove its typing and evaluation laws in a section of `Internal/ConventionLaws` or
   `Internal/MappingLaws`. Follow the existing sections: their evaluation laws name every binder the
   convention inserts and the store it shares.
3. If callers need evaluation stage by stage, add bridges as `Internal/LocalLoopCorrespondence` does
   for loops (a6392d98d).
4. Test it in a section of `Test/Core/LocalFragments.lean` or `Test/Core/DataAndCells.lean`, with a
   `run` entry point called from `Tests.run`.

Changing an existing convention is a larger change: the native compiler emits it, and Core lowering
proves over its exact shape. The shift work copied `LocalAssignment.compound`'s shape in the frontend
rather than extend it.

## Pitfalls

- **Keep the specification closed.** `Syntax`, `Data`, `Primitive`, `Typing`, `Check`, `Eval`,
  `Machine`, `Host`, `HostMachine`, `RuntimeTyping` and `HostTyping` import only one another. The
  main-theorem files (`Safety`, `Correspondence`, `Fuel`, `HostRunner`) import `Internal/`; the
  specification never does.
- **Five specification files keep proofs.** `private` is per file: `Typing` unfolds the private
  helpers of `infer?`, and `Check` its private diagnosis. `Data` keeps the laws `Typing` needs,
  `Syntax` the `HostFunction` laws and the proofs behind its hand-written equality, and `Primitive`
  the typing theorems of `apply`.
- **Two value typings.** `RuntimeTyping` has no host values, and the plain machine faults with
  `unhandledHostFunction` on one. `HostTyping` adds them. Extend both.
- **Host functions are positional.** `hostContext` and `hostEnvironment` follow `HostFunction.all`,
  and code names functions by index. The Abi dispatcher reads
  `.var (HostFunction.inputDataWordBE?.index + 1)`, and Synthesis proofs write
  `environment[13 + depth]?` for `emitLogWord`. Append; never insert or reorder.
- **Wildcards hide new forms.** Every `Wire.….ofCore?` ends in `| _ => none`, so a new Core form
  silently has no wire form. `SourceCoreDataEquality.ReadOnly` in `Frontend/SourceCore/Data.lean`
  treats an unknown form as read-only.
- **The native compiler rechecks what it emits** with `Core.infer?`, and reports an error when the
  check fails. A typing change can therefore surface as a compile error in a runtime test.
- **`@[simp]` reach decides some file boundaries**
  ([Conventions](conventions.md#what-moving-code-can-change)).
  `PrimitiveLaws` reaches few modules, while `WordComparisons`, `ByteSelection` and `DerivedForms`
  each reach about half of the repository, each a different set. Few modules reach
  `LocalLoopCorrespondence`, and many reach `ConventionLaws`, which has no simp lemma. Put a simp
  lemma next to lemmas of the same reach.
- **Matchers.** `HostRunner` keeps its own definitions, and `Wire/Conversions` stays apart from
  `Wire/Syntax`. Moving either would change the binder names in the equation lemmas of
  `HostRunResult.HasType` or `Wire.Expr.toCore`.
- **Older markers.** Besides `-- leanmerge: from`, some sections carry a heading
  `## Consolidated module: …` from an earlier merge, which the moves map does not list. For example,
  `Solcore.Core.HostMachineProperties`, named by bad9d383e, is in `HostMachine` and
  `Internal/HostLaws`. The type `Renaming` is in `Internal/Renaming`; the module
  `Solcore.Core.Renaming` no longer exists.

## Testing

| File | Covers |
| --- | --- |
| [`Test/Core/Primitives.lean`](../../Solcore/Test/Core/Primitives.lean) | operators, derived comparisons and flags, integers |
| [`Test/Core/DataAndCells.lean`](../../Solcore/Test/Core/DataAndCells.lean) | products, sums, functions, cells and optional cells, named data, tagged functions, callable contracts, mappings |
| [`Test/Core/LocalFragments.lean`](../../Solcore/Test/Core/LocalFragments.lean) | the local fragment, renaming, exact fuel, language results, local conventions, store safety |
| [`Test/Core/HostMachine.lean`](../../Solcore/Test/Core/HostMachine.lean) | host requests and suspensions |
| [`Test/Core/Wire.lean`](../../Solcore/Test/Core/Wire.lean) | wire codec, conversions, host table, integers, public names |
| [`Tests/Main.lean`](../../Tests/Main.lean) | `testSemanticCore`, `testPrimitiveAlgebra`, `testM1cKernel` and `testDetailedCoreChecker`, defined there |

The [ContractRuntime](contract-runtime.md#testing) tests exercise host requests as well.

```sh
lake build Solcore.Core                    # the area, without Wire
lake build Solcore.Core.Wire               # the JSON boundary
lake build Solcore.Test.Core.Primitives    # one test file's compile-time checks
lake build                                 # everything: other areas match on Core syntax
lake test                                  # all IO tests
```

`lake test` runs every `IO` test; the driver takes no filter. See [Workflow](workflow.md).
