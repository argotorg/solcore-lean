# Core

`Solcore/Core` is the typed language that every program compiles to: its syntax, typing and checker,
a big-step evaluator, a CEK machine with fuel, host requests, and the safety proofs. The
[umbrella](../../Solcore/Core.lean) imports all of it except the JSON boundary
[`Wire`](../../Solcore/Core/Wire.lean) and `Internal/LocalLoopCorrespondence`, which only the Rust
Hull import uses.

- **Builds on.** Nothing in `Solcore`, except that the wire codec imports `Util/Json` and
  `ContractRuntime/Internal/ScalarText`.
- **Built on by.** [ContractRuntime](contract-runtime.md), which runs checked Core contracts; the
  [Frontend](frontend.md), whose native compiler emits Core and rechecks it with `infer?`, and whose
  Rust Hull import translates Hull into Core; [Core lowering](core-lowering.md), over `Evaluates`
  and the conventions below; `Resolved` and `Abi` ([Foundations](foundations.md)); and
  [Synthesis](synthesis.md), which exchanges Core programs as wire JSON.

Most language changes need no Core change: shifts compile to the existing `wordShl` and `wordShr`.

## Where things are

The front is the specification and the main theorems:

| File | Holds | Edit it when you add |
| --- | --- | --- |
| [`Syntax`](../../Solcore/Core/Syntax.lean) | `Ty`, `Expr`, `Value`, `Program`, the operator types, `HostFunction` with its order (`HostFunction.all`, `HostFunction.index`), the hand-written `Expr.equal` and `Value.decEq` | a type, expression, value, operator or host function |
| [`Data`](../../Solcore/Core/Data.lean) | data lookups, `Ty.WellFormed`, `DataEnvironment.WellFormed` | a type former |
| [`Primitive`](../../Solcore/Core/Primitive.lean) | word and integer arithmetic, `UnaryOp.apply`, `BinaryOp.apply`, `TernaryOp.apply` with their typing theorems, `Expr.weakenAt`, derived forms such as `Expr.wordLt` | an operator or a derived form |
| [`Typing`](../../Solcore/Core/Typing.lean) | `HasType`, `infer?`, `Program.WellTyped`, `Program.check` | an expression form |
| [`Check`](../../Solcore/Core/Check.lean) | `inferDetailed`, `Program.checkDetailed`, `CheckError`, `CheckPath` | an expression form or a diagnostic |
| [`Eval`](../../Solcore/Core/Eval.lean) | the store and `Evaluates` | an expression form |
| [`Machine`](../../Solcore/Core/Machine.lean) | `Frame`, `Transition`, `advance`, `Steps`, `runStateful`, `run`, `MachineFault` | an expression form |
| [`Host`](../../Solcore/Core/Host.lean) | `hostContext`, `hostEnvironment`, `Program.checkHost` | nothing: they follow `HostFunction.all` |
| [`HostMachine`](../../Solcore/Core/HostMachine.lean) | `HostRequest`, `HostSuspension`, `hostAdvance`, `HostTransition`, `HostRequestEmission` | a host function |
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

Keep these proved, or change them deliberately. `Safety` states what README's Proof status claims
for Core.

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
  an uninitialized read, must be a language failure, and a revert an ordinary result that the entry
  profile reads as reverted: a typed stuck state breaks `state_progress`.
- Operators are total on typed operands: `Word.udiv` and `Integer.divide` return zero for a zero
  divisor, and `Word.shiftLeft` returns zero for an amount of 256 or more.
- A failure keeps the effects before it (`LanguageResult.bind_failure`).
- `LanguageResult.Observation` keeps fuel exhaustion (`.outOfFuel`) apart from faults
  (`.internalFault`, which `LanguageResult.checked_run_ne_internalFault` excludes).
- `hostRun` charges one unit of fuel for an ordinary step and one for reaching a host request.

## Making changes

### Add an operator

1. `Syntax`: the constructor in `UnaryOp`, `BinaryOp` or `TernaryOp`, with its `operandType` and
   `resultType` cases. Keep it scalar (bool, word or integer): `Internal/Preservation` and
   `Internal/Renaming` rely on scalar results.
2. `Primitive`: the computation, such as `Word.clz`, and the `apply` case, total on typed operands.
   Typing, evaluation and the machine use `op.apply` generically, so nothing else in the
   specification changes.
3. `Internal/PrimitiveLaws`: a section with value lemmas, an `@[simp]` `apply` lemma and an
   evaluation lemma, as for `wordClz`.
4. `Wire`, only if the operator crosses the JSON boundary: `Wire/Syntax`, `Wire/Conversions` and
   the encoder and decoder of `Wire/Codec`, with the decoder's `expected` list.
5. Tests in `Test/Core/Primitives.lean` and `Test/Core/Wire.lean`, then build the whole library:
   proofs elsewhere may unfold the type functions, as `Abi/StaticWord`'s did.

### Add an expression form or a value form

`Ty.integer`, `Expr.integer` and `Value.integer` were added this way.

1. Specification: the constructor in `Syntax` (with `Expr.equal` or `Value.decEq`), then its rule
   or case in `Data`, `Primitive` (`Expr.weakenAt`), `Typing`, `Check`, `Eval`, `Machine` (its
   `Frame`s, `Transition` rules and `MachineFault`s), `RuntimeTyping` and `HostTyping`.
2. Proofs: `Safety`, `HostRunner`, and the `Internal/` laws. Many proofs list every value
   constructor; a new value form joins each list.
3. `Wire`, if the form crosses the boundary: `Wire/Syntax`, `Wire/Conversions` and `Wire/Codec`.
4. Build everything, and check by hand the matches with a wildcard: `acceptsAt` and the shrinker in
   `Synthesis/Core` match on `Wire.Expr`, and `SourceCoreDataEquality.ReadOnly` on Core's `Expr`.

### Add a host function and its request

[ContractRuntime](contract-runtime.md#add-a-host-effect) continues from here.

1. `Syntax`: append the constructor to `HostFunction` and to `HostFunction.all`, with the next
   `HostFunction.index`.
2. `HostMachine`: the `HostRequest` constructor with its `Response`, the `hostAdvance` case (which
   faults with `invalidHostArgument` on a wrong argument shape) and the `HostRequestEmission`
   constructor.
3. Laws: the function's lemmas in `Internal/HostLaws`, as `emitLogWord` has, and its cases in
   `Internal/HostPreservation` and `HostRunner`.
4. `Wire/Host` writes its table out on purpose, and `Wire.Host.functions_eq_current` proves it
   equals `HostFunction.all`: extend the table, or prove the prefix relation directly.
5. ContractRuntime's handlers and scheduler match on every request. Tests in
   `Test/Core/HostMachine.lean` and `Test/Core/Wire.lean`.

### Add a convention of compiled code

A convention is a function that builds ordinary `Expr`, such as `CallableContract`,
`LocalAssignment` or `OptionalCell`. It needs no new syntax or rule, and the safety theorems cover
it unchanged. Define it in a section of `Conventions`, `Mappings` or `LanguageResult`, prove its
laws in `Internal/ConventionLaws` or `Internal/MappingLaws` (naming every binder it inserts), and
test it in `Test/Core/LocalFragments.lean` or `DataAndCells.lean`. Changing an existing convention
is larger: the native compiler emits it, and Core lowering proves over its exact shape.

## Pitfalls

- **Keep the specification closed.** `Syntax` through `HostTyping` import only one another, and
  never `Internal/`; the main-theorem files (`Safety`, `Correspondence`, `Fuel`, `HostRunner`) do.
- **Five specification files keep proofs**, because `private` is per file: `Typing` and `Check`
  unfold their private helpers, and `Data`, `Syntax` and `Primitive` keep the laws others need.
- **Two value typings.** `RuntimeTyping` has no host values (the plain machine faults with
  `unhandledHostFunction` on one); `HostTyping` adds them. Extend both.
- **Host functions are positional.** Code names them by index, as the Abi dispatcher and Synthesis
  proofs do. Append; never insert or reorder.
- **Wildcards hide new forms.** Every `Wire.….ofCore?` ends in `| _ => none`, and
  `SourceCoreDataEquality.ReadOnly` treats an unknown form as read-only.
- **The native compiler rechecks what it emits** with `Core.infer?`, so a typing change can surface
  as a compile error in a runtime test.
- **`@[simp]` reach decides some file boundaries**
  ([Conventions](conventions.md#what-moving-code-can-change)): `WordComparisons`, `ByteSelection`
  and `DerivedForms` each reach a different half of the repository. Put a simp lemma next to lemmas
  of the same reach.
- **Matchers.** `HostRunner` keeps its own definitions, and `Wire/Conversions` stays apart from
  `Wire/Syntax`, or the equation lemmas of `HostRunResult.HasType` or `Wire.Expr.toCore` would
  change their binder names.
- **Older markers.** Some sections carry a `## Consolidated module: …` heading from an earlier merge
  ([Conventions](conventions.md#following-older-notes)). For example,
  `Solcore.Core.HostMachineProperties` is now in `HostMachine` and `Internal/HostLaws`.

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
