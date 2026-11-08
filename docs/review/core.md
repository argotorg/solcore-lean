# Reviewer's guide: Core

`Solcore/Core` is the typed language every program compiles to, with its semantics and its safety
proofs. The [umbrella](../../Solcore/Core.lean) gives this reading order in brief.

## Main definitions and theorems

These decided the front. README's "Proof status" says that Core has proofs of type preservation and
finite execution safety, and the theorems below state that. Most of them are also the top of the
theorem dependencies in this area: nothing in the area uses `Program.checked_run_never_faults`, and
it rests on 665 declarations of the area.

| Claim | Theorems | Evidence |
| --- | --- | --- |
| Type preservation | `evaluation_preserves_type`, `transition_preserves_state_type`, `state_progress` | README; the theorems every safety result below rests on |
| Finite execution safety | `Program.checked_run_never_faults`, `Program.checked_runStateful_has_type`, `well_typed_runStateful_resume_has_type` | README; roots of the dependencies |
| The evaluator and the machine agree | `run_evaluation_sound`, `evaluation_run_complete` | roots of the dependencies; the big-step relation is what the source-to-Core work targets |
| The checker decides the judgment | `Program.check_sound`, `Program.check_complete`, `Program.checkDetailed_sound`, `Program.checkDetailed_complete` | roots of the dependencies; every theorem above starts from `Program.check` |
| Exact fuel | `runStateful_resume`, `Steps.resumed_done_iff` | used outside the area |
| Safety with host requests | `hostRun_hasType`, `hostRun_never_faults` | roots of the dependencies; `ContractRuntime` builds on them |

The definitions in the front are what those statements mention: the closure of their types, followed
through definitions. The conventions in `Conventions` and `Mappings` are outside that closure. They
are in the front because the compiler emits them, so the correspondence theorems are stated over them.

## Reading order

1. **Language.** Syntax, data, primitives, typing.
2. **Semantics.** The big-step relation, the CEK machine, and host requests.
3. **Typing of states.** The relations the theorems are stated over.
4. **Main theorems.**
5. **Conventions of compiled code.** How the compiler encodes source constructs.
6. **Wire.** The canonical JSON boundary.

Everything else is proof machinery in `Internal/`.

## Front

### Language

| File | Main declarations |
| --- | --- |
| [`Syntax`](../../Solcore/Core/Syntax.lean) | `Ty`, `Expr`, `Value`, `Program`, `UnaryOp`, `BinaryOp`, `TernaryOp`, `HostFunction` |
| [`Data`](../../Solcore/Core/Data.lean) | `DataEnvironment.lookupConstructorPayloadType?`, `Ty.WellFormed`, `DataEnvironment.WellFormed` |
| [`Primitive`](../../Solcore/Core/Primitive.lean) | `UnaryOp.apply`, `BinaryOp.apply`, `TernaryOp.apply`, `Word.add`, `Expr.wordLt`, `Expr.boolAnd`, `Integer.divide` |
| [`Typing`](../../Solcore/Core/Typing.lean) | `HasType`, `infer?`, `Program.WellTyped`, `Program.check` |
| [`Check`](../../Solcore/Core/Check.lean) | `inferDetailed`, `Program.checkDetailed`, `CheckError`, `CheckPath` |

### Semantics

| File | Main declarations |
| --- | --- |
| [`Eval`](../../Solcore/Core/Eval.lean) | `Store.allocate`, `Store.read?`, `Store.write?`, `Evaluates` |
| [`Machine`](../../Solcore/Core/Machine.lean) | `State`, `Frame`, `Transition`, `advance`, `Steps`, `runStateful`, `run`, `Program.run`, `MachineFault` |
| [`Host`](../../Solcore/Core/Host.lean) | `hostContext`, `hostEnvironment`, `Program.HostWellTyped`, `Program.checkHost` |
| [`HostMachine`](../../Solcore/Core/HostMachine.lean) | `HostRequest`, `HostSuspension`, `ContractCallWordResult`, `hostAdvance`, `HostTransition`, `HostRequestEmission` |

### Typing of states

| File | Main declarations |
| --- | --- |
| [`RuntimeTyping`](../../Solcore/Core/RuntimeTyping.lean) | `ValueHasType`, `WorldExtends`, `RuntimeValueHasType`, `RuntimeStoreHasTypes`, `StoreHasTypes`, `FrameHasType`, `StateHasType` |
| [`HostTyping`](../../Solcore/Core/HostTyping.lean) | `HostRuntimeValueHasType`, `HostStoreHasTypes`, `HostFrameHasType`, `HostStateHasType`, `HostSuspensionHasType` |

### Main theorems

| File | Holds |
| --- | --- |
| [`Safety`](../../Solcore/Core/Safety.lean) | Type preservation, progress, and finite execution safety |
| [`Correspondence`](../../Solcore/Core/Correspondence.lean) | The evaluator and the machine agree |
| [`Fuel`](../../Solcore/Core/Fuel.lean) | Exact cost of a terminating path, and resuming after exhaustion |
| [`HostRunner`](../../Solcore/Core/HostRunner.lean) | `hostRun`, `HostRunResult`, `HostSteps`, and the same results with host requests |

### Conventions of compiled code

None of this adds syntax or a machine rule. A convention is a definition in ordinary Core.

| File | Main declarations |
| --- | --- |
| [`LanguageResult`](../../Solcore/Core/LanguageResult.lean) | `LanguageResult.resultType`, `LanguageResult.bind`, `LanguageResult.decode?`, `LanguageResult.run` |
| [`Conventions`](../../Solcore/Core/Conventions.lean) | `OptionalCell.read`, `LocalSequence.pair`, `LocalControl.sequence`, `LocalLoop.whileLoop`, `LocalAssignment.compound`, `IntegerAssignment.compound`, `LocalPrimitiveResults.binary`, `TaggedFunction.call`, `CallableContract.dispatch` |
| [`Mappings`](../../Solcore/Core/Mappings.lean) | `WordMapping.lookup`, `WordMapping.assign`, `OrderedMapping.lookup`, `OrderedMapping.assign` |

### Wire

| File | Main declarations |
| --- | --- |
| [`Wire`](../../Solcore/Core/Wire.lean) | the umbrella of this boundary |
| [`Wire/Syntax`](../../Solcore/Core/Wire/Syntax.lean) | `Wire.Ty`, `Wire.Expr`, `Wire.Program` |
| [`Wire/Conversions`](../../Solcore/Core/Wire/Conversions.lean) | `Wire.Expr.toCore`, `Wire.Program.toCore`, `Wire.Expr.ofCore?` |
| [`Wire/Codec`](../../Solcore/Core/Wire/Codec.lean) | `Wire.decodeProgram`, `Wire.encodeProgram`, `Wire.canonicalizeProgramWithBudget`, `Wire.CoreBudgetLimits` |
| [`Wire/Host`](../../Solcore/Core/Wire/Host.lean) | `Wire.Program.check`, `Wire.Program.checkDetailed` |

## Main theorems

Each is stated for a program that passes `Program.check`, or for a state that `StateHasType` accepts.
A fault is a `MachineFault`: a stuck machine. A language failure, a revert and exhausted fuel are not
faults.

| Result | Theorems | File | Reading |
| --- | --- | --- | --- |
| Preservation, big-step | `evaluation_preserves_type` | [`Safety`](../../Solcore/Core/Safety.lean) | evaluating a typed expression in a typed store gives a typed value and a typed store in an extended world |
| Preservation, machine | `transition_preserves_state_type`, `Steps.preserve_state_type` | [`Safety`](../../Solcore/Core/Safety.lean) | a step keeps the state typed, at the same result type |
| Progress | `state_progress`, `well_typed_state_never_faults` | [`Safety`](../../Solcore/Core/Safety.lean) | a typed state is final or can step, so `advance` never faults |
| Safety of a checked program | `Program.checked_run_never_faults`, `Program.checked_runStateful_never_faults` | [`Safety`](../../Solcore/Core/Safety.lean) | with any fuel, a checked program does not fault |
| Result type | `Program.checked_run_preserves_result_type`, `Program.checked_runStateful_preserves_result_type` | [`Safety`](../../Solcore/Core/Safety.lean) | a completed run gives a value of the declared type |
| Every finite execution | `Program.checked_runStateful_has_type`, `well_typed_runStateful_has_type` | [`Safety`](../../Solcore/Core/Safety.lean) | every result is typed, including a fuel checkpoint |
| Resuming a checkpoint | `well_typed_runStateful_resume_has_type`, `well_typed_runStateful_preserves_checkpoint_world` | [`Safety`](../../Solcore/Core/Safety.lean) | a resumed checkpoint is one larger run, still typed |
| Completion | `Program.checked_run_completes`, `Program.checked_run_has_sufficient_fuel` | [`Safety`](../../Solcore/Core/Safety.lean) | an evaluation of a checked program is reached by a run, with enough fuel |
| Machine is sound for evaluation | `run_evaluation_sound`, `runStateful_evaluation_sound` | [`Correspondence`](../../Solcore/Core/Correspondence.lean) | a run that ends is an evaluation |
| Machine is complete for evaluation | `evaluation_run_complete`, `evaluation_runStateful_complete`, `evaluation_runStateful_complete_with_sufficient_fuel` | [`Correspondence`](../../Solcore/Core/Correspondence.lean) | an evaluation is reached by a run, and more fuel changes nothing |
| Exact cost | `Steps.final_unique`, `Steps.runStateful_done_iff`, `Steps.runStateful_outOfFuel_iff` | [`Fuel`](../../Solcore/Core/Fuel.lean) | a terminating path has one length, which decides what any fuel does |
| Resumption | `runStateful_resume`, `Steps.resumed_done_iff`, `Steps.resumed_outOfFuel_iff` | [`Fuel`](../../Solcore/Core/Fuel.lean) | continuing an exhausted state is one larger run, with the exact remainder |
| Checker | `Program.check_iff_wellTyped`, `Program.check_sound`, `typing_deterministic` | [`Typing`](../../Solcore/Core/Typing.lean) | `Program.check` decides `Program.WellTyped`, and an expression has one type |
| Checker with diagnostics | `Program.checkDetailed_sound`, `Program.checkDetailed_complete`, `inferDetailed_iff_typing` | [`Check`](../../Solcore/Core/Check.lean) | diagnostics decide the same judgment |
| Host requests | `hostRun_done_sound`, `hostRun_done_complete`, `hostRun_suspended_sound` | [`HostRunner`](../../Solcore/Core/HostRunner.lean) | `hostRun` agrees with `HostSteps` |
| Safety with host requests | `hostRun_hasType`, `hostRun_never_faults` | [`HostRunner`](../../Solcore/Core/HostRunner.lean) | every result is typed, including a suspension, and no run faults |
| Language results | `LanguageResult.checked_completion_decodes`, `LanguageResult.checked_run_ne_invalidCarrier`, `LanguageResult.checked_run_ne_internalFault` | [`LanguageResult`](../../Solcore/Core/LanguageResult.lean) | a checked program ends in a well-formed language result |
| Wire checking | `Wire.Program.check_full_sound`, `Wire.Program.check_complete`, `Wire.Program.checkDetailed_full_sound` | [`Wire/Host`](../../Solcore/Core/Wire/Host.lean) | the wire checker decides the host-aware judgment |
| Wire decoding | `Wire.canonicalizeProgramWithBudget_of_decode_eq_ok` | [`Wire/Codec`](../../Solcore/Core/Wire/Codec.lean) | JSON that decodes canonicalizes to the encoding of what it decoded to |

Below these sit the results a reader may want while checking a proof: `advance_next_iff` and
`runStateful_sound` in `Internal/MachineLaws`, `Evaluates.toSteps` and `steps_from_initial_sound` in
`Internal/Simulation`, and `Evaluates.rename` in `Internal/Renaming`.

## Internal

| File | Topic |
| --- | --- |
| [`EvaluationLaws`](../../Solcore/Core/Internal/EvaluationLaws.lean) | Store laws, determinism of `Evaluates`, store growth, the cell-free fragment |
| [`MachineLaws`](../../Solcore/Core/Internal/MachineLaws.lean) | `advance` against `Transition`, and the runners against `Steps` |
| [`Simulation`](../../Solcore/Core/Internal/Simulation.lean) | Both directions between `Evaluates` and `Steps` |
| [`Preservation`](../../Solcore/Core/Internal/Preservation.lean) | Laws of the relations in `RuntimeTyping` |
| [`Renaming`](../../Solcore/Core/Internal/Renaming.lean) | `Expr.rename`, renaming of typing and evaluation, weakening, data definition extension |
| [`PrimitiveLaws`](../../Solcore/Core/Internal/PrimitiveLaws.lean) | Value, application and evaluation laws of single primitives |
| [`WordComparisons`](../../Solcore/Core/Internal/WordComparisons.lean) | Direct and signed word comparisons |
| [`ByteSelection`](../../Solcore/Core/Internal/ByteSelection.lean) | Word byte selection |
| [`DerivedForms`](../../Solcore/Core/Internal/DerivedForms.lean) | Laws of the conversions and derived comparisons |
| [`LocalFragment`](../../Solcore/Core/Internal/LocalFragment.lean) | `Expr.LocalFragment`: typing, inference, evaluation, exact cost under insertion |
| [`HostLaws`](../../Solcore/Core/Internal/HostLaws.lean) | Host lookups, request responses, `HostSuspension.resume`, `hostAdvance` against its relations |
| [`HostPreservation`](../../Solcore/Core/Internal/HostPreservation.lean) | Laws of the relations in `HostTyping`, preservation and progress with host capabilities |
| [`ConventionLaws`](../../Solcore/Core/Internal/ConventionLaws.lean) | Typing and evaluation laws of `Conventions` |
| [`LocalLoopCorrespondence`](../../Solcore/Core/Internal/LocalLoopCorrespondence.lean) | Evaluation bridges for `LocalLoop`, stage by stage |
| [`MappingLaws`](../../Solcore/Core/Internal/MappingLaws.lean) | Typing and evaluation laws of `Mappings` |

## What a reviewer should know

- **The specification closes on itself.** `Syntax`, `Data`, `Primitive`, `Typing`, `Check`, `Eval`,
  `Machine`, `Host`, `HostMachine`, `RuntimeTyping` and `HostTyping` import only one another, 5,700
  lines in all. No proof is in their closure, apart from what those files hold themselves.
- **Four of those files keep proofs.** `Typing` and `Check` unfold private helpers of `infer?`, and
  `private` is per file. `Data` stays whole because `Typing` needs its laws. `Syntax` keeps the small
  laws of `HostFunction` and the equality proofs behind its `DecidableEq`.
- **Files that look like one topic are separate on purpose.**
  - `PrimitiveLaws`, `WordComparisons`, `ByteSelection` and `DerivedForms` are one topic in four
    files, because of `@[simp]`. A `@[simp]` lemma reaches every module that imports any part of
    its file. `PrimitiveLaws` reaches few modules, and the other three about half of the repository,
    each a different set, so merging them would change what `simp` does in the difference. The same
    goes for `LocalLoopCorrespondence`, which few modules reach, and `ConventionLaws`.
  - `HostRunner` holds its own definitions, and `Wire/Conversions` stays apart from `Wire/Syntax`.
    Moving either changes which matcher Lean reuses, so the binder names in the equation lemmas of
    `HostRunResult.HasType`, or of `Wire.Expr.toCore`, would change.
- **`Solcore.Core.Renaming` is a module and a type.** The module is now `Internal/Renaming`. The type
  `Renaming` keeps its name, as does every declaration: namespaces do not follow files.
- **Shims.** Old paths that another area imports hold one `import` line and go at consolidation.
