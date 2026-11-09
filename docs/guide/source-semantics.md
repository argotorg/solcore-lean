# Source semantics

`Solcore/SourceSemantics`, apart from `CoreLowering`, is the independent declarative semantics of the
source language. It defines static typing, staging and a big-step dynamic semantics with faults,
proves source type preservation, and connects the executable frontend to these judgments. No judgment
here defines validity as success of an executable pass. The correspondence with Core is on
[its own page](core-lowering.md).

- **Input.** The judgments are stated over the frontend's typed source
  (`Frontend.SourceInference.TypedSource`) and its signatures; `Program.ofChecked` turns a checked
  program into a `Program`. Values use Core's words.
- **Builds on.** [Syntax](syntax.md), the type system and resolved syntax
  ([Foundations](foundations.md)), the frontend's typed IR, checker and inference
  ([Frontend](frontend.md)), and Core's primitives ([Core](core.md)).
- **Built on by.** [Core lowering](core-lowering.md), the tests, and two compiler passes: the native
  lowering imports [CaptureBinders](../../Solcore/SourceSemantics/CaptureBinders.lean) and the stage
  analysis imports [Staging/Classification](../../Solcore/SourceSemantics/Staging/Classification.lean).

The umbrella, [SourceSemantics](../../Solcore/SourceSemantics.lean), reaches the specification,
dynamic preservation, the substitution laws, the checker theorems and part of `Internal/Inference`,
`Soundness` included. The rest of `Internal/`, `Staging/Preservation` and `CompiledBodies` are
reached only through the [CoreLowering umbrella](../../Solcore/SourceSemantics/CoreLowering.lean).
[Conventions](conventions.md) says how to find a section by its namespace, and where new
declarations go.

## Where things are

### Static semantics

| File | Holds |
| --- | --- |
| [Context](../../Solcore/SourceSemantics/Context.lean) | `Context`, the context of every static judgment |
| [Types](../../Solcore/SourceSemantics/Types.lean), [Binders](../../Solcore/SourceSemantics/Binders.lean) | `TypeWellFormed`, `TypeAdmissible`, `SchemeWellFormed`; `BinderExtends`, `BindersExtend`, `MonoBindersExtend` |
| [CaptureBinders](../../Solcore/SourceSemantics/CaptureBinders.lean) | `CaptureBinders.copiedBinder?`, which bindings a closure copies |
| [WellFormed](../../Solcore/SourceSemantics/WellFormed.lean), [Graph](../../Solcore/SourceSemantics/Graph.lean) | The occurrence graph: `OccurrenceGraphWellFormed`, `ContainsExpression`, `Reachable`, `OccurrenceGraphClosed` |
| [Ownership](../../Solcore/SourceSemantics/Ownership.lean), [Instantiation](../../Solcore/SourceSemantics/Instantiation.lean) | `LocalIdentityOwnership`, `RequirementOwnership`; `ExactSubstitution`, `SchemeInstantiates`, `StructuralSubstitution.applyScheme` |
| [Traits](../../Solcore/SourceSemantics/Traits.lean), [Typing](../../Solcore/SourceSemantics/Typing.lean), [Requirements](../../Solcore/SourceSemantics/Requirements.lean) | Trait evidence (`EvidenceValid`), reference typing (`ReferenceHasRawType`), requirements and coercions (`RequirementValid`, `CoercionPathValid`) |
| [Expressions](../../Solcore/SourceSemantics/Expressions.lean) | The construct rules: literals, operators (`BinaryOperatorHasType`, its operator classes, `BinaryTraitDispatch`), calls, patterns, places and assignments (`WordCompoundAssignmentOperator`). A new operator's typing goes here |
| [Control](../../Solcore/SourceSemantics/Control.lean) | `ControlContext`, `ControlSummary`, `BodyFacts` |
| [Static](../../Solcore/SourceSemantics/Static.lean) | `ExpressionHasType`, `ExpressionFormHasRawType`, `StatementHasType`, `StatementsHaveType`, `BodyHasType`, `MatchExhaustive`. A new expression or statement form gets its typing rule here |
| [StaticValidation](../../Solcore/SourceSemantics/StaticValidation.lean) | An executable scope validator and its correctness, `validateTypesWellScopedWith` |
| [Program](../../Solcore/SourceSemantics/Program.lean) | `Program`, `ProgramWellFormed` |

### Dynamic semantics

[Dynamic](../../Solcore/SourceSemantics/Dynamic.lean) is the umbrella. Faults are positive evidence,
not the complement of success.

| File | Holds |
| --- | --- |
| [Value](../../Solcore/SourceSemantics/Dynamic/Value.lean) | `Dynamic.Value`, `Dynamic.Closure`, `Dynamic.SemanticFault`, `Dynamic.ControlOutcome` |
| [Heap](../../Solcore/SourceSemantics/Dynamic/Heap.lean) | `Dynamic.Heap`, `Dynamic.Heap.Reads`, `Dynamic.Heap.Allocates`, `Dynamic.Heap.AllocatesCopy`, `Dynamic.EnvironmentCopies` |
| [GeneralizedClosure](../../Solcore/SourceSemantics/Dynamic/GeneralizedClosure.lean), [Evidence](../../Solcore/SourceSemantics/Dynamic/Evidence.lean) | Generalized local closures (`Dynamic.GeneralizedClosure.instantiate`), evidence closure (`Dynamic.EvidenceCloses`) |
| [Typing](../../Solcore/SourceSemantics/Dynamic/Typing.lean) | `Dynamic.ValueHasType`, `Dynamic.HeapWellTyped`, `Dynamic.EnvironmentAgrees`, with their allocation and copy lemmas |
| [Primitive](../../Solcore/SourceSemantics/Dynamic/Primitive.lean) | `Dynamic.BinaryPrimitiveApplies`, `Dynamic.StrictBinaryOperator`, coercions, `Dynamic.PatternMatches`. A new primitive operation goes here |
| [Place](../../Solcore/SourceSemantics/Dynamic/Place.lean) | `Dynamic.PlaceResolves`, `Dynamic.ProjectionsUpdate`, `Dynamic.PlaceAssignment` |
| [Evaluation](../../Solcore/SourceSemantics/Dynamic/Evaluation.lean) | Success: `Dynamic.ExpressionFormEvaluates`, `Dynamic.StatementExecutes`, `Dynamic.CallableApplies`, `Dynamic.AssignmentValueApplies` |
| [Fault](../../Solcore/SourceSemantics/Dynamic/Fault.lean) | Faults: `Dynamic.ExpressionFormFaults`, `Dynamic.StatementFaults`, `Dynamic.CallableFaults`, and the invalid-operand relations (`Dynamic.WordBinaryOperator`, `Dynamic.AssignmentOperatorBinary`) |
| [Control](../../Solcore/SourceSemantics/Dynamic/Control.lean), [Preservation](../../Solcore/SourceSemantics/Dynamic/Preservation.lean) | Control outcomes against static summaries (`TypingControlShape`); the statement `Dynamic.WholeLanguagePreservation`, `Dynamic.SourceRuntimeValid`, and the cases that need no recursion, such as `Dynamic.BinaryPrimitiveApplies.preserves` |
| [WholeLanguagePreservation](../../Solcore/SourceSemantics/Dynamic/WholeLanguagePreservation.lean) | One mutual block of private cases (`preserveFormRec`, `preserveBinaryRec`, `preserveStatementRec`, …) and `ProgramWellFormed.wholeLanguagePreservation` |
| [Program](../../Solcore/SourceSemantics/Dynamic/Program.lean) | `Dynamic.ProgramEvaluates`, `Dynamic.ProgramOutcome`, `Dynamic.ProgramEvaluates.preserves` |

### Staging and the frontend

| File | Holds |
| --- | --- |
| [Stage](../../Solcore/SourceSemantics/Staging/Stage.lean), [Classification](../../Solcore/SourceSemantics/Staging/Classification.lean), [Program](../../Solcore/SourceSemantics/Staging/Program.lean) | The stages (`Staging.Stage`: compile-time, runtime, deferred), scope-aware classification (`Staging.FunctionHasStages`), whole-program staging (`Staging.ProgramHasStages`) |
| [Materialization](../../Solcore/SourceSemantics/Staging/Materialization.lean), [CallGuard](../../Solcore/SourceSemantics/Staging/CallGuard.lean), [CallBoundary](../../Solcore/SourceSemantics/Staging/CallBoundary.lean) | The compile-time evaluation boundary (`Staging.Materializes`) and the stage guards of calls |
| [RecursiveProfile](../../Solcore/SourceSemantics/Staging/RecursiveProfile.lean) | The staged traces that the source-to-Core theorems are stated over: `Staging.Recursive.Expression`, `Staging.Recursive.Statements`, `Staging.Recursive.Applies`, `Staging.Recursive.Registry` |
| [Erasure](../../Solcore/SourceSemantics/Staging/Erasure.lean), [Preservation](../../Solcore/SourceSemantics/Staging/Preservation.lean) | Staged outcomes project to the dynamic semantics; staged runs preserve heap typing |
| [ProgramCheckingSoundness](../../Solcore/SourceSemantics/ProgramCheckingSoundness.lean), [SourceProgramCheckingSoundness](../../Solcore/SourceSemantics/SourceProgramCheckingSoundness.lean) | What the checker establishes, up to `ProgramWellFormed` |
| [InferenceSoundness](../../Solcore/SourceSemantics/InferenceSoundness.lean), [TraitResolutionSoundness](../../Solcore/SourceSemantics/TraitResolutionSoundness.lean), [SourceStageAnalysisSoundness](../../Solcore/SourceSemantics/SourceStageAnalysisSoundness.lean) | Soundness of inference, trait resolution and stage analysis |
| [CompiledBodies](../../Solcore/SourceSemantics/CompiledBodies.lean) | Validity of every body the actual compiler cached |

### Internal

| Directory | Topic, and the file a new lemma goes to |
| --- | --- |
| [Internal/Substitution](../../Solcore/SourceSemantics/Internal/Substitution) | Substitution preserves typing: `StructuralLaws` (structural and flexible substitution of every static judgment), `TraitLaws` (closed generic bodies and evidence), `Unification` |
| [Internal/Inference](../../Solcore/SourceSemantics/Internal/Inference) | Typing soundness of inference. Finalization: `Soundness`. Expressions: `ExpressionInduction`, `ExpressionDispatch`, `ExpressionCalls`, `ExpressionRetained`, `CoercionFitting`. Statements: `StatementDispatch`, `StatementControl`, `StatementResources`, `StatementSequences`. Ledgers: `Ledgers`, `ExpressionLedgers`, `LedgerFamilies`, `LedgerSoundness`. Lets: `LetCertificates`, `GeneralizationBarriers`, `CaptureOrigins`. Rooted typing: `RootedContracts`, `RootedSoundness`, `Subtrees`, `ShapeClosure`, `ExecutableInterfaces` |
| [Internal/Privacy](../../Solcore/SourceSemantics/Internal/Privacy) | Scheme quantifiers stay private: protected variables (`ProtectedVariables`, `ProtectedFrames`, `ProtectedInference`), generalization lifetimes (`Lifetimes`, `LifetimeContinuations`, `LifetimeMatches`, `Active`), the selected route (`SelectedReferences`, `SelectedCalls`, `SelectedInference`) |
| [Internal/Selected](../../Solcore/SourceSemantics/Internal/Selected) | Soundness of the selected route, one file per construct (`Expressions`, `Operators`, `Calls`, `Lets`, `Loops`, `Matches`, `Statements`, …), closed by `ExpressionSoundness` |
| [Internal/Compiled](../../Solcore/SourceSemantics/Internal/Compiled), [Internal/Prepared](../../Solcore/SourceSemantics/Internal/Prepared) | What the compiler's selected bodies and prepared plans keep, from `BodySelection` and `Finalization` to `BodyAssembly` and `Barriers` |
| [Internal/Execution](../../Solcore/SourceSemantics/Internal/Execution) | The call tree of successful inference: `CallGraph`, `CallInputs`, `Reads`, `NodeShapes`, progress, binder retention, generalization events |
| [Internal/Formation](../../Solcore/SourceSemantics/Internal/Formation), [Internal/Checking](../../Solcore/SourceSemantics/Internal/Checking) | Formation under the final substitution (`Normalized*`, `Requirements`, `CoercionTargets`); typing certificates of selected bodies |
| [Staging/Internal](../../Solcore/SourceSemantics/Staging/Internal) | `TraceSize` (the sizes the staged inductions use) and the cases of staged preservation: `SelectedContracts`, `SelectedPreservation`, `FaultCalls`, `FaultStatements` |
| [Dynamic/Internal](../../Solcore/SourceSemantics/Dynamic/Internal) | `ControlTransfer`, `PatternCompleteness` |

## Definitions and theorems you build on

Premises matter: several results are conditional on purpose.

| Name | Reading | Used by |
| --- | --- | --- |
| `ProgramWellFormed` | A valid program: signatures, unique and complete definitions, valid bodies | The premise of preservation; the checker theorems conclude it |
| `ProgramWellFormed.wholeLanguagePreservation` | A well-formed program gives `Dynamic.WholeLanguagePreservation`: successful expressions, statement lists and body invocations preserve typing, in structurally instantiated contexts, with the residual inference scope left open | `Internal/Owned` of Core lowering reads its `expression` field |
| `Dynamic.ProgramEvaluates.preserves` | A successful admitted run preserves the instantiated entry body. It says nothing about termination | Tests |
| `Dynamic.FunctionStatementsExecute.noEscapedControl` | A complete typed function body cannot leave a `break` or `continue` | `Internal/Owned/BodyReadyState` of Core lowering |
| `Staging.Recursive.Expression`, `Staging.Recursive.Statements`, `Staging.Recursive.Applies` | Staged traces of a finite profile | The statements of Core lowering's theorems |
| `Staging.Recursive.Expression.value_plain`, `Staging.Recursive.Expressions.values_plain` | A staged trace means an ordinary run | Core lowering, tests |
| `Staging.Recursive.SelectedPreservation.expression`, `.statements`, `.applies` | Staged runs preserve heap typing for a registry of selected bodies (`SelectedBodies`), without whole-program validity | Core lowering's `CellAware`, `Selected` and `Generalized` families |
| `Staging.Recursive.FaultPreservation.expression`, `.statements` | Faulting staged runs preserve heap typing, given `ProgramWellFormed` | — |
| `StructuralSubstitution.BodyHasType.applyParameters`, `FlexibleSubstitution.BodyHasType.applySubstitution`, `Dynamic.FunctionInstantiates.hasType` | Typing survives rigid and flexible substitution; an instantiated body has its substituted type | Inference soundness, preservation |
| `programWellFormed_ofCheckProgram_statements` | Checker success and statement typing of every body give `ProgramWellFormed` | Core lowering's test fixtures build `wellFormed` with it |
| `SourceInferenceSoundness.programWellFormed_ofCheckProgram_inferStatementsFuel_sound`, `programHasStages_ofCheckProgram_and_analysis` | The same from inference, with one premise left open, `SourceInferenceSoundness.InferStatementsFuelSoundness`; with it and a successful stage analysis of every body, the program has stages | — |
| `TraitResolutionSoundness.resolve_success_evidenceValid` | A successful resolution gives valid evidence | `Internal/Callable` of Core lowering |
| `SourceStageAnalysisSoundness.analyzeFunction_success_hasStages_of_wellFormed` | Stage analysis establishes the declarative stages | `Internal/RecursiveNamed` of Core lowering |
| `SourceCompiledActualInitializerBarriers.compile_cached_bodies` | A successful compilation with an artifact gives validity of every cached body. No other premise | `PublicSessions` of Core lowering |
| `CaptureBinders.copiedBinder?` | The copy decision of closures | The native lowering, Core lowering |

[SemanticsBoundary](../../Solcore/Test/SourceSemantics/SemanticsBoundary.lean) names the public
declarations with `example := @…`, so renaming one breaks it on purpose.

## Closures capture by value

solcore-rs issue #120 compared Rust and Lean on two closure programs, and its maintainers decided that
captured variables are passed by value. Lean follows that decision (7ac75aea3). A closure captures the
values its captured variables have when it is created:

1. a later assignment in the enclosing scope does not reach the closure;
2. an assignment inside the body does not reach the enclosing scope;
3. each call starts again from the creation-time values, so an assignment in the body does not carry
   over to the next call of the same closure;
4. a closure that captures another closure captures that closure value, which keeps its own
   creation-time values.

Rust passes captured values as ordinary runtime arguments of the lifted lambda (the module comment of
`crates/specialize/src/evaluate/closures.rs`), which gives rule 3. `Tests.SourceCoreExecution` in
[Foundations/Execution](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean)
runs #120's two programs and a repeated call: they give 42, 83 and 11, where shared cells gave 101,
84 and 212.

**Uninitialized locals.** Rust reads an uninitialized local as zero, also through a capture. Lean
faults on such a read, by decision rather than by defining a zero value for every type. The semantics
faults with `Dynamic.SemanticFault.uninitializedLocation` (`Dynamic.ExpressionFormFaults.localUninitialized`),
except for a local of mapping type, which reads as the empty mapping; compiled code reports
`SourceTypedRuntime.RuntimeError.uninitializedLocal`. A copy of an uninitialized cell is uninitialized,
so the capture never faults, but a read in the body does. Lean and Rust disagree on any program that
reads a local before assigning it, directly or through a capture, so such a program is not a
comparison case ([differential testing](differential-testing.md#rules)).

**How the semantics does it.** A closure still holds an environment of locations; the copies are
fresh cells.

- `CaptureBinders.copiedBinder? source id` copies a binding when its identifier has exactly one
  declaration among the source's inputs, lambda parameters and `let`, `for` and `match` binders, and
  that declaration is monomorphic. A generalized local holds an immutable principal and a hidden match
  scrutinee has no declaration, so both are shared. The lowering calls the same function on the same
  source, so no invariant relates the two sides.
- `Dynamic.EnvironmentCopies` gives each copied binding a fresh cell holding an exact copy of its cell
  (`Dynamic.Heap.AllocatesCopy`); any other binding keeps its location.
- At creation, `ExpressionFormEvaluates.lambda` stores the copies of the creation environment;
  `StatementExecutes.letInitializedGeneralized` and `ForItemExecutes.letInitializedGeneralized` copy
  once, and every instance shares the copies. At each call, `CallableApplies.closure` and
  `closureUnit` copy `function.captured` again and bind the parameters on top; `CallableFaults.closureBody`
  and `closureControlEscape` do the same.
- Copying an exact cell keeps heap typing (`Dynamic.HeapWellTyped.copy`) and lexical agreement
  (`Dynamic.EnvironmentCopies.agrees`), with no further fact about the closure. The body sees only
  per-call copies, so nothing writes a snapshot cell and a captured closure needs no deeper copy.

[Core lowering](core-lowering.md#closures-by-value) describes the lowering and its proofs.

## Making changes

[Adding a language feature](adding-a-feature.md) follows the shifts through every layer; these are
this area's steps, in order.

### Add a primitive operator

As for the shifts (5b8c6e96d) and the unchecked arithmetic (e8d28e957). No preservation statement
changes; each exhaustive `cases` over operators gains a case, and the build finds them.

1. **Typing**, in [Expressions](../../Solcore/SourceSemantics/Expressions.lean): an operator class
   (`ShiftBinaryOperator`, `UncheckedBinaryOperator`), a `BinaryOperatorHasType` constructor
   (`wordShift`, `wordUnchecked`), a `BinaryTraitDispatch` row if the operator dispatches to a trait,
   and `WordCompoundAssignmentOperator` for the compound form.
2. **Evaluation and faults**: `BinaryPrimitiveApplies` and `StrictBinaryOperator` in
   [Primitive](../../Solcore/SourceSemantics/Dynamic/Primitive.lean), leaving a Word-only operator out
   of `IntegerStrictBinaryOperator`; `AssignmentValueApplies` in
   [Evaluation](../../Solcore/SourceSemantics/Dynamic/Evaluation.lean); `WordBinaryOperator` and
   `AssignmentOperatorBinary` in [Fault](../../Solcore/SourceSemantics/Dynamic/Fault.lean), so that a
   wrong operand faults.
3. **Preservation**: `PrimitiveBinaryHasType` and its cases in `PrimitiveBinaryHasType.sourceTyping`,
   `BinaryPrimitiveApplies.preserves` and `AssignmentValueApplies.wordCompoundPreserves`, then the
   binary case of `preserveBinaryRec`.
4. **Substitution and staging**: `StructuralSubstitution.BinaryOperatorHasType.applyParameters`,
   `BinaryOperatorHasType.result_type_admissible` and
   `FlexibleSubstitution.BinaryOperatorHasType.applySubstitution` in `StructuralLaws`; the
   `operatorTyped` cases of `Staging/Preservation` and `Staging/Internal/SelectedPreservation`.
5. **Inference soundness**: `BinaryOperatorInferenceCase`, `binaryBuiltin_hasType`,
   `binaryInteger_hasType`, `inferBinaryOperator_success_case` and `inferAssignedValueFuel_success_sound`
   in `Internal/Inference/Soundness`; then a case each in `Internal/Inference` (`StatementDispatch`,
   `ExpressionLedgers`, `LedgerFamilies`, `StatementResources`), `Internal/Formation`
   (`NormalizedCalls`, `NormalizedCoercions`), `Internal/Privacy` (`ProtectedFrames`,
   `ProtectedInference`, `SelectedReferences`, `SelectedInference`) and `Internal/Selected`
   (`Operators`, `OperatorMetadata`, `State`, `Statements`).
6. **Core lowering and tests**: see [Core lowering](core-lowering.md#making-changes). Each commit
   added a public-API test with the probe's results (`Tests.SourceCoreShiftExecution`,
   `Tests.SourceCoreUncheckedExecution`), registered in [Tests/Main.lean](../../Tests/Main.lean).

### Change an evaluation rule

As for closures by value (7ac75aea3):

1. Change the success and the fault rules together, in
   [Heap](../../Solcore/SourceSemantics/Dynamic/Heap.lean),
   [Evaluation](../../Solcore/SourceSemantics/Dynamic/Evaluation.lean) and
   [Fault](../../Solcore/SourceSemantics/Dynamic/Fault.lean): `CallableApplies.closure` and
   `CallableFaults.closureBody` take the same copy premise.
2. Add the typing facts the new premises need to
   [Dynamic/Typing](../../Solcore/SourceSemantics/Dynamic/Typing.lean) (`Dynamic.HeapWellTyped.copy`),
   then repair `Dynamic/Preservation` and `WholeLanguagePreservation`. The statement
   `Dynamic.WholeLanguagePreservation` did not change.
3. Mirror the rule in staging. `Staging/RecursiveProfile` reuses the dynamic rules for atomic forms
   (`Staging.Recursive.AtomicForm`, lambdas included), but restates calls, statements and generalized
   lets. Then repair `Staging/Erasure`, `Staging/Internal/TraceSize` and the staged preservation cases.
4. Core lowering keeps a sized copy of every dynamic rule in
   [Internal/Foundations/SourceExecutionSize](../../Solcore/SourceSemantics/CoreLowering/Internal/Foundations/SourceExecutionSize.lean).
   Change it in the same commit.
5. Update the hand-built traces of [Semantics](../../Solcore/Test/SourceSemantics/Semantics.lean). Its
   `Tests.SourceSemanticsCaptureCopies` section computes the copies those traces need.

### Add an expression or statement form

Add the typing rule to `Static` (`ExpressionFormHasRawType` or `StatementHasType`) and the rules to
`ExpressionFormEvaluates` and `ExpressionFormFaults` (or `StatementExecutes` and `StatementFaults`);
then the cases of `WholeLanguagePreservation`, `Dynamic/Control` if the form transfers control,
`Staging/Classification`, the staged profile, the sized copies and the substitution laws. Inference
reads `Syntax.Statement` itself, so a statement form reaches its proofs even if no typed program keeps
it; the [integer note](../design/integer-types-unchecked-shifts.md) explains why `unchecked` blocks
have none.

### Work in the two large files

[Internal/Inference/Soundness](../../Solcore/SourceSemantics/Internal/Inference/Soundness.lean) (the
bridge from finalization to typing, namespace `SourceInferenceSoundness`) and
[Internal/Substitution/StructuralLaws](../../Solcore/SourceSemantics/Internal/Substitution/StructuralLaws.lean)
(namespaces `StructuralSubstitution`, then `FlexibleSubstitution`, with short sections per judgment)
were one module each before the layout refactor. They have no `leanmerge` markers: find a proof by
its namespace and name.

- They cannot be cut: private helpers declared near the top are used thousands of lines below
  (`list_eq_singleton_of_length_eq_one` in `Soundness`, `StructuralSubstitution.nominal_injective` in
  `StructuralLaws`).
- A change to either file rebuilds most of `Internal/` and of Core lowering. Put a lemma that needs no
  private helper in a topic file that imports the large one, as `Internal/Inference/StatementResources`
  imports `Soundness`.

## Pitfalls

- **Validity is never success of a pass.** State a rule as a judgment, and connect a pass to it by a
  theorem, as `SourceProgramCheckingSoundness` and `InferenceSoundness` do.
- **Faults are not derived by negation.** A new success rule whose premises can fail needs its fault
  rules; without them a failing program has no outcome at all.
- **Two files stay low.** `CaptureBinders` and `Staging/Classification` are imported by the compiler, so
  an import there that reaches the frontend's lowering or stage analysis makes a cycle.
- **A bare `Context` depends on imports.** [Context](../../Solcore/SourceSemantics/Context.lean) keeps
  its own file because lower Core lowering files mean `Core.Context` through `open Core`, and
  `Internal/Execution/Reads` sits below it because its proofs mean `Frontend.SourceInference.Context`.
  An import that reaches `Context` changes what the name means in those files.
- **`private` is per file.** Some files declare private helpers with the same name and different text,
  so merging them needs a rename: `Internal/Inference/ExpressionInduction` and `ExpressionDispatch`
  (`recordExpressionWithExpected_success_nodesPrefix`), `Internal/Formation/NormalizedLambdas`
  (`unify_fields`), `Internal/Privacy/SelectedReferences`, `SelectedCalls` and `SelectedInference`
  (`unify_requirements`).
- **One public theorem, two proofs.** `RecursiveLedgerInvariant.fresh` is proved in `ExpressionLedgers`
  and in `LedgerFamilies`, `SubtreePreserved.directChild` in `Selected/StatementReferences` and in
  `Selected/Children`. Lean refuses to declare a visible name again, so neither file of a pair may
  import the other; a third may import both, as `LedgerSoundness` does.
- **`@[simp]` reaches every importer.** `Internal/Inference/CoercionFitting` stays alone because the
  selected coercion plan lemmas it needs are `simp` lemmas; `Internal/Formation/CoercionTargets` stays
  apart so that a neighbour's `simp` lemmas cannot fire in its proofs; the test `IntegerBitNot` stays
  apart from `Semantics` for the same reason.
- **The umbrella does not reach most of `Internal/`.** `lake build Solcore.SourceSemantics` can pass
  while `Internal/Selected` or `Staging/Preservation` is broken. Build the CoreLowering umbrella, or
  the whole library, before you commit.
- **The compiled route sits above part of Core lowering.** `CompiledBodies`, `Internal/Compiled`,
  `Internal/Prepared` and `Staging/Internal/FaultCalls` import a few `CoreLowering/Internal` files
  (`Selected/CatalogOrigins`, `Selected/MethodBodies`, and some of `Generalized` and `Callable`), so a
  change there can break them.
- **Front files hold proofs.** The front was not split into definitions and laws; `Graph`,
  `Dynamic/Typing` and `Static` hold the most proofs.

## Testing

| File | Covers |
| --- | --- |
| [Semantics](../../Solcore/Test/SourceSemantics/Semantics.lean) | Admission and execution in the source semantics: capture copies, faults, generalized closures, local schemes |
| [SemanticsBoundary](../../Solcore/Test/SourceSemantics/SemanticsBoundary.lean) | The public names, scoped requirements, static validation |
| [SemanticsSubstitution](../../Solcore/Test/SourceSemantics/SemanticsSubstitution.lean) | Rigid substitution through implementation matching, evidence and requirement ledgers |
| [Inference](../../Solcore/Test/SourceSemantics/Inference.lean) | Source inference, the typed IR, closure capture boundaries, mapping defaults |
| [CompiledOrigins](../../Solcore/Test/SourceSemantics/CompiledOrigins.lean) | Origins and owners of compiled calls and templates, recursive stage operations |
| [IntegerBitNot](../../Solcore/Test/SourceSemantics/IntegerBitNot.lean) | Integer bit-not against its lowering |
| [Foundations/Execution](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean) | The public API on closures by value (`captureWorkspace`), shifts and unchecked arithmetic |

Lean checks a test file's theorems and examples when it builds the file; `lake test` runs the `IO`
entry points that [Tests/Main.lean](../../Tests/Main.lean) calls. Focused checks, from fast to
complete:

```sh
lake build Solcore.SourceSemantics                    # specification, preservation, checker theorems
lake build Solcore.Test.SourceSemantics.Semantics     # hand-built traces
lake build Solcore.SourceSemantics.Staging.Preservation
lake build Solcore.SourceSemantics.CoreLowering       # the rest of Internal/, and every consumer
```

Then run the checks of [Workflow](workflow.md#before-you-commit): `lake build`, `lake test` and
`node scripts/check-kernel.mjs` among them.
