# Reviewer's guide: source semantics

`Solcore/SourceSemantics`, apart from `CoreLowering`, is the independent declarative semantics of the
source language, and the proofs that connect the executable frontend to it. No judgment here defines
validity as success of an executable pass. The correspondence with Core is on
[its own page](core-lowering.md).

Read this area from its [umbrella](../../Solcore/SourceSemantics.lean) and the front files below.
Everything else is in `Internal/`. A namespace names a section of a file, not a file: search for the
marker `-- leanmerge: from <module>` or for the namespace to find a section.

The layout below is the plan for the whole area. A file named without a link has not landed yet.

## Main definitions and theorems

| Claim | Theorems | Evidence |
| --- | --- | --- |
| Source type preservation | `ProgramWellFormed.wholeLanguagePreservation`, `Dynamic.ProgramEvaluates.preserves` | README's "Proof status"; the umbrella; the root of the `Dynamic` theorems |
| Faulting runs preserve heap typing too | `Staging.Recursive.FaultPreservation.expression`, `Staging.Recursive.FaultPreservation.statements` | Dependency roots, with the largest closures in `Staging` |
| Staged runs of selected bodies preserve typing | `Staging.Recursive.SelectedPreservation.expression`, `Staging.Recursive.SelectedPreservation.statements`, `Staging.Recursive.SelectedPreservation.applies` | Dependency roots; used by the CoreLowering public theorems |
| Staged traces mean ordinary runs | `Staging.Recursive.Expression.value_plain`, `Staging.Recursive.Expressions.values_plain` | Dependency roots; used outside the area |
| Generic bodies close under substitution | `BodyHasType.applySubstitution`, `Dynamic.FunctionInstantiates.hasType`, `Dynamic.TraitMethodInstantiates.hasType` | The umbrella; dependency roots |
| The checker gives program validity from body typing | `programWellFormed_ofCheckProgram_deep`, `programWellFormed_ofCheckProgram_statements` | The umbrella; used by 45 modules outside the area |
| One premise is left for that | `SourceInferenceSoundness.programWellFormed_ofCheckProgram_inferStatementsFuel_sound`, `programHasStages_ofCheckProgram_and_analysis` | Dependency roots |
| Trait resolution is sound | `resolve_success_evidenceValid`, `resolve_success_entails` | The umbrella |
| Stage analysis is sound | `SourceStageAnalysisSoundness.analyzeFunction_success_hasStages_of_wellFormed` | The umbrella; a dependency root |
| Selected inference is sound | `SourceInferenceSoundness.actualInferExprFuelRootedSoundness_selected` | Dependency root |
| Every cached body of a public compilation is valid | `SourceCompiledActualInitializerBarriers.compile_cached_bodies` | Cited by the [design note](../design/core-runtime-unification.md); the root of the compiled family |

**How these were chosen.** README's "Proof status" claims source type preservation. The design note
cites one theorem of this area by path, and that theorem has no premise beyond a successful compile,
so it ends the compiled route. A query over the environment lists 1,007 theorems of the area that no
other declaration uses. 107 of them depend on at least 1,000 constants: 80 in the compiled route, 18
in staging, 5 in the dynamic semantics and 4 in inference. The table names the top of each family.
The rest are body-level steps that those families build on.

## Front

47 files, about 44,000 lines. Merged modules keep their old paths as shims until consolidation.
[Dynamic](../../Solcore/SourceSemantics/Dynamic.lean) and [Staging](../../Solcore/SourceSemantics/Staging.lean) are umbrellas, and each module doc is a reading guide.

### Static semantics

| File | Holds |
| --- | --- |
| [Context](../../Solcore/SourceSemantics/Context.lean) | `Context`, the context of every static judgment |
| [Types](../../Solcore/SourceSemantics/Types.lean) | `TypeWellFormed`, `TypeAdmissible`, `SchemeWellFormed`, `PredicateWellFormed` |
| [Binders](../../Solcore/SourceSemantics/Binders.lean) | `BinderWellFormed`, `BinderExtends`, `BindersExtend`, `MonoBindersExtend` |
| [CaptureBinders](../../Solcore/SourceSemantics/CaptureBinders.lean) | `CaptureBinders.declaredBinders`, `CaptureBinders.copiedBinder?` |
| [WellFormed](../../Solcore/SourceSemantics/WellFormed.lean) | `OccurrenceGraphWellFormed`, `ContainsExpression`, `ContainsStatement` |
| [Instantiation](../../Solcore/SourceSemantics/Instantiation.lean) | `ExactSubstitution`, `SchemeInstantiates`, `StructuralSubstitution.applyScheme` |
| [Traits](../../Solcore/SourceSemantics/Traits.lean) | `ImplHeadInstantiates`, `TraitEvidence`, `EvidenceValid` |
| [Typing](../../Solcore/SourceSemantics/Typing.lean) | `ReferenceHasRawType`, `SolvedRequirementValid` |
| [Requirements](../../Solcore/SourceSemantics/Requirements.lean) | `RequirementLedgerWellFormed`, `RequirementValid`, `CoercionPathValid` |
| `Expressions` | `IntegerLiteralValid`, `BinaryOperatorHasType`, `DeclarationApplicationValid`, `TypedMatchPatternHasType`, `PlaceHasType` |
| [Ownership](../../Solcore/SourceSemantics/Ownership.lean) | `LocalIdentityOwnership`, `RequirementOwnership`, `definedLocalIds` |
| [Graph](../../Solcore/SourceSemantics/Graph.lean) | `Reachable`, `OccurrenceGraphClosed`, `OccurrenceGraphAcyclic` |
| [Control](../../Solcore/SourceSemantics/Control.lean) | `ControlContext`, `ControlSummary`, `BodyFacts` |
| [Static](../../Solcore/SourceSemantics/Static.lean) | `ExpressionHasType`, `StatementHasType`, `StatementsHaveType`, `BodyHasType`, `MatchExhaustive` |
| [StaticValidation](../../Solcore/SourceSemantics/StaticValidation.lean) | `StaticValidationError`, `validateTypesWellScopedWith` |
| [Program](../../Solcore/SourceSemantics/Program.lean) | `Program`, `Program.ofChecked`, `ProgramWellFormed` |

### Dynamic semantics

| File | Holds |
| --- | --- |
| [Value](../../Solcore/SourceSemantics/Dynamic/Value.lean) | `Dynamic.Value`, `Dynamic.SemanticFault`, `Dynamic.ExpressionOutcome`, `Dynamic.ValueRuntimeType` |
| [Heap](../../Solcore/SourceSemantics/Dynamic/Heap.lean) | `Dynamic.Heap`, `Dynamic.Heap.Reads`, `Dynamic.HeapMetadataExtend` |
| [GeneralizedClosure](../../Solcore/SourceSemantics/Dynamic/GeneralizedClosure.lean) | `Dynamic.RuntimeContextFields`, `Dynamic.GeneralizedClosure.instantiate` |
| [Evidence](../../Solcore/SourceSemantics/Dynamic/Evidence.lean) | `Dynamic.EvidenceCloses`, `Dynamic.RequirementsProduceEnvironment`, `Dynamic.LocalSchemeRuntimeInstantiation` |
| [Typing](../../Solcore/SourceSemantics/Dynamic/Typing.lean) | `Dynamic.ValueHasType`, `Dynamic.HeapWellTyped`, `Dynamic.EnvironmentAgrees`, `Dynamic.DefaultValue` |
| [Primitive](../../Solcore/SourceSemantics/Dynamic/Primitive.lean) | `Dynamic.BinaryPrimitiveApplies`, `Dynamic.CoercionPathApplies`, `Dynamic.PatternMatches` |
| [Place](../../Solcore/SourceSemantics/Dynamic/Place.lean) | `Dynamic.PlaceResolves`, `Dynamic.ProjectionsUpdate`, `Dynamic.PlaceAssignment` |
| [Evaluation](../../Solcore/SourceSemantics/Dynamic/Evaluation.lean) | `Dynamic.ExpressionEvaluates`, `Dynamic.StatementExecutes`, `Dynamic.CallableApplies`, `Dynamic.BodyInstance` |
| [Fault](../../Solcore/SourceSemantics/Dynamic/Fault.lean) | `Dynamic.ExpressionFaults`, `Dynamic.StatementFaults`, `Dynamic.BodyFaults` |
| [Control](../../Solcore/SourceSemantics/Dynamic/Control.lean) | `TypingControlShape`, `ControlRuntimeValid` |
| [Preservation](../../Solcore/SourceSemantics/Dynamic/Preservation.lean) | `Dynamic.WholeLanguagePreservation`, `Dynamic.SourceRuntimeValid`, and the cases that need no recursion |
| [WholeLanguagePreservation](../../Solcore/SourceSemantics/Dynamic/WholeLanguagePreservation.lean) | `ProgramWellFormed.wholeLanguagePreservation` |
| [Program](../../Solcore/SourceSemantics/Dynamic/Program.lean) | `Dynamic.ProgramEntry`, `Dynamic.ProgramEvaluates`, `Dynamic.ProgramOutcome`, `Dynamic.ProgramEvaluates.preserves` |

### Staging

| File | Holds |
| --- | --- |
| [Stage](../../Solcore/SourceSemantics/Staging/Stage.lean) | `Staging.Stage`, `Staging.StagesJoin` |
| [CallGuard](../../Solcore/SourceSemantics/Staging/CallGuard.lean), [CallBoundary](../../Solcore/SourceSemantics/Staging/CallBoundary.lean) | `Staging.CallGuard.Accepts`, `Staging.CallBoundary.Executes` |
| [Classification](../../Solcore/SourceSemantics/Staging/Classification.lean) | `Staging.FunctionHasStages`, `Staging.BinderGetsStage`, `Staging.StatementAssigns` |
| [Materialization](../../Solcore/SourceSemantics/Staging/Materialization.lean) | `Staging.Materializes`, `Staging.ComptimeEvaluationBoundary` |
| [Program](../../Solcore/SourceSemantics/Staging/Program.lean) | `Staging.ProgramHasStages` |
| `RecursiveProfile` | `Staging.Recursive.Expression`, `Staging.Recursive.Statements`, `Staging.Recursive.Registry` |
| `Erasure` | `Staging.Recursive.Expression.value_plain` |
| `Preservation` | The staged preservation theorems of the table above |

### Checking, inference and compiled bodies

| File | Holds |
| --- | --- |
| [ProgramCheckingSoundness](../../Solcore/SourceSemantics/ProgramCheckingSoundness.lean) | `CheckedProgramWellFormedConditions` and what the checker gives before any body is proved |
| [TraitResolutionSoundness](../../Solcore/SourceSemantics/TraitResolutionSoundness.lean) | `resolve_success_evidenceValid` |
| [SourceProgramCheckingSoundness](../../Solcore/SourceSemantics/SourceProgramCheckingSoundness.lean) | `programWellFormed_ofCheckProgram_deep`, `programWellFormed_ofCheckProgram_statements` |
| [SourceStageAnalysisSoundness](../../Solcore/SourceSemantics/SourceStageAnalysisSoundness.lean) | `SourceStageAnalysisSoundness.analyzeFunction_success_hasStages_of_wellFormed` |
| [InferenceSoundness](../../Solcore/SourceSemantics/InferenceSoundness.lean) | `programHasStages_ofCheckProgram_and_analysis` and its premise |
| [CompiledBodies](../../Solcore/SourceSemantics/CompiledBodies.lean) | `SourceCompiledActualInitializerBarriers.compile_cached_bodies` |

## Reading order

1. **Static semantics.** [Context](../../Solcore/SourceSemantics/Context.lean),
   [Types](../../Solcore/SourceSemantics/Types.lean) and
   [Binders](../../Solcore/SourceSemantics/Binders.lean), then
   `Expressions` and
   [Static](../../Solcore/SourceSemantics/Static.lean), which assembles the construct rules. End with
   [Program](../../Solcore/SourceSemantics/Program.lean).
2. **Dynamic semantics.** [Value](../../Solcore/SourceSemantics/Dynamic/Value.lean),
   [Heap](../../Solcore/SourceSemantics/Dynamic/Heap.lean),
   [Evaluation](../../Solcore/SourceSemantics/Dynamic/Evaluation.lean), then
   [Fault](../../Solcore/SourceSemantics/Dynamic/Fault.lean). Faults are positive evidence, not a
   total complement of success.
3. **Source type preservation.** The statement is `Dynamic.WholeLanguagePreservation`, in
   [Preservation](../../Solcore/SourceSemantics/Dynamic/Preservation.lean). Its proof is in
   [WholeLanguagePreservation](../../Solcore/SourceSemantics/Dynamic/WholeLanguagePreservation.lean),
   and [Program](../../Solcore/SourceSemantics/Dynamic/Program.lean) states it for a whole run.
4. **Staging.** [Classification](../../Solcore/SourceSemantics/Staging/Classification.lean), then
   `RecursiveProfile`, which the
   source-to-Core theorems are stated over. Then
   `Erasure` and
   `Preservation`.
5. **The executable frontend.**
   [SourceProgramCheckingSoundness](../../Solcore/SourceSemantics/SourceProgramCheckingSoundness.lean),
   then [InferenceSoundness](../../Solcore/SourceSemantics/InferenceSoundness.lean).
6. **Actual compilation.** [CompiledBodies](../../Solcore/SourceSemantics/CompiledBodies.lean).

## Main theorems

Premises matter here. Several results are stated conditionally on purpose, and the reading says so.

| Theorem | File | Reading |
| --- | --- | --- |
| `ProgramWellFormed.wholeLanguagePreservation` | [WholeLanguagePreservation](../../Solcore/SourceSemantics/Dynamic/WholeLanguagePreservation.lean) | A well-formed program gives preservation of every successful expression, statement list and body invocation. Runs are of structurally instantiated contexts, and the residual inference scope stays open |
| `Dynamic.ProgramEvaluates.preserves` | [Program](../../Solcore/SourceSemantics/Dynamic/Program.lean) | A successful admitted run preserves the instantiated entry body. It says nothing about termination |
| `Dynamic.FunctionStatementsExecute.noEscapedControl` | [WholeLanguagePreservation](../../Solcore/SourceSemantics/Dynamic/WholeLanguagePreservation.lean) | A complete typed function body cannot leave a break or continue transfer |
| `Staging.Recursive.FaultPreservation.statements` | `Preservation` | Faulting staged statements preserve heap typing, for a well-formed program |
| `Staging.Recursive.SelectedPreservation.statements` | `Preservation` | The same for a registry of selected bodies, which needs no whole-program validity |
| `Dynamic.FunctionInstantiates.hasType` | `TraitLaws` | An instantiated function body has its substituted type |
| `programWellFormed_ofCheckProgram_statements` | [SourceProgramCheckingSoundness](../../Solcore/SourceSemantics/SourceProgramCheckingSoundness.lean) | Checker success and statement typing of every body give `ProgramWellFormed` |
| `SourceInferenceSoundness.programWellFormed_ofCheckProgram_inferStatementsFuel_sound` | [InferenceSoundness](../../Solcore/SourceSemantics/InferenceSoundness.lean) | The same, with one premise left: `SourceInferenceSoundness.InferStatementsFuelSoundness`, the recursive soundness of statement inference. It is not discharged here |
| `programHasStages_ofCheckProgram_and_analysis` | [InferenceSoundness](../../Solcore/SourceSemantics/InferenceSoundness.lean) | With that premise and a successful stage analysis of every body, the program has stages. Static checking alone gives no staging conclusion |
| `resolve_success_evidenceValid` | [TraitResolutionSoundness](../../Solcore/SourceSemantics/TraitResolutionSoundness.lean) | A successful resolution gives valid evidence |
| `SourceInferenceSoundness.actualInferExprFuelRootedSoundness_selected` | [ExpressionSoundness](../../Solcore/SourceSemantics/Internal/Selected/ExpressionSoundness.lean) | Selected inference is sound for every successful expression |
| `SourceCompiledActualInitializerBarriers.compile_cached_bodies` | [CompiledBodies](../../Solcore/SourceSemantics/CompiledBodies.lean) | A successful public compilation with an artifact gives validity of every original cached body, including late ordinary functions and implementation methods. Its only premises are the compilation and the artifact |

## Internal

| Directory | Files | Lines | Topic |
| --- | ---: | ---: | --- |
| [Internal/Inference](../../Solcore/SourceSemantics/Internal/Inference) | 22 | 62,000 | Typing soundness of inference: finalization, expressions, statements, ledgers and let certificates |
| [Internal/Privacy](../../Solcore/SourceSemantics/Internal/Privacy) | 10 | 20,000 | Scheme quantifiers stay private through inference, and generalization lifetimes |
| [Internal/Selected](../../Solcore/SourceSemantics/Internal/Selected) | 14 | 20,000 | The selected route: soundness for retained children and generalized initializers |
| [Internal/Compiled](../../Solcore/SourceSemantics/Internal/Compiled) | 19 | 26,000 | What the actual compiler's selected bodies keep, and their recursive typing |
| [Internal/Execution](../../Solcore/SourceSemantics/Internal/Execution) | 10 | 14,000 | The call tree of successful inference: calls, inputs, reads, binders, shapes and progress |
| [Internal/Formation](../../Solcore/SourceSemantics/Internal/Formation) | 7 | 8,000 | Types and requirements are well formed under the final substitution |
| [Internal/Prepared](../../Solcore/SourceSemantics/Internal/Prepared) | 7 | 5,000 | Prepared plans: call edges, qualified reads and template scope |
| `Internal/Substitution` | 3 | 15,000 | Structural and trait substitution preserve typing |
| `Internal/Checking` | 1 | 1,000 | Typing certificates of selected bodies |
| `Staging/Internal` | 5 | 8,000 | Trace sizes and the cases of staged preservation |
| `Dynamic/Internal` | 2 | 1,000 | Pattern completeness and control transfers |

The families follow the namespaces of the base: `SourceInferenceExecution`, `SourceInferenceSoundness`,
`SourceInferenceSoundness.ProtectedVariables`, and the two formation namespaces.

## Why some files are apart

Each row comes from a check. Only the row on public theorems failed a build first; the others come from a
predictor, so a row may be stricter than it has to be. Undoing one needs that check again.

| Cause | Split |
| --- | --- |
| Shadowing: bare `Context` must keep meaning `Frontend.SourceInference.Context` | [Internal/Execution/Reads](../../Solcore/SourceSemantics/Internal/Execution/Reads.lean) stays below [Context](../../Solcore/SourceSemantics/Context.lean) |
| Private names that differ, in text or only in a doc comment | `Internal/Inference/ExpressionInduction` apart from `ExpressionDispatch`, whose private copies of `recordExpressionWithExpected_success_nodesPrefix` differ only in their doc comment; `Internal/Formation/NormalizedLambdas` apart from `NormalizedCalls`; `Internal/Privacy/SelectedReferences`, `SelectedCalls` and `SelectedInference` |
| Height: a low body must not reach a high import | `Internal/Execution/ExpressionProgress` sits above the compiled body layer, and `StatementProgress` below it |
| Two proofs of one public theorem. A third file may see both copies, but Lean refuses a new declaration of a visible public name | [ExpressionLedgers](../../Solcore/SourceSemantics/Internal/Inference/ExpressionLedgers.lean) and [LedgerFamilies](../../Solcore/SourceSemantics/Internal/Inference/LedgerFamilies.lean) both declare `RecursiveLedgerInvariant.fresh`; [StatementReferences](../../Solcore/SourceSemantics/Internal/Selected/StatementReferences.lean) and [Children](../../Solcore/SourceSemantics/Internal/Selected/Children.lean) both declare `SubtreePreserved.directChild`. Neither file of a pair may reach the other |
| `simp` lemmas of one import | `Internal/Inference/CoercionFitting` alone, because only it needs the selected coercion plan lemmas; `Internal/Inference/ShapeClosure`; `Internal/Formation/CoercionTargets` |

Two choices were not forced. [CaptureBinders](../../Solcore/SourceSemantics/CaptureBinders.lean) and
[Classification](../../Solcore/SourceSemantics/Staging/Classification.lean) are imported by the frontend, so they
take nothing from above, although a check would allow it. [Context](../../Solcore/SourceSemantics/Context.lean)
keeps its own file because the CoreLowering layout constraints name it.

## What stays mixed

- **Two files stay long.** [Soundness](../../Solcore/SourceSemantics/Internal/Inference/Soundness.lean)
  has 26,295 lines and `StructuralLaws`
  12,986. Each is one module of the base, and the layout rule lets an existing file keep its length:
  no merge made them long. They cannot be cut either. `private` is per file, a few `private` helpers
  are used across almost all of each, and `list_eq_singleton_of_length_eq_one` runs for 16,895 lines
  of the first. Cutting one would mean making a helper public, which this refactor does not do.
- **Front files hold proofs.** The front files were not split into definitions and laws. The 37
  specification files have about 28,000 lines, and about 7,500 of those are proofs that `private`
  would let leave. The most are in
  [Graph](../../Solcore/SourceSemantics/Graph.lean), [Dynamic/Typing](../../Solcore/SourceSemantics/Dynamic/Typing.lean)
  and [Static](../../Solcore/SourceSemantics/Static.lean).
