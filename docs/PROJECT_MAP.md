# Project map

This is a reading route, not a list of every theorem. For the current source
pipeline, import [`Solcore.Frontend.Current`](../Solcore/Frontend/Current.lean);
[`Solcore.Frontend`](../Solcore/Frontend.lean) and
[`Solcore`](../Solcore.lean) remain full compatibility umbrellas. For focused
proof work, start from the narrow module for the question at hand instead of
following every umbrella import. Lean module names follow file paths:
`Solcore.Frontend.SourceCompiler` is
`Solcore/Frontend/SourceCompiler.lean`.

## Choose an entry point

| Question | Read first | Continue with |
| --- | --- | --- |
| How do I run the restricted source compiler? | [`SourceCompiler.lean`](../Solcore/Frontend/SourceCompiler.lean) | [`SourceCompilerProperties.lean`](../Solcore/Frontend/SourceCompilerProperties.lean), [Current status](CURRENT_STATUS.md) |
| How is a raw workspace checked? | [`ProgramChecking.lean`](../Solcore/Frontend/ProgramChecking.lean) | [`ProgramLoading.lean`](../Solcore/Frontend/ProgramLoading.lean), [`ProgramSignatures.lean`](../Solcore/Frontend/ProgramSignatures.lean) |
| Where are source expression types inferred? | [`SourceInference.lean`](../Solcore/Frontend/SourceInference.lean) | [`SourceInference/Program.lean`](../Solcore/Frontend/SourceInference/Program.lean), [`Expression.lean`](../Solcore/Frontend/SourceInference/Expression.lean) |
| Where is the independent source-level formal spec? | [`SourceSemantics.lean`](../Solcore/SourceSemantics.lean) | [`Static.lean`](../Solcore/SourceSemantics/Static.lean), [`Program.lean`](../Solcore/SourceSemantics/Program.lean), [`Dynamic/Evaluation.lean`](../Solcore/SourceSemantics/Dynamic/Evaluation.lean), [`Dynamic/Fault.lean`](../Solcore/SourceSemantics/Dynamic/Fault.lean), [`Dynamic/PatternCompletenessProperties.lean`](../Solcore/SourceSemantics/Dynamic/PatternCompletenessProperties.lean), [`Dynamic/ControlTypingProperties.lean`](../Solcore/SourceSemantics/Dynamic/ControlTypingProperties.lean), [`Dynamic/Preservation.lean`](../Solcore/SourceSemantics/Dynamic/Preservation.lean), [`Dynamic/WholeLanguagePreservation.lean`](../Solcore/SourceSemantics/Dynamic/WholeLanguagePreservation.lean), [`Dynamic/ProgramPreservation.lean`](../Solcore/SourceSemantics/Dynamic/ProgramPreservation.lean), [`Staging.lean`](../Solcore/SourceSemantics/Staging.lean), [ADR-0378](adr/0378-declarative-resolved-source-semantics.md) |
| How does one root become executable? | [`SourceSpecializationWorklist.lean`](../Solcore/Frontend/SourceSpecializationWorklist.lean) | [`SourceCoreDirectLinking.lean`](../Solcore/Frontend/SourceCoreDirectLinking.lean), [`SourceRuntimeLinking.lean`](../Solcore/Frontend/SourceRuntimeLinking.lean), [`SourceTypedRuntime.lean`](../Solcore/Frontend/SourceTypedRuntime.lean) |
| What is the Core language? | [`Core.lean`](../Solcore/Core.lean) | [`Typing.lean`](../Solcore/Core/Typing.lean), [`Eval.lean`](../Solcore/Core/Eval.lean), [`Safety.lean`](../Solcore/Core/Safety.lean) |
| How does Oracle v5 execute contracts? | [`Oracle/V5.lean`](../Solcore/Oracle/V5.lean) | [`Input.lean`](../Solcore/Oracle/V5/Input.lean), [`Execution.lean`](../Solcore/Oracle/V5/Execution.lean), [wire catalog](ORACLE_V5_WIRE.md) |

## Source-library route

The main path is:

```text
Syntax lexer/parser → Workspace identities → ProgramLoading
  → ProgramEnvironment / ProgramImports / ProgramModuleResolution
  → ProgramTypeResolution / ProgramSignatures / ProgramChecking
  → SourceInference → SourceSpecializationWorklist
  → SourceCompiler → selected backend
```

The following smaller modules make that path easier to inspect:

- [`Solcore/Syntax`](../Solcore/Syntax.lean) is the canonical parser umbrella;
  [`Lexer.lean`](../Solcore/Syntax/Lexer.lean) and
  [`Parser.lean`](../Solcore/Syntax/Parser.lean) are the executable entry
  modules. Parser proofs occupy many focused `*Properties.lean` files.
- [`Solcore/Workspace`](../Solcore/Workspace.lean) defines canonical workspace
  identities and validation. [`Solcore/Resolved`](../Solcore/Resolved.lean) is
  an already-resolved local-expression foundation, **not** the complete
  whole-program source resolver.
- [`Solcore/SourceSemantics`](../Solcore/SourceSemantics) is the independent
  formal specification over the resolved, occurrence-addressed source carrier.
  It now covers whole-program static admission, every retained expression and
  statement form, successful big-step dynamics, positive fault propagation,
  generic static-preservation and successful whole-language subject reduction,
  plus independent staging and materialization boundaries. It does not define
  raw-source/module resolution, fault-complete evaluation, progress, or
  checker/backend correctness.
- [`ProgramEnvironment.lean`](../Solcore/Frontend/ProgramEnvironment.lean)
  catalogs declarations;
  [`ProgramModuleResolution.lean`](../Solcore/Frontend/ProgramModuleResolution.lean)
  handles module paths; [`ProgramTypeResolution.lean`](../Solcore/Frontend/ProgramTypeResolution.lean)
  and [`ProgramSignatures.lean`](../Solcore/Frontend/ProgramSignatures.lean)
  form the type/signature boundary.
- [`Solcore/TypeSystem`](../Solcore/TypeSystem.lean) contains source-level
  types, substitution, schemes, unification, and inference machinery.
  [`SourceInference/TypedIR.lean`](../Solcore/Frontend/SourceInference/TypedIR.lean)
  records typed source occurrences used after checking.
- [`SourceSpecialization.lean`](../Solcore/Frontend/SourceSpecialization.lean)
  substitutes a ground root;
  [`SourceSpecializationWorklist.lean`](../Solcore/Frontend/SourceSpecializationWorklist.lean)
  builds its finite executable plan.
- [`SourceCompiler.lean`](../Solcore/Frontend/SourceCompiler.lean) is the
  canonical facade. [`SourceProgramExecution.lean`](../Solcore/Frontend/SourceProgramExecution.lean)
  is the earlier, narrower Core/graph entry path.

## Declarative source-semantics route

Read the proof-facing resolved-source specification in this order:

```text
Context / Types / Instantiation / Traits / Requirements
  → Coercions / Binders / Literals / Operators / Calls / Patterns / Places
  → Graph / Ownership / Control → Static → Program

Substitution → GraphSubstitutionProperties / SubstitutionProperties
  → TraitSubstitutionProperties

Dynamic.Value → Dynamic.Heap → Dynamic.Typing
  → Dynamic.Default / Primitive / Evidence / Pattern / Place
  → Dynamic.Evaluation → Dynamic.Fault
  → Dynamic.PatternCompletenessProperties / ControlTypingProperties
  → Dynamic.Preservation → Dynamic.WholeLanguagePreservation
  → Dynamic.Program / ProgramPreservation

Staging.Stage / Assignment → Staging.Classification
  → Staging.Materialization → Staging.Program
```

[`Substitution.lean`](../Solcore/SourceSemantics/Substitution.lean) defines
normative structural substitution over the retained source carrier.
[`SubstitutionCorrespondence.lean`](../Solcore/SourceSemantics/SubstitutionCorrespondence.lean)
then states the explicit equations with the frontend specialization helper;
the helper is not a premise of the semantic judgments. Start with
[ADR-0377](adr/0377-declarative-source-semantics-foundation.md) for the original
authority boundary and [ADR-0378](adr/0378-declarative-resolved-source-semantics.md)
for the current static, successful-dynamic, and staging boundary.

## Runtime and proof route

| Runtime | Definition and linking | Preservation starting point |
| --- | --- | --- |
| Direct Core | [`SourceCoreElaboration.lean`](../Solcore/Frontend/SourceCoreElaboration.lean), [`SourceCoreDirectLinking.lean`](../Solcore/Frontend/SourceCoreDirectLinking.lean) | [`Core/Safety.lean`](../Solcore/Core/Safety.lean), [`SourceCompilerProperties.lean`](../Solcore/Frontend/SourceCompilerProperties.lean) |
| Finite graph | [`SourceRuntime/Checking.lean`](../Solcore/Frontend/SourceRuntime/Checking.lean) (static syntax and checking), [`SourceRuntime.lean`](../Solcore/Frontend/SourceRuntime.lean) (runtime), [`SourceRuntimeLinking.lean`](../Solcore/Frontend/SourceRuntimeLinking.lean) | [`SourceRuntimeDeep/ValueEnvironment.lean`](../Solcore/Frontend/SourceRuntimeDeep/ValueEnvironment.lean) → [`Application.lean`](../Solcore/Frontend/SourceRuntimeDeep/Application.lean) → [`Evaluation.lean`](../Solcore/Frontend/SourceRuntimeDeep/Evaluation.lean) → [`Preservation.lean`](../Solcore/Frontend/SourceRuntimeDeep/Preservation.lean); [`SourceCompilerGraphDeepProperties.lean`](../Solcore/Frontend/SourceCompilerGraphDeepProperties.lean) |
| Typed source | [`SourceTypedRuntime.lean`](../Solcore/Frontend/SourceTypedRuntime.lean) | [`SourceTypedRuntimeProperties.lean`](../Solcore/Frontend/SourceTypedRuntimeProperties.lean), [`SourceTypedStaticSafetyProperties.lean`](../Solcore/Frontend/SourceTypedStaticSafetyProperties.lean) |

The graph proof chain is about successful runs with deep input and initial
store premises. The separate declarative resolved-source semantics now has a
whole-language successful-evaluation preservation theorem; the executable
typed-source backend still has only its own local value/heap dependencies, not
an evaluator-wide deep-preservation theorem. See
[ADR-0376](adr/0376-deep-runtime-typing-foundations.md) for the exact boundary.

## Other top-level areas

| Directory | Role |
| --- | --- |
| [`Solcore/Semantics`](../Solcore/Semantics) | Contract world, transitions, checkpoint/commit/rollback, and their proofs; separate from Core's local cell store |
| [`Solcore/Oracle`](../Solcore/Oracle) | Versioned protocol and strict wire handling; v5 consumes Core, not canonical source |
| [`Solcore/Synthesis`](../Solcore/Synthesis) | Reproducible checked Core generation and shrinking |
| [`Solcore/Surface`](../Solcore/Surface) | Frozen historical Surface v1 and Multi compatibility/reference code; not the canonical parser |
| [`Solcore/Test`](../Solcore/Test) and [`Tests/golden`](../Tests/golden) | Lean tests and public wire fixtures |
| [`docs/adr`](adr) | Historical decisions and rationale; use [Current status](CURRENT_STATUS.md) for today's supported boundary |

For changes, import the smallest module containing the definitions you need,
keep executable definitions and their proof modules distinguishable, and run
the checks in the [development guide](DEVELOPMENT.md). Existing public
umbrellas and frozen versioned interfaces are compatibility surfaces.
