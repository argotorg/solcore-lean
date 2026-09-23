# Project map

Use this guide to enter the source tree by task. The root
[`Solcore.lean`](../Solcore.lean) imports the complete public library; focused
work should normally import a narrower umbrella.

## Choose an entry point

| Goal | Start here | Read next |
| --- | --- | --- |
| Lex or parse source | [`Solcore/Syntax.lean`](../Solcore/Syntax.lean) | `Solcore/Syntax/Lexer.lean`, `Parser.lean`, declaration and grammar modules |
| Validate workspace identity | [`Solcore/Workspace.lean`](../Solcore/Workspace.lean) | path, syntax, validation, judgment, and property modules |
| Check or compile a source workspace | [`Solcore/Frontend/Current.lean`](../Solcore/Frontend/Current.lean) | program loading/checking, inference, specialization, linking, execution |
| Study independent source rules | [`Solcore/SourceSemantics.lean`](../Solcore/SourceSemantics.lean) | static, dynamic, staging, substitution, and program modules |
| Work with resolved local expressions | [`Solcore/Resolved.lean`](../Solcore/Resolved.lean) | identity, scope, typing, evaluation, and Core correspondence |
| Extend source type inference | [`Solcore/TypeSystem.lean`](../Solcore/TypeSystem.lean) | type, substitution, scheme, unification, inference, properties |
| Extend Semantic Core | [`Solcore/Core.lean`](../Solcore/Core.lean) | data, typing, evaluation, checking, machines, safety |
| Execute checked contracts | [`Solcore/ContractRuntime.lean`](../Solcore/ContractRuntime.lean) | world, frame, transaction, host, call, creation, observation modules |
| Change ABI support | [`Solcore/Abi.lean`](../Solcore/Abi.lean) | Keccak-256 and static-word modules |
| Generate checked Core cases | [`Solcore/Synthesis.lean`](../Solcore/Synthesis.lean) | CoreV3 seed, fragment, generator, and shrinker |
| Inspect canonical library bytes | [`Solcore/Standard/CanonicalData.lean`](../Solcore/Standard/CanonicalData.lean) | workspace/frontend consumers and metadata validation |

## Canonical syntax route

The main source path is:

```text
Syntax.Identifier / Declaration
        |
        v
Syntax.Lexer
        |
        v
Syntax.Parser + recovery and diagnostics
        |
        v
Workspace validation
        |
        v
Frontend program loading and checking
```

Declarative grammar modules state the accepted structure independently of the
executable parser. Exactness and soundness modules connect component parsers to
those relations. Begin with [the canonical syntax plan](M2_PLAN.md) before
changing this route.

## Frontend route

[`Solcore/Frontend/Current.lean`](../Solcore/Frontend/Current.lean) collects
the current whole-program modules. The central stages are:

1. `ProgramIdentity`, `ProgramLoading`, and `ProgramEnvironment`;
2. `ProgramImports`, `ProgramInterfaces`, and `ProgramModuleResolution`;
3. `ProgramSignatures`, `ProgramTypeResolution`, and `SourceInference`;
4. `ExecutableImplMethods` and retained evidence/coercions;
5. `SourceStageAnalysis`, `SourceSpecialization`, and its worklist;
6. `SourceCoreElaboration` plus direct or graph linking; and
7. `SourceProgramExecution` / `SourceCompiler` backend selection.

`Solcore.Frontend.Fragments` contains smaller reusable paths. It is not a
second whole-language definition.

## Declarative source-semantics route

Read the proof-facing source model in this order:

1. `Context`, `WellFormed`, and `Graph`;
2. `Instantiation`, `Substitution`, and substitution properties;
3. `Types`, `Traits`, `Requirements`, and `Coercions`;
4. `Binders`, `Calls`, `Patterns`, `Places`, and `Ownership`;
5. `Typing`, `Control`, `Static`, and `Program`;
6. `Staging`; and
7. `Dynamic`, including faults and preservation.

This route states rules over resolved source data. It does not parse files or
make the executable frontend authoritative.

## Semantic Core route

For the local executable language, start with:

1. [`Core/Data.lean`](../Solcore/Core/Data.lean) and
   [`Core/Syntax.lean`](../Solcore/Core/Syntax.lean);
2. [`Core/Typing.lean`](../Solcore/Core/Typing.lean) and
   [`Core/Eval.lean`](../Solcore/Core/Eval.lean);
3. [`Core/Check.lean`](../Solcore/Core/Check.lean);
4. [`Core/Machine.lean`](../Solcore/Core/Machine.lean), host machine, and
   runners; and
5. safety, correspondence, fuel, renaming, local-fragment, and primitive
   property modules.

The retained encoding modules are
[`Core/Wire.lean`](../Solcore/Core/Wire.lean),
[`Core/Wire/V2.lean`](../Solcore/Core/Wire/V2.lean), and
[`Core/Wire/V3.lean`](../Solcore/Core/Wire/V3.lean). The current encoding is
documented in [Core Wire v3](CORE_WIRE_V3.md).

## Checked-contract route

Start from scalar and state carriers, then follow execution:

1. `RuntimeScalars`, `Account`, and `WorldState`;
2. checked program, contract, registry, and code-selection modules;
3. host storage inputs, context, handlers, and drivers;
4. frame run, outcome, trace, checkpoint, continuation, and resolution;
5. parent-indexed and one-level nested execution;
6. transaction journal/storage and world-state deltas; and
7. top-level execution and balanced-state results.

[`Solcore/ContractRuntime.lean`](../Solcore/ContractRuntime.lean) imports the
complete retained boundary.

## Tests and repository checks

- `Tests/` contains executable regression and property modules imported by
  `Tests/Main.lean`.
- `scripts/verify-metadata.mjs` validates repository-owned data and digests.
- `scripts/check-kernel.mjs` enforces the configured semantic-source policy.
- `metadata/baselines.json` records pinned external-comparison evidence.

Run all four checks listed in the [development guide](DEVELOPMENT.md) before
handing off a cross-layer change.

## Documentation routes

- [Architecture](ARCHITECTURE.md) for ownership and dependencies.
- [Current status](CURRENT_STATUS.md) for implemented scope and limitations.
- [Feature matrix](FEATURE_MATRIX.md) for a compact coverage table.
- [Specification charter](SPEC_CHARTER.md) for authority and trust.
- [`docs/adr/`](adr/) for accepted design decisions.
