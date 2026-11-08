# Reviewer's guide

This guide says what to read in each area of the repository, in which order, and which theorems
the project claims. README's [Proof status](../../README.md#proof-status) states the claims, and
these pages lead from each claim to its statement and its proof.

## How an area is laid out

- **Umbrella.** `Solcore/<Area>.lean` imports the area. Its module doc gives the reading order in
  brief.
- **Front.** The files of `Solcore/<Area>/` outside `Internal/` hold the specification (the
  definitions the theorems are stated over) and the main theorems. Each opens with a module doc that
  names its main declarations. A large area, such as `Frontend/RustHull` or `Syntax/Parser`, has
  subdirectories laid out the same way.
- **`Internal/`.** Everything else: supporting lemmas, case analyses, certificates and executable
  helpers, merged by topic. Lean checks every proof in it, so a reviewer can read the front's
  statements and leave their proofs to the kernel (see [Trust](#trust)).
- **Sections.** A merged file is a sequence of sections. Each starts at a line
  `-- leanmerge: from <old module>` and keeps the namespace of that module, so a namespace names a
  section of a file, not a file. Search for the namespace or the marker to find a section.

Each area's page has about the same parts: the main definitions and theorems with the evidence
that they are the claims, a reading order, the front files, what `Internal/` holds, and what a
reviewer should know. The tests page says instead how to run the tests and which tests cover which
area.

## Reading order

Read the specification bottom-up: the source language, the target language, what source programs
mean, then the compilers and the proofs that connect them.

| Page | Area | What it holds | Main theorems |
| --- | --- | --- | --- |
| [Syntax](syntax.md) | `Solcore/Syntax` | AST, lexer, parser, and the parser against an independent grammar | `Parser.parse_ok_publicSourceFileOrdinary_sound`, `Parser.parse_exists_ok_iff_publicSourceFileOrdinary`, `Parser.parse_ok_parsed_value_unique` |
| [Foundations](foundations.md) | `Solcore/TypeSystem`, `Resolved`, `Workspace`, `Abi`, `Util` | Source types and inference, resolved expressions, the workspace kernel, the ABI layer | `TypeSystem.Unification.unify_sound`, `Resolved.Lowers.typing_iff`, `Workspace.Validation.validate_sound` |
| [Core](core.md) | `Solcore/Core` | The typed target language, its semantics and its safety | `evaluation_preserves_type`, `Program.checked_run_never_faults`, `run_evaluation_sound` |
| [ContractRuntime](contract-runtime.md) | `Solcore/ContractRuntime` | Accounts, frames, transactions, nested calls and creation over checked Core | `TopLevelExecution.rawRun_ne_fault`, `TopLevelExecution.resumeWithFuel_run` |
| [Source semantics](source-semantics.md) | `Solcore/SourceSemantics` without `CoreLowering` | The independent declarative semantics of the source language and its type preservation | `ProgramWellFormed.wholeLanguagePreservation`, `Dynamic.ProgramEvaluates.preserves` |
| [Frontend](frontend.md) | `Solcore/Frontend` | The native compiler pipeline, and the Rust Hull import with its safety and meaning theorems | `Contract.prepare_resumes_safe`, `Correspondence.prepare_recursive_program_resumes` |
| [Core lowering](core-lowering.md) | `Solcore/SourceSemantics/CoreLowering` | The source-to-Core correspondence proved so far | `CellAwareInvocationAcceptedFlow.body_preserves`, `CellAwareInvocationAcceptedFlow.body_reflects`, `SelectedCompilationRawPublicReceipt.of_compile` |
| [Synthesis](synthesis.md) | `Solcore/Synthesis` | The generators of the differential tests, and the emitters' meaning proofs | `emit_source_meaning` of each emitter, `parseSource_print` |
| [Tests](tests.md) | `Solcore/Test`, `Tests` | Tests by subject, the test driver and the tool executables | — |

Each theorem's premises matter. The source-to-Core correspondence covers parts of the language;
the [Core runtime unification design](../design/core-runtime-unification.md) records what remains.

## Trust

[`scripts/check-kernel.mjs`](../../scripts/check-kernel.mjs) rejects `sorry`, `admit`, `axiom`,
`partial`, `unsafe`, `noncomputable`, `extern` and `implemented_by` in every file of the semantic
areas: Syntax, TypeSystem, Resolved, Workspace, Util, Core, ContractRuntime, SourceSemantics,
Frontend and `Synthesis/Source/ScalarMeaning`. No file there uses `native_decide` either. `Abi`,
which the check does not visit, has none of these, so the theorems of those areas rest on Lean's
kernel and its standard axioms alone. Tests are outside the check, and a few of them decide a
fixture with `native_decide`. README's
[Build and test](../../README.md#build-and-test) section runs the check.

## Following older notes

Commit messages, integration records and notes written before the reviewable layout name modules
that no longer exist. `.refactor/moves-<lane>.tsv` maps each old module to the file that
holds it now, and the `-- leanmerge: from <old module>` marker finds its section in that file. An
old module whose definitions and laws were split points to the laws; its definitions are in the
area's front, under the same namespace. `.refactor/renames-<lane>.tsv` lists the private helpers
that were renamed, and `.refactor/deleted-<lane>.tsv` the identical private copies that were
removed. [Reviewable layout](../design/reviewable-layout.md) describes the refactor and its checks.
