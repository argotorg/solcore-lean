# Foundations

Five small areas that the compilers, the runtime and the semantics build on. Each has an umbrella
and a short front; only TypeSystem and Resolved have an `Internal/`.

| Area | Holds | Feeds | Builds on |
| --- | --- | --- | --- |
| [`TypeSystem`](../../Solcore/TypeSystem.lean) | source types, substitutions, unification, schemes, inference state | the native frontend (type resolution, inference, specialization) and the source semantics (types, instantiation, inference soundness) | `Resolved/Identity` |
| [`Resolved`](../../Solcore/Resolved.lean) | stable identities and scopes; resolved local expressions and their lowering to Core | identities: both. Expressions: the frontend's staging, `Frontend/Fragments`, and the staging proofs of Core lowering | `Workspace/Syntax`, [Core](core.md) |
| [`Workspace`](../../Solcore/Workspace.lean) | canonical paths and identities, validation of a raw workspace | the native frontend, which validates every input; its `ModuleId` reaches everything through `Resolved.DeclarationId` | nothing |
| [`Abi`](../../Solcore/Abi.lean) | Keccak-256 and the static Word ABI | the frontend's public API (`Frontend/SourceCoreExecution`), Synthesis | [ContractRuntime](contract-runtime.md), Core |
| [`Util`](../../Solcore/Util.lean) | fixed-width radix and hex codecs, a JSON number helper | ContractRuntime's `RuntimeScalars`, the Core wire codec, the Rust Hull decoder | nothing |

The import chain is `Workspace/Path`, `Workspace/Syntax`, `Resolved/Identity`, then
`TypeSystem/Type`: a type parameter belongs to a `Resolved.DeclarationId`, which holds a
`Workspace.ModuleId`. `Abi` sits above ContractRuntime, not below it.

## TypeSystem

`TypeSystem.Ty` is the source type language, in front of `Core.Ty`. It separates flexible inference
variables (`variable`) from rigid generic parameters (`parameter`).

| File | Holds |
| --- | --- |
| [`Type`](../../Solcore/TypeSystem/Type.lean) | `TypeSystem.Ty`, `TypeVarId`, `TypeParameterId`, `BuiltinType`, `TypeParameterOccurs`, `Ty.freeVariables`, `Ty.VariablesBelow` |
| [`Substitution`](../../Solcore/TypeSystem/Substitution.lean) | `Substitution`, `Substitution.apply`, `Substitution.compose` |
| [`Unification`](../../Solcore/TypeSystem/Unification.lean) | `Constraint`, `Unification.unify`, `Unification.unifyTypes`, and every proof about the private `loop` |
| [`Scheme`](../../Solcore/TypeSystem/Scheme.lean) | `Scheme`, `DeclarationScheme`, `Environment`, `Scheme.instantiateWithSubstitution`, `Scheme.matchInstance?` |
| [`Inference`](../../Solcore/TypeSystem/Inference.lean) | `InferState` with `fresh`, `instantiate`, `unify` and `solve`; `Inference.infer` over a small `TypeSystem.Expr` |
| [`Internal/SubstitutionLaws`](../../Solcore/TypeSystem/Internal/SubstitutionLaws.lean) | structural invariants of substitutions, including the definitions `Substitution.SolvedBelow` and `Substitution.RangeAvoidsDomain` |
| [`Internal/SchemeLaws`](../../Solcore/TypeSystem/Internal/SchemeLaws.lean) | small laws of substitutions and schemes, correlated rigid instances |
| [`Internal/InferenceLaws`](../../Solcore/TypeSystem/Internal/InferenceLaws.lean) | laws of `InferState`, `Inference.infer_solved_variablesBelow` |

**Definitions and theorems you build on.**

| Declarations | Reading | Used by |
| --- | --- | --- |
| `Unification.unify_sound`, `unify_sound_of_below`, `unify_solvedBelow`, `unify_rangeAvoidsDomain` | a solution satisfies the constraints, is solved below the variable bound, and avoids an older domain | tests; the `unifyTypes_…` forms below |
| `unifyTypes_sound`, `unifyTypes_solvedBelow`, `unifyTypes_rangeAvoidsDomain`, `unify_domain_origin` | the same for one equation, and a solution binds only variables of its input | the source semantics' inference proofs, such as `SourceSemantics/Internal/Substitution/Unification` |
| `Scheme.matchInstance?`, `Scheme.matchInstance?_sound` | a match binds exactly the quantified variables and turns the scheme's body into the given type | `Frontend/SourceSpecialization`, `SourceSemantics/Instantiation` |
| `InferState`, `Scheme.instantiateWithSubstitution`, `Substitution.apply` | the inference state and instantiation | `Frontend/SourceInference` and the source semantics |

Unification is proved sound, not complete. It runs on a fuel bound (`Unification.defaultFuel`) and
can fail with `occursCheck`, `mismatch` or `exhausted`. Only tests use `Inference.infer`, which
exists to exercise the kernel end to end; the frontend's inference threads an `InferState` itself.

### Add a builtin type

`integer` was added in 2bf3e5547: the type in `TypeSystem/Type`, its name in the frontend's type
resolution, a literal conversion in `Frontend/WordLiteral`, a case in `SourceCoreElaboration`, and
tests now in `Test/Frontend/Programs.lean`, `Test/Frontend/WordOperators.lean` and
`Test/SourceSemantics/CoreLowering/Foundations/Execution.lean`. 0ce7c5f07 and f3d644700 later gave
it a Core representation.

1. `TypeSystem/Type`: a `BuiltinType` constructor and an abbreviation such as `Ty.integer`.
2. Frontend: its source name in `ProgramTypeResolution`. `builtinTypeName?` maps fixed names;
   `resolveIntegerFallback` resolves `integer` only after every user type at the lookup boundary.
3. Frontend: every projection from source types to Core types, such as
   `SourceCoreElaboration.lowerType` and the `Catalog.project` functions in `Frontend/SourceCore`.
   Search for `.builtin .word` to find them.
4. A Core type, if the type has a runtime representation
   ([Core](core.md#add-an-expression-form-or-a-value-form)).
5. The source semantics' rules for its values and literals ([Source semantics](source-semantics.md)).
   `TypeWellScoped.builtin` already admits every builtin.

### Extend unification or inference

Examples: a3796d7a5 (solved form through unification), 52bb55f5d (solved inference states),
1cba496b8 (constraint soundness). Each changed `Unification`, the laws now in `Internal/`, and the
public-boundary test; a3796d7a5 also changed `Type`, and 52bb55f5d `Scheme`.

1. Change the algorithm in `Unification`'s private `loop`. Proofs that unfold it must stay in that
   file, since `private` is per file; the same holds for `Scheme`'s private helpers.
2. Keep the guarantees in the table above. A new invariant on substitutions belongs in
   `Internal/SubstitutionLaws`, which `Unification` and `Scheme` import.
3. A new `TypeSystem.Ty` constructor also reaches `Substitution.apply`, `Ty.freeVariables`,
   `TypeParameterOccurs`, `loop`, instance matching, and every match on `TypeSystem.Ty` in the
   frontend and the source semantics.
4. Add each new public theorem to the public-boundary section of `Test/TypeSystem/Inference.lean`
   (`example := @…`).

**Pitfall.** `SchemeLaws` holds `@[simp]` lemmas about substitutions, and many modules import
`InferenceLaws` without it. Merging them would change what `simp` does there.

## Resolved

The foundation for already-resolved local expressions: exact lookup, lowering, typing, evaluation,
and agreement with Core. It is not a source resolver.

| File | Holds |
| --- | --- |
| [`Identity`](../../Solcore/Resolved/Identity.lean) | `Resolved.DeclarationId`, `Resolved.LocalId`, `Resolved.freshLocalId` |
| [`LocalScope`](../../Solcore/Resolved/LocalScope.lean) | `Resolved.LocalScope` with first-match `lookup?` and `index?`, and the witnesses `LocalScope.Lookup` and `LocalScope.IndexOf` |
| [`Expr`](../../Solcore/Resolved/Expr.lean) | `Resolved.Expr`, `Expr.lower?`, the relation `Resolved.Lowers`, `Expr.lower?_sound` |
| [`Typing`](../../Solcore/Resolved/Typing.lean), [`Eval`](../../Solcore/Resolved/Eval.lean) | `Resolved.HasType` with `Lowers.typing_iff`; `Resolved.Evaluates` with `Lowers.evaluates_iff` |
| [`ExecutionProperties`](../../Solcore/Resolved/ExecutionProperties.lean) | `Lowers.evaluates_iff_run_done`, `Lowers.closed_run_never_faults`, `HasType.closed_run_has_sufficient_fuel` |
| [`Internal/ScopeLaws`](../../Solcore/Resolved/Internal/ScopeLaws.lean) | well-scoped expressions, weakening, uniform renaming, the word less-than builder |
| [`Internal/LocalFragmentLaws`](../../Solcore/Resolved/Internal/LocalFragmentLaws.lean) | `Lowers.localFragment`: lowering produces only Core's local fragment |

**You build on** `Lowers.typing_iff` (from `Lowers.preserves_type` and `Lowers.reflects_type`)
and `Lowers.evaluates_iff`: lowering preserves and reflects typing and evaluation.
`Frontend/Fragments` uses `Lowers.evaluates_iff`; Core lowering's staging proofs use
`Expr.lower?_sound`, `Lowers.reflects_type`, `Resolved.HasType` and `Resolved.Evaluates`.

`Resolved.Expr` uses Core's `UnaryOp` and `BinaryOp`, and its rules apply `op.apply` and the type
functions generically. A new Core operator therefore works here with no change.

**Add an expression form.** Ordered pairs took three commits: a7381280b (`Expr`, `Typing`, `Eval`,
scopes and renaming), d71740836 (the lowering, typing, evaluation and scope proofs) and f684c0d4d
(the public-boundary tests, now in `Test/Resolved/Semantics.lean` and
`Test/Frontend/PublicBoundary.lean`). Keep the lowered form inside Core's `Expr.LocalFragment`, or
extend that fragment first (03d28bf7f added pairs to it).

**Pitfall.** `Internal/LocalFragmentLaws` stays apart from `Expr`: importing the local fragment
there would put `Core/Internal/DerivedForms` and its `simp` lemmas under everything that imports
`Resolved.Expr`.

## Workspace

The Workspace Identity Kernel. It turns a `RawWorkspace` (an entry path, main sources and named
external libraries) into a `ValidatedUserWorkspace`, or rejects it with every error at once. It does
not resolve modules or names.

| File | Holds |
| --- | --- |
| [`Path`](../../Solcore/Workspace/Path.lean) | `CanonicalSourcePath` (`.sol`, or the legacy `.solc`), `ModulePath`, `ExternalLibraryName`, with parsers and total orders |
| [`Syntax`](../../Solcore/Workspace/Syntax.lean) | `RawWorkspace`, `ValidatedUserWorkspace`, `WorkspaceFile`, `LibraryId`, `SourceId`, `ModuleId` |
| [`Error`](../../Solcore/Workspace/Error.lean) | `ValidationError` and its canonical order |
| [`Judgment`](../../Solcore/Workspace/Judgment.lean) | the independent specification: `Validates`, `Rejects`, `RawWorkspace.Equivalent` |
| [`Validation`](../../Solcore/Workspace/Validation.lean) | `Workspace.Validation.validate`, exported as `Workspace.validate` |
| [`Properties`](../../Solcore/Workspace/Properties.lean) | the theorems below |

**What it validates.** One `ValidationError` constructor per check:

| Error | Raised when |
| --- | --- |
| `invalidEntryPath` | the entry is not a canonical source path |
| `invalidExternalLibraryName`, `duplicateExternalLibraryName` | a library name is not canonical, or two libraries share one |
| `invalidMainSourcePath`, `invalidExternalSourcePath` | a source path is not canonical |
| `duplicateMainSourcePath`, `duplicateExternalSourcePath` | two main sources, or two sources of one library, have the same canonical path |
| `missingEntry` | no main source has the entry's path |

Errors come sorted by constructor rank, fixed by ADR-0014, then by their arguments
(`ValidationError.compare`). A duplicate is a duplicate path, suffix included. `main.sol` and
`main.solc` both validate and share one `ModuleId` (`SourceId.toModuleId_eq_iff`); the frontend
then rejects them with `ProgramEnvironmentError.duplicateModule`.

**You build on** these theorems in `Properties`:
- `Validation.validate_sound`, `validate_complete`, `validate_errors_sound` and
  `validate_errors_complete`: `validate` succeeds exactly when `Validates` holds, and rejects with
  exactly the errors `Rejects` gives.
- `validates_or_rejects` and `Validates.not_rejected`: one of the two holds, never both.
- `validate_equivalent`, `validate_preserves_sourceFiles` and `validate_preserves_sourceBytes`:
  inputs that differ only in the order of their sources and libraries (`RawWorkspace.Equivalent`)
  give the same result, and sources keep their count and bytes.

The frontend calls `Workspace.validate` first, in `Frontend.loadProgram`; `Frontend.checkProgram`
takes a `RawWorkspace`.

**Add or change a check.** Add the constructor to `ValidationError`, with its `rank` and `arguments`;
its case in `ValidationError.Applies` (`Judgment`); the executable check in `Validation`; and the
cases of the proofs in `Properties`. 6a46559af, which accepted `.sol`, changed `Path` and `Syntax`
and added the test now in `Tests.SourcePathExtensions`. Many proofs in `Path`, `Validation` and
`Properties` name private helpers, so they stay in those files.

## Abi

Solcore's ABI layer for methods that take and return one Word.

| File | Holds |
| --- | --- |
| [`Keccak256`](../../Solcore/Abi/Keccak256.lean) | `Abi.V1.Keccak256.hash`, Ethereum-compatible Keccak-256 |
| [`StaticWord`](../../Solcore/Abi/StaticWord.lean) | method metadata and selectors, the codec, method tables, the generated dispatcher, `StaticWordContract` and its `run` |

The pieces of `StaticWord`, in order:
- **Metadata.** `SupportedType` has only `uint256`. A selector is the first four bytes of the
  Keccak-256 of the canonical signature, such as `f(uint256)` (`MethodMetadata.selector`).
- **Codec.** `encodeCall` and `decodeCall` use a 36-byte prefix, a 4-byte selector then one
  big-endian word, and ignore the rest. `encodeResult` and `decodeResult` use exactly 32 bytes.
- **Tables.** `MethodTable.validate` rejects an empty table, duplicate signatures and selector
  collisions. Whether it accepts, and the entries it gives, do not depend on the order of the
  methods (`MethodTable.validate_accepts_iff_of_input_perm`, `MethodTable.entries_eq_of_input_perm`).
- **Dispatcher.** `MethodTable.dispatchProgram` is a Core program. It reads the calldata through the
  host functions `inputDataSize` and `inputDataWordBE?`, by their `HostFunction.index`, and reverts
  with `malformedCalldataReason` or `unknownSelectorReason`. `MethodTable.dispatchProgram_checked`
  proves that `Program.checkHost` accepts it.
- **Contracts.** `MethodTable.generate` makes it a `wordOutcomeV1` contract.
  `StaticWordContract.validate` validates a method list and keeps its table with the contract
  generated from it, and `StaticWordContract.run` runs that contract through
  `BalancedTopLevelExecution.runWithEnvironment`.

**Change the codec.** The Lean codec and the Core dispatcher describe the same bytes, so change them
together and re-prove `dispatchProgram_checked`. `StaticWordContract.callInvocation_inputData_bytes`
states that a call's input is `encodeCall` of its selector and argument. A new `SupportedType`
changes the signature text, and so every selector. The end-to-end tests (`AbiStaticWordEndToEnd` in
`Test/Abi/StaticWord.lean`) run the two together. The codec and dispatcher came in 8761c6530,
ebf59aeaf and 6226e7ab7.

**Pitfalls.** About half of `StaticWord`'s proofs name private helpers, so they stay in the file.
The kernel check visits `Abi` too. It matches words anywhere, comments included, so a name such as
`admit` or a comment that says "partial" fails it ([Conventions](conventions.md#proof-rules)).

## Util

Generic helpers with no Solcore syntax, typing or semantics:
[`FixedRadix`](../../Solcore/Util/FixedRadix.lean) (`Util.FixedRadix.encodeNat`, `decodeNat`,
`decodeNat_encodeNat_of_lt`), [`FixedHex`](../../Solcore/Util/FixedHex.lean)
(`Util.FixedHex.encodeText`, `encodeText_injective`) and [`Json`](../../Solcore/Util/Json.lean)
(`Util.jsonNatural?`, `jsonNatural_toJson`).

`jsonNatural?` accepts every JSON number whose value is a natural number, decimal and exponent
spellings included. The Core wire codec and the Rust Hull decoder both use it, so a change there
changes what both accept. Keep `Util` free of Solcore types.

## Testing

| Area | Tests |
| --- | --- |
| TypeSystem | [`Test/TypeSystem/Inference.lean`](../../Solcore/Test/TypeSystem/Inference.lean): compile-time examples and the public-boundary list |
| Resolved | [`Test/Resolved/Semantics.lean`](../../Solcore/Test/Resolved/Semantics.lean): compile-time examples, and the `IO` tests `resolvedPairBoundaryTests` and `resolvedLocalSemanticsTests`; many `Test/Frontend` files use resolved expressions |
| Workspace | `testWorkspacePathIdentity`, `testWorkspaceCanonicalValidation`, `testWorkspaceEqualContentIdentity`, `testWorkspaceValidationErrors` and `testWorkspaceValidationEquivalence` in [`Tests/Main.lean`](../../Tests/Main.lean); `Tests.SourcePathExtensions` in [`Test/Frontend/Source/Inference.lean`](../../Solcore/Test/Frontend/Source/Inference.lean) |
| Abi | [`Test/Abi/StaticWord.lean`](../../Solcore/Test/Abi/StaticWord.lean): Keccak, metadata, codec, tables, dispatcher, contracts, end to end |
| Util | no test of its own; `testRuntimeScalars` in `Test/ContractRuntime/HostDriver.lean` and the wire tests exercise it |

```sh
lake build Solcore.TypeSystem                 # likewise Solcore.Resolved, .Workspace, .Abi, .Util
lake build Solcore.Test.TypeSystem.Inference  # one test file's compile-time checks
lake build                                    # the frontend and the semantics build on these
lake test                                     # all IO tests, Resolved, Workspace and Abi included
```

See [Workflow](workflow.md) and [Tests](tests.md).
