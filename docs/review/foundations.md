# Reviewer's guide: foundations

The small areas under the compiler: the source type system, resolved expressions, the workspace
kernel, and shared utilities. Each has a short front, and its umbrella gives the reading order.

## Main definitions and theorems

README's "Proof status" names no result here. The areas' own results are the top of their theorem
dependencies, and these decided the front:

| Area | Claim | Theorems | Evidence |
| --- | --- | --- | --- |
| `TypeSystem` | Unification is sound | `TypeSystem.Unification.unify_sound`, `TypeSystem.Unification.unify_sound_of_below` | root of the dependencies |
| `TypeSystem` | A successful unification binds only input variables | `TypeSystem.Unification.unify_domain_origin` | used by four modules outside the area |
| `TypeSystem` | Instance matching is sound | `TypeSystem.Scheme.matchInstance?_sound` | used outside the area |
| `TypeSystem` | Inference stays below its variable bound | `TypeSystem.Inference.infer_solved_variablesBelow` | root of the dependencies |
| `Resolved` | Lowering preserves and reflects typing and evaluation | `Resolved.Lowers.typing_iff`, `Resolved.Lowers.evaluates_iff` | roots of the dependencies; used outside the area |
| `Resolved` | A lowered expression runs on the Core machine | `Resolved.Lowers.evaluates_iff_run_done`, `Resolved.Lowers.closed_run_never_faults` | the largest closures in the area |
| `Workspace` | Validation decides the judgments | `Workspace.Validation.validate_sound`, `Workspace.Validation.validate_complete`, `Workspace.validates_or_rejects` | the umbrella's "correspondence theorems"; roots of the dependencies |
| `Workspace` | Validation depends only on the inputs that matter | `Workspace.validate_equivalent` | the largest closure in the area |

`Util` has no main theorem of its own. `Util.FixedRadix.decodeNat_encodeNat_of_lt` and
`Util.FixedHex.encodeText_injective` are its top results.

## TypeSystem

`Solcore/TypeSystem` holds executable source-level types, substitutions, rank-1 schemes and
first-order inference. It stays separate from the closed monomorphic Core types until specialization.

| File | Main declarations |
| --- | --- |
| [`Type`](../../Solcore/TypeSystem/Type.lean) | `TypeSystem.Ty`, `TypeSystem.TypeVarId` |
| [`Substitution`](../../Solcore/TypeSystem/Substitution.lean) | `TypeSystem.Substitution`, `TypeSystem.Substitution.apply`, `TypeSystem.Substitution.compose` |
| [`Unification`](../../Solcore/TypeSystem/Unification.lean) | `TypeSystem.Constraint`, `TypeSystem.Unification.unify` |
| [`Scheme`](../../Solcore/TypeSystem/Scheme.lean) | `TypeSystem.Scheme`, `TypeSystem.Environment`, `TypeSystem.Scheme.instantiateWithSubstitution`, `TypeSystem.Scheme.matchInstance?` |
| [`Inference`](../../Solcore/TypeSystem/Inference.lean) | `TypeSystem.InferState`, `TypeSystem.Inference.infer` |

| Result | Theorems | File | Reading |
| --- | --- | --- | --- |
| Soundness of unification | `TypeSystem.Unification.unify_sound`, `TypeSystem.Unification.unify_sound_of_below` | [`Unification`](../../Solcore/TypeSystem/Unification.lean) | a solution satisfies every constraint |
| Origin of a solution | `TypeSystem.Unification.unify_domain_origin` | [`Unification`](../../Solcore/TypeSystem/Unification.lean) | a solution binds only variables of its input |
| Instance matching | `TypeSystem.Scheme.matchInstance?_sound` | [`Scheme`](../../Solcore/TypeSystem/Scheme.lean) | a match gives a substitution that turns the scheme's body into the actual type |
| Inference | `TypeSystem.Inference.infer_solved_variablesBelow` | [`Internal/InferenceLaws`](../../Solcore/TypeSystem/Internal/InferenceLaws.lean) | inference ends in a solved state, with every variable of the type below the next fresh one |

| Internal file | Topic |
| --- | --- |
| [`SubstitutionLaws`](../../Solcore/TypeSystem/Internal/SubstitutionLaws.lean) | Structural invariants of substitutions |
| [`SchemeLaws`](../../Solcore/TypeSystem/Internal/SchemeLaws.lean) | Small laws of substitutions and schemes, and correlated rigid instances |
| [`InferenceLaws`](../../Solcore/TypeSystem/Internal/InferenceLaws.lean) | Laws of the inference state |

`Unification` and `Scheme` keep their proofs, because those unfold private helpers. `SchemeLaws` and
`InferenceLaws` are separate because `SchemeLaws` holds `@[simp]` lemmas about substitutions, and
about 500 modules see `InferenceLaws` without seeing it.

## Resolved

`Solcore/Resolved` is the foundation for already-resolved local expressions. It is not a canonical
source resolver or a complete source-to-Core pipeline.

| File | Main declarations |
| --- | --- |
| [`Identity`](../../Solcore/Resolved/Identity.lean) | `Resolved.LocalId`, `Resolved.freshLocalId` |
| [`LocalScope`](../../Solcore/Resolved/LocalScope.lean) | `Resolved.LocalScope`, `Resolved.LocalScope.Lookup`, `Resolved.LocalScope.IndexOf` |
| [`Expr`](../../Solcore/Resolved/Expr.lean) | `Resolved.Expr`, `Resolved.Expr.lower?`, `Resolved.Lowers` |
| [`Typing`](../../Solcore/Resolved/Typing.lean) | `Resolved.HasType` |
| [`Eval`](../../Solcore/Resolved/Eval.lean) | `Resolved.Evaluates` |
| [`ExecutionProperties`](../../Solcore/Resolved/ExecutionProperties.lean) | the main theorems below |

| Result | Theorems | File | Reading |
| --- | --- | --- | --- |
| Typing | `Resolved.Lowers.typing_iff`, `Resolved.typing_deterministic` | [`Typing`](../../Solcore/Resolved/Typing.lean) | lowering preserves and reflects typing |
| Evaluation | `Resolved.Lowers.evaluates_iff`, `Resolved.evaluation_deterministic` | [`Eval`](../../Solcore/Resolved/Eval.lean) | lowering preserves and reflects evaluation |
| Execution | `Resolved.Lowers.evaluates_iff_run_done` | [`ExecutionProperties`](../../Solcore/Resolved/ExecutionProperties.lean) | an evaluation is a finished Core machine run |
| Safety | `Resolved.Lowers.closed_run_never_faults`, `Resolved.HasType.closed_run_has_sufficient_fuel` | [`ExecutionProperties`](../../Solcore/Resolved/ExecutionProperties.lean) | a closed typed expression does not fault, and enough fuel finishes it |

| Internal file | Topic |
| --- | --- |
| [`ScopeLaws`](../../Solcore/Resolved/Internal/ScopeLaws.lean) | Well-scoped expressions, weakening, uniform renaming, and the word less-than builder |

## Workspace

`Solcore/Workspace` is the Workspace Identity Kernel: canonical logical identities, structural
validation, independent judgments, and their correspondence. It does not resolve modules or names.

| File | Main declarations |
| --- | --- |
| [`Path`](../../Solcore/Workspace/Path.lean) | `Workspace.CanonicalSourcePath`, `Workspace.ModulePath`, `Workspace.ExternalLibraryName` |
| [`Syntax`](../../Solcore/Workspace/Syntax.lean) | `Workspace.RawWorkspace`, `Workspace.ValidatedUserWorkspace`, `Workspace.WorkspaceFile`, `Workspace.SourceId`, `Workspace.ModuleId` |
| [`Error`](../../Solcore/Workspace/Error.lean) | `Workspace.ValidationError` |
| [`Judgment`](../../Solcore/Workspace/Judgment.lean) | `Workspace.Validates`, `Workspace.Rejects`, `Workspace.RawWorkspace.Equivalent` |
| [`Validation`](../../Solcore/Workspace/Validation.lean) | `Workspace.Validation.validate` |
| [`Properties`](../../Solcore/Workspace/Properties.lean) | the main theorems below |

| Result | Theorems | File | Reading |
| --- | --- | --- | --- |
| Success | `Workspace.Validation.validate_sound`, `Workspace.Validation.validate_complete` | [`Properties`](../../Solcore/Workspace/Properties.lean) | `validate` succeeds exactly where `Workspace.Validates` holds |
| Rejection | `Workspace.Validation.validate_errors_sound`, `Workspace.Validation.validate_errors_complete` | [`Properties`](../../Solcore/Workspace/Properties.lean) | `validate` rejects with exactly the errors `Workspace.Rejects` gives |
| Dichotomy | `Workspace.validates_or_rejects`, `Workspace.Validates.not_rejected` | [`Properties`](../../Solcore/Workspace/Properties.lean) | a raw workspace validates or is rejected, and never both |
| Invariance | `Workspace.validate_equivalent`, `Workspace.validate_preserves_sourceFiles`, `Workspace.validate_preserves_sourceBytes` | [`Properties`](../../Solcore/Workspace/Properties.lean) | equivalent inputs give the same result, and sources keep their bytes |

`Workspace` has no `Internal/`: it was already six files, all of them front. `Properties` holds
supporting lemmas with the main theorems, because most of them name private helpers, and `private` is
per file.

## Util

Generic representation and codec helpers. They define no source syntax, typing or semantics.

| File | Main declarations |
| --- | --- |
| [`FixedRadix`](../../Solcore/Util/FixedRadix.lean) | `Util.FixedRadix.encodeNat`, `Util.FixedRadix.decodeNat` |
| [`FixedHex`](../../Solcore/Util/FixedHex.lean) | `Util.FixedHex.encodeText` |
| [`Json`](../../Solcore/Util/Json.lean) | helpers shared by the codecs |
