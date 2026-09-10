import Solcore.Frontend.LocalReference
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.LocalReferenceElaboration
import Solcore.Frontend.LocalReferenceElaborationProperties
import Solcore.Frontend.LocalReferenceEvaluation
import Solcore.Frontend.LocalReferenceExecutionProperties
import Solcore.Frontend.LocalExpression
import Solcore.Frontend.LocalExpressionShapeProperties
import Solcore.Frontend.LocalExpressionResolutionProperties
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalExpressionTypingResolution
import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.LocalFunctionApplicationProperties
import Solcore.Frontend.LocalFunctionApplicationEvaluation
import Solcore.Frontend.LocalFunctionApplicationEvaluationProperties
import Solcore.Frontend.LocalFunctionApplicationStepComposition
import Solcore.Frontend.LocalFunctionApplicationExecutionProperties
import Solcore.Frontend.LocalFunctionApplicationRuntimeSafetyProperties
import Solcore.Frontend.LocalFunctionApplicationRuntimeStateProperties
import Solcore.Frontend.LocalFunctionApplicationInsertionProperties
import Solcore.Frontend.LocalFunctionApplicationInsertionPaths
import Solcore.Frontend.LocalFunctionApplicationExactInsertionProperties
import Solcore.Frontend.LocalComputation
import Solcore.Frontend.LocalComputationEvaluation
import Solcore.Frontend.LocalComputationProperties
import Solcore.Frontend.LocalComputationEvaluationProperties
import Solcore.Frontend.LocalComputationExecutionProperties
import Solcore.Frontend.LocalComputationInsertionProperties
import Solcore.Frontend.LocalComputationFragment
import Solcore.Frontend.LocalComputationReturnTree
import Solcore.Frontend.LocalComputationReturnTreeEvaluation
import Solcore.Frontend.LocalComputationFragmentProperties
import Solcore.Frontend.LocalComputationFragmentInsertionProperties
import Solcore.Frontend.LocalComputationFragmentInsertionPaths
import Solcore.Frontend.LocalComputationReturnTreeProperties
import Solcore.Frontend.LocalComputationReturnTreeTypingProperties
import Solcore.Frontend.LocalComputationReturnTreeEvaluationProperties
import Solcore.Frontend.LocalComputationReturnTreeEmbeddingProperties
import Solcore.Frontend.LocalComputationReturnTreeExecutionProperties
import Solcore.Frontend.LocalComputationReturnTreeCostProperties
import Solcore.Frontend.RuntimeComputationFunctionCompilation
import Solcore.Frontend.RuntimeComputationFunctionEntry
import Solcore.Frontend.RuntimeComputationFunctionProperties
import Solcore.Frontend.RuntimeComputationFunctionFactorizationProperties
import Solcore.Frontend.DirectWordBinary
import Solcore.Frontend.DirectWordBinaryProperties
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RecursiveLocalComputationCost
import Solcore.Frontend.RecursiveLocalComputationEvaluation
import Solcore.Frontend.RecursiveLocalComputationFragment
import Solcore.Frontend.RecursiveLocalComputationTypingProperties
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationRenamingProperties
import Solcore.Frontend.RecursiveLocalComputationDeterminismProperties
import Solcore.Frontend.RecursiveLocalComputationEvaluationProperties
import Solcore.Frontend.RecursiveLocalComputationEvaluationRenamingProperties
import Solcore.Frontend.RecursiveLocalComputationCostExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Frontend.ComputationBodyFragment
import Solcore.Frontend.WordMatch
import Solcore.Frontend.WordMatchProperties
import Solcore.Frontend.ComputationBodyFragmentInsertionPaths
import Solcore.Frontend.ComputationBodyFragmentInsertionProperties
import Solcore.Frontend.ComputationBodyFragmentProperties
import Solcore.Frontend.ComputationReturnTree
import Solcore.Frontend.ComputationReturnTreeCheckingProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Frontend.ComputationReturnTreeEvaluation
import Solcore.Frontend.ComputationReturnTreeEvaluationProperties
import Solcore.Frontend.ComputationReturnTreeExecutionProperties
import Solcore.Frontend.ComputationReturnTreeFragmentProperties
import Solcore.Frontend.ComputationReturnTreeProperties
import Solcore.Frontend.ComputationReturnTreeTypeExtensionProperties
import Solcore.Frontend.ComputationReturnTreeOwnerProperties
import Solcore.Frontend.ComputationReturnTreeRawOwnerProperties
import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.ComputationReturnTreeRuntimeSafetyProperties
import Solcore.Frontend.ComputationReturnTreeRuntimeCheckpointProperties
import Solcore.Frontend.ComputationReturnTreeRuntimeWorldProperties
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveComputationReturnTreeEmbeddingProperties
import Solcore.Frontend.ComputationFunctionCompilation
import Solcore.Frontend.ComputationFunctionEntry
import Solcore.Frontend.ComputationFunctionProperties
import Solcore.Frontend.ComputationFunctionArgumentProperties
import Solcore.Frontend.ComputationFunctionOwnerProperties
import Solcore.Frontend.ComputationFunctionTypeExtensionProperties
import Solcore.Frontend.ComputationFunctionFactorizationProperties
import Solcore.Frontend.ComputationFunctionRuntimeSafetyProperties
import Solcore.Frontend.ComputationFunctionRuntimeCheckpointProperties
import Solcore.Frontend.RuntimeInputValidation
import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.LocalFragmentProperties
import Solcore.Frontend.LocalExpressionEvaluationRules
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Frontend.LocalExpressionEvaluationProperties
import Solcore.Frontend.LocalExpressionSafetyProperties
import Solcore.Frontend.LocalExpressionExecutionProperties
import Solcore.Frontend.LocalReferenceEmbeddingProperties
import Solcore.Frontend.LocalInputs
import Solcore.Frontend.LocalInputsProperties
import Solcore.Frontend.LocalInputsLookupProperties
import Solcore.Frontend.LocalInputsExecution
import Solcore.Frontend.LocalInputsExecutionProperties
import Solcore.Frontend.LocalInputsApplication
import Solcore.Frontend.LocalInputsApplicationProperties
import Solcore.Frontend.LocalInputsApplicationCostProperties
import Solcore.Frontend.LocalInputsApplicationRuntimeProperties
import Solcore.Frontend.LocalApplicationReturnBody
import Solcore.Frontend.LocalApplicationReturnBodyProperties
import Solcore.Frontend.LocalApplicationReturnBodyEvaluationProperties
import Solcore.Frontend.LocalApplicationReturnBodyRunnerProperties
import Solcore.Frontend.RuntimeApplicationFunctionCompilation
import Solcore.Frontend.RuntimeApplicationFunctionEntry
import Solcore.Frontend.RuntimeApplicationFunctionCompilationProperties
import Solcore.Frontend.RuntimeApplicationFunctionEntryProperties
import Solcore.Frontend.RuntimeApplicationFunctionFactorizationProperties
import Solcore.Frontend.LocalNameAvoidance
import Solcore.Frontend.LocalNameAvoidanceProperties
import Solcore.Frontend.LocalInputsExtensionLookupSupport
import Solcore.Frontend.LocalInputsExtensionTyping
import Solcore.Frontend.LocalInputsExtensionSemantics
import Solcore.Frontend.LocalInputsExtensionProperties
import Solcore.Frontend.LocalExpressionRenamingProperties
import Solcore.Frontend.LocalExpressionRenamingSemantics
import Solcore.Frontend.LocalInputsRenaming
import Solcore.Frontend.LocalInputsRenamingProperties
import Solcore.Frontend.LocalNameRenaming
import Solcore.Frontend.NumericDigits
import Solcore.Frontend.NumericDigitsProperties
import Solcore.Frontend.WordLiteral
import Solcore.Frontend.WordLiteralProperties
import Solcore.Frontend.LocalExpressionCost
import Solcore.Frontend.LocalExpressionCostErasureProperties
import Solcore.Frontend.LocalExpressionCostProperties
import Solcore.Frontend.LocalExpressionCostStepComposition
import Solcore.Frontend.LocalExpressionCostCorrespondence
import Solcore.Frontend.LocalExpressionCostExecutionProperties
import Solcore.Frontend.LocalExpressionCostRenamingProperties
import Solcore.Frontend.LocalExpressionCostInvariance
import Solcore.Frontend.LocalInputsCostInvariance
import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Frontend.LocalExpressionEvaluatorSoundnessProperties
import Solcore.Frontend.LocalExpressionEvaluatorCompletenessProperties
import Solcore.Frontend.LocalExpressionEvaluatorProperties
import Solcore.Frontend.LocalExpressionEvaluatorExecutionProperties
import Solcore.Frontend.TypeName
import Solcore.Frontend.TypeNameProperties
import Solcore.Frontend.TypeNameTableExtensionProperties
import Solcore.Frontend.StructuralType
import Solcore.Frontend.StructuralTypeProperties
import Solcore.Frontend.StructuralTypeTableProperties
import Solcore.Frontend.RuntimeFunctionHeaderTypeExtensionProperties
import Solcore.Frontend.RuntimeParameterDeclarationsTypeExtensionProperties
import Solcore.Frontend.RuntimeFunctionCompilationTypeExtensionProperties
import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.RuntimeParametersProperties
import Solcore.Frontend.RuntimeParametersTypeExtensionProperties
import Solcore.Frontend.RuntimeParametersLayout
import Solcore.Frontend.ReturnBody
import Solcore.Frontend.ReturnBodyProperties
import Solcore.Frontend.ReturnBodyExecutionProperties
import Solcore.Frontend.ReturnBodyElaboration
import Solcore.Frontend.RuntimeFunctionHeader
import Solcore.Frontend.RuntimeFunctionEntry
import Solcore.Frontend.RuntimeFunctionEntryProperties
import Solcore.Frontend.RuntimeFunctionTypeExtensionProperties
import Solcore.Frontend.RuntimeFunctionEntryCost
import Solcore.Frontend.RuntimeFunctionEntryExecutionProperties
import Solcore.Frontend.RuntimeFunctionEvaluator
import Solcore.Frontend.RuntimeFunctionEvaluatorProperties
import Solcore.Frontend.RuntimeParametersPositionProperties
import Solcore.Frontend.RuntimeParameterReferenceProperties
import Solcore.Frontend.RuntimeFunctionParameterReturnProperties
import Solcore.Frontend.RuntimeParametersStaticProperties
import Solcore.Frontend.RuntimeFunctionStaticProperties
import Solcore.Frontend.RuntimeParametersOwnerProperties
import Solcore.Frontend.RuntimeFunctionOwnerProperties
import Solcore.Frontend.LocalTypeInputs
import Solcore.Frontend.LocalTypeInputsProperties
import Solcore.Frontend.ExpectedUnaryLambdaHeader
import Solcore.Frontend.ExpectedComputationLambda
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.RuntimeParameterDeclarationsLayout
import Solcore.Frontend.RuntimeParameterDeclarationsPositionProperties
import Solcore.Frontend.RuntimeParameterDeclarationReferenceProperties
import Solcore.Frontend.LocalInputsTypeErasure
import Solcore.Frontend.LocalOwnerRenaming
import Solcore.Frontend.LocalTypeInputsRenaming
import Solcore.Frontend.LocalInputsTypeErasureRenamingProperties
import Solcore.Frontend.RuntimeParameterDeclarationsOwnerProperties
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties
import Solcore.Frontend.RuntimeFunctionCompilation
import Solcore.Frontend.RuntimeFunctionCompilationProperties
import Solcore.Frontend.RuntimeFunctionLocalFragmentProperties
import Solcore.Frontend.RuntimeFunctionCompilationOwnerProperties
import Solcore.Frontend.RuntimeFunctionParameterCompilationProperties
import Solcore.Frontend.RuntimeFunctionConditionalParameterCompilationProperties
import Solcore.Frontend.RuntimeFunctionPreparationFactorization
import Solcore.Frontend.RuntimeFunctionExecutionFactorization
import Solcore.Frontend.RuntimeFunctionCompiledExecutionProperties
import Solcore.Frontend.RuntimeFunctionObservationProperties
import Solcore.Frontend.LocalExpressionStoreProperties
import Solcore.Frontend.RuntimeFunctionStoreProperties
import Solcore.Frontend.LocalExpressionFuelBound
import Solcore.Frontend.LocalExpressionFuelBoundProperties
import Solcore.Frontend.ReturnBodyFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Frontend.ReturnBodyResumptionProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Resolved.WordLessWithIds
import Solcore.Resolved.WordLessWithIdsEvaluationProperties
import Solcore.Frontend.WordLessCostStepComposition
import Solcore.Core.LocalFragment
import Solcore.Core.LocalFragmentInsertionProperties
import Solcore.Core.LocalFragmentTypingInsertionProperties
import Solcore.Core.LocalFragmentInferenceInsertionProperties
import Solcore.Core.LocalFragmentInsertionPaths
import Solcore.Core.LocalFragmentExactInsertionProperties
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Core.LocalRightWordLessTypingProperties
import Solcore.Core.LocalRightWordLessEvaluationProperties
import Solcore.Frontend.WordLessLocalRightCostProperties
import Solcore.Frontend.ConditionalReturnBody
import Solcore.Frontend.ConditionalReturnBodyProperties
import Solcore.Frontend.ConditionalReturnBodyEvaluation
import Solcore.Frontend.ConditionalReturnBodyEvaluationProperties
import Solcore.Frontend.ReturnBodyContinuationProperties
import Solcore.Frontend.ConditionalReturnBodyExecutionProperties
import Solcore.Frontend.ConditionalReturnBodyRunnerProperties
import Solcore.Frontend.ConditionalReturnBodyFuelBoundProperties
import Solcore.Frontend.ConditionalReturnBodyResumptionProperties
import Solcore.Frontend.TerminalReturnBody
import Solcore.Frontend.TerminalReturnBodyProperties
import Solcore.Frontend.TerminalReturnBodyEvaluation
import Solcore.Frontend.TerminalReturnBodyEvaluationProperties
import Solcore.Frontend.TerminalReturnBodyExecutionProperties
import Solcore.Frontend.TerminalReturnBodyRunnerProperties
import Solcore.Frontend.TerminalReturnBodyFuelBoundProperties
import Solcore.Frontend.TerminalReturnBodyResumptionProperties
import Solcore.Frontend.ReturnBodyRenamingProperties
import Solcore.Frontend.ConditionalReturnBodyRenamingProperties
import Solcore.Frontend.TerminalReturnBodyRenamingProperties
import Solcore.Frontend.ReturnBodyStoreProperties
import Solcore.Frontend.ConditionalReturnBodyStoreProperties
import Solcore.Frontend.TerminalReturnBodyStoreProperties
import Solcore.Frontend.TerminalReturnTree
import Solcore.Frontend.TerminalReturnTreeElaboration
import Solcore.Frontend.TerminalReturnTreeProperties
import Solcore.Frontend.TerminalReturnTreeEmbeddingProperties
import Solcore.Frontend.TerminalReturnTreeEvaluation
import Solcore.Frontend.TerminalReturnTreeEvaluationProperties
import Solcore.Frontend.TerminalReturnTreeExecutionProperties
import Solcore.Frontend.TerminalReturnTreeEvaluationEmbeddingProperties
import Solcore.Frontend.TerminalReturnTreeRunner
import Solcore.Frontend.TerminalReturnTreeRunnerProperties
import Solcore.Frontend.TerminalReturnTreeFuelBoundProperties
import Solcore.Frontend.TerminalReturnTreeResumptionProperties
import Solcore.Frontend.TerminalReturnTreeRunnerEmbeddingProperties
import Solcore.Frontend.TerminalReturnTreeRenamingProperties
import Solcore.Frontend.TerminalReturnTreeStoreProperties
import Solcore.Frontend.TypedLetReturnBody
import Solcore.Frontend.TypedLetReturnBodyElaboration
import Solcore.Frontend.TypedLetReturnBodyProperties
import Solcore.Frontend.TypedLetReturnBodyEmbeddingProperties
import Solcore.Frontend.TypedLetReturnBodyEvaluation
import Solcore.Frontend.TypedLetReturnBodyEvaluationProperties
import Solcore.Frontend.TypedLetReturnBodyExecutionProperties
import Solcore.Frontend.TypedLetReturnBodyEvaluationEmbeddingProperties
import Solcore.Frontend.TypedLetReturnBodyRunner
import Solcore.Frontend.TypedLetReturnBodyRunnerProperties
import Solcore.Frontend.TypedLetReturnBodyFuelBoundProperties
import Solcore.Frontend.TypedLetReturnBodyResumptionProperties
import Solcore.Frontend.TypedLetReturnBodyRunnerEmbeddingProperties
import Solcore.Frontend.TypedLetReturnBodyStoreProperties
import Solcore.Frontend.LocalTypeInputsOwnerProperties
import Solcore.Frontend.TypedLetReturnBodyOwnerProperties
import Solcore.Frontend.TypedLetReturnBodyRunnerOwnerProperties
import Solcore.Frontend.TypedLetReturnBodyTypeExtensionProperties
import Solcore.Frontend.TypedLetReturnBodyRunnerTypeExtensionProperties
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.TypedLetReturnTreeElaboration
import Solcore.Frontend.TypedLetReturnTreeProperties
import Solcore.Frontend.TypedLetReturnTreeEmbeddingProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluation
import Solcore.Frontend.TypedLetReturnTreeEvaluationProperties
import Solcore.Frontend.TypedLetReturnTreeExecutionProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluationEmbeddingProperties
import Solcore.Frontend.TypedLetReturnTreeRunner
import Solcore.Frontend.TypedLetReturnTreeRunnerProperties
import Solcore.Frontend.TypedLetReturnTreeFuelBoundProperties
import Solcore.Frontend.TypedLetReturnTreeResumptionProperties
import Solcore.Frontend.TypedLetReturnTreeRunnerEmbeddingProperties
import Solcore.Frontend.TypedLetReturnTreeStoreProperties
import Solcore.Frontend.TypedLetReturnTreeOwnerProperties
import Solcore.Frontend.TypedLetReturnTreeRunnerOwnerProperties
import Solcore.Frontend.TypedLetReturnTreeTypeExtensionProperties
import Solcore.Frontend.TypedLetReturnTreeRunnerTypeExtensionProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluator
import Solcore.Frontend.TypedLetReturnTreeEvaluatorCorrespondence
import Solcore.Frontend.TypedLetReturnTreeEvaluatorProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluatorExecutionProperties
import Solcore.Frontend.TypedLetReturnTreeRawOwnerProperties
import Solcore.Frontend.LocalExpressionLookupProperties
import Solcore.Frontend.TypedLetReturnTreeLookupProperties

/-!
Canonical explicit-table frontend adapters for local expressions, type names,
type-only and runtime parameter inputs, singleton and terminal-conditional return bodies,
and restricted explicit
function entries with value-free compilation. A structural type adapter interprets
named leaves and arbitrary finite tuple types as Unit, singleton identity or
right-associated products with independent meaning and table-extension proofs.
Explicit nested children are not flattened. Single return, parameter and recursive let
annotations use it at the existing entry; each parameter retains exactly one
original argument and position. Older prefix let annotations remain named-only,
and empty/multiple return clauses remain outside the entry profile.

A separate static root-application adapter specializes a known Function type
with exactly one original argument. Both children use the old pure local
grammar and caller scope; independent typing and exact provenance yield their
ordered Core application. Unit/products are single arguments, not argument-list
packing. This adds no call evaluator or entry integration and does not inherit
the local fragment's store-preservation or source-only fuel guarantees.

Independent call evaluation now retains the actual closure body and captures,
ordered original pure children, and all store endpoints. Its exact cost includes
the actual body path plus three application transitions, uniformly under every
continuation. Aligned runtime IDs connect it bidirectionally to the original
Core application without inferring runtime typing, allocated cells, termination,
or execution of pending continuation frames. Whole entries remain unchanged.

Explicit runtime-world and store typing now give original-call result type
preservation and successful actual costs. A typed outer continuation also gives
fault exclusion at every fuel and typing/safety of genuine saved checkpoints.
These premises cover actual captures and allocated cells, not merely structural
value types; they imply neither an unchanged store nor a source-only bound.

Independent source rules
connect to checked Core execution. A direct original-expression evaluator
accepts empty canonical tuples as Unit and arbitrary finite lists of two or more
elements as right-associated products, using original child scopes and actual
values without an implicit Unit tail. Explicit nesting and existing grouping/trailing
commas need no parser change; manual singleton tuple nodes and projections remain
outside this expression adapter. The evaluator
returns exactly the independent raw value and transition cost without checking
or Core execution; whole checking and actual ID alignment separately connect
successful output to checked Core paths and fuel thresholds. Raw selected success
is not whole acceptance. A direct recursive-body evaluator composes these raw
expression results with strict old-scope initialization, actual fresh tails and
selected arms. Its exact raw correspondence and checked bridges preserve the
same acceptance, identity and continuation boundaries. Globally injective owner-only
relabeling additionally preserves complete direct results and raw value/cost paths
for arbitrary caller rows, without whole checking, alignment or runtime typing.
More generally, equal composed actual-value lookups preserve full expression and
recursive results and raw paths even with different owners and independently
allocated fresh IDs; internal layouts and Core checkpoints need not be equal.
General source-program resolution, parser
changes, and wire publication are not implied. A direct checked entry retains
the existing preparation gate and original actual parameter bundle; its result
exactly matches independent entry cost, and absence is exactly preparation
failure. Static preparation still lowers; result computation does not run Core.
Function entries support finite
alternation of typed lets and terminal if/else trees inside either arm; compilation owner
invariance requires no runtime argument inhabitants.
Recursive terminal return trees additionally have independent static and
selected-path evaluation/cost semantics with exact Core continuation paths,
a checked body runner, recursive fuel bounds and genuine-state resumption.
Injective identity relabeling retains full results; store replay retains value,
cost and observation thresholds with each result's own store. Existing function
entries reuse these recursive contracts with unchanged headers and parameters.
Typed, initialized, non-shadowing local-declaration prefixes have a separate
value-free static adapter with exact nested Core letE. Independent raw evaluation
and cost correspond to the actual checked Core and exact continuation paths.
A separate checked body runner adds exact fuel thresholds, a source-only bound
and genuine-state resumption. Store replay preserves values and costs, with
each completed or suspended observation retaining its own store. Injective
owner-only relabeling commutes with fresh binding and preserves exact Core,
whole optional results and checkpoints at a fixed store. First-match type-meaning
extension preserves success, and mutual extension also preserves rejection.
Older prefix successes retain their exact Core and complete runner results.
A separate recursive static
adapter admits initialized, nonshadowing lets inside either arm, with a written
structural annotation or the independently inferred initializer type,
with exact ordered Core, independent typing and success-only old embeddings.
Sibling scopes start from the same inputs and may reuse the same fresh ID.
Independent recursive evaluation and cost now retain strict old-scope
initialization and only selected arms, with exact checked Core paths under
arbitrary retained continuations. Raw paths do not imply whole checking;
typed existence separately requires actual aligned, typed environments.
A separate recursive body runner supplies exact fuel thresholds, a source-only
additive/max-arm upper bound and complete genuine-checkpoint resumption. Old
runner successes retain their full results; singleton shapes retain rejection
as well. Arbitrary-store raw replay preserves values and exact costs; completed
observations and exhaustion presence keep their own stores, not identical full
results or checkpoints. Pending Core frames receive no store-independence law.
Globally injective owner-only relabeling preserves independent static provenance,
full checker rejection and same-store complete runner results, without changing
indices, source, positional values or scope-local sibling allocation.
First-match type-name extension retains successful exact checker and full runner
pairs with fixed inputs; mutual extension retains whole Options. One-way extension
can repair unknown annotations, and conflicting first-match overrides are not
semantic extensions.
The actual parameter binder and whole-entry preparation now retain their full
value-bearing records under the same meaning preservation. Initial rows,
generated IDs and caller-supplied values remain unchanged, not merely their
compiled projection. Successful whole run results preserve all machine states
at the same fuel and store; mutual extension also preserves rejection. These
laws require the same actual arguments and do not invent nominal inhabitants.
Existing function entries reuse these recursive judgments and additive/max-arm
bound, retaining original parameter-only records, header/argument guards and
direct Core execution. Actual branch-local work contributes no wrapper overhead.
Unannotated initializers keep their original syntax and scope; inference changes
neither strict evaluation nor the two existing let transitions. Old annotated
binding rules and generic proof contracts remain intact. Older body-only adapters
and bounds remain unchanged. No general inference, default initialization,
general calls or broader binding policy is added.

Semicolon-terminated expression prefixes now execute strictly before their
original tail, without adding a source name, identity or parameter row. Exact
Core uses a let whose tail is positionally weakened under the hidden binder;
typing, raw evaluation and exact costs reuse local-fragment insertion/reflection.
Four independent discard rules retain all earlier constructors and generic
contracts. Costs add head plus tail plus two even when the head is unused.
Unterminated expressions, missing terminal tails and general early returns are
not introduced, and narrower body-only adapters keep their original boundaries.

Singleton terminal lexical blocks now preserve the inner statement list and
its original braces' span, checking it in the same input scope. Four independent
block rules retain exactly the child's Core, type, runtime value, stores and
cost. There is no extra Core binder or transition. All earlier generic
contracts remain intact, and a full-Option equality preserves both acceptance
and rejection of the inner body. Empty or nonterminal blocks, scope escape,
implicit returns and general early-return semantics are not introduced.

Exact expression, singleton-return, terminal-tree and recursive-let provenance
now expose membership in the independent local Core fragment. Compilation and
preparation project the same structural fact without restricting actual opaque
values. Existing insertion laws then preserve typing, values and exact path
lengths; original and inserted checkpoint payloads need not be equal. Membership
alone is neither source provenance nor typing or execution of arbitrary records.
-/
