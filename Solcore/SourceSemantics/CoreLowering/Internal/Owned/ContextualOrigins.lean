import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadFaultPolicies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedStageOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectApplication
import Solcore.SourceSemantics.CoreLowering.ReachedLoweredReadOutcomePorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes

/-!
# Owned callables: contextual origins

Policy profiles, formation receipts, cell origins, callee receipts and function views of contextual callables.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles
/-! The original contextual bind retains one policy for all child budgets.
Pointwise metadata ports preserve that root callback and its minimum budget. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedOwnedIndirectCompilerReceipts
open CallableIndexedOwnedIndirectCompilerPolicyInputs

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Profiles belong to the literal selected root policy, rather than an
arbitrary policy whose lowered output happens to agree. -/
structure RootPolicyReceipt (named : Named)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  selected : ContextualPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    fuel source scope id reasonAt lowered
  sourceCells : selected.policy.sourceCells = some (allocator compiled.indexed named)
  rawLambdaBody : selected.policy.rawLambdaBody = SourceCoreLambdaTemplates.hook
    compiled.indexed.ancestry.templates named.signature.key []
  rawLambdaExpression : selected.policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook
    compiled.indexed.ancestry named.signature.key []
  projectType : selected.policy.projectType = SourceCoreCompatibleDataExpressions.projectType compiled.compatible.checked
  compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation fuel selected.policy

/-- Unwrap the actual outer bind once and construct the selected receipt and
all its profiles together. No child contextual acceptance is selected. -/
theorem RootPolicyReceipt.of_accepted
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) source scope id reasonAt = .ok lowered) :
    Nonempty (RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
      fuel source scope id reasonAt lowered) := by
  rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  dsimp only at accepted
  change (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key
    |>.mapError SourceCoreBasic.Error.callPreparation) >>= _ = .ok lowered at accepted
  rw [record] at accepted
  simp only [Except.mapError, bind, Except.bind] at accepted
  exact ⟨⟨⟨_, _, accepted, rfl, rfl, _, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, by funext lambda; simp⟩⟩⟩

section Pointwise
variable
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
      rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- Both fields apply at the actual child occurrence while rootFuel remains
inside the original selected callback. -/
structure PointwiseFor (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) : Prop where
  read : root.selected.policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id
  special : ∀ child budget, (match root.selected.policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower (context compiled.indexed named) child budget source scope id reasonAt) = .ok none

/-- The actual graph selection supplies the callable convention. -/
theorem RootPolicyReceipt.callables :
    root.selected.policy.callables = SourceCoreGeneralFunctions.callablePolicy
      (some compiled.indexed.ancestry.graph.inputs.callable) [] := by
  rw [root.selected.callables]
  rw [compiled.indexed.ancestry.graph.inputs.callableSelected]

private theorem evidence_none_lambda
    (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (current : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    {source : TypedSource} (scope : SourceCoreLocalCell.Scope)
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId}
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller current child budget
      source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions]

/-- Genuine lambda metadata excludes only this node's original override gates. -/
theorem lambda_policy
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none) :
    PointwiseFor root source scope id reasonAt := by
  have sameSource : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed named).plan compiled.indexed.base.locals
      (context compiled.indexed named).owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  constructor
  · rw [root.selected.readExpression]
    simp only [sameSource, bind, Except.bind]
    rw [representation_read]
  · intro child budget
    rw [root.selected.special_eq, root.selected.special_body]
    have noEvidence := evidence_none_lambda compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized (context compiled.indexed named) child budget scope reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
      found form requirements coercions
    simp only [sameSource, bind, Except.bind, found, pure, Except.pure, ordinary,
      Option.filter_none, noEvidence, form]

/-- Empty raw argument coercions and initializer absence remain independent
conditions at the actual indirect child. -/
theorem indirect_policy
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (arguments : metadata.argumentCoercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none) :
    PointwiseFor root source scope id reasonAt := by
  have sameSource := contextualSource_indirect compiled.indexed.base.sourceProgram
    (context compiled.indexed named).plan compiled.indexed.base.locals
    (context compiled.indexed named).owner none found form
  constructor
  · rw [root.selected.readExpression]
    simp only [sameSource, bind, Except.bind]
    rw [representation_read]
  · intro child budget
    rw [root.selected.special_eq, root.selected.special_body]
    have noEvidence := evidence_none_indirect compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized (context compiled.indexed named) child budget scope reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
      found form requirements coercions arguments
    simp only [sameSource, bind, Except.bind, found, pure, Except.pure, ordinary,
      Option.filter_none, noEvidence, form]

end Pointwise
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts
/-! Formation retains the actual chosen Site rather than a later code-shaped
replacement. Binder policy comes from the original contextual producer; full
Syntax and the production recipe are retained at that same body context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedOwnedContextualLambdaProvenance

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The original ordinary formation with its same-Site static facets. -/
structure OrdinaryFormation
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    extends CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads.Formation
      (registry := registry) (faults := faults) caller context evidence scope id lowered where
  callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller context evidence
  binderPolicy : BinderPolicy caller.named site.code
  recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained caller.named site.code
  compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained caller.named site.code
  issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained caller.named site.code
  bodyView : BodyView site.code
  bodyReasons : BodyReasons site.code caller.named
  declarations : CompatibleExpressionReads.ScopeDeclarations
    (CallableIndexedNamedGeneration.source caller.named) scope context
  syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source caller.named)
    (expressionSyntax (CallableIndexedNamedGeneration.source caller.named)) body.context
    (.statements true statements) result

/-- The principal formation already retained its full Syntax. -/
structure PrincipalFormation {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    extends CallableIndexedOwnedMethodLambdaExpressionHeads.Formation
      (registry := registry) (faults := faults) principal context scope id lowered where
  binderPolicy : BinderPolicy principal.named site.code
  recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained principal.named site.code
  compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained principal.named site.code
  issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained principal.named site.code
  bodyView : BodyView site.code

theorem OrdinaryFormation.at
    {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : OrdinaryFormation (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (environment : Dynamic.Environment)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    OrdinaryAt (receipt.toFormation.code environment) (receipt.toFormation.support environment) :=
  .recaptured caller receipt.site receipt.expressionSyntax receipt.certificates receipt.body
    receipt.binderPolicy receipt.recipe receipt.compilerPolicy receipt.issuedRecipe receipt.bodyView receipt.bodyReasons receipt.declarations receipt.syntaxTree environment globals receipt.callerReceipt

theorem PrincipalFormation.at {method : ExecutableImplMethods.CheckedMethod}
    {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : PrincipalFormation (registry := registry) (faults := faults) principal context scope id lowered)
    (environment : Dynamic.Environment) :
    PrincipalAt (receipt.toFormation.code environment) (receipt.toFormation.support environment) :=
  .recaptured principal receipt.site receipt.expressionSyntax receipt.certificates receipt.body
    receipt.binderPolicy receipt.recipe receipt.compilerPolicy receipt.issuedRecipe receipt.bodyView receipt.syntaxTree environment

/-- Actual producer selection and independently accepted same-Site body
receipts construct the ordinary certificate without choosing another head. -/
def ordinary_of_producer
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : CallableIndexedOwnedContextualLambdaProducerReceipts.Produced caller.named parameters result
      statements context evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
      expressionSyntax certificates produced.site.code (Program.ofChecked compiled.sourceProgram) registry faults)
    (bodyView : BodyView produced.site.code)
    (bodyReasons : BodyReasons produced.site.code caller.named)
    (declarations : CompatibleExpressionReads.ScopeDeclarations
      (CallableIndexedNamedGeneration.source caller.named) scope context)
    (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source caller.named)
      (expressionSyntax (CallableIndexedNamedGeneration.source caller.named)) body.context
      (.statements true statements) result)
    (sourceType : produced.site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence []))
    (ordinary : Dynamic.OrdinaryRequirementLayout produced.site.code.sourceNode.requirements produced.site.code.sourceNode.coercions [])
    (coercions : produced.site.code.sourceNode.coercions = [])
    (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller context evidence) :
    OrdinaryFormation (registry := registry) (faults := faults) caller context evidence scope id lowered where
  parameters := parameters
  result := result
  statements := statements
  site := produced.site
  expressionSyntax := expressionSyntax
  certificates := certificates
  body := body
  identifier := produced.identifier
  emitted := produced.emitted
  sourceType := sourceType
  ordinary := ordinary
  coercions := coercions
  callerReceipt := callerReceipt
  binderPolicy := produced.binderPolicy
  recipe := produced.recipe
  compilerPolicy := produced.compilerPolicy
  issuedRecipe := produced.issuedRecipe
  bodyView := bodyView
  bodyReasons := bodyReasons
  declarations := declarations
  syntaxTree := syntaxTree

/-- The principal certificate keeps its own Source dictionary and exact
producer seed, with independent full Syntax at that same body context. -/
def principal_of_producer {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : CallableIndexedOwnedContextualLambdaProducerReceipts.Produced principal.named parameters result
      statements context principal.dictionary scope (CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal) id lowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
      expressionSyntax certificates produced.site.code (Program.ofChecked compiled.sourceProgram) registry faults)
    (bodyView : BodyView produced.site.code)
    (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source principal.named)
      (expressionSyntax (CallableIndexedNamedGeneration.source principal.named)) body.context
      (.statements true statements) result)
    (sourceType : produced.site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure principal.named parameters result statements context principal.dictionary []))
    (ordinary : Dynamic.OrdinaryRequirementLayout produced.site.code.sourceNode.requirements produced.site.code.sourceNode.coercions [])
    (coercions : produced.site.code.sourceNode.coercions = []) :
    PrincipalFormation (registry := registry) (faults := faults) principal context scope id lowered where
  parameters := parameters
  result := result
  statements := statements
  site := produced.site
  expressionSyntax := expressionSyntax
  certificates := certificates
  body := body
  identifier := produced.identifier
  emitted := produced.emitted
  sourceType := sourceType
  ordinary := ordinary
  coercions := coercions
  binderPolicy := produced.binderPolicy
  recipe := produced.recipe
  compilerPolicy := produced.compilerPolicy
  issuedRecipe := produced.issuedRecipe
  bodyView := bodyView
  syntaxTree := syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualInitializedClosureReceipts
/-! Positive contextual ordinary members follow one actual initialized allocation
and one initialized local read. The original accepted Selection supplies the
same code's escaped-control row. Source typing comes from the real judgment
and deep input heap; the actual current state and full member stay associated. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualInitializedClosureReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedContextualStoredClosureAssociationReceipts (Member)
open CallableIndexedAllocationCompletion TypedLexicalControl
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Real Source typing fixes the reported type of the exact stored occurrence. -/
theorem reported_type_at {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) : node.type = type := by
  obtain ⟨original, contains, sameType⟩ := typed.stored_type
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases same
  exact sameType

/-- This static list induction only identifies the actual reported type row.
It carries no child evaluation, body law or mutual semantic induction. -/
theorem source_types_at_tree {source : TypedSource} {context : SourceSemantics.Context}
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {ids : List ExpressionId} {types reported : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (tree : DataExpressionSequence.Tree source certificate scope ids reported codes)
    (typed : ExpressionsHaveTypes source context ids types) : types = reported := by
  induction tree generalizing types with
  | nil => cases typed; rfl
  | single found _ =>
    cases typed with
    | cons head tail =>
      cases tail
      exact congrArg (fun type => [type]) (reported_type_at unique found head).symm
  | cons found _ _ ih =>
    cases typed with
    | cons head tail =>
      exact congr (congrArg List.cons (reported_type_at unique found head).symm) (ih tail)

section Selection
variable {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (formation : CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
    (registry := registry) (faults := faults) caller context evidence scope id lowered)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {parentScope : SourceCoreLocalCell.Scope}
  {parentId callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {parentLowered : SourceCoreBasic.LoweredExpr}
  {certificate : GenericExpressionMeaning.Certificate}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source parentScope
    parentId callee ids metadata reasonAt parentLowered)
  {nativeContext : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler nativeContext)
  (selected : CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
    (certificate := certificate) compiler prepared formation.site.code)

include selected in
/-- Recapture changes the Source capture environment only. The authentic
accepted call's fault row belongs to exactly this retained compiler context. -/
theorem escaped_at_formation (environment : Dynamic.Environment) :
    faults .controlEscapedFunction (formation.toFormation.code environment).compilation.internalReason :=
  selected.escaped

include selected in
/-- Ordered argument counts and native packing are consequences of this
original Selection and compiler vector, before any argument execution. -/
theorem selected_argument_shape :
    ids.length = formation.site.code.receipt.loweredParameters.length ∧
    SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (formation.site.code.receipt.loweredParameters.map Prod.snd) := by
  have counts := congrArg List.length selected.nativeTypes
  simp only [List.length_map] at counts
  exact ⟨compiler.ordered_children.1.trans counts,
    congrArg SourceCoreCompatibleCatalog.packTypes selected.nativeTypes⟩

include selected in
/-- Every accepted static call facet is retained at the same recaptured code.
Only the Source capture environment changes; no codebook or policy is selected. -/
theorem selection_at_formation (environment : Dynamic.Environment) :
    CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
      (certificate := certificate) compiler prepared (formation.toFormation.code environment) :=
  ⟨selected.children, selected.nativeTypes, selected.escaped, selected.rawResult,
    selected.nativeResult, selected.stageAccepted, selected.arityAccepted⟩

include selected in
/-- The raw argument bundle uses the original Source typing row, independently
of native projection. Lookup uniqueness aligns it with the accepted child Tree. -/
theorem selected_source_bundle {argumentContext : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source argumentContext ids types) :
    TypeSystem.Ty.productMany types = TypeSystem.Ty.productMany
      (formation.site.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) :=
  congrArg TypeSystem.Ty.productMany (source_types_at_tree unique selected.children typed)
end Selection

variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Core.Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- The initialized cell carries a positive member as an additional receipt.
The Source location and native target are the original allocation/read witnesses. -/
def StoredAt
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (location : Dynamic.Location) (function : Dynamic.Closure) (native : Core.Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameterCore resultCore : Ty) : Prop :=
  Member headers keys registry faults mapping world function native bindings parameterCore resultCore ∧
  ∃ target, ReferenceRepresents mapping world location target (CallableContract.functionType parameterCore resultCore) ∧
    Dynamic.Heap.Reads heap location ⟨FunctionValues.sourceType function, some (.closure function), none⟩ ∧
    store.read? target = some (.inRight .unit native)

theorem payload_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) :=
  .function member.represents

/-- Mutation or extension never manufactures a live stored value. Both actual
future reads are required alongside genuine map/world growth. -/
theorem StoredAt.extend_with_reads
    {heap futureHeap : Dynamic.Heap} {store futureStore : Store} {location : Dynamic.Location}
    (stored : StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (read : Dynamic.Heap.Reads futureHeap location ⟨FunctionValues.sourceType function, some (.closure function), none⟩)
    (nativeReads : ∀ target, ReferenceRepresents mapping world location target (CallableContract.functionType parameterCore resultCore) →
      futureStore.read? target = some (.inRight .unit native)) :
    StoredAt headers keys registry faults futureMapping futureWorld futureHeap futureStore location function native bindings parameterCore resultCore := by
  obtain ⟨member, target, reference, _, _⟩ := stored
  exact ⟨member.extend maps worlds, target, reference.extend maps worlds, read, nativeReads target reference⟩

section FormationMember
variable {scope : SourceCoreLocalCell.Scope} {actual canonical : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {parentScope : SourceCoreLocalCell.Scope}
  {parentId callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {certificate : GenericExpressionMeaning.Certificate}
  (compiler : CallableIndirectCallCertificates.Receipt policy lowerBody fuel compilation source parentScope
    parentId callee ids metadata reasonAt lowered)
  {nativeContext : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler nativeContext)
  (selected : CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
    (certificate := certificate) compiler prepared code)

open CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation (history_at source_origin reference_index)

include profile prefixContext observed provenance inclusion selected in
/-- One original contextual formation retains its complete traces and
represented value, plus the same positive member for later initialized reads.
The escaped row is supplied by the actual accepted compiler selection. The
member is the formed closure over the copies of its captured cells. -/
theorem formation_member_from_selection
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      Member headers keys registry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  exact CallableIndexedOwnedContextualStoredClosureAssociationReceipts.formation_member
    (captured := captured) (code := code) (support := support) (owner := owner)
    (initial := initial) (packet := packet) (profile := profile) (prefixContext := prefixContext)
    (observed := observed) (provenance := provenance) (functions := functions)
    (inclusion := inclusion) (escaped := selected.escaped) heaps copied ordinary coercions

end FormationMember

section Allocation
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}

local notation "receiving" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile

/-- The positive constructor supplies the payload relation, and the original
stateful producer runs once. Every output belongs to its same allocation tuple. -/
theorem allocate_initialized
    (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry receiving))
    {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    (binderType : binder.scheme.body = FunctionValues.sourceType function)
    (payloadType : payload = CallableContract.functionType parameterCore resultCore)
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {nativeFrame : NativeFrame} {location : Dynamic.Location}
    (valueTyped : Dynamic.ValueHasType context before (.closure function) binder.scheme.body)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry receiving mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame nativeFrame))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some (.closure function)) location after)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation nativeFrame)
    (admitted : Admission bridge context initial) :
    ∃ captured,
      Captures (native :: canonical)
        (initializedRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope)
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      let closureValue := native
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame nativeFrame,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit closureValue]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (closureValue :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical)
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry receiving nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: closureValue :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: closureValue :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext)
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame nativeFrame) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ∃ (_maps : LocationMap.Extends mapping nextMap) (_worlds : WorldExtends world nextWorld),
        Dynamic.HeapMetadataExtend before after ∧
        ReferenceRepresents nextMap nextWorld location (store.length + 2) payload ∧
        StoredAt headers keys registry faults nextMap nextWorld after nextStore location function native bindings parameterCore resultCore ∧
        ∃ reached : callerProtocol.State
            ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
          callerProtocol.Relates initial reached ∧
          Relates (bridge.pool initial) (bridge.pool reached) ∧
          Admission bridge nextContext reached := by
  have represented : ValueRep compiled.compatible.checked registry receiving mapping world
      binder.scheme.body (.closure function)
      native payload := by
    rw [binderType, payloadType]
    exact payload_member profile member
  obtain ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related, nextAdmission⟩ :=
    CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge receiving definitions registered
      producer.toOrdinary mono extended ordinary allocation annotation same valueTyped represented
      environments heaps locals agrees actualTyped reference read allocated initial ready admitted
  have maps : LocationMap.Extends mapping (mapping ++ [store.length + 2]) := ⟨_, rfl⟩
  have worlds : WorldExtends world
      (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) := ⟨_, rfl⟩
  have freshReference : ReferenceRepresents (mapping ++ [store.length + 2])
      (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload])
      location (store.length + 2) payload := by
    refine ⟨?_, ?_⟩
    · rw [allocated.location_fresh, ← heaps.length_eq]
      simp
    · cases nextTyped with
      | cons typed _ =>
        cases typed with
        | cellRef found => exact found
  have stored : StoredAt headers keys registry faults (mapping ++ [store.length + 2])
      (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) after
      (store ++ [SourceCoreCallableIndexedFrames.encode frame nativeFrame,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
        .inRight .unit native]) location function native bindings parameterCore resultCore := by
    refine ⟨member.extend maps worlds, store.length + 2,
      payloadType ▸ freshReference, ?_, ?_⟩
    · change after.Reads location ⟨FunctionValues.sourceType function, some (.closure function), none⟩
      simpa only [binderType] using allocated.reads_new
    · simp [Store.read?] <;> rfl
  exact ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps,
    nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation,
    maps, worlds, .of_allocation allocated, freshReference, stored,
    reached, related, bridge.related related, nextAdmission⟩

end Allocation

section Read
open CompatibleExpressionReads
variable {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {code : Expr}
  (certificate : Certificate fuel (.initial compiled.compatible.checked) source scope id reason code)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {location : Dynamic.Location}

/-- The real binder and initialized cell exclude the reached empty witness. -/
theorem initialized_policy
    (stored : StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    UninitializedPolicy certificate context environment heap faults := by
  intro other cell witness
  have same := witness.lookup.functional lookup
  subst other
  obtain ⟨_, target, reference, read, nativeRead⟩ := stored
  have same := witness.read.functional read
  subst cell
  cases witness.empty

/-- Genuine lexical and stored receipts construct the exact initialized
Source/native read; no heap-relation inverse supplies the qualified member. -/
theorem initialized_traces
    (binding : StaticBinding certificate context)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    (CallableContract.functionType parameterCore resultCore) = certificate.type ∧
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence source environment heap
      id (.closure function) heap ∧
    Evaluates actual store (code.rename ξ) (.inRight .word native) store := by
  rcases certificate with ⟨node, readType, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
  dsimp only at *
  obtain ⟨_member, target, reference, read, nativeRead⟩ := stored
  obtain ⟨other, cell, otherLookup, otherRead, cellType, _⟩ := locals.lookup binding.declared
  have same := otherLookup.functional lookup
  subst other
  have same := otherRead.functional read
  subst cell
  have nominal : FunctionValues.sourceType function = declared.scheme.body := cellType
  have notMapping : ¬ ∃ key value, declared.scheme.body = .mapping key value := by
    intro ⟨key, value, mapped⟩
    have mapped : FunctionValues.sourceType function = .mapping key value := nominal.trans mapped
    cases mapped
  obtain ⟨selectedTarget, nativeLookup, selectedReference⟩ := environments.lookup_visible lookup slot
  have same : selectedTarget = target := Option.some.inj (selectedReference.mapped.symm.trans reference.mapped)
  subst selectedTarget
  have sameType : CallableContract.functionType parameterCore resultCore = readType := by
    exact (Ty.sum.inj (Option.some.inj (reference.typed.symm.trans selectedReference.typed))).2
  have sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
      source environment heap id (.closure function) heap := by
    have formTrace : Dynamic.ExpressionFormEvaluates (Program.ofChecked compiled.sourceProgram) context evidence
        source environment heap node.form [] [] (.closure function) heap :=
      form ▸ Dynamic.ExpressionFormEvaluates.local (coercions := []) rfl lookup read rfl rfl
    exact .intro (lookupExpression?_sound metadata.found)
      (by rw [metadata.requirements, metadata.coercions]; exact formTrace)
      (by rw [metadata.coercions]; exact .nil)
  refine ⟨sameType, sourceTrace, ?_⟩
  cases emitted with
  | ordinary _ =>
    change Evaluates actual store (OptionalCell.read readType (.var (ξ index)) reason)
      (.inRight .word native) store
    exact OptionalCell.read_success reason (.var (agrees nativeLookup)) nativeRead
  | mapping declared _ => exact False.elim (notMapping ⟨_, _, declared⟩)

/-- One original read producer retains its broad result, heap/frame/metadata
and the same initialized qualifier. Its empty-cell policy is derived above. -/
theorem read_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compiled.sourceProgram) context evidence
      source environment heap id (.value (.closure function)) heap ∧
    Evaluates actual store (code.rename ξ) (.inRight .word native) store ∧
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile))
      mapping world certificate.node.type certificate.type faults (.value (.closure function)) (.inRight .word native) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world heap store ∧
    AdministrativePreserved mapping store mapping store ∧ Dynamic.HeapMetadataExtend heap heap ∧
    StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore := by
  obtain ⟨_, sourceTrace, nativeTrace⟩ := initialized_traces certificate binding environments locals agrees stored lookup
  obtain ⟨outcome, after, result, finalStore, actualSource, actualNative, related, finalHeaps, frame, metadata⟩ :=
    certificate.evaluates_with_diagnostics
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      extension (Program.ofChecked compiled.sourceProgram) context evidence binding environments heaps locals agrees
      (initialized_policy certificate stored lookup)
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic actualNative nativeTrace
  subst result
  subst finalStore
  obtain ⟨sameOutcome, sameHeap⟩ := source_outcome_unique unique
    (lookupExpression?_sound certificate.metadata.found) certificate.form certificate.metadata.coercions
    lookup stored.2.choose_spec.2.1 rfl actualSource (.value sourceTrace)
  subst outcome
  subst after
  exact ⟨actualSource, actualNative, related, finalHeaps, frame, metadata, stored⟩

section Parent
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {childFuel : Nat}
  {parentCompilation : SourceCoreFunctions.Context} {parentId : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body childFuel parentCompilation source scope parentId id ids metadata reasonAt lowered)
  {calleeNode : ExpressionNode}
  (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile) mapping world heap store)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (stored : StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore)
  (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)

include evidence unique locals stored lookup in
/-- Raw success typing comes from the actual Source judgment and typed input
heap. Neither a native type nor erased function representation supplies it. -/
theorem source_value_typed
    (typed : ExpressionHasType source context id certificate.node.type)
    (heapTyped : Dynamic.HeapWellTyped context heap) :
    Dynamic.ValueHasType context heap (.closure function) certificate.node.type := by
  generalize reportedEq : certificate.node.type = reported at typed
  cases typed with
  | @intro _ _ node raw plan contains formTyped rawEq _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans certificate.metadata.found)
    subst node
    have path := requirements.outputPath
    rw [certificate.metadata.coercions] at path
    cases path
    rw [certificate.form] at formTyped
    have formTrace : Dynamic.ExpressionFormEvaluates (Program.ofChecked compiled.sourceProgram)
        context evidence source environment heap
        (.reference certificate.name (.local certificate.binder)) [] [] (.closure function) heap :=
      Dynamic.ExpressionFormEvaluates.local (coercions := []) rfl lookup stored.2.choose_spec.2.1 rfl rfl
    exact (Dynamic.ExpressionFormEvaluates.referencePreserves locals heapTyped formTyped formTrace).1

include evidence unique locals stored lookup in
/-- The initialized read's admission belongs to the identical input state,
heap and row pool, independently of the eventual argument/application suffix. -/
theorem post_admission
    (typed : ExpressionHasType source context id certificate.node.type)
    (admitted : Admission bridge context initial) :
    PostAdmission bridge context certificate.node.type (.value (.closure function)) initial := by
  refine ⟨admitted.rows, ?_⟩
  intro result same
  cases same
  exact ⟨source_value_typed (evidence := evidence) (certificate := certificate) (unique := unique)
      (locals := locals) (stored := stored) (lookup := lookup) typed admitted.heap,
    admitted.heap⟩

include extension binding unique environments heaps locals agrees stored lookup in
/-- One original accepted read produces the same callee Source trace, genuine
ValuePost and positive invocation Association. Source/native grades stay distinct. -/
theorem callee_post
    (sameCode : compiler.calleeCode.expression = code)
    (sameNode : calleeNode = certificate.node) (sameType : compiler.calleeCode.type = certificate.type)
    (sourceTyped : ExpressionHasType source context id certificate.node.type)
    (admitted : Admission bridge context initial) :
    ∃ sourceSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment heap id (.closure function) heap ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
        compiler initial (.closure function) heap native store mapping world ∧
      CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
        function native bindings parameterCore resultCore ∧
      CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world
        (FunctionValues.sourceType function) (.closure function) native
        (CallableContract.functionType parameterCore resultCore) ∧
      StoredAt headers keys registry faults mapping world heap store location function native bindings parameterCore resultCore := by
  obtain ⟨sourceTrace, nativeTrace, represented, finalHeaps, frame, metadata, retained⟩ :=
    read_member certificate profile extension binding unique environments heaps locals agrees stored lookup
  have payload : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile)
      mapping world certificate.node.type (.closure function) native certificate.type := by
    cases represented with
    | value related => exact related
  have admittedPost := post_admission (evidence := evidence) (certificate := certificate)
    (bridge := bridge) (initial := initial) (unique := unique) (locals := locals)
    (stored := stored) (lookup := lookup) sourceTyped admitted
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size sourceTrace
  cases sized with
  | value sized =>
    refine ⟨sourceSize, sized, ?_, stored.1.association, stored.1.selection, retained⟩
    unfold CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost
    rw [sameCode, sameNode, sameType]
    exact ⟨nativeTrace, payload, finalHeaps, ⟨[], by simp⟩, ⟨[], by simp⟩,
      frame, metadata, initial, callerProtocol.refl initial, admittedPost⟩
end Parent
end Read
/-- A diagnostic-free stored receipt keeps the same physical source/native
cell witnesses and the contextual typed member. It does not recover a legacy
diagnostic from an erased payload or from native type information. -/
def TypedStoredAt
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (location : Dynamic.Location) (function : Dynamic.Closure) (native : Core.Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameterCore resultCore : Ty) : Prop :=
  CallableIndexedOwnedContextualTypedClosureReceipts.StaticMember
    headers keys registry faults mapping world function native bindings parameterCore resultCore ∧
  ∃ target, ReferenceRepresents mapping world location target (CallableContract.functionType parameterCore resultCore) ∧
    Dynamic.Heap.Reads heap location ⟨FunctionValues.sourceType function, some (.closure function), none⟩ ∧
    store.read? target = some (.inRight .unit native)

/-- A genuine legacy member projects forward; its physical cell and read
witnesses remain exactly those supplied by the original stored receipt. -/
theorem StoredAt.to_static {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    (stored : StoredAt headers keys registry faults mapping world heap store
      location function native bindings parameterCore resultCore) :
    TypedStoredAt headers keys registry faults mapping world heap store
      location function native bindings parameterCore resultCore :=
  ⟨stored.1.to_static, stored.2⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualInitializedClosureReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
/-! Proof-only prototype for positive contextual closure leaves in ordinary
optional cells. The existing mutually recursive payload relation retains
products, nominal constructor fields, ordered mapping entries and defaults.
Actual allocation and writes update that relation at the same heap/store.
Formation keeps its original receiving model; its positive static member is attached
forward at the actual returned value. This model supplies no reverse inclusion
from the old general model and no administrative transport for mapped cells.
The backend covers ordinary optional cells; generalized cells stay separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualTypedClosureReceipts (StaticMember)
open CallableIndexedOwnedContextualStoredClosureAssociationReceipts (Member)
open CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- A closure leaf carries its exact positive static member. Named and builtin leaves
retain their existing source-shaped general receipts; neither branch admits an
erased closure. The body registry is independent of outer payload metadata. -/
inductive FunctionOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | closure {function : Dynamic.Closure} {native : Value}
      {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
      (member : StaticMember headers keys bodyRegistry faults mapping world
        function native bindings parameter result) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        (FunctionValues.sourceType function) (.closure function) native
        (CallableContract.functionType parameter result)
  | global {function : Dynamic.GlobalFunction} {sourceType : TypeSystem.Ty}
      {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys
        bodyRegistry faults mapping world sourceType (.global function) native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        sourceType (.global function) native type
  | builtin {function : Dynamic.BuiltinFunction} {sourceType : TypeSystem.Ty}
      {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys
        bodyRegistry faults mapping world sourceType (.builtin function) native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        sourceType (.builtin function) native type

/-- Forward erasure preserves the original source and native value verbatim. -/
theorem FunctionOrigins.forget {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (origin : FunctionOrigins headers keys bodyRegistry faults mapping world
      sourceType source native type) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
      mapping world sourceType source native type := by
  cases origin with
  | closure member => exact member.represents
  | global related => exact related
  | builtin related => exact related

/-- Only map/world extension acts on a positive member; it does not assert that
any source or native cell still contains that member after a write. -/
def functions (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => FunctionOrigins headers keys bodyRegistry faults mapping world
  projection := fun origin =>
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).projection
      (registry := bodyRegistry) origin.forget
  runtime_hasType := fun origin =>
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
      (registry := bodyRegistry) origin.forget
  source_function := fun origin =>
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).source_function
      (registry := bodyRegistry) origin.forget
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type
      origin registries maps worlds
    cases origin with
    | closure member => exact .closure (member.extend maps worlds)
    | global related =>
        exact .global ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
          related registries maps worlds)
    | builtin related =>
        exact .builtin ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
          related registries maps worlds)

theorem functions_include_general
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (functions headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile) :=
  fun origin => origin.forget

/-- Existing payload constructors recurse over positive function leaves. -/
abbrev PayloadOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  ValueRep compiled.compatible.checked registry (functions headers keys bodyRegistry faults profile)

abbrev CellOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (functions headers keys bodyRegistry faults profile)

section Payload
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}
  {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}

/-- Attach a newly formed member to that exact value, without changing the
original formation action or its receiving model. -/
theorem payload_static_member {function : Dynamic.Closure}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result) :=
  .function (.closure member)

/-- Legacy attachment preserves its original Member hypothesis and forwards
that witness into the same static backend. -/
theorem payload_member {function : Dynamic.Closure}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : Member headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result) :=
  payload_static_member profile member.to_static

theorem PayloadOrigins.forget
    (origin : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      sourceType source native type) :
    ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
      mapping world sourceType source native type :=
  origin.map_functions (functions_include_general profile)

/-- Positive source-shape projection includes compatible raw-type wrappers.
It does not inspect an erased general-model representation. -/
theorem PayloadOrigins.closure_member
    (origin : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      sourceType source native type) :
    ∀ function, source = .closure function →
      ∃ bindings parameter result,
        StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
        type = CallableContract.functionType parameter result := by
  induction origin using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
      cases related with
      | closure member =>
          intro function same
          cases same
          exact ⟨_, _, _, member, rfl⟩
      | global related => intro function impossible; cases impossible
      | builtin related => intro function impossible; cases impossible
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
      intro function impossible
      cases impossible
  | nil | cons | empty | entry | absent | present => trivial

end Payload

section Heap
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}
  {heap after : Dynamic.Heap} {store : Store}

/-- The initial empty heap has no manufactured closure leaves. -/
theorem CellOrigins.empty :
    CellOrigins headers keys bodyRegistry registry faults profile [] [] ⟨[]⟩ [] :=
  GenericHeap.HeapRepresents.empty

theorem CellOrigins.forget
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store) :
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
      mapping world heap store :=
  CompatibleAmbientHeap.extend_definitions (functions_include_general profile)
    (.refl _) origins

/-- Real administrative allocation appends a typed native cell while preserving
all mapped source cells. No blanket administrative write premise is used. -/
theorem CellOrigins.allocate_administrative {native : Value} {type : Ty}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (typed : RuntimeValueHasType world native type compiled.indexed.layouts.definitions) :
    CellOrigins headers keys bodyRegistry registry faults profile mapping (world ++ [type])
      heap (store.allocate native).1 :=
  GenericHeap.HeapRepresents.allocate_administrative origins typed

/-- Actual source allocation and its optional payload grow both stores at their
independent lengths. Every old leaf is transported by the original generic
heap proof. -/
theorem CellOrigins.allocate
    {sourceType : TypeSystem.Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {native : Value} {payload : Ty}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (cell : GenericHeap.CellRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions headers keys bodyRegistry faults profile)) mapping world
      ⟨sourceType, sourceValue, none⟩ native payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    CellOrigins headers keys bodyRegistry registry faults profile
      (mapping ++ [store.length]) (world ++ [OptionalCell.cellType payload]) after (store.allocate native).1 ∧
    ReferenceRepresents (mapping ++ [store.length]) (world ++ [OptionalCell.cellType payload])
      location store.length payload :=
  GenericHeap.HeapRepresents.allocate origins cell allocated

/-- Only the real write and an authenticated replacement payload update a
mapped cell. The replacement may contain positive closure leaves at any depth. -/
theorem CellOrigins.write_initialized
    {location : Dynamic.Location} {target : Location} {payload : Ty}
    {cell : Dynamic.Cell} {sourceValue : Dynamic.Value} {native : Value}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (reference : ReferenceRepresents mapping world location target payload)
    (read : Dynamic.Heap.Reads heap location cell)
    (replacement : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      cell.type sourceValue native payload)
    (written : Dynamic.Heap.Writes heap location (some sourceValue) after) :
    ∃ updated, store.write? target (.inRight .unit native) = some updated ∧
      CellOrigins headers keys bodyRegistry registry faults profile mapping world after updated ∧
      AdministrativePreserved mapping store mapping updated :=
  GenericHeap.HeapRepresents.write_initialized origins reference read replacement written

/-- A real typed write to an unmapped administrative cell retains every
positive source-visible leaf. An arbitrary administrative-frame relation does
not replace these actual write, type and separation receipts. -/
theorem CellOrigins.write_administrative
    {updated : Store} {target : Location} {native : Value} {type : Ty}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (absent : ∀ {source : Nat}, mapping[source]? ≠ some target)
    (found : world[target]? = some type)
    (typed : RuntimeValueHasType world native type compiled.indexed.layouts.definitions)
    (written : store.write? target native = some updated) :
    CellOrigins headers keys bodyRegistry registry faults profile mapping world heap updated :=
  GenericHeap.HeapRepresents.write_administrative origins absent found typed written

/-- An actual initialized closure read extracts its positive static member, native
read and reference from the jointly indexed heap relation. -/
theorem CellOrigins.stored_at {location : Dynamic.Location} {function : Dynamic.Closure}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (read : Dynamic.Heap.Reads heap location
      ⟨FunctionValues.sourceType function, some (.closure function), none⟩) :
    ∃ native bindings parameter result,
      CallableIndexedOwnedContextualInitializedClosureReceipts.TypedStoredAt headers keys bodyRegistry faults
        mapping world heap store location function native bindings parameter result := by
  obtain ⟨target, value, payload, reference, nativeRead, represented⟩ := origins.read read
  cases represented with
  | initialized positive =>
      obtain ⟨bindings, parameter, result, member, sameType⟩ :=
        PayloadOrigins.closure_member profile positive function rfl
      subst payload
      exact ⟨_, bindings, parameter, result, member, target, reference, read, nativeRead⟩

end Heap

/-- A child facet belongs inside the original existential at the SAME reached
state. It retains strong cells for values and faults; successful value origins
also remain attached to that child's actual native result. -/
structure PostWithOrigins
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun _ => True) callerProtocol)
    (context : SourceSemantics.Context)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (sourceType : TypeSystem.Ty) (type : Ty)
    (outcome : Dynamic.ExpressionOutcome) (value : Value)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  admission : PostAdmission bridge context sourceType outcome reached
  cells : CellOrigins headers keys bodyRegistry registry faults profile
    index.mapping index.world index.heap index.store
  result : FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functions headers keys bodyRegistry faults profile))
    index.mapping index.world sourceType type faults outcome value

/-- Pure attachment preserves the exact caller witness and every row's own
history. The stronger child producer must establish cells and result; ordinary
PostAdmission alone cannot supply these fields. -/
theorem post_at_same_state
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun _ => True) callerProtocol)
    {context : SourceSemantics.Context}
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {sourceType : TypeSystem.Ty} {type : Ty}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)
    (post : PostAdmission bridge context sourceType outcome reached)
    (cells : CellOrigins headers keys bodyRegistry registry faults profile
      index.mapping index.world index.heap index.store)
    (result : FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions headers keys bodyRegistry faults profile))
      index.mapping index.world sourceType type faults outcome value) :
    PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile sourceType type outcome value reached :=
  ⟨post, cells, result⟩

/-- Sequential use receives the very same successful state, deep Source heap,
all stable rows and positive result payload. No alternate state is selected. -/
theorem PostWithOrigins.at_value
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    {bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun _ => True) callerProtocol}
    {context : SourceSemantics.Context}
    {profile : compiled.compatible.checked.catalog.callableContracts = true}
    {sourceType : TypeSystem.Ty} {type : Ty} {source : Dynamic.Value} {native : Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile sourceType type
      (.value source) (.inRight .word native) reached) :
    Admission bridge context reached ∧
    Dynamic.ValueHasType context index.heap source sourceType ∧
    PayloadOrigins headers keys bodyRegistry registry faults profile
      index.mapping index.world sourceType source native type := by
  have typed := post.admission.at_value
  cases post.result with
  | value represented => exact ⟨typed.2, typed.1, represented⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeOriginReadReceipts
/-! Positive callee leaves and actual initialized ordinary reads retain their
original raw Source type, native payload and reference. Compatible payload
wrappers preserve a runtime view of the original positive function leaf.
The closure branch retains its full static member; global and builtin branches retain
their original source-shaped receipts. No erased model is inverted. These pure
receipts supply no selected compiler code, generalized-cell classification,
callee execution or whole-call meaning. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeOriginReadReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualTypedClosureReceipts (StaticMember)
open CallableIndexedOwnedContextualCellOrigins

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}

/-- The raw occurrence or cell view remains separate from the retained positive
function leaf. Neither compatible raw views nor identical native carriers
identify the leaf's hidden Code or immutable owner. -/
def CalleeAt (raw : TypeSystem.Ty) (source : Dynamic.Value)
    (native : Core.Value) (type : Core.Ty) : Prop :=
  ∃ parameter result,
    SourceCoreRawMetadata.runtimeType raw =
      SourceCoreRawMetadata.runtimeType (.function parameter result) ∧
    FunctionOrigins headers keys bodyRegistry faults mapping world
      (.function parameter result) source native type

section Payload
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {raw : TypeSystem.Ty} {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty}

/-- Only the positive payload constructors and compatible wrappers are
projected. The actual Source callable variant is an independent shape receipt;
native type tags and erased general representation supply no classification. -/
theorem callable_at
    (payload : PayloadOrigins headers keys bodyRegistry registry faults profile
      mapping world raw source native type) :
    IsFunction source →
    CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := mapping) (world := world) raw source native type := by
  induction payload using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function positive => intro _; exact ⟨_, _, rfl, positive⟩
  | compatible same inner ih =>
      intro callable
      obtain ⟨parameter, result, view, positive⟩ := ih callable
      exact ⟨parameter, result, same.trans view, positive⟩
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
      intro callable
      cases callable
  | nil | cons | empty | entry | absent | present => trivial

/-- Closure classification retains the exact static member already carried by the
positive leaf, even when the original raw type has compatible wrappers. -/
theorem CalleeAt.closure_member {function : Dynamic.Closure}
    (callee : CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := mapping) (world := world) raw (.closure function) native type) :
    ∃ bindings parameter result,
      StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
      type = CallableContract.functionType parameter result ∧
      SourceCoreRawMetadata.runtimeType raw =
        SourceCoreRawMetadata.runtimeType (FunctionValues.sourceType function) := by
  obtain ⟨_, _, view, positive⟩ := callee
  cases positive with
  | closure member => exact ⟨_, _, _, member, rfl, view⟩

/-- Global classification keeps the exact original named-function receipt at
the function leaf and the independent compatible raw view. -/
theorem CalleeAt.global_receipt {function : Dynamic.GlobalFunction}
    (callee : CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := mapping) (world := world) raw (.global function) native type) :
    ∃ parameter result,
      SourceCoreRawMetadata.runtimeType raw =
        SourceCoreRawMetadata.runtimeType (.function parameter result) ∧
      CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world (.function parameter result) (.global function) native type := by
  obtain ⟨parameter, result, view, positive⟩ := callee
  cases positive with
  | global related => exact ⟨parameter, result, view, related⟩

/-- Builtins retain their original source-shaped receipt; no closure branch
or body syntax is manufactured for them. -/
theorem CalleeAt.builtin_receipt {function : Dynamic.BuiltinFunction}
    (callee : CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := mapping) (world := world) raw (.builtin function) native type) :
    ∃ parameter result,
      SourceCoreRawMetadata.runtimeType raw =
        SourceCoreRawMetadata.runtimeType (.function parameter result) ∧
      CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world (.function parameter result) (.builtin function) native type := by
  obtain ⟨parameter, result, view, positive⟩ := callee
  cases positive with
  | builtin related => exact ⟨parameter, result, view, related⟩
end Payload

section Read
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {heap : Dynamic.Heap} {store : Store}

/-- This receipt is indexed by the same actual cell, mapping, world and stores.
The raw cell type is retained rather than replaced by a closure's source type. -/
structure InitializedReadAt (location : Dynamic.Location) (raw : TypeSystem.Ty)
    (source : Dynamic.Value) (target : Core.Location) (native : Core.Value)
    (type : Core.Ty) : Prop where
  source_read : Dynamic.Heap.Reads heap location ⟨raw, some source, none⟩
  reference : ReferenceRepresents mapping world location target type
  native_read : store.read? target = some (.inRight .unit native)
  payload : PayloadOrigins headers keys bodyRegistry registry faults profile
    mapping world raw source native type

/-- One original generic heap read extracts the actual optional cell and its
positive payload. This constructs no Source or native execution. -/
theorem initialized_read_at {location : Dynamic.Location} {raw : TypeSystem.Ty}
    {source : Dynamic.Value}
    (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (read : Dynamic.Heap.Reads heap location ⟨raw, some source, none⟩) :
    ∃ target native type,
      InitializedReadAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
        (registry := registry) (faults := faults) (mapping := mapping) (world := world)
        (heap := heap) (store := store) profile location raw source target native type := by
  obtain ⟨target, optional, type, reference, nativeRead, represented⟩ := cells.read read
  cases represented with
  | initialized payload => exact ⟨target, _, type, read, reference, nativeRead, payload⟩

/-- A genuine occurrence/declaration raw view wraps only the retained payload.
The actual cell and both reads remain indexed by their original raw cell type. -/
theorem InitializedReadAt.payload_at_view
    {location : Dynamic.Location} {raw occurrence : TypeSystem.Ty}
    {source : Dynamic.Value} {target : Core.Location} {native : Core.Value} {type : Core.Ty}
    (read : InitializedReadAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (heap := heap) (store := store) profile location raw source target native type)
    (view : SourceCoreRawMetadata.runtimeType occurrence = SourceCoreRawMetadata.runtimeType raw) :
    PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      occurrence source native type :=
  .compatible view read.payload

/-- The initialized closure branch extracts its static member at this exact read,
without requiring raw = FunctionValues.sourceType function. -/
theorem InitializedReadAt.closure_member
    {location : Dynamic.Location} {raw : TypeSystem.Ty} {function : Dynamic.Closure}
    {target : Core.Location} {native : Core.Value} {type : Core.Ty}
    (read : InitializedReadAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (heap := heap) (store := store) profile location raw (.closure function) target native type) :
    ∃ bindings parameter result,
      StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
      type = CallableContract.functionType parameter result ∧
      SourceCoreRawMetadata.runtimeType raw =
        SourceCoreRawMetadata.runtimeType (FunctionValues.sourceType function) :=
  (callable_at profile read.payload (.closure function)).closure_member
end Read
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeOriginReadReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeStageReceipts
/-! Actual positive callee leaves supply their original artifact origin. Real
caller preparation then yields a user-callable Dispatch or the authentic builtin
row, whose absent user contract passes the first gate. Both paths retain the
original codebook request and physical counts. No selected hidden Code, guard
verdict, body execution law or receiving-model inverse is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeStageReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualCellOrigins
open CallableIndexedOwnedContextualCalleeOriginReadReceipts (CalleeAt)
open CallableIndexedOwnedIndirectSourceAdapters
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Only retained positive constructors are projected. Closures keep their
actual static member code/support; named and builtin branches use their real original
source-shaped leaf receipts and the actual projection-parameterized factory. -/
theorem function_origin {mapping : LocationMap} {world : StoreTyping}
    {raw : TypeSystem.Ty} {sourceValue : Dynamic.Value} {carrier : Value} {type : Ty}
    (positive : FunctionOrigins headers keys bodyRegistry faults mapping world raw sourceValue carrier type) :
    CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier := by
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  cases positive with
  | closure member =>
      exact member.stage_origin
  | global related =>
      cases related with
      | prior prior =>
          cases prior with
          | prior original =>
              cases original with
              | builtin builtin => cases builtin
              | named owner member sourceAt capture installed number projection descriptor typed =>
                  apply RecursiveStageProjection.named_origin stages.accepted descriptor
                  rw [sourceAt.retained]
                  simpa only [CallableNamedReversal.global, CallableNamedReversal.target_reverse,
                    CallableNamedMetadata.global] using sourceAt.row.target
  | builtin related =>
      cases related with
      | prior prior =>
          cases prior with
          | prior original =>
              cases original with
              | builtin builtin =>
                  cases builtin with
                  | builtin selected number descriptor typed =>
                      exact RecursiveStageProjection.builtin_origin stages.accepted descriptor _

/-- Compatible raw views retain exactly the same positive function leaf. The
occurrence's raw type does not select its hidden code or native descriptor. -/
theorem callee_origin {mapping : LocationMap} {world : StoreTyping}
    {raw : TypeSystem.Ty} {sourceValue : Dynamic.Value} {carrier : Value} {type : Ty}
    (callee : CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := mapping) (world := world) raw sourceValue carrier type) :
    CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier := by
  obtain ⟨parameter, result, _view, positive⟩ := callee
  exact function_origin positive

/-- Builtins have no user staging contract. Their exact original row retains
its full request, entry origin, native tag and absent guard independently of
physical application arity, which is checked by the second gate. -/
structure BuiltinAt (sidecar : SourceCoreStageContracts.Sidecar)
    (site : SourceCoreCallableContracts.Callsite) (callee : ExpressionId)
    (ids : List ExpressionId) (metadata : IndirectCallResolution) (node : ExpressionNode)
    (function : Dynamic.BuiltinFunction) (carrier : Value) (row : SourceCoreStageCodebook.Decision) : Prop where
  selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata node row
  entryOrigin : row.entry.origin = .builtin function.id
  uncontracted : row.entry.contract = none
  shape : ∃ raw, carrier = .pair raw (.word row.entry.id)
  unguarded : row.guard = none

/-- Authentication retains the builtin's actual physical parameter list. -/
theorem BuiltinAt.parameter_count
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
    {function : Dynamic.BuiltinFunction} {carrier : Value} {row : SourceCoreStageCodebook.Decision}
    (receipt : BuiltinAt sidecar site callee ids metadata node function carrier row) :
    row.entry.parameterCount = function.id.parameterTypes.length := by
  have authenticated := receipt.selected.authenticated
  unfold CallEntryCertificates.Authenticated at authenticated
  rw [receipt.entryOrigin] at authenticated
  generalize count : row.entry.parameterCount = actualCount at authenticated
  generalize attached : row.entry.contract = actualContract at authenticated
  cases authenticated
  rfl

/-- A user contract retains real Dispatch; the builtin alternative retains its
real unguarded row. No impossible builtin user-contract binding is asserted. -/
inductive BoundaryAt (sidecar : SourceCoreStageContracts.Sidecar)
    (site : SourceCoreCallableContracts.Callsite) (callee : ExpressionId)
    (ids : List ExpressionId) (metadata : IndirectCallResolution) (node : ExpressionNode) :
    Dynamic.Value → Value → Prop where
  | user {sourceValue : Dynamic.Value} {carrier : Value}
      (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call ids sourceValue carrier)
      (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata node dispatch.row) :
      BoundaryAt sidecar site callee ids metadata node sourceValue carrier
  | builtin {function : Dynamic.BuiltinFunction} {carrier : Value} {row : SourceCoreStageCodebook.Decision}
      (receipt : BuiltinAt sidecar site callee ids metadata node function carrier row) :
      BoundaryAt sidecar site callee ids metadata node (.builtin function) carrier

section Caller
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (unique : NodeOccurrencesUnique source)

include caller sidecarSource unique in
/-- Real caller preparation and the exact positive callee construct the actual
row at this source call. User and builtin alternatives both retain the original
Generated request from this actual same-carrier origin; no uniform
post-to-Dispatch or guard law is an input. -/
theorem boundary_at_origin {sourceValue : Dynamic.Value} {carrier : Value}
    (actualOrigin : CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier) :
    BoundaryAt sidecar prepared.site callee ids metadata compiler.original sourceValue carrier := by
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  have atSite := stages.accepted
  rw [← prepared.table] at atSite
  have contains : ContainsExpression sidecar.source prepared.site.call compiler.original := by
    rw [sidecarSource, prepared.call]
    exact lookupExpression?_sound compiler.found
  have uniqueAt : NodeOccurrencesUnique sidecar.source := sidecarSource.symm ▸ unique
  have rows := CallCodebookCertificates.rows_of_prepareWithProjection atSite caller contains compiler.originalForm
  have origin : CallableLedger.OriginRep sidecar.plan prepared.site.table sourceValue carrier := by
    have plan := (CallContractCertificates.sidecar_of_accepted caller).1
    rw [plan, prepared.table]
    exact actualOrigin
  cases origin with
  | @closure function raw entry owner occurrence active contract member entryOrigin retained provenance =>
      obtain ⟨dispatch⟩ := CallableLedger.dispatch rows
        (CallableLedger.OriginRep.closure member entryOrigin retained provenance) provenance.binds
      have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages
        prepared.table caller contains compiler.originalForm uniqueAt dispatch.found
      exact .user dispatch selected
  | @named function raw entry key contract member entryOrigin retained target contractPrepared =>
      obtain ⟨dispatch⟩ := CallableLedger.dispatch rows
        (CallableLedger.OriginRep.named member entryOrigin retained target contractPrepared)
        (CallableLedger.Binds.named target contractPrepared)
      have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages
        prepared.table caller contains compiler.originalForm uniqueAt dispatch.found
      exact .user dispatch selected
  | @builtin function raw entry member entryOrigin retained =>
      obtain ⟨ledger⟩ := rows entry member
      have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages
        prepared.table caller contains compiler.originalForm uniqueAt ledger.found
      refine .builtin ⟨selected, ?_, ?_, ?_, ledger.builtin retained⟩
      · rw [ledger.entry_eq]; exact entryOrigin
      · rw [ledger.entry_eq]; exact retained
      · refine ⟨raw, ?_⟩
        rw [ledger.entry_eq]

include caller sidecarSource unique in
/-- The positive callee projection feeds the model-independent actual origin
factory. Diagnostic-free typed formation may use boundary_at_origin directly
with its own genuine same-code origin, without rebuilding a function model. -/
theorem boundary_at_callee {mapping : LocationMap} {world : StoreTyping}
    {raw : TypeSystem.Ty} {sourceValue : Dynamic.Value} {carrier : Value} {type : Ty}
    (calleeAt : CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := mapping) (world := world) raw sourceValue carrier type) :
    BoundaryAt sidecar prepared.site callee ids metadata compiler.original sourceValue carrier :=
  boundary_at_origin compiler prepared caller sidecarSource unique (callee_origin calleeAt)

include caller sidecarSource unique in
/-- A genuine successful child post classifies its retained positive payload
and constructs the actual first-gate boundary at that same value and state.
Raw callable shape remains a genuine Source fact; no native tag supplies it. -/
theorem boundary_at_post
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    {context : SourceSemantics.Context} {index : ProtectedStateTransition.Index}
    (reached : callerProtocol.State index)
    {calleeNode : ExpressionNode} {sourceValue : Dynamic.Value} {carrier : Value}
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (shape : IsFunction sourceValue)
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile calleeNode.type compiler.calleeCode.type
      (.value sourceValue) (.inRight .word carrier) reached) :
    BoundaryAt sidecar prepared.site callee ids metadata compiler.original sourceValue carrier ∧
    CallableIndexedOwnedSourceAdmission.Admission bridge context reached ∧
    CellOrigins headers keys bodyRegistry registry faults profile
      index.mapping index.world index.heap index.store ∧
    CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (faults := faults)
      (mapping := index.mapping) (world := index.world) calleeNode.type sourceValue carrier compiler.calleeCode.type := by
  have successful := post.at_value
  have calleeAt := CallableIndexedOwnedContextualCalleeOriginReadReceipts.callable_at profile successful.2.2 shape
  exact ⟨boundary_at_callee compiler prepared caller sidecarSource unique calleeAt,
    successful.1, post.cells, calleeAt⟩
end Caller

section BuiltinGate
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {function : Dynamic.BuiltinFunction} {carrier : Value} {row : SourceCoreStageCodebook.Decision}
  (receipt : BuiltinAt sidecar site callee ids metadata node function carrier row)

include receipt

/-- The authentic absent guard fixes the original first-gate native result.
Source builtin bypass and native row acceptance remain separate retained facts. -/
theorem BuiltinAt.first_gate (unknown : Word) (actual : Environment) (store : Store) :
    Evaluates (carrier :: actual) store
      (CallableContract.dispatch site.gates .beforeArguments unknown (.second (.var 0)))
      (.inRight .word .unit) store := by
  obtain ⟨raw, shape⟩ := receipt.shape
  have read : Evaluates (carrier :: actual) store (.second (.var 0)) (.word row.entry.id) store :=
    .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some shape))
  have accepted : row.beforeArguments = .ok () := by
    simp only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer, receipt.unguarded]
  have original := site.dispatch_known .beforeArguments unknown row.entry.id row receipt.selected.found read
  rw [SourceCoreCallableContracts.reason_accepted row site.reasonAt .beforeArguments accepted] at original
  simpa only [CallableContract.resultValue] using original

/-- An actual original first-gate prefix keeps its full remaining argument/
application trace and strict budget. The failed prefix is impossible only for
this authentic builtin row; no argument or body computation is performed. -/
theorem BuiltinAt.resolve_prefix {budget : Nat} {unknown : Word} {result : Ty}
    {arguments : Expr} {actual : Environment} {calleeStore finalStore : Store} {value : Value}
    (prefixTrace : CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget site unknown result arguments
      actual calleeStore carrier value finalStore) :
    Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) site.call ids (.builtin function) ∧
    ∃ size, EvaluationSize size (.unit :: carrier :: actual) calleeStore
      (CallableIndexedOwnedStoredIndirectNativePrefix.suffix site unknown result arguments) value finalStore ∧ size < budget := by
  have accepted := receipt.first_gate unknown actual calleeStore
  cases prefixTrace with
  | failed gate strict =>
      have same := (evaluation_deterministic gate.sound accepted).1
      cases same
  | passed gate remaining gateStrict suffixStrict =>
      obtain ⟨same, stores⟩ := evaluation_deterministic gate.sound accepted
      cases same
      subst stores
      exact ⟨.builtin function, _, remaining, suffixStrict⟩
end BuiltinGate

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeStageReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualFunctionViews
/-! Contextual callable values expose their runtime types and identities through
the existing general representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualFunctionViews
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualCellOrigins (functions PayloadOrigins CellOrigins)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

theorem functions_include_general :
    (functions headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile) := by
  intro registry mapping world sourceType source native type origin
  exact CallableIndexedOwnedContextualCellOrigins.FunctionOrigins.forget origin

theorem observations :
    FunctionObservations compiled.compatible.checked.catalog
      (functions headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations keys bodyRegistry faults profile
    (registry := registry) (functions_include_general profile origin)

theorem runtime_views :
    FunctionRuntimeViews (functions headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.runtime_views keys bodyRegistry faults profile
    (registry := registry) (functions_include_general profile origin)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualFunctionViews
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginExpressionPosts
/-! Model-generic admitted expression children already retain their result,
heap and actual reached state. Under the positive receiving model those first
two fields are positive result/cell receipts. Pure attachment records them in
PostWithOrigins at the same witness; forgetting reconstructs the original
child contract. This supplies no missing formation/read/call head or mutual
body law and changes neither the protocol nor either execution grade. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginExpressionPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedContextualCellOrigins (CellOrigins PostWithOrigins post_at_same_state)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The receiving model itself carries positive closure origins through every
payload layer; an old general heap is not an input to this contract. -/
def model
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)

variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
  (certificate : GenericExpressionMeaning.Certificate)

/-- Source children retain the original input and grade and return the full
causal spine with their positive post inside the very same reached witness. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    CellOrigins headers keys bodyRegistry registry faults profile mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (model headers keys bodyRegistry registry faults profile)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          bridge context profile node.type lowered.type outcome value reached

/-- A native child keeps its measured native grade and independently returned
Source grade. No Source/native grade equality is introduced by attachment. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    CellOrigins headers keys bodyRegistry registry faults profile mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (model headers keys bodyRegistry registry faults profile)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          bridge context profile node.type lowered.type outcome value reached

/-- One actual original child producer supplies every witness. Attachment is
pure and performs no Source/native evaluation, allocation or restoration. -/
theorem preserves_at {size : Nat}
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (model headers keys bodyRegistry registry faults profile) context evidence source certificate faults size) :
    PreservesAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge profile context evidence source certificate size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments cells locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalCells,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified found sourceTyped environments cells locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalCells,
    maps, worlds, frame, metadata, reached, related,
    post_at_same_state bridge profile reached post finalCells represented⟩

/-- Reflection uses the original completed child exactly once and retains its
actual independently reconstructed Source trace and reached state. -/
theorem reflects_at {size : Nat}
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (model headers keys bodyRegistry registry faults profile) context evidence source certificate faults size) :
    ReflectsAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge profile context evidence source certificate size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments cells locals agrees typed initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalCells,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified found sourceTyped environments cells locals agrees typed initial admitted completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalCells,
    maps, worlds, frame, metadata, reached, related,
    post_at_same_state bridge profile reached post finalCells represented⟩

/-- Pure forgetting feeds the existing Tree and lexical family ports without
changing the selected reached state or weakening the receiving heap model. -/
theorem PreservesAt.forget {size : Nat}
    (meaning : PreservesAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge profile context evidence source certificate size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (model headers keys bodyRegistry registry faults profile) context evidence source certificate faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments cells locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalCells,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified found sourceTyped environments cells locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalCells,
    maps, worlds, frame, metadata, reached, related, post.admission⟩

/-- The same native/source witnesses and all original effects survive
forgetting; only the added packaging around the real post is removed. -/
theorem ReflectsAt.forget {size : Nat}
    (meaning : ReflectsAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge profile context evidence source certificate size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (model headers keys bodyRegistry registry faults profile) context evidence source certificate faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments cells locals agrees typed initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalCells,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified found sourceTyped environments cells locals agrees typed initial admitted completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalCells,
    maps, worlds, frame, metadata, reached, related, post.admission⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginExpressionPosts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginFormationReceipts
/-! One actual contextual formation returns its original source/native traces,
receiving-model value and positive Member. Formation copies the captured cells
over the incoming CellOrigins receipt, so that receipt holds again at the formed
state, where the Member is the formed closure over the copies. Forward
attachment of the Member supplies the strong payload at that actual native
value. Ordinary and principal packets retain their original authority and
history. The original Selection supplies its same-code escaped-control row; no
general-model inverse, allocation replay or body meaning is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualStoredClosureAssociationReceipts (Member)
open CallableIndexedOwnedContextualCellOrigins (PayloadOrigins CellOrigins)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (receiving : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).Includes receiving)
  (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {parentScope : SourceCoreLocalCell.Scope}
  {parentId callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {certificate : GenericExpressionMeaning.Certificate}
  (compiler : CallableIndirectCallCertificates.Receipt policy lowerBody fuel compilation source parentScope
    parentId callee ids metadata reasonAt lowered)
  {nativeContext : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler nativeContext)
  (selected : CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
    (certificate := certificate) compiler prepared code)

section Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry faults)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)

open CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation (history_at source_origin reference_index)

include inclusion cells selected prefixContext observed provenance in
/-- The original ordinary formation factory runs once over the incoming
positive cells, under its actual receiving model. The strong result, Member
and heap describe the same formed closure over the copies of its captured
cells and its original packet-derived history. -/
theorem ordinary_formation
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      receiving.Represents bodyRegistry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      Member headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      PayloadOrigins headers keys bodyRegistry registry faults profile formed.finalMap formed.finalWorld
        (FunctionValues.sourceType function) (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      CellOrigins headers keys bodyRegistry registry faults profile formed.finalMap formed.finalWorld
        formed.finalHeap formed.finalStore ∧
      FunctionCalls.ResultRepresents
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
        formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) faults
        (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding
          (history_at captured code support owner initial packet).native formed.closureActual)) := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedGeneralLambdaValues.ordinary_lambda_of_formation initial owner captured code
      (history_at captured code support owner initial packet) support
      (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) rfl profile cells copied ordinary coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
    (registry := bodyRegistry) represented
  have member : Member headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore :=
    .ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨(source_origin captured code support owner initial packet).metadata⟩
      prefixContext (observed.of_slots formed.slots) (reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.provenance_recapture provenance formed.captured)
      selected.escaped
  have payload := CallableIndexedOwnedContextualCellOrigins.payload_member (registry := registry) profile member
  exact ⟨formed, sourceTrace, nativeTrace, inclusion member.represents, determined, member, payload, formed.heaps,
    .value payload⟩

end Ordinary

section Principal
variable
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code bodyRegistry faults)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code support)

open CallableIndexedOwnedMethodLambdaFormationReceipts (history_at source_origin leading reference_index)

include inclusion cells selected packet provenance in
/-- The original principal formation factory runs once over the incoming
positive cells. Its actual leading bundle, Source origin and history stay in
the same Member, now at the formed closure over the copies of its captured
cells; a forward strong payload receipt is added at the formed heap and store. -/
theorem principal_formation
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      receiving.Represents bodyRegistry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      Member headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      PayloadOrigins headers keys bodyRegistry registry faults profile formed.finalMap formed.finalWorld
        (FunctionValues.sourceType function) (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      CellOrigins headers keys bodyRegistry registry faults profile formed.finalMap formed.finalWorld
        formed.finalHeap formed.finalStore ∧
      FunctionCalls.ResultRepresents
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
        formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) faults
        (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding
          (history_at captured code support owner initial packet).native formed.closureActual)) := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedAdmittedPrincipalLambdaFormation.principal_representation captured code support owner
      initial packet profile cells copied ordinary coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
    (registry := bodyRegistry) represented
  have leadingFormed : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    leading captured code support owner initial packet
  have member : Member headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore :=
    .principal (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support formed.captured)
      (CallableIndexedOwnedMethodLambdaValues.recaptureOrigin (source_origin captured code support owner initial packet)
        formed.captured)
      (packet.observed.of_slots formed.slots) leadingFormed (reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation.provenance_recapture provenance formed.captured)
      selected.escaped
  have payload := CallableIndexedOwnedContextualCellOrigins.payload_member (registry := registry) profile member
  exact ⟨formed, sourceTrace, nativeTrace, inclusion member.represents, determined, member, payload, formed.heaps,
    .value payload⟩

end Principal
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginFormationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginReadPosts
/-! Certified local reads use the positive receiving model directly. The
original finite producer covers initialized values, actual uninitialized faults
and real lazy mapping writes. Its result/cells and the actual protocol transport
witness are retained together with Source admission at that same reached state.
Positive callable classification projects this returned payload, including its
compatible raw view. Formation and whole indirect call branches remain separate.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginReadPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedContextualCellOrigins (CellOrigins PostWithOrigins post_at_same_state)
open CallableIndexedOwnedContextualCalleeOriginReadReceipts (CalleeAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
  {fuel : Nat} {reasonAt : ExpressionId → Word}

/-- The static read certificate retains real declaration/occurrence typing;
there is no initialized-cell or positive Member assumption in this certificate. -/
abbrev Reads (context : SourceSemantics.Context) (source : TypedSource)
    (fuel : Nat) (reasonAt : ExpressionId → Word) :=
  CompatibleExpressionReads.LoweredRead fuel (.initial compiled.compatible.checked) source context reasonAt

section Family
variable
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked)
    source context reasonAt faults)
  (unique : NodeOccurrencesUnique source)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)

include extension policies unique transport wellFormed runtime covers in
/-- One original read producer handles every actual read branch. The positive
heap is returned by that producer, including its real mapped-cell write; frame
transport is used only to construct the actual protocol endpoint. -/
theorem preserves_reads_at (size : Nat) :
    CallableIndexedOwnedContextualCellOriginExpressionPosts.PreservesAt
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge profile context evidence source (Reads (compiled := compiled) context source fuel reasonAt) size := by
  intro scope id lowered receipt node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments cells locals agrees _typed initial admitted trace
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨value, finalStore, evaluated, represented, finalCells, frame, metadata, _faultOrigin⟩ :=
    ReachedExpressionPrimitiveOutcomeProviders.read_preserves certificate
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      extension (Program.ofChecked compiled.sourceProgram) context evidence binding
      environments cells locals agrees (policies certificate binding environment before) unique trace.sound
  have actualResult : GenericExpressionMeaning.ResultRepresents
      (CallableIndexedOwnedContextualCellOriginExpressionPosts.model headers keys bodyRegistry registry faults profile)
      mapping world node.type lowered.type faults outcome value := by
    simpa only [nodeEq, typeEq, GenericExpressionMeaning.ResultRepresents,
      CallableIndexedOwnedContextualCellOriginExpressionPosts.model, SourceCoreCompatibleValues.Context.initial]
      using represented
  let reached := transport.extend initial (LocationMap.Extends.refl mapping) (WorldExtends.refl world) frame metadata
  have admittedPost := CallableIndexedOwnedSourceAdmission.after_expression_sized initial reached admitted
    wellFormed runtime covers locals sourceTyped trace frame
  exact ⟨value, finalStore, mapping, world, evaluated, actualResult, finalCells,
    .refl _, .refl _, frame, metadata, reached,
    transport.related initial (.refl _) (.refl _) frame metadata,
    post_at_same_state bridge profile reached admittedPost finalCells actualResult⟩

include extension policies unique transport wellFormed runtime covers in
/-- The actual completed read reconstructs its own independent Source grade.
No Source run is supplied to reflection, and no native evaluation is repeated
for positive classification or Source admission. -/
theorem reflects_reads_at (size : Nat) :
    CallableIndexedOwnedContextualCellOriginExpressionPosts.ReflectsAt
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge profile context evidence source (Reads (compiled := compiled) context source fuel reasonAt) size := by
  intro scope id lowered receipt node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments cells locals agrees _typed initial admitted completed
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨outcome, after, sourceTrace, represented, finalCells, frame, metadata, _faultOrigin⟩ :=
    ReachedExpressionPrimitiveOutcomeProviders.read_completed certificate
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      extension (Program.ofChecked compiled.sourceProgram) context evidence binding
      environments cells locals agrees unique (policies certificate binding environment before) completed.sound
  have actualResult : GenericExpressionMeaning.ResultRepresents
      (CallableIndexedOwnedContextualCellOriginExpressionPosts.model headers keys bodyRegistry registry faults profile)
      mapping world node.type lowered.type faults outcome value := by
    simpa only [nodeEq, typeEq, GenericExpressionMeaning.ResultRepresents,
      CallableIndexedOwnedContextualCellOriginExpressionPosts.model, SourceCoreCompatibleValues.Context.initial]
      using represented
  obtain ⟨sourceSize, trace⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size sourceTrace
  let reached := transport.extend initial (LocationMap.Extends.refl mapping) (WorldExtends.refl world) frame metadata
  have admittedPost := CallableIndexedOwnedSourceAdmission.after_expression_sized initial reached admitted
    wellFormed runtime covers locals sourceTyped trace frame
  exact ⟨sourceSize, outcome, after, mapping, world, trace, actualResult, finalCells,
    .refl _, .refl _, frame, metadata, reached,
    transport.related initial (.refl _) (.refl _) frame metadata,
    post_at_same_state bridge profile reached admittedPost finalCells actualResult⟩
end Family

section ActualView
variable {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Word} {code : Expr}
  (certificate : CompatibleExpressionReads.Certificate fuel (.initial compiled.compatible.checked)
    source scope id reason code)
  (binding : CompatibleExpressionReads.StaticBinding certificate context)

include binding in
/-- The genuine declared scheme fixes the raw cell type. Source occurrence
and declaration typing supply the runtime view used by the original read leaf;
equal native tags are not used to recover this Source fact. -/
theorem initialized_at_binding
    {location : Dynamic.Location} {raw : TypeSystem.Ty}
    {value : Dynamic.Value}
    (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (read : Dynamic.Heap.Reads heap location ⟨raw, some value, none⟩)
    (cellType : raw = certificate.declared.scheme.body) :
    ∃ target native type,
      CallableIndexedOwnedContextualCalleeOriginReadReceipts.InitializedReadAt
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
        (registry := registry) (faults := faults) (mapping := mapping) (world := world)
        (heap := heap) (store := store) profile location raw value target native type ∧
      CallableIndexedOwnedContextualCellOrigins.PayloadOrigins headers keys bodyRegistry registry faults profile
        mapping world certificate.node.type value native type := by
  obtain ⟨target, native, type, actualRead⟩ :=
    CallableIndexedOwnedContextualCalleeOriginReadReceipts.initialized_read_at profile cells read
  have view : SourceCoreRawMetadata.runtimeType certificate.node.type = SourceCoreRawMetadata.runtimeType raw :=
    binding.occurrence.trans (congrArg SourceCoreRawMetadata.runtimeType cellType).symm
  exact ⟨target, native, type, actualRead, actualRead.payload_at_view profile view⟩

include binding in
/-- Actual Source local agreement supplies the cell-type equality used above.
Both lookups and reads are aligned by their original finite uniqueness proofs;
no raw type is reconstructed from a native payload. -/
theorem initialized_at_local
    {environment : Dynamic.Environment} {location : Dynamic.Location} {raw : TypeSystem.Ty}
    {value : Dynamic.Value}
    (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    (read : Dynamic.Heap.Reads heap location ⟨raw, some value, none⟩) :
    ∃ target native type,
      CallableIndexedOwnedContextualCalleeOriginReadReceipts.InitializedReadAt
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
        (registry := registry) (faults := faults) (mapping := mapping) (world := world)
        (heap := heap) (store := store) profile location raw value target native type ∧
      CallableIndexedOwnedContextualCellOrigins.PayloadOrigins headers keys bodyRegistry registry faults profile
        mapping world certificate.node.type value native type := by
  obtain ⟨typedLocation, cell, typedLookup, typedRead, cellType, _storage⟩ := locals.lookup binding.declared
  have sameLocation := lookup.functional typedLookup
  subst typedLocation
  have sameCell := read.functional typedRead
  subst cell
  exact initialized_at_binding profile context source certificate binding cells read cellType
end ActualView

/-- At a successful callable read, classify only the actual returned positive
payload. This keeps the same reached caller, all its rows and cells, genuine raw
typing and the original Member/global/builtin alternative behind its raw view. -/
theorem callee_at_post
    {raw : TypeSystem.Ty} {type : Core.Ty} {value : Dynamic.Value} {native : Core.Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile raw type (.value value) (.inRight .word native) reached)
    (callable : IsFunction value) :
    Admission bridge context reached ∧ Dynamic.ValueHasType context index.heap value raw ∧
    CellOrigins headers keys bodyRegistry registry faults profile index.mapping index.world index.heap index.store ∧
    CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := index.mapping) (world := index.world) raw value native type := by
  obtain ⟨admitted, typed, payload⟩ := post.at_value
  exact ⟨admitted, typed, post.cells,
    CallableIndexedOwnedContextualCalleeOriginReadReceipts.callable_at profile payload callable⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginReadPosts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyFormationReceipts
/-! Full policy provenance follows the original selected producer Site through
ordinary or principal formation and exact recapture. Existing body receipts
remain the same static inputs. No policy is recovered from a body recipe. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaFormationReceipts
open CallableIndexedOwnedContextualLambdaProvenance

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : CallableIndexedNamedGeneration.Prepared checked}
  {named : Named} {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}

/-- Only the captured environment changes; all retained compiler fields are literal. -/
theorem retained_recapture {code : Code prepared function scope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (environment : Dynamic.Environment) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named
      (RecursiveNamedLambdaFormationHeads.recaptureCode
        (values := .initial checked) (indexed := prepared) code environment) := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, body, policy, sameCompilation⟩ := retained
  exact ⟨diagnostics, namedCode, compilation, rootFuel, body, policy, sameCompilation⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- An additional proof belongs to this existing ordinary Formation and Site. -/
structure OrdinaryWithPolicy
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    extends OrdinaryFormation (registry := registry) (faults := faults)
      caller context evidence scope id lowered where
  policyRecipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained caller.named site.code

/-- Principal formation retains its own dictionary and selected policy. -/
structure PrincipalWithPolicy {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    extends PrincipalFormation (registry := registry) (faults := faults)
      principal context scope id lowered where
  policyRecipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained principal.named site.code

/-- Ordinary provenance and policy refer to the same exact recaptured Code. -/
theorem OrdinaryWithPolicy.at
    {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : OrdinaryWithPolicy (registry := registry) (faults := faults)
      caller context evidence scope id lowered)
    (environment : Dynamic.Environment)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    OrdinaryAt (receipt.toOrdinaryFormation.toFormation.code environment)
      (receipt.toOrdinaryFormation.toFormation.support environment) ∧
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained caller.named
      (receipt.toOrdinaryFormation.toFormation.code environment) :=
  ⟨receipt.toOrdinaryFormation.at environment globals, retained_recapture receipt.policyRecipe environment⟩

/-- The method principal and all policy inputs survive this same recapture. -/
theorem PrincipalWithPolicy.at {method : ExecutableImplMethods.CheckedMethod}
    {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : PrincipalWithPolicy (registry := registry) (faults := faults)
      principal context scope id lowered)
    (environment : Dynamic.Environment) :
    PrincipalAt (receipt.toPrincipalFormation.toFormation.code environment)
      (receipt.toPrincipalFormation.toFormation.support environment) ∧
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained principal.named
      (receipt.toPrincipalFormation.toFormation.code environment) :=
  ⟨receipt.toPrincipalFormation.at environment, retained_recapture receipt.policyRecipe environment⟩

/-- Build the existing ordinary Formation from one actual ProducedWithPolicy.
Both its static BodyWith and retained policy belong to that original Site. -/
def ordinary_of_produced_with_policy
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : CallableIndexedOwnedContextualLambdaProducerReceipts.ProducedWithPolicy
      (compiled := compiled) caller.named parameters result statements context evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      id lowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
      expressionSyntax certificates produced.produced.site.code
      (Program.ofChecked compiled.sourceProgram) registry faults)
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.produced.site.code)
    (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.produced.site.code caller.named)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope context)
    (syntaxTree : GenericImperativeMatch.Syntax (source caller.named)
      (expressionSyntax (source caller.named)) body.context (.statements true statements) result)
    (sourceType : produced.produced.site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence []))
    (ordinary : Dynamic.OrdinaryRequirementLayout produced.produced.site.code.sourceNode.requirements
      produced.produced.site.code.sourceNode.coercions [])
    (coercions : produced.produced.site.code.sourceNode.coercions = [])
    (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller context evidence) :
    OrdinaryWithPolicy (registry := registry) (faults := faults) caller context evidence scope id lowered where
  toOrdinaryFormation := ordinary_of_producer caller produced.produced expressionSyntax certificates body bodyView bodyReasons declarations
    syntaxTree sourceType ordinary coercions callerReceipt
  policyRecipe := produced.policyRecipe

/-- The same producer attachment preserves the actual method dictionary.
No ordinary Header, new Site or accepted-policy witness is selected. -/
def principal_of_produced_with_policy {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : CallableIndexedOwnedContextualLambdaProducerReceipts.ProducedWithPolicy
      (compiled := compiled) principal.named parameters result statements context principal.dictionary scope
      (CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal) id lowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
      expressionSyntax certificates produced.produced.site.code
      (Program.ofChecked compiled.sourceProgram) registry faults)
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.produced.site.code)
    (syntaxTree : GenericImperativeMatch.Syntax (source principal.named)
      (expressionSyntax (source principal.named)) body.context (.statements true statements) result)
    (sourceType : produced.produced.site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure principal.named parameters result statements
        context principal.dictionary []))
    (ordinary : Dynamic.OrdinaryRequirementLayout produced.produced.site.code.sourceNode.requirements
      produced.produced.site.code.sourceNode.coercions [])
    (coercions : produced.produced.site.code.sourceNode.coercions = []) :
    PrincipalWithPolicy (registry := registry) (faults := faults) principal context scope id lowered where
  toPrincipalFormation := principal_of_producer principal produced.produced expressionSyntax certificates body bodyView
    syntaxTree sourceType ordinary coercions
  policyRecipe := produced.policyRecipe

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyFormationReceipts
end
