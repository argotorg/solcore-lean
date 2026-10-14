import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedProducer

/-! The accepted original contextual producer chooses one Site and retains
its actual binder policy and production recipe. Later static body receipts are indexed by that same
Site; this packet has no execution callback. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProducerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaProvenance

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

structure Produced (named : Named) (parameters : List TypedBinder) (result : TypeSystem.Ty)
    (statements : List StatementId) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  site : Site compiled.indexed named parameters result statements context evidence [] scope administrative
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  binderPolicy : BinderPolicy named site.code
  recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named site.code
  compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named site.code
  issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained named site.code

/-- The policy proof is attached to the same already selected producer Site. -/
structure ProducedWithPolicy (named : Named) (parameters : List TypedBinder) (result : TypeSystem.Ty)
    (statements : List StatementId) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  produced : Produced (compiled := compiled) named parameters result statements context evidence
    scope administrative id lowered
  policyRecipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named produced.site.code

/-- One real outer bind produces the Site and all correlated policy/body fields. -/
theorem of_contextual_with_policy
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions) :
    Nonempty (ProducedWithPolicy (compiled := compiled) named parameters result body sourceContext evidence
      scope administrative id lowered) := by
  obtain ⟨site, identifier, emitted, binderPolicy, _bodyRecipe, issuedRecipe, _view, _reason⟩ :=
    CallableIndexedLambdaGeneration.of_contextual_with_issued_recipe_exact
      compiled.indexed compilation issued record sourceContext evidence [] profile viewOfSource
      sourceFound sourceForm found form owner requirements coercions ordinary read accepted typed
  let produced : Produced (compiled := compiled) named parameters result body sourceContext evidence
      scope administrative id lowered := {
    site := site
    identifier := identifier
    emitted := emitted
    binderPolicy := binderPolicy
    recipe := issuedRecipe.body_recipe
    compilerPolicy := issuedRecipe.policy_recipe
    issuedRecipe := issuedRecipe }
  exact ⟨{ produced := produced, policyRecipe := issuedRecipe.policy_recipe }⟩

/-- The original producer interface now retains its actual expression policy. -/
theorem of_contextual
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions) :
    Nonempty (Produced (compiled := compiled) named parameters result body sourceContext evidence
      scope administrative id lowered) := by
  obtain ⟨produced⟩ := of_contextual_with_policy compilation issued record sourceContext evidence
    profile viewOfSource sourceFound sourceForm found form owner requirements coercions
    ordinary read accepted typed
  exact ⟨produced.produced⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProducerReceipts
