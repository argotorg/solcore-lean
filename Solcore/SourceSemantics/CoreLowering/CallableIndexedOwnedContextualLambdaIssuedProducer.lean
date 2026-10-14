import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedRecipes

/-! The actual contextual producer retains its literal view and diagnostic
function together with the same Site and full compiler policy. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaValues

theorem of_contextual_with_issued_recipe_exact {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt prepared diagnostics)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
        site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
          ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [] ∧
        site.code.lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
          ((representation prepared).atContext named.signature.key [])
          (context prepared named).solvedRequirements compiled.own.assignments diagnostics
          (context prepared named).owner
          (SourceCoreGeneralFunctions.contextualBinder
            ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key []) ∧
        CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained named site.code ∧
        site.code.view = view ∧ site.code.reasonAt = reasonAt := by
  obtain ⟨policy, lowerBody, accepted, ⟨receipt⟩, allocationProfile, manifest, expressionProfile, callables, projector, binderPolicy, bodyRecipe, policyRecipe⟩ :=
    contextual_certificate_with_policy_recipe prepared compiled record found (form.trans sourceForm) owner requirements coercions ordinary read accepted
  obtain ⟨site, identifier, emitted, samePolicy, sameBody, sameFuel, sameView, sameReasonAt, _sourceNode, _node, _receipt⟩ :=
    of_certificate prepared sourceContext evidence captured receipt accepted profile viewOfSource
      sourceFound sourceForm found form allocationProfile manifest expressionProfile callables projector typed
  have actualBody : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compiled site.code :=
    sameBody.trans bodyRecipe
  have actualPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe
      compiled site.code.fuel site.code.policy := by
    rw [sameFuel, samePolicy]
    exact policyRecipe
  exact ⟨site, identifier, emitted,
    (congrArg SourceCoreFunctions.Policy.lowerBinder samePolicy).trans binderPolicy,
    sameBody.trans bodyRecipe,
    CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained.of_recipes
      compiled issued actualBody actualPolicy site.compilation, sameView, sameReasonAt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
