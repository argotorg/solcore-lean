import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaScalarNativeTyping

/-! The actual contextual lambda producer retains its original binder policy.
Original Source monomorphic extension then supplies every canonical binder
projection for the same returned Code. Accepted lowering alone does not
establish that Source metadata. No body execution law is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaBinderProjections
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues

/-- The genuine Source binder extension supplies its own monomorphic metadata. -/
theorem monomorphic {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner context parameters types final) :
    ∀ binder ∈ parameters, binder.scheme.quantified = [] := by
  intro binder member
  have schemes : binder.scheme ∈ parameters.map (fun item => item.scheme) := List.mem_map.mpr ⟨binder, member, rfl⟩
  rw [extended.schemes_eq] at schemes
  obtain ⟨type, _member, same⟩ := List.mem_map.mp schemes
  rw [← same]
  rfl

/-- The actual returned policy and original Source metadata identify all
selected native binder projections at this same static Site. -/
theorem Site.projected_bindings {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {captured : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (site : Site prepared named parameters result body sourceContext evidence captured scope administrative)
    (binderPolicy : site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
      ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [])
    {types : List TypeSystem.Ty} {bodyContext : SourceSemantics.Context}
    (extended : MonoBindersExtend (source named).owner sourceContext parameters types bodyContext) :
    ∀ binding ∈ site.code.receipt.loweredParameters,
      checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  have projected := CallableIndexedLambdaScalarNativeTyping.parameter_projections
    site.code.receipt.parametersCompiled binderPolicy (by rfl) (monomorphic extended)
  intro binding member
  exact CompatibleExpressionReads.projectType_of_accepted (projected binding member)

/-- Genuine accepted contextual lowering chooses the actual policy internally;
the same Site carries its original Source binder projection vector. -/
theorem of_contextual_with_projections {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
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
    {types : List TypeSystem.Ty} {bodyContext : SourceSemantics.Context}
    (extended : MonoBindersExtend (source named).owner sourceContext parameters types bodyContext)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
        ∀ binding ∈ site.code.receipt.loweredParameters, checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  obtain ⟨site, sameId, sameLowered, binderPolicy⟩ := CallableIndexedLambdaGeneration.of_contextual_with_binder
    prepared compiled record sourceContext evidence captured profile viewOfSource sourceFound sourceForm
    found form owner requirements coercions ordinary read accepted typed
  exact ⟨site, sameId, sameLowered, Site.projected_bindings site binderPolicy extended⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaBinderProjections
